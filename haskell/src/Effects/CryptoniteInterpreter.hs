-- DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.

-- This material is based upon work supported by the Department of the Air Force under Air Force
-- Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed
-- in this material are those of the author(s) and do not necessarily reflect the views of the
-- Department of the Air Force.

-- © 2020 Massachusetts Institute of Technology.

-- MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)

-- The software/firmware is provided to you on an As-Is basis

-- Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
-- or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
-- defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
-- as specifically authorized by the U.S. Government may violate any copyrights that exist in this work.

module Effects.CryptoniteInterpreter
  (
    CryptoData(..)
  , runCryptoWithCryptonite

  ) where

import           Unsafe.Coerce

import           Crypto.Cipher.AES (AES256)
import           Crypto.Cipher.Types (BlockCipher(..), Cipher(..), makeIV, IV(..))
import           Crypto.Error (CryptoFailable(..), CryptoError(..))
-- Symmetric Signagures
import           Crypto.MAC.HMAC (hmac)
-- Asymmetric Operations
import           Crypto.PubKey.RSA.PKCS15 (decryptSafer, signSafer, encrypt, verify)
import           Crypto.PubKey.RSA (PublicKey, PrivateKey, generate)
--import           Crypto.PubKey.Ed25519 (PublicKey, SecretKey, Signature, generateSecretKey, toPublic, sign, verify)
import           Crypto.Random (MonadRandom, SystemDRG, withDRG)
import           Crypto.Random.Types (getRandomBytes)

import           Data.ByteArray (ByteArray)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as C8

import           Data.Function ((&))
import qualified Data.Map.Strict as M

import           Polysemy
import           Polysemy.State (State(..), get, put)

import           Effects
import           Interpreter

import qualified Keys as KS
import           Messages
import qualified RealWorld as R


data CryptoKey =
    SymmKey ByteString
  | AsymKey PublicKey PrivateKey
  -- | SymmSigKey ByteString 
  -- | AsymSigKey PublicKey PrivateKey

data StoredCipher =
  StoredPermission Bool Key ByteString
  | StoredContent ByteString
  | StoredPair StoredCipher StoredCipher

strToBs :: Show a => a -> ByteString
strToBs = C8.pack . show

mkEncCipher :: MonadRandom m =>
  M.Map Int CryptoKey -> (ByteString -> m ByteString) -> MsgPayload -> m StoredCipher
mkEncCipher keys enc (R.Coq_message__Permission (kid,tf)) =
  let k = keys M.! kid
  in  StoredPermission tf kid <$>
       case k of
         SymmKey bs       -> enc bs
         AsymKey pub priv -> if tf then (enc . strToBs) priv else (enc . strToBs) pub

mkEncCipher _ enc (R.Coq_message__Content i) =
  StoredContent <$> (enc . C8.pack . show $ i)

mkEncCipher keys enc (R.Coq_message__MsgPair _ _ m1 m2) =
  do c1 <- mkEncCipher keys enc m1
     c2 <- mkEncCipher keys enc m2
     return $ StoredPair c1 c2
  
decryptCipher :: M.Map Int CryptoKey -> (ByteString -> ByteString) -> StoredCipher -> MsgPayload
decryptCipher keys dec (StoredPermission tf kid bs) =
  let k = keys M.! kid
      plain = dec bs
  in  R.Coq_message__Permission $
       case k of -- probably want to be handing around keys here, and not ids
         SymmKey _   -> (kid,True)
         AsymKey _ _ -> (kid,tf)

decryptCipher _ dec (StoredContent bs) =
  case C8.readInt (dec bs) of
    Nothing    -> error "Decrypting content didn't work"
    Just (m,_) -> R.Coq_message__Content m

decryptCipher keys dec (StoredPair c1 c2) =
  let m1 = decryptCipher keys dec c1
      m2 = decryptCipher keys dec c2
  in  R.Coq_message__MsgPair Nat Nat m1 m2 -- do I need to track types

 --  data Coq_message__Coq_message =
 --   Coq_message__Permission RW_message__Coq_access
 -- | Coq_message__Content Prelude.Int
 -- | Coq_message__MsgPair Messages.Coq_type Messages.Coq_type Coq_message__Coq_message Coq_message__Coq_message




data CryptoData = CryptoData {
    ciphers :: M.Map Int StoredCipher
  , keys    :: M.Map Int CryptoKey
  , drg     :: SystemDRG
  }

-- | Add provided cipher in the next slot
addCipher :: SystemDRG -> StoredCipher -> CryptoData -> (Int,CryptoData)
addCipher drg' cipher cryptoData@CryptoData{..} =
  let k =
        case M.lookupMax ciphers of
          Nothing -> 0
          Just (k',_) -> k'
  in 
    (k, cryptoData { ciphers = M.insert k cipher ciphers, drg = drg' })

-- | Add provided key in the next slot
addKey :: SystemDRG -> CryptoKey -> CryptoData -> (Int,CryptoData)
addKey d v cryptoData@CryptoData{..} =
  let k =
        case M.lookupMax keys of
          Nothing -> 0
          Just (k',_) -> k'
  in
    (k, cryptoData { keys = M.insert k v keys, drg = d })

genRandomIV :: (MonadRandom m, BlockCipher c) => c -> m (IV c)
genRandomIV c = do
  bs :: ByteString <- getRandomBytes (blockSize c)
  return $
    case (makeIV bs) of
      Nothing -> error "Couldn't make IV"
      Just iv -> iv

encryptMessage :: MonadRandom m => CryptoKey -> ByteString -> m ByteString
encryptMessage (AsymKey pub _) msg = do
  eitherMsg <- encrypt pub msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically encrypting: " ++ show e
             Right m -> m
encryptMessage (SymmKey k) msg = do
  iv <- genRandomIV (undefined :: AES256)
  return $ case cipherInit k of
             CryptoFailed e -> error $ "Symmetric encrypt failed: " ++ show e
             CryptoPassed c -> ctrCombine c iv msg

decryptMessage :: MonadRandom m => CryptoKey -> ByteString -> m ByteString
decryptMessage (AsymKey _ priv) msg = do
  eitherMsg <- decryptSafer priv msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically decrypting: " ++ show e
             Right m -> m
decryptMessage key msg =
  encryptMessage key msg

runCryptoWithCryptonite :: Member (State CryptoData) r
  => Sem (Crypto : r) a -> Sem r a
runCryptoWithCryptonite = interpret $ \case
  MkSymmetricKey _  -> do
    cryptData <- get
    -- generate the key (23*8 = 256 bits)
    let (bs, drg') = withDRG (drg cryptData) (getRandomBytes 32)
    let (k,cryptData') = addKey drg'  (SymmKey bs) cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (k,True)
  MkAsymmetricKey _  -> do
    cryptData <- get
    -- generate RSA pub/priv key
    let ((pub,priv), drg') = withDRG (drg cryptData) (generate 4096 0x10001)
    let (k,cryptData') = addKey drg' (AsymKey pub priv) cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (k,True)
  SignMessage _ _ _ m -> do
    cryptData@CryptoData{..} <- get
    let (cid,cryptData') = addCipher drg undefined cryptData -- FIXME
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  SignEncryptMessage _ _ kenc _ m -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! kenc
    let (cipher,drg')    = withDRG drg (mkEncCipher keys (encryptMessage k) m)
    let (cid,cryptData') = addCipher drg' cipher cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  VerifyMessage _ _ (R.SignedCiphertext _ k) -> do
    cryptData <- get
    let m = (ciphers cryptData) M.! k -- use (!) or explicitly case on Maybe?
    (return . unsafeCoerce) (True, m)
  VerifyMessage _ _ _ -> error "Can only verify ciphertexts"
  DecryptMessage _ (R.SignedCiphertext _ k) -> do
    cryptData <- get
    let m = (ciphers cryptData) M.! k -- use (!) or explicitly case on Maybe?
    (return . unsafeCoerce) m
  DecryptMessage _ _ -> error "Can only decrypt ciphertexts"
