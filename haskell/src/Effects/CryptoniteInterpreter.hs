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
import           Crypto.Hash.Algorithms (SHA256(..))
-- Symmetric Signagures
import           Crypto.MAC.HMAC (HMAC(..), hmac)
-- Asymmetric Operations
import           Crypto.PubKey.RSA.PKCS15 (decryptSafer, signSafer, encrypt, verify)
import           Crypto.PubKey.RSA (PublicKey, PrivateKey, generate)
--import           Crypto.PubKey.Ed25519 (PublicKey, SecretKey, Signature, generateSecretKey, toPublic, sign, verify)
import           Crypto.Random (MonadRandom, SystemDRG, withDRG)
import           Crypto.Random.Types (getRandomBytes)

import           Data.ByteArray (ByteArray, convert)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
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

data EncMsg =
  StoredPermission ByteString ByteString
  | StoredContent ByteString
  | StoredPair EncMsg EncMsg

data StoredCipher =
  SignedCipher ByteString MsgPayload
  | EncryptedCipher ByteString EncMsg

-- | Simple utility function to create a ByteString out of anything that can
-- be converted to a String
showAsBytes :: Show a => a -> ByteString
showAsBytes = C8.pack . show

-- | Utility te pull out all data from MsgPayloads in order to build
-- up a ByteString for digital signature purposes
msgPayloadAsByteString :: MsgPayload -> ByteString
msgPayloadAsByteString (R.Coq_message__Permission (kid,tf)) =
  showAsBytes kid `BS.append` showAsBytes tf
msgPayloadAsByteString (R.Coq_message__Content i) =
  showAsBytes i
msgPayloadAsByteString (R.Coq_message__MsgPair _ _ m1 m2) =
  msgPayloadAsByteString m1 `BS.append` msgPayloadAsByteString m2

-- | Given an encryption function, convert MsgPayload into a EncMsg
mkEncCipher :: MonadRandom m =>
  (ByteString -> m ByteString) -> MsgPayload -> m EncMsg
mkEncCipher enc (R.Coq_message__Permission (kid,tf)) = do
  kid' <- (enc . showAsBytes) kid
  tf'  <- (enc . showAsBytes) tf
  return $ StoredPermission kid' tf'
mkEncCipher enc (R.Coq_message__Content i) =
  StoredContent <$> (enc . showAsBytes $ i)
mkEncCipher enc (R.Coq_message__MsgPair _ _ m1 m2) =
  do c1 <- mkEncCipher enc m1
     c2 <- mkEncCipher enc m2
     return $ StoredPair c1 c2

-- | Decrypt an EncMsg, given a decryption function
decryptCipher :: MonadRandom m => (ByteString -> m ByteString) -> EncMsg -> m MsgPayload
decryptCipher dec (StoredPermission tfenc kidenc) = do
  tf  <- (read . C8.unpack) <$> dec tfenc
  kid <- (read . C8.unpack) <$> dec kidenc
  return $ R.Coq_message__Permission (kid,tf)
decryptCipher dec (StoredContent bs) = do
  content <- dec bs
  case C8.readInt content of
    Nothing    -> error "Decrypting content didn't work"
    Just (m,_) -> return $ R.Coq_message__Content m
decryptCipher dec (StoredPair c1 c2) = do
  m1 <- decryptCipher dec c1
  m2 <- decryptCipher dec c2
  return $ R.Coq_message__MsgPair Nat Nat m1 m2 -- do I need to track types (that is, little t types?)

-- | Data structure to pass through State monad which handles redirection of
-- key ids to the actual keys, and cipher ids to the actual ciphers
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

-- | Helper for BlockCipher encryption
genRandomIV :: (MonadRandom m, BlockCipher c) => c -> m (IV c)
genRandomIV c = do
  bs :: ByteString <- getRandomBytes (blockSize c)
  return $
    case (makeIV bs) of
      Nothing -> error "Couldn't make IV"
      Just iv -> iv

-- | Build up an encryption function, given an encryption key.
-- The key determines which algorith we are using based on whether it
-- is a symmetric or asymmetric key.  In the future, we probably want
-- to abstract out the /actual/ algorithms, but that is to be left
-- for future work.
encryptFn :: MonadRandom m => CryptoKey -> ByteString -> m ByteString
encryptFn (AsymKey pub _) msg = do
  eitherMsg <- encrypt pub msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically encrypting: " ++ show e
             Right m -> m
encryptFn (SymmKey k) msg = do
  iv <- genRandomIV (undefined :: AES256)
  return $ case cipherInit k of
             CryptoFailed e -> error $ "Symmetric encrypt failed: " ++ show e
             CryptoPassed c -> ctrCombine c iv msg

-- | Build up a decryption function, given a decryption key.
-- The key determines which algorith we are using based on whether it
-- is a symmetric or asymmetric key.  In the future, we probably want
-- to abstract out the /actual/ algorithms, but that is to be left
-- for future work.
decryptFn :: MonadRandom m => CryptoKey -> ByteString -> m ByteString
decryptFn (AsymKey _ priv) msg = do
  eitherMsg <- decryptSafer priv msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically decrypting: " ++ show e
             Right m -> m
decryptFn key msg =
  encryptFn key msg

-- | Build up a digital signature function, given a key.
-- The key determines which algorith we are using based on whether it
-- is a symmetric or asymmetric key.  In the future, we probably want
-- to abstract out the /actual/ algorithms, but that is to be left
-- for future work.
signatureFn :: MonadRandom m => CryptoKey -> ByteString -> m ByteString
signatureFn (AsymKey _ priv) msg = do
  eitherMsg <- signSafer (Just SHA256) priv msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically signing: " ++ show e
             Right m -> m
signatureFn (SymmKey k) msg = do
  let hmacV :: HMAC SHA256 = hmac k msg
  return ((convert . hmacGetDigest) hmacV)

-- | Encrypt and sign a MsgPayload.  Most of the work is deferred to the helper functions
-- /signatureFn/ and /encryptFn/.  Handles ordering of encryption vs signing.
encryptMsgPayload :: MonadRandom m => CryptoKey -> CryptoKey -> MsgPayload -> m StoredCipher
encryptMsgPayload sigKey encKey msg = do
  signed <- signMsgPayload sigKey msg
  case signed of
    EncryptedCipher _ _ -> error "Cannot happen"
    SignedCipher sig _ -> do
      encMsg <- mkEncCipher (encryptFn encKey) msg
      return $ EncryptedCipher sig encMsg

-- | Encrypt and sign a MsgPayload.  Most of the work is deferred to the helper functions
-- /signatureFn/ and /decryptFn/.  Handles ordering of encryption vs signing.
decryptMsgPayload :: MonadRandom m => CryptoKey -> CryptoKey -> StoredCipher -> m MsgPayload
decryptMsgPayload sigKey encKey (SignedCipher _ _) =
  error "Already decrypted"
decryptMsgPayload sigKey encKey (EncryptedCipher sig encMsg) = do
  msg <- decryptCipher (decryptFn encKey) encMsg
  ver <- verifyMsgPayload sigKey (SignedCipher sig msg)
  return msg -- FIXME should probably only return if sig matches

-- | Sign a MsgPayload.  Most of the work is deferred to the helper function
-- /signatureFn/.  If encryption is to happen, it should happen next.
signMsgPayload :: MonadRandom m => CryptoKey -> MsgPayload -> m StoredCipher
signMsgPayload k msg = do
  sig <- signatureFn k (msgPayloadAsByteString msg)
  return $ SignedCipher sig msg

-- | Verify the signature on a message.  This function assumes that the
-- payload has already been decrypted (if it was, in fact encrypted) so
-- we error out on one branch of the case analysis.  Too bad the types
-- can't help us out a bit more.  (I guess we could make them more sophisticated,
-- but we leave that as an exercise to the reader).
verifyMsgPayload :: MonadRandom m => CryptoKey -> StoredCipher -> m Bool
verifyMsgPayload (AsymKey pub _) (SignedCipher sig msg) =
  return $ verify (Just SHA256) pub (msgPayloadAsByteString msg) sig
verifyMsgPayload (SymmKey k) (SignedCipher sig msg) = do
  let hmacV :: HMAC SHA256 = hmac k (msgPayloadAsByteString msg)
  let sig' :: ByteString   = (convert . hmacGetDigest) hmacV
  return (sig == sig')
verifyMsgPayload _ _ =
  error "Unpack your encrypted cipher first"

-- | Here's where the action happens.  Execute each cryptographic command
-- within our DSL using /cryptonite/ primitives.  All algorithms are currently
-- hardcoded.  Future work could generalize this.
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
  SignMessage _ kid _ m -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! kid
    let (cipher,drg')    = withDRG drg (signMsgPayload k m)
    let (cid,cryptData') = addCipher drg' cipher cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  SignEncryptMessage _ ksignid kencid _ m -> do
    cryptData@CryptoData{..} <- get
    let kenc  = keys M.! kencid
    let ksign = keys M.! ksignid
    let (cipher,drg')    = withDRG drg (encryptMsgPayload ksign kenc m)
    let (cid,cryptData') = addCipher drg' cipher cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  VerifyMessage _ kid (R.SignedCiphertext _ cid) -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! kid
    let cipher = ciphers M.! cid -- use (!) or explicitly case on Maybe?
    let (tf,drg')    = withDRG drg (verifyMsgPayload k cipher)
    _ <- put cryptData { drg = drg' }
    (return . unsafeCoerce) $
      case cipher of
        SignedCipher _ msg -> (tf, msg)
        _ -> error "This message is encrypted"
  VerifyMessage _ _ _ -> error "Can only verify ciphertexts"
  DecryptMessage _ (R.SignedCiphertext _ cid) -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! 1 -- FIXME
    let cipher = ciphers M.! cid -- use (!) or explicitly case on Maybe?
    let (msg,drg')    = withDRG drg (decryptMsgPayload k k cipher)
    _ <- put cryptData { drg = drg' }
    (return . unsafeCoerce) msg
  DecryptMessage _ _ -> error "Can only decrypt ciphertexts"
