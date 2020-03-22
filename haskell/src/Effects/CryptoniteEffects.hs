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

module Effects.CryptoniteEffects
  (
    CryptoData(..)
  , CryptoKey(..)
  , RealMsgPayload(..)
  , StoredCipher(..)
  , convertFromRealMsg
  , convertToRealMsg
  , decryptMsgPayload
  , getKeyId
  , initKey
  , runCryptoWithCryptonite
  , verifyMsgPayload
  
  ) where

import           Unsafe.Coerce

import           Crypto.Cipher.AES (AES256)
import           Crypto.Cipher.Types (BlockCipher(..), Cipher(..), makeIV, IV)
import           Crypto.Error (CryptoFailable(..))
import           Crypto.Hash.Algorithms (SHA256(..))
-- Symmetric Signagures
import           Crypto.MAC.HMAC (HMAC(..), hmac)
-- Asymmetric Operations
import           Crypto.PubKey.RSA.PKCS15 (decryptSafer, signSafer, encrypt, verify)
import           Crypto.PubKey.RSA (PublicKey(..), PrivateKey(..), generate)

import           Crypto.Random (MonadRandom, SystemDRG, withDRG)
import           Crypto.Random.Types (getRandomBytes)

-- import qualified Data.Aeson as Aeson
-- import           Data.Aeson (FromJSON, ToJSON)
import           Data.ByteArray (convert)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8
import           Data.Serialize (Serialize)
import qualified Data.Serialize as Serialize
-- import qualified Data.Text.Encoding as T

import qualified Data.Map.Strict as M

import           GHC.Generics

import           Polysemy
import           Polysemy.State (State(..), get, put)

import           Effects

import           Messages

import qualified Keys as KS
import qualified RealWorld as R


deriving instance Generic PublicKey
deriving instance Generic PrivateKey

data CryptoKey =
  SymmKey Int ByteString
  | AsymKey Int PublicKey (Maybe PrivateKey)
  deriving (Show, Generic)

getKeyId :: CryptoKey -> Int
getKeyId (SymmKey kid _) = kid
getKeyId (AsymKey kid _ _) = kid

data RealMsgPayload =
  PermissionPayload Int CryptoKey
  | ContentPayload Int
  | PairPayload RealMsgPayload RealMsgPayload
  deriving (Show, Generic)

data EncMsg =
  StoredPermission ByteString CryptoKey
  | StoredContent ByteString
  | StoredPair EncMsg EncMsg
  deriving (Show, Generic)

data StoredCipher =
  SignedCipher Int ByteString RealMsgPayload
  | EncryptedCipher Int Int ByteString EncMsg
  deriving (Show, Generic)

instance Serialize PublicKey
instance Serialize PrivateKey
instance Serialize CryptoKey
instance Serialize RealMsgPayload
instance Serialize EncMsg
instance Serialize StoredCipher

-- instance ToJSON ByteString where
--   toJSON = Aeson.toJSON . T.decodeUtf8

-- instance FromJSON ByteString where
--   parseJSON (Aeson.String s) = (pure . T.encodeUtf8) s
--   parseJSON x = error $ "Can't parse " ++ show x

-- instance ToJSON PublicKey
-- instance FromJSON PublicKey
-- instance ToJSON PrivateKey
-- instance FromJSON PrivateKey
-- instance ToJSON CryptoKey
-- instance FromJSON CryptoKey
-- instance ToJSON RealMsgPayload
-- instance FromJSON RealMsgPayload
-- instance ToJSON EncMsg
-- instance FromJSON EncMsg
-- instance ToJSON StoredCipher
-- instance FromJSON StoredCipher

-- | Simple utility function to create a ByteString out of anything that can
-- be converted to a String
showAsBytes :: Show a => a -> ByteString
showAsBytes = C8.pack . show

convertToRealMsg :: M.Map Key CryptoKey -> MsgPayload -> RealMsgPayload
convertToRealMsg keyMap (R.Coq_message__Permission (kid,tf)) =
  let k = keyMap M.! kid
  in  PermissionPayload kid $
      case k of
        SymmKey _ _ -> k
        AsymKey keyId pub _ -> if tf then k else AsymKey keyId pub Nothing
convertToRealMsg _ (R.Coq_message__Content i) =
  ContentPayload i
convertToRealMsg keyMap (R.Coq_message__MsgPair _ _ m1 m2) =
  PairPayload (convertToRealMsg keyMap m1) (convertToRealMsg keyMap m2)

convertFromRealMsg :: RealMsgPayload -> MsgPayload
convertFromRealMsg (PermissionPayload kid k) =
  let tf = case k of
             AsymKey kid _ Nothing ->
               False
             _ ->
               True
  in  R.Coq_message__Permission (kid,tf)
convertFromRealMsg (ContentPayload i) =
  R.Coq_message__Content i
convertFromRealMsg (PairPayload m1 m2) =
  R.Coq_message__MsgPair Nat Nat (convertFromRealMsg m1) (convertFromRealMsg m2)

-- | Utility te pull out all data from MsgPayloads in order to build
-- up a ByteString for digital signature purposes
msgPayloadAsByteString :: RealMsgPayload -> ByteString
msgPayloadAsByteString (PermissionPayload _ k) =
  Serialize.encode k
msgPayloadAsByteString (ContentPayload i) =
  showAsBytes i
msgPayloadAsByteString (PairPayload m1 m2) =
  msgPayloadAsByteString m1 `BS.append` msgPayloadAsByteString m2

-- | Given an encryption function, convert MsgPayload into a EncMsg
mkEncCipher :: MonadRandom m =>
  (ByteString -> m ByteString) -> RealMsgPayload -> m EncMsg
mkEncCipher enc (PermissionPayload kid k) = do
  kid' <- (enc . showAsBytes) kid
  return $ StoredPermission kid' k
mkEncCipher enc (ContentPayload i) =
  StoredContent <$> (enc . showAsBytes $ i)
mkEncCipher enc (PairPayload m1 m2) =
  do c1 <- mkEncCipher enc m1
     c2 <- mkEncCipher enc m2
     return $ StoredPair c1 c2

-- | Decrypt an EncMsg, given a decryption function
decryptCipher :: MonadRandom m => (ByteString -> m ByteString) -> EncMsg -> m RealMsgPayload
decryptCipher dec (StoredPermission kidenc k) = do
  kid <- (read . C8.unpack) <$> dec kidenc
  return $ PermissionPayload kid k
decryptCipher dec (StoredContent bs) = do
  content <- dec bs
  case C8.readInt content of
    Nothing    -> error "Decrypting content didn't work"
    Just (m,_) -> return $ ContentPayload m
decryptCipher dec (StoredPair c1 c2) = do
  m1 <- decryptCipher dec c1
  m2 <- decryptCipher dec c2
  return $ PairPayload m1 m2

-- | Data structure to pass through State monad which handles redirection of
-- key ids to the actual keys, and cipher ids to the actual ciphers
data CryptoData = CryptoData {
    ciphers :: M.Map Int StoredCipher
  , keys    :: M.Map Int CryptoKey
  , drg     :: SystemDRG
  }

-- | Add provided cipher in the next slot
addCipher :: SystemDRG -> Int -> StoredCipher -> CryptoData -> CryptoData
addCipher drg' cid cipher cryptoData@CryptoData{..} =
  cryptoData { ciphers = M.insert cid cipher ciphers, drg = drg' }

-- | Add provided key in the next slot
addKey :: SystemDRG -> Int -> CryptoKey -> CryptoData -> CryptoData
addKey d k v cryptoData@CryptoData{..} =
  cryptoData { keys = M.insert k v keys, drg = d }

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
encryptFn (AsymKey _ pub _) msg = do
  eitherMsg <- encrypt pub msg
  return $ case eitherMsg of
             Left e -> C8.pack $ "Error asymmetrically encrypting: " ++ show e
             Right m -> m
encryptFn (SymmKey _ k) msg = do
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
decryptFn (AsymKey _ _ Nothing) _ =
  error "You don't have the private key"
decryptFn (AsymKey _ _ (Just priv)) msg = do
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
signatureFn (AsymKey _ _ Nothing) _ =
  error "You don't have the private key"
signatureFn (AsymKey _ _ (Just priv)) msg = do
  eitherMsg <- signSafer (Just SHA256) priv msg
  return $ case eitherMsg of
             Left e -> error $ "Error asymmetrically signing: " ++ show e
             Right m -> m
signatureFn (SymmKey _ k) msg = do
  let hmacV :: HMAC SHA256 = hmac k msg
  return ((convert . hmacGetDigest) hmacV)

-- | Encrypt and sign a MsgPayload.  Most of the work is deferred to the helper functions
-- /signatureFn/ and /encryptFn/.  Handles ordering of encryption vs signing.
encryptMsgPayload :: MonadRandom m => CryptoKey -> CryptoKey -> RealMsgPayload -> m StoredCipher
encryptMsgPayload sigKey encKey msg = do
  signed <- signMsgPayload sigKey msg
  case signed of
    EncryptedCipher _ _ _ _ -> error "Cannot happen"
    SignedCipher _ sig _ -> do
      encMsg <- mkEncCipher (encryptFn encKey) msg
      return $ EncryptedCipher (getKeyId sigKey) (getKeyId encKey) sig encMsg

-- | Encrypt and sign a MsgPayload.  Most of the work is deferred to the helper functions
-- /signatureFn/ and /decryptFn/.  Handles ordering of encryption vs signing.
decryptMsgPayload :: MonadRandom m => M.Map Int CryptoKey -> StoredCipher -> m RealMsgPayload
decryptMsgPayload _ (SignedCipher _ _ _) =
  error "Already decrypted"
decryptMsgPayload keys (EncryptedCipher ksignid kencid sig encMsg) = do
  let sigKey = keys M.! ksignid
  let encKey = keys M.! kencid
  msg <- decryptCipher (decryptFn encKey) encMsg
  _ <- verifyMsgPayload sigKey (SignedCipher (getKeyId sigKey) sig msg)
  return msg -- FIXME should probably only return if sig matches

-- | Sign a MsgPayload.  Most of the work is deferred to the helper function
-- /signatureFn/.  If encryption is to happen, it should happen next.
signMsgPayload :: MonadRandom m =>  CryptoKey -> RealMsgPayload -> m StoredCipher
signMsgPayload k msg = do
  sig <- signatureFn k (msgPayloadAsByteString msg)
  return $ SignedCipher (getKeyId k) sig msg

-- | Verify the signature on a message.  This function assumes that the
-- payload has already been decrypted (if it was, in fact encrypted) so
-- we error out on one branch of the case analysis.  Too bad the types
-- can't help us out a bit more.  (I guess we could make them more sophisticated,
-- but we leave that as an exercise to the reader).
verifyMsgPayload :: MonadRandom m => CryptoKey -> StoredCipher -> m Bool
verifyMsgPayload (AsymKey _ pub _) (SignedCipher _ sig msg) =
  return $ verify (Just SHA256) pub (msgPayloadAsByteString msg) sig
verifyMsgPayload (SymmKey _ k) (SignedCipher _ sig msg) = do
  let hmacV :: HMAC SHA256 = hmac k (msgPayloadAsByteString msg)
  let sig' :: ByteString   = (convert . hmacGetDigest) hmacV
  return (sig == sig')
verifyMsgPayload _ _ =
  error "Unpack your encrypted cipher first"

initKey :: MonadRandom m => KS.Coq_key -> m CryptoKey
initKey (KS.MkCryptoKey kid _ kt) = mkKey kid kt

-- | Helper keygen for initialization
mkKey :: MonadRandom m => Key -> KS.Coq_key_type -> m CryptoKey
mkKey kid KS.SymKey = do
  -- generate the key (23*8 = 256 bits)
  bs <- getRandomBytes 32
  return $ SymmKey kid bs
mkKey kid KS.AsymKey = do
  -- generate RSA pub/priv key
  (pub,priv) <- generate 512 0x10001
  return $ AsymKey kid pub (Just priv)

nextKey :: M.Map Int a -> Int
nextKey m =
  case M.lookupMax m of
    Nothing -> 0
    Just (k,_) -> k+10
 
-- | Here's where the action happens.  Execute each cryptographic command
-- within our DSL using /cryptonite/ primitives.  All algorithms are currently
-- hardcoded.  Future work could generalize this.
runCryptoWithCryptonite :: Member (State CryptoData) r
  => Sem (Crypto : r) a -> Sem r a
runCryptoWithCryptonite = interpret $ \case
  MkSymmetricKey _  -> do
    cryptData@CryptoData{..} <- get
    let kid = nextKey keys
    let (k, drg') = withDRG drg (mkKey kid KS.SymKey)
    _ <- put $ addKey drg' kid k cryptData
    (return . unsafeCoerce) (kid,True)
  MkAsymmetricKey _  -> do
    cryptData@CryptoData{..} <- get
    let kid = nextKey keys
    let (k, drg') = withDRG drg (mkKey kid KS.AsymKey)
    _ <- put $ addKey drg' kid k cryptData
    (return . unsafeCoerce) (kid,True)
  SignMessage _ kid _ m -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! kid
    let msg = convertToRealMsg keys m
    let cid = nextKey ciphers
    let (cipher,drg')    = withDRG drg (signMsgPayload k msg)
    _ <- put $ addCipher drg' cid cipher cryptData
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  SignEncryptMessage _ ksignid kencid _ m -> do
    cryptData@CryptoData{..} <- get
    let ksign = keys M.! ksignid
    let kenc  = keys M.! kencid
    -- let kenc = case M.lookup kencid keys of
    --              Nothing -> ksign
    --              Just k  -> k
    let msg = convertToRealMsg keys m
    let cid = nextKey ciphers
    let (cipher,drg')    = withDRG drg (encryptMsgPayload ksign kenc msg)
    _ <- put $ addCipher drg' cid cipher cryptData
    (return . unsafeCoerce) (R.SignedCiphertext Nat cid)
  VerifyMessage _ kid (R.SignedCiphertext _ cid) -> do
    cryptData@CryptoData{..} <- get
    let k = keys M.! kid
    let cipher = ciphers M.! cid -- use (!) or explicitly case on Maybe?
    let (tf,drg')    = withDRG drg (verifyMsgPayload k cipher)
    _ <- put cryptData { drg = drg' }
    (return . unsafeCoerce) $
      case cipher of
        SignedCipher _ _ msg -> (tf, convertFromRealMsg msg)
        _ -> error "This message is encrypted"
  VerifyMessage _ _ _ -> error "Can only verify ciphertexts"
  DecryptMessage _ (R.SignedCiphertext _ cid) -> do
    cryptData@CryptoData{..} <- get
    let cipher = ciphers M.! cid -- use (!) or explicitly case on Maybe?
    let (msg,drg')    = withDRG drg (decryptMsgPayload keys cipher)
    _ <- put cryptData { drg = drg' }
    (return . unsafeCoerce . convertFromRealMsg) msg
  DecryptMessage _ _ -> error "Can only decrypt ciphertexts"
