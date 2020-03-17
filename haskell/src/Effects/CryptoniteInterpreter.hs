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
import           Crypto.Random (SystemDRG, withDRG)
import           Crypto.Random.Types (getRandomBytes)

import           Data.ByteArray (ByteArray)
import           Data.ByteString (ByteString)

import           Data.Function ((&))
import qualified Data.Map.Strict as M

import           Polysemy
import           Polysemy.State (State(..), get, put)

import           Effects
import           Interpreter

import           Messages
import qualified RealWorld as R


data CryptoKey =
    SymmetricKey ByteString
  | AsymmetricKey ByteString ByteString

type StoredCipher = MsgPayload

data CryptoData = CryptoData {
    ciphers :: M.Map Int StoredCipher
  , keys    :: M.Map Int CryptoKey
  , drg     :: SystemDRG
  }

-- | Add provided cipher in the next slot
addCipher :: StoredCipher -> CryptoData -> (Int,CryptoData)
addCipher v cryptoData@CryptoData{..} =
  let k =
        case M.lookupMax ciphers of
          Nothing -> 0
          Just (k',_) -> k'
  in
    (k, cryptoData { ciphers = M.insert k v ciphers })

-- | Add provided key in the next slot
addKey :: SystemDRG -> CryptoKey -> CryptoData -> (Int,CryptoData)
addKey d v cryptoData@CryptoData{..} =
  let k =
        case M.lookupMax keys of
          Nothing -> 0
          Just (k',_) -> k'
  in
    (k, cryptoData { keys = M.insert k v keys, drg = d })


runCryptoWithCryptonite :: Member (State CryptoData) r
  => Sem (Crypto : r) a -> Sem r a
runCryptoWithCryptonite = interpret $ \case
  MkSymmetricKey _  -> do
    cryptData <- get
    -- generate the key
    let (bs, drg') = withDRG (drg cryptData) (getRandomBytes 32)
    let (k,cryptData') = addKey drg'  (SymmetricKey bs) cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (k,True)
  MkAsymmetricKey _  -> do
    cryptData <- get
    -- generate the key INCORRECT/PLACEHOLDER
    let (bs, drg') = withDRG (drg cryptData) (getRandomBytes 32)
    let (k,cryptData') = addKey drg' (AsymmetricKey bs bs) cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (k,True)
  SignMessage _ _ _ m -> do
    cryptData <- get
    let (k,cryptData') = addCipher m cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat k)
  SignEncryptMessage _ _ _ _ m -> do
    cryptData <- get
    let (k,cryptData') = addCipher m cryptData
    _ <- put cryptData'
    (return . unsafeCoerce) (R.SignedCiphertext Nat k)
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
