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

module Effects.TChanMessaging
  (

    UserHeaps(..)
  , QueuedMessage(..)
  , convertFromQueuedMessage
  , convertToQueuedMessage
  , findKeysQueuedMsg
  , recvUntilAccept
  , runMessagingWithTChan
    
  ) where

import           Unsafe.Coerce

import           Control.Concurrent.STM
import           Control.Concurrent (threadDelay)

import qualified Data.Map.Strict as M
import           Data.Serialize (Serialize)

import           GHC.Generics

import           Polysemy
import           Polysemy.State (State(..), get, put)

import           Effects
import           Effects.ColorizedOutput
import           Effects.CryptoniteEffects (CryptoData(..), CryptoKey
                                           , RealMsgPayload(..), StoredCipher(..)
                                           , decryptMsgPayload, verifyMsgPayload
                                           , convertToRealMsg, convertFromRealMsg
                                           )

import           Messages
import qualified RealWorld as R



data QueuedMessage =
  QueuedContent !RealMsgPayload
  | QueuedCipher R.Coq_cipher_id !StoredCipher
  deriving (Show, Generic)

instance Serialize QueuedMessage

convertToQueuedMessage :: CryptoData -> Msg -> QueuedMessage
convertToQueuedMessage CryptoData{..} (R.Content _ msg) =
  QueuedContent (convertToRealMsg keys msg)
convertToQueuedMessage CryptoData{..} (R.SignedCiphertext _ cid) =
  QueuedCipher cid (ciphers M.! cid)

convertFromQueuedMessage :: QueuedMessage -> Msg
convertFromQueuedMessage (QueuedContent payload) =
  (R.Content Nat (convertFromRealMsg payload))
convertFromQueuedMessage (QueuedCipher cid _) =
  (R.SignedCiphertext Nat cid)

findKeysRealPayload :: RealMsgPayload -> [(Int,CryptoKey)]
findKeysRealPayload (PermissionPayload kid k) = [(kid,k)]
findKeysRealPayload (ContentPayload _) = []
findKeysRealPayload (PairPayload m1 m2) =
  findKeysRealPayload m1 ++ findKeysRealPayload m2

findKeysQueuedMsg :: QueuedMessage -> [(Int,CryptoKey)]
findKeysQueuedMsg (QueuedContent realPayload) =
  findKeysRealPayload realPayload
findKeysQueuedMsg (QueuedCipher _ (SignedCipher _ _ realPayload)) =
  findKeysRealPayload realPayload
findKeysQueuedMsg (QueuedCipher _ (EncryptedCipher _ _ _ _)) =
  []

type Mailboxes = M.Map Int (TChan QueuedMessage)

data UserHeaps = UserHeaps {
    me :: Int
  , mailboxes :: Mailboxes
  }

matchesPattern :: CryptoData -> Pattern -> QueuedMessage -> Bool
matchesPattern _ R.Accept _            = True
matchesPattern _ _ (QueuedContent _) = False
matchesPattern CryptoData{..} (R.Signed kid _) (QueuedCipher _ c) =
  case c of
    SignedCipher ksign _ _ ->
      ksign == kid
    _ -> False
  -- case M.lookup kid keys of
  --   Nothing -> return False
  --   Just k  -> verifyMsgPayload k c
matchesPattern CryptoData{..} (R.SignedEncrypted ksignid kencid _) (QueuedCipher _ c) =
  case c of
    EncryptedCipher ksign kenc _ _ ->
      ksign == ksignid && kenc == kencid
    _ -> False
  
  -- case (M.lookup ksignid keys, M.lookup kencid keys) of

  --   (Just ksign, Just kenc) -> do
  --     _ <- decryptMsgPayload keys c
  --     return True
      
  --   _ -> return False

recvUntilAccept :: CryptoData -> TChan QueuedMessage -> Pattern -> IO (CryptoData, QueuedMessage)
recvUntilAccept cryptoData mbox pat = do
  qm <- atomically $ readTChan mbox
  let done = matchesPattern cryptoData pat qm
  if done
    then  do
      printMessage "Processed message"
      return (cryptoData, qm)
    else do
      printErrorLn "Dropping potentially malicious message"
      recvUntilAccept cryptoData mbox pat

-- | Here's where the action happens.  Execute each cryptographic command
-- within our DSL using /cryptonite/ primitives.  All algorithms are currently
-- hardcoded.  Future work could generalize this.
runMessagingWithTChan :: (Member (State UserHeaps) r, Member (State CryptoData) r, Member (Embed IO) r)
  => Sem (Messaging : r) a -> Sem r a
runMessagingWithTChan = interpret $ \case
  Send _ uid msg -> do
    UserHeaps{..} <- get
    cryptoData <- get
    let qm = convertToQueuedMessage cryptoData msg
    let mbox = mailboxes M.! uid
    _ <- embed (putStrLn $ "Sending to user " ++ show uid)
    _ <- embed (atomically $ writeTChan mbox qm)
    _ <- embed ( threadDelay 2000000 )
    (return . unsafeCoerce) ()

  Recv _ pat -> do
    UserHeaps{..} <- get
    cryptoData <- get
    let mbox = mailboxes M.! me
    _ <- embed ( threadDelay 1000000 )
    _ <- embed (putStrLn $ "Waiting on my mailbox " ++ show me)
    (cryptoData', qm) <- embed (recvUntilAccept cryptoData mbox pat)
    let newKeys = findKeysQueuedMsg qm
    let keys' = foldr (\(kid,k) m -> M.insert kid k m) (keys cryptoData') newKeys
    let cryptoData'' =
          case qm of
            QueuedContent _ -> cryptoData' { keys = keys' }
            QueuedCipher cid c -> cryptoData' { keys = keys' ,
                                               ciphers = M.insert cid c (ciphers cryptoData') }
    _ <- put cryptoData''
    -- _ <- put userHeaps { cryptoData = cryptoData' }
    let msg = convertFromQueuedMessage qm
    (return . unsafeCoerce) msg
