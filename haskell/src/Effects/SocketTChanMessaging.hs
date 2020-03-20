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

module Effects.SocketTChanMessaging
  (
    UserMailbox(..)
  , recvHandler
  , runMessagingWithSocket
    
  ) where

import           Unsafe.Coerce

import           Control.Concurrent.STM
import           Control.Concurrent (threadDelay)

import           Crypto.Random (MonadRandom, withDRG)

import qualified Data.Map.Strict as M
import qualified Data.Serialize as Serialize

import           Polysemy
import           Polysemy.State (State(..), get, put)

import           Effects
import           Effects.CryptoniteEffects (CryptoData(..)
                                           , RealMsgPayload(..), StoredCipher(..)
                                           , decryptMsgPayload, verifyMsgPayload
                                           , convertToRealMsg, convertFromRealMsg
                                           )
import           Effects.TChanMessaging
import qualified Network.Simple.TCP as N

import           Messages
import qualified RealWorld as R

data UserMailbox = UserMailbox {
    me :: Int
  , mailbox :: TChan QueuedMessage
  }

uidToSocket :: Int -> String
uidToSocket = show . (30000 +)

recvHandler :: Int -> TChan QueuedMessage -> IO ()
recvHandler uid mbox =
  N.serve N.HostAny (uidToSocket uid) $ \(connectionSocket, remoteAddr) -> do
       putStrLn $ "Connection established to " ++ show remoteAddr
       msg <- N.recv connectionSocket 1024
       case msg of
         Nothing -> putStrLn "Received no data"
         Just m  ->
           let (eqm :: Either String QueuedMessage) = Serialize.decode m
           in  case eqm of
                 Left err -> putStrLn $ "Error decoding: " ++ err
                 Right qm -> do
                   putStrLn "Queueing message"
                   atomically $ writeTChan mbox qm

sendToSocket :: Int -> QueuedMessage -> IO ()
sendToSocket uid qm =
  N.connect "localhost" (uidToSocket uid) $ \(connectionSocket, remoteAddr) -> do
    putStrLn $ "Connected establishted to " ++ show remoteAddr
    let msgBytes = Serialize.encode qm
    N.send connectionSocket msgBytes

-- | Here's where the action happens.  Execute each cryptographic command
-- within our DSL using /cryptonite/ primitives.  All algorithms are currently
-- hardcoded.  Future work could generalize this.
runMessagingWithSocket :: (Member (State UserMailbox) r, Member (State CryptoData) r, Member (Embed IO) r)
  => Sem (Messaging : r) a -> Sem r a
runMessagingWithSocket = interpret $ \case
  Send _ uid msg -> do
    cryptoData <- get
    let qm = convertToQueuedMessage cryptoData msg
    _ <- embed (putStrLn $ "Sending to user " ++ show uid)
    _ <- embed (sendToSocket uid qm)
    _ <- embed ( threadDelay 2000000 )
    (return . unsafeCoerce) ()

  Recv _ pat -> do
    UserMailbox{..} <- get
    cryptoData <- get
    _ <- embed ( threadDelay 1000000 )
    _ <- embed (putStrLn $ "Waiting on my mailbox " ++ show me)
    (cryptoData', qm) <- embed (recvUntilAccept cryptoData mailbox pat)
    let cryptoData'' =
          case qm of
            QueuedContent _ -> cryptoData'
            QueuedCipher cid c -> cryptoData' { ciphers = M.insert cid c (ciphers cryptoData') }
            
    _ <- put cryptoData''
    -- _ <- put userHeaps { cryptoData = cryptoData' }
    let msg = convertFromQueuedMessage qm
    (return . unsafeCoerce) msg
