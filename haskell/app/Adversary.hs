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

module Adversary where

import           Control.Concurrent (threadDelay)
import           Control.Concurrent.Async
import           Control.Concurrent.STM
import           Control.Monad (when, forever)
import           Crypto.Random (MonadRandom, SystemDRG, getSystemDRG, withDRG)
import qualified Data.ByteString as BS
import           Data.Function ((&))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Serialize as Serialize

import           Polysemy
import           Polysemy.State (evalState)

import           Options.Generic
import           System.Directory (doesFileExist)
import           System.IO

import           Effects
import           Effects.ColorizedOutput
import           Effects.CryptoniteEffects
import           Effects.SocketTChanMessaging
import           Effects.TChanMessaging


import qualified RealWorld as R
import qualified Keys as KS


-- buildCryptoData ks = do
--   sysDrg <- getSystemDRG
  
--   return CryptoData {
--     ciphers = M.empty
--     , keys = M.fromList ks
--     , drg = sysDrg
--     }

-- instance Show (KS.Coq_key) where
--   show (KS.MkCryptoKey kid _ _) = show kid

data CLI = CLI {
  port :: Int
  , usrs :: [Int]
  } deriving (Generic, Show)

instance ParseRecord CLI


main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  printInfoLn "Starting"

  CLI{..} <- getRecord "CLI"

  bchan <- newBroadcastTChanIO
  socketRecvThr <- async $ recvHandler port bchan
  mbox <- atomically (dupTChan bchan)
  keys <- newTVarIO M.empty

  recvThread <- async $ forever $ do
    qm <- atomically $ readTChan mbox
    let newKeys = findKeysQueuedMsg qm

    when (newKeys /= []) $ do
      printMessage "Reading unencrypted keys out of message:"
      _ <- traverse (\(kid,_) -> printMessage $ "Key id : " ++ show kid) newKeys
      atomically (modifyTVar keys (\ks -> foldr (\(kid,k) m -> M.insert kid k m) ks newKeys))

    case qm of
      QueuedContent payload -> printMessage (show payload)
      QueuedCipher _ c -> printMessage "Ciphertext"

  sendThread <- async $ forever $ do
    let m = ContentPayload 100
    ksig <- mkKey 1 KS.AsymKey
    c <- signMsgPayload ksig m
    let qm = QueuedCipher 1 c

    printMessage $ "Sending to users: " ++ show usrs

    traverse (\uid -> sendToSocket uid qm) usrs

  _ <- waitEither recvThread sendThread
  printInfoLn "Done"
