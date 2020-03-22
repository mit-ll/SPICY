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

module RunProto where

import           Control.Concurrent (threadDelay)
import           Control.Concurrent.Async (mapConcurrently)
import           Control.Concurrent.STM
import           Crypto.Random (MonadRandom, SystemDRG, getSystemDRG, withDRG)
import           Data.Function ((&))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Polysemy
import           Polysemy.State (evalState)

import           System.IO

import           Effects
import           Effects.CryptoniteEffects
import           Effects.TChanMessaging
import           Interpreter
import           ProtocolExtraction


import qualified Keys as KS


type Keys = [(Int,CryptoKey)]

data UserData = 
  UserData Keys Protocol

permToKey :: Map Int CryptoKey -> (Int,Bool) -> (Int,CryptoKey)
permToKey keys (kid,tf) =
  let k = keys M.! kid
  in  (kid, if tf 
            then k
            else case k of
                   AsymKey pub _ ->
                     AsymKey pub Nothing
                   _ ->
                     k)

buildCryptoData :: Keys -> IO CryptoData
buildCryptoData ks = do
  sysDrg <- getSystemDRG
  
  return CryptoData {
    ciphers = M.empty
    , keys = M.fromList ks
    , drg = sysDrg
    }

instance Show (KS.Coq_key) where
  show (KS.MkCryptoKey kid usage typ) = show kid

parseInitialData :: IO [UserData]
parseInitialData = do
  let (keys, permsProtos) = simpleSendProto
  cryptoKeysList <- traverse initKey keys
  let keyMap = M.fromList cryptoKeysList
  let permsProtos' = (\(perms,proto) -> (permToKey keyMap <$> perms , proto)) <$> permsProtos
  return $ (uncurry UserData) <$> permsProtos'


buildUserHeaps :: Int -> IO [UserHeaps]
buildUserHeaps n = do
  tchanPairs <- traverse (\i -> (i,) <$> newTChanIO) [0 .. (n-1)]
  let mboxes = M.fromList tchanPairs
  return $ (\(i,_) -> UserHeaps { me = i, mailboxes = mboxes }) <$> tchanPairs

interpreterPolysemy :: UserHeaps -> CryptoData -> Protocol -> IO a
interpreterPolysemy uh cd p =
  protocolInterpreter p
  & runCryptoWithCryptonite
  & runMessagingWithTChan
  & evalState uh
  & evalState cd
  & runM

runUser :: UserHeaps -> UserData -> IO ()
runUser heaps (UserData keys proto) = do
  let uid = me heaps
  _ <- threadDelay (uid * 500000)
  putStrLn $ "Running user: " ++ show uid
  _ <- threadDelay 500000
  cryptoData <- buildCryptoData keys
  a <- interpreterPolysemy heaps cryptoData proto

  let i :: Int = unsafeCoerce a
  putStrLn $ "User: " ++ show (me heaps) ++ " produced " ++ show i   

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "Starting"
  putStrLn "Building Initial Data..."
  userDatas <- parseInitialData
  putStrLn "Building Heaps..."
  uheaps <- buildUserHeaps (length userDatas)
  _ <- traverse (\ UserHeaps{..} -> putStrLn $ "User id: " ++ show me) uheaps

  putStrLn "Running protocol..."
  _ <- mapConcurrently (uncurry runUser) (zip uheaps userDatas)

  putStrLn "Done"
