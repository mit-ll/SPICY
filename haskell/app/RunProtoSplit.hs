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

module RunProtoSplit where

import           Control.Concurrent (threadDelay)
import           Control.Concurrent.Async (async)
import           Control.Concurrent.STM
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
                   AsymKey kid' pub _ ->
                     AsymKey kid' pub Nothing
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
  show (KS.MkCryptoKey kid _ _) = show kid

loadKeyFromFile :: Key -> FilePath -> IO (Key, CryptoKey)
loadKeyFromFile kid fname = do
  keyBytes <- BS.readFile fname
  case Serialize.decode keyBytes of
    Left _ -> error $ "Error reading file " ++ fname
    Right k  -> return (kid, k)

mkOrReadKey :: KS.Coq_key -> IO (Key, CryptoKey)
mkOrReadKey k@(KS.MkCryptoKey kid _ _) = do
  let fname = show kid ++ ".key"
  ex <- doesFileExist fname
  if ex
    then loadKeyFromFile kid fname
    else do
            ck <- initKey k
            _ <- BS.writeFile fname (Serialize.encode ck)
            return (getKeyId ck, ck)

buildUserMailbox :: Int -> IO UserMailbox
buildUserMailbox n = do
  mbox <- newTChanIO
  return UserMailbox { me = n, mailbox = mbox }

interpreterPolysemy :: UserMailbox -> CryptoData -> Protocol -> IO a
interpreterPolysemy um cd p =
  protocolInterpreter p
  & runCryptoWithCryptonite
  & runMessagingWithSocket
  & evalState um
  & evalState cd
  & runM

runUser :: Int -> [UserData] -> IO ()
runUser uid userDatas = do
  printMessage $ "Running user: " ++ show uid
  _ <- threadDelay (uid * 500000)
  let (UserData keys proto) = userDatas !! uid
  cryptoData <- buildCryptoData keys
  um <- buildUserMailbox uid
  thr <- async (recvHandler uid (mailbox um))
  
  a <- interpreterPolysemy um cryptoData proto
  let i :: Int = unsafeCoerce a
  printMessage $ "User: " ++ show uid ++ " produced " ++ show i

data CLI = CLI {
  user :: Int
  , proto :: String
  } deriving (Generic, Show)

instance ParseRecord CLI

parseInitialData :: String -> IO [UserData]
parseInitialData p = do
  let (keys, permsProtos) =
        case p of
          "ping" ->
            simpleSendProto
          "sharesec" ->
            shareSecretProto

  cryptoKeysList <- traverse mkOrReadKey keys
  let keyMap = M.fromList cryptoKeysList
  let permsProtos' = (\(perms,proto) -> (permToKey keyMap <$> perms , proto)) <$> permsProtos
  return $ (uncurry UserData) <$> permsProtos'

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  printInfoLn "Starting"
  CLI{..} <- getRecord "CLI"

  datas <- parseInitialData proto
  runUser user datas

  printInfoLn "Done"
