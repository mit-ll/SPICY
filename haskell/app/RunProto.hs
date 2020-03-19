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

import           Control.Concurrent.STM
import           Crypto.Random (getSystemDRG)
import           Data.Function ((&))
import qualified Data.Map.Strict as M

import           Polysemy
import           Polysemy.State (evalState)


import           Effects
import           Effects.CryptoniteEffects
import           Effects.TChanMessaging
import           Interpreter
import           ProtocolExtraction

buildUserHeaps :: IO UserHeaps
buildUserHeaps = do
  mbox1 <- newTChanIO
  mbox2 <- newTChanIO

  return UserHeaps {
    me = 0
    , mailboxes = M.fromList [(0,mbox1), (1,mbox2)]
    }

buildCryptoData :: IO CryptoData
buildCryptoData = do
  drg1 <- getSystemDRG
  -- drg2 <- getSystemDRG
  
  return CryptoData {
    ciphers = M.empty
    , keys = M.fromList []
    , drg = drg1
    }
      
interpreterPolysemy :: UserHeaps -> CryptoData -> Protocol -> IO a
interpreterPolysemy uh cd p =
  protocolInterpreter p
  & runCryptoWithCryptonite
  & runMessagingWithTChan
  & evalState uh
  & evalState cd
  & runM


main :: IO ()
main = do
  uh <- buildUserHeaps
  cd <- buildCryptoData
  a <- interpreterPolysemy uh cd coq_UserProto1
  let i :: Int = unsafeCoerce a
  putStrLn $ "And we have: " ++ show i
