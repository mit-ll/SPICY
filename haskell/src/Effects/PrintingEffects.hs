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

module Effects.PrintingEffects
  (

    runMessagingAsPrintLn
  , runCryptoAsPrintLn
  , printingInterpreter
  , printingInterpreterPolysemy

  ) where

import           Unsafe.Coerce
import           Data.Function ((&))

import           Polysemy

import           Effects
import           Interpreter

import           Messages
import qualified RealWorld as R

-- | This monstrosity is necessary because Coq's type system
-- is quite a bit more sophisticated than Haskell's.  We can
-- be assured that there will be no type errors, since Coq's
-- type checker has already done the work for us.
ret :: Applicative m => a -> m b
ret = pure . unsafeCoerce

runMessagingAsPrintLn :: Member (Embed IO) r
  => Sem (Messaging : r) a -> Sem r a
runMessagingAsPrintLn = interpret $ \case
  Send _ _ _ -> embed (putStrLn "Send") >> ret ()
  Recv _ _   -> embed (putStrLn "Recv") >> ret ( R.SignedCiphertext Nat 1 )

runCryptoAsPrintLn :: Member (Embed IO) r
  => Sem (Crypto : r) a -> Sem r a
runCryptoAsPrintLn = interpret $ \case
  GenRand -> embed (putStrLn "Gen") >> ret (1::Int)
  MkSymmetricKey _  -> embed (putStrLn "MkSym") >> ret (1::Int,True)
  MkAsymmetricKey _ -> embed (putStrLn "MkAsym") >> ret (1::Int,True)
  SignMessage _ _ _ _ -> embed (putStrLn "Sign") >> ret (R.SignedCiphertext Nat 1)
  SignEncryptMessage _ _ _ _ _ -> embed (putStrLn "Encrypt") >> ret (R.SignedCiphertext Nat 1)
  VerifyMessage _ _ _ -> embed (putStrLn "Verify") >> ret (True, R.Coq_message__Content 1)
  DecryptMessage _ _ -> embed (putStrLn "Decrypt") >> ret (R.Coq_message__Content 1)

printingInterpreterPolysemy :: Protocol -> IO a
printingInterpreterPolysemy p =
  protocolInterpreter p
  & runMessagingAsPrintLn
  & runCryptoAsPrintLn
  & runM

-- | Simple Interpreter to get things going.  Basically just
-- prints out the command to standard out.
--
printingInterpreter :: Protocol -> IO a
printingInterpreter (R.Return _ r) =
  putStrLn "Return" >> ret r
printingInterpreter (R.Bind _ _ cmd nxt) = 
  do
    _ <- putStrLn "Bind"
    v <- printingInterpreter cmd
    printingInterpreter (nxt (unsafeCoerce v))
printingInterpreter R.Gen =
  putStrLn "Gen" >> ret (1 :: Int)
printingInterpreter (R.Send _ _ _) =
  putStrLn "Send" >> ret ()
printingInterpreter (R.Recv _ _) =
  putStrLn "Recv" >> ret ( R.SignedCiphertext Nat 1 )
printingInterpreter (R.SignEncrypt _ _ _ _ _ ) =
  putStrLn "Encrypt" >> ret (R.SignedCiphertext Nat 1)
printingInterpreter (R.Decrypt _ _) =
  putStrLn "Decrypt" >> ret ( R.Coq_message__Content 1 )
printingInterpreter (R.Sign _ _ _ _) =
  putStrLn "Sign" >> ret (R.SignedCiphertext Nat 1)
printingInterpreter (R.Verify _ _ _) =
  putStrLn "Verify" >> ret (True, R.Coq_message__Content 1 )
printingInterpreter (R.GenerateSymKey _) =
  putStrLn "GenSym" >> ret (1 :: Int,True)
printingInterpreter (R.GenerateAsymKey _) =
  putStrLn "GenAsym" >> ret (1 :: Int,True)
