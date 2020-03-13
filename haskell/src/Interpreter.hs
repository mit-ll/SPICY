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

module Interpreter
  (

    printingInterpreter
  
  ) where

import           Unsafe.Coerce (unsafeCoerce)

import           Polysemy
import           Polysemy.Internal (send)

import           Effects.Types

import           RealWorld
import           Messages


ret :: a -> IO b
ret = pure . unsafeCoerce

printingInterpreter :: Coq_user_cmd -> IO a
printingInterpreter (Return _ r) =
  putStrLn "Return" >> ret r
printingInterpreter (Bind _ _ cmd nxt) = 
  do
    _ <- putStrLn "Bind"
    v <- printingInterpreter cmd
    printingInterpreter (nxt (unsafeCoerce v))
printingInterpreter Gen =
  putStrLn "Gen" >> ret 1
printingInterpreter (Send _ user_id c) =
  putStrLn "Send" >> ret ()
printingInterpreter (Recv _ _) =
  putStrLn "Recv" >> ret ( SignedCiphertext Nat 1 )
printingInterpreter (SignEncrypt _ ksign kenc uid msg) =
  putStrLn "Encrypt" >> ret (SignedCiphertext Nat 1)
printingInterpreter (Decrypt _ m) =
  putStrLn "Decrypt" >> ret ( Coq_message__Content 1 )
printingInterpreter (Sign _ ksign uid msg) =
  putStrLn "Sign" >> ret (SignedCiphertext Nat 1)
printingInterpreter (Verify _ ksign msg) =
  putStrLn "Verify" >> ret (True, Coq_message__Content 1 )
printingInterpreter (GenerateSymKey _) =
  putStrLn "GenSym" >> ret (1,True)
printingInterpreter (GenerateAsymKey _) =
  putStrLn "GenAsym" >> ret (1,True)
