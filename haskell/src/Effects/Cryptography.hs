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

module Effects.Cryptography
  (

    Crypto

  , mkSymmetricKey
  , mkAsymmetricKey
  , signMessage
  , signEncryptMessage
  , verifyMessage
  , decryptMessage
  
  ) where

import           Polysemy
import           Polysemy.Internal (send)

import           Effects.Types



data Crypto m a where
  MkSymmetricKey :: Crypto m Key
  MkAsymmetricKey :: Crypto m (Key,Key)

  SignMessage :: Key -> Msg -> Crypto m CipherText
  SignEncryptMessage :: Key -> Key -> Msg -> Crypto m CipherText

  VerifyMessage :: Key -> CipherText -> Crypto m (Bool, Msg)
  DecryptMessage :: Key -> Key -> CipherText -> Crypto m Msg

mkSymmetricKey :: Member Crypto r => Sem r Key
mkSymmetricKey = send ( MkSymmetricKey :: Crypto (Sem r) Key )

mkAsymmetricKey :: Member Crypto r => Sem r (Key,Key)
mkAsymmetricKey = send ( MkAsymmetricKey :: Crypto (Sem r) (Key,Key) )

signMessage :: Member Crypto r => Key -> Msg -> Sem r CipherText
signMessage k msg = send ( SignMessage k msg :: Crypto (Sem r) CipherText )

signEncryptMessage :: Member Crypto r => Key -> Key -> Msg -> Sem r CipherText
signEncryptMessage k1 k2 msg = send ( SignEncryptMessage k1 k2 msg :: Crypto (Sem r) CipherText )

verifyMessage :: Member Crypto r => Key -> CipherText -> Sem r (Bool, Msg)
verifyMessage k msg = send ( VerifyMessage k msg :: Crypto (Sem r) (Bool, Msg) )

decryptMessage :: Member Crypto r => Key -> Key -> CipherText -> Sem r Msg
decryptMessage k1 k2 msg = send ( DecryptMessage k1 k2 msg :: Crypto (Sem r) Msg )
