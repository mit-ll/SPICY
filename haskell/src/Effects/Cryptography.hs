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

    Crypto(..)

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
  MkSymmetricKey :: KeyUsage -> Crypto m Permission
  MkAsymmetricKey :: KeyUsage -> Crypto m Permission

  SignMessage :: Typ -> Key -> UserId -> MsgPayload -> Crypto m Msg
  SignEncryptMessage :: Typ -> Key -> Key -> UserId -> MsgPayload -> Crypto m Msg

  VerifyMessage :: Typ -> Key -> Msg -> Crypto m (Bool, MsgPayload)
  DecryptMessage :: Typ -> Msg -> Crypto m MsgPayload

mkSymmetricKey :: Member Crypto r => KeyUsage -> Sem r Permission
mkSymmetricKey ku = send ( MkSymmetricKey ku :: Crypto (Sem r) Permission )

mkAsymmetricKey :: Member Crypto r => KeyUsage -> Sem r Permission
mkAsymmetricKey ku = send ( MkAsymmetricKey ku :: Crypto (Sem r) Permission )

signMessage :: Member Crypto r => Typ -> Key -> UserId -> MsgPayload -> Sem r Msg
signMessage typ k u msg = send ( SignMessage typ k u msg :: Crypto (Sem r) Msg )

signEncryptMessage :: Member Crypto r => Typ -> Key -> Key -> UserId -> MsgPayload -> Sem r Msg
signEncryptMessage typ k1 k2 u msg = send ( SignEncryptMessage typ k1 k2 u msg :: Crypto (Sem r) Msg )

verifyMessage :: Member Crypto r => Typ -> Key -> Msg -> Sem r (Bool, MsgPayload)
verifyMessage typ k msg = send ( VerifyMessage typ k msg :: Crypto (Sem r) (Bool, MsgPayload) )

decryptMessage :: Member Crypto r => Typ -> Msg -> Sem r MsgPayload
decryptMessage typ msg = send ( DecryptMessage typ msg :: Crypto (Sem r) MsgPayload )
