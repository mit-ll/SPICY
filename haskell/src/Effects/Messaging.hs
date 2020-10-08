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

module Effects.Messaging
  (

    Messaging(..)

  , send
  , recv

  ) where

import           Polysemy
import qualified Polysemy.Internal as P (send)

import           Effects.Types


data Messaging m a where
  Send :: Typ -> UserId -> Msg -> Messaging m ()
  Recv :: Typ -> Pattern -> Messaging m Msg

send :: Member Messaging r => Typ -> UserId -> Msg -> Sem r ()
send typ u msg = P.send ( Send typ u msg :: Messaging (Sem r) () )

recv :: Member Messaging r => Typ -> Pattern -> Sem r Msg
recv typ pat = P.send ( Recv typ pat :: Messaging (Sem r) Msg )
