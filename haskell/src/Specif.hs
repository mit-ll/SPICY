module Specif where

import qualified Prelude

type Coq_sig a = a
  -- singleton inductive, whose constructor was exist
  
data Coq_sigT a p =
   Coq_existT a p

