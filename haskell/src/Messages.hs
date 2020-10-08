module Messages where

import qualified Prelude

data Coq_type =
   Access
 | Bool
 | Nat
 | Unit
 | TPair Coq_type Coq_type

