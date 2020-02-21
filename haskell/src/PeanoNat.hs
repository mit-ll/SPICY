module PeanoNat where

import qualified Prelude
import qualified Datatypes

_Nat__compare :: Prelude.Int -> Prelude.Int -> Datatypes.Coq_comparison
_Nat__compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
             (\_ -> Datatypes.Eq)
             (\_ -> Datatypes.Lt)
             m)
    (\n' -> (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ -> Datatypes.Gt)
              (\m' -> _Nat__compare n' m')
              m)
    n

