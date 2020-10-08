module OrderedTypeEx where

import qualified Prelude
import qualified Datatypes
import qualified OrderedType
import qualified PeanoNat

_Nat_as_OT__compare :: Prelude.Int -> Prelude.Int -> OrderedType.Compare Prelude.Int
_Nat_as_OT__compare x y =
  case PeanoNat._Nat__compare x y of {
   Datatypes.Eq -> OrderedType.EQ;
   Datatypes.Lt -> OrderedType.LT;
   Datatypes.Gt -> OrderedType.GT}

_Nat_as_OT__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_Nat_as_OT__eq_dec =
  (Prelude.==)

