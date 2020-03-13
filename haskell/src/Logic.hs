module Logic where

import qualified Prelude

coq_False_rect :: a1
coq_False_rect =
  Prelude.error "absurd case"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

