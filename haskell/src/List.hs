module List where

import qualified Prelude

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

