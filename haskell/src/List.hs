module List where

import qualified Prelude
import qualified Datatypes

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   ([]) -> ([]);
   (:) x l' -> Datatypes.app (rev l') ((:) x ([]))}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   ([]) -> a0;
   (:) b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

filter :: (a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
filter f l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> case f x of {
                Prelude.True -> (:) x (filter f l0);
                Prelude.False -> filter f l0}}

