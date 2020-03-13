{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Maps where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified OrderedType
import qualified OrderedTypeEx
import qualified PeanoNat

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type NatMap__Map__Raw__MX__TO__Coq_t = Prelude.Int

_NatMap__Map__Raw__MX__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__MX__eq_dec =
  OrderedTypeEx._Nat_as_OT__eq_dec

_NatMap__Map__Raw__MX__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__MX__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False)
    (OrderedTypeEx._Nat_as_OT__compare x y)

_NatMap__Map__Raw__MX__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__MX__eqb x y =
  case _NatMap__Map__Raw__MX__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type NatMap__Map__Raw__PX__MO__TO__Coq_t = Prelude.Int

_NatMap__Map__Raw__PX__MO__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__PX__MO__eq_dec =
  OrderedTypeEx._Nat_as_OT__eq_dec

_NatMap__Map__Raw__PX__MO__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__PX__MO__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False)
    (OrderedTypeEx._Nat_as_OT__compare x y)

_NatMap__Map__Raw__PX__MO__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__Raw__PX__MO__eqb x y =
  case _NatMap__Map__Raw__PX__MO__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type NatMap__Map__Raw__Coq_key = Prelude.Int

type NatMap__Map__Raw__Coq_t elt = ([]) ((,) Prelude.Int elt)

_NatMap__Map__Raw__empty :: NatMap__Map__Raw__Coq_t a1
_NatMap__Map__Raw__empty =
  ([])

_NatMap__Map__Raw__is_empty :: (NatMap__Map__Raw__Coq_t a1) -> Prelude.Bool
_NatMap__Map__Raw__is_empty l =
  case l of {
   ([]) -> Prelude.True;
   (:) _ _ -> Prelude.False}

_NatMap__Map__Raw__mem :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Bool
_NatMap__Map__Raw__mem k s =
  case s of {
   ([]) -> Prelude.False;
   (:) p l ->
    case p of {
     (,) k' _ ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> Prelude.False;
       OrderedType.EQ -> Prelude.True;
       OrderedType.GT -> _NatMap__Map__Raw__mem k l}}}

data NatMap__Map__Raw__R_mem elt =
   NatMap__Map__Raw__R_mem_0 (NatMap__Map__Raw__Coq_t elt)
 | NatMap__Map__Raw__R_mem_1 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_mem_2 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_mem_3 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) Prelude.Bool 
 (NatMap__Map__Raw__R_mem elt)

_NatMap__Map__Raw__coq_R_mem_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                     ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                     a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                     a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                     (NatMap__Map__Raw__R_mem a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t a1) ->
                                     Prelude.Bool -> (NatMap__Map__Raw__R_mem a1) -> a2
_NatMap__Map__Raw__coq_R_mem_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Map__Raw__R_mem_0 s -> f s __;
   NatMap__Map__Raw__R_mem_1 s k' _x l -> f0 s k' _x l __ __ __;
   NatMap__Map__Raw__R_mem_2 s k' _x l -> f1 s k' _x l __ __ __;
   NatMap__Map__Raw__R_mem_3 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (_NatMap__Map__Raw__coq_R_mem_rect k f f0 f1 f2 l _res r0)}

_NatMap__Map__Raw__coq_R_mem_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                    ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                    ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                    a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2)
                                    -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                    ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                    (NatMap__Map__Raw__R_mem a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t a1) ->
                                    Prelude.Bool -> (NatMap__Map__Raw__R_mem a1) -> a2
_NatMap__Map__Raw__coq_R_mem_rec =
  _NatMap__Map__Raw__coq_R_mem_rect

_NatMap__Map__Raw__mem_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                               ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                               () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                               ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                               Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) ->
                               (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__mem_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> Prelude.False;
      (:) p l ->
       case p of {
        (,) k' _ ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> Prelude.False;
          OrderedType.EQ -> Prelude.True;
          OrderedType.GT -> _NatMap__Map__Raw__mem k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      ([]) -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {f8 = \_ _ -> let {hrec = _NatMap__Map__Raw__mem_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Map__Raw__mem k s)

_NatMap__Map__Raw__mem_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                              ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                              () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                              ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                              Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) ->
                              (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__mem_rec =
  _NatMap__Map__Raw__mem_rect

_NatMap__Map__Raw__coq_R_mem_correct :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Bool ->
                                        NatMap__Map__Raw__R_mem a1
_NatMap__Map__Raw__coq_R_mem_correct k s _res =
  unsafeCoerce _NatMap__Map__Raw__mem_rect k (\y _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Map__Raw__R_mem_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Map__Raw__R_mem_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.True (NatMap__Map__Raw__R_mem_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r (_NatMap__Map__Raw__mem k y2) (NatMap__Map__Raw__R_mem_3 y y0 y1 y2
      (_NatMap__Map__Raw__mem k y2) (y6 (_NatMap__Map__Raw__mem k y2) __)) z) s _res __

_NatMap__Map__Raw__find :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Maybe a1
_NatMap__Map__Raw__find k s =
  case s of {
   ([]) -> Prelude.Nothing;
   (:) p s' ->
    case p of {
     (,) k' x ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> Prelude.Nothing;
       OrderedType.EQ -> Prelude.Just x;
       OrderedType.GT -> _NatMap__Map__Raw__find k s'}}}

data NatMap__Map__Raw__R_find elt =
   NatMap__Map__Raw__R_find_0 (NatMap__Map__Raw__Coq_t elt)
 | NatMap__Map__Raw__R_find_1 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_find_2 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_find_3 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (Prelude.Maybe
                                                                                                         elt) 
 (NatMap__Map__Raw__R_find elt)

_NatMap__Map__Raw__coq_R_find_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                      ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                      a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                      a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe a1) ->
                                      (NatMap__Map__Raw__R_find a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t 
                                      a1) -> (Prelude.Maybe a1) -> (NatMap__Map__Raw__R_find a1) -> a2
_NatMap__Map__Raw__coq_R_find_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Map__Raw__R_find_0 s -> f s __;
   NatMap__Map__Raw__R_find_1 s k' x s' -> f0 s k' x s' __ __ __;
   NatMap__Map__Raw__R_find_2 s k' x s' -> f1 s k' x s' __ __ __;
   NatMap__Map__Raw__R_find_3 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (_NatMap__Map__Raw__coq_R_find_rect k f f0 f1 f2 s' _res r0)}

_NatMap__Map__Raw__coq_R_find_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                     ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                     a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                     a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe a1) ->
                                     (NatMap__Map__Raw__R_find a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t 
                                     a1) -> (Prelude.Maybe a1) -> (NatMap__Map__Raw__R_find a1) -> a2
_NatMap__Map__Raw__coq_R_find_rec =
  _NatMap__Map__Raw__coq_R_find_rect

_NatMap__Map__Raw__find_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 ->
                                a2) -> (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__find_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> Prelude.Nothing;
      (:) p s' ->
       case p of {
        (,) k' x ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> Prelude.Nothing;
          OrderedType.EQ -> Prelude.Just x;
          OrderedType.GT -> _NatMap__Map__Raw__find k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      ([]) -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {f8 = \_ _ -> let {hrec = _NatMap__Map__Raw__find_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Map__Raw__find k s)

_NatMap__Map__Raw__find_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                               ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                               () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                               ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                               Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) ->
                               (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__find_rec =
  _NatMap__Map__Raw__find_rect

_NatMap__Map__Raw__coq_R_find_correct :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) -> (Prelude.Maybe
                                         a1) -> NatMap__Map__Raw__R_find a1
_NatMap__Map__Raw__coq_R_find_correct k s _res =
  unsafeCoerce _NatMap__Map__Raw__find_rect k (\y _ z _ ->
    Logic.eq_rect_r Prelude.Nothing (NatMap__Map__Raw__R_find_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.Nothing (NatMap__Map__Raw__R_find_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r (Prelude.Just y1) (NatMap__Map__Raw__R_find_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r (_NatMap__Map__Raw__find k y2) (NatMap__Map__Raw__R_find_3 y y0 y1 y2
      (_NatMap__Map__Raw__find k y2) (y6 (_NatMap__Map__Raw__find k y2) __)) z) s _res __

_NatMap__Map__Raw__add :: NatMap__Map__Raw__Coq_key -> a1 -> (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__Coq_t
                          a1
_NatMap__Map__Raw__add k x s =
  case s of {
   ([]) -> (:) ((,) k x) ([]);
   (:) p l ->
    case p of {
     (,) k' y ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> (:) ((,) k x) s;
       OrderedType.EQ -> (:) ((,) k x) l;
       OrderedType.GT -> (:) ((,) k' y) (_NatMap__Map__Raw__add k x l)}}}

data NatMap__Map__Raw__R_add elt =
   NatMap__Map__Raw__R_add_0 (NatMap__Map__Raw__Coq_t elt)
 | NatMap__Map__Raw__R_add_1 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_add_2 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_add_3 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (NatMap__Map__Raw__Coq_t
                                                                                                        elt) 
 (NatMap__Map__Raw__R_add elt)

_NatMap__Map__Raw__coq_R_add_rect :: NatMap__Map__Raw__Coq_key -> a1 -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2)
                                     -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                     a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                     a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                     ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Map__Raw__Coq_t a1) ->
                                     (NatMap__Map__Raw__R_add a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t a1) ->
                                     (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__R_add a1) -> a2
_NatMap__Map__Raw__coq_R_add_rect k x f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Map__Raw__R_add_0 s -> f s __;
   NatMap__Map__Raw__R_add_1 s k' y l -> f0 s k' y l __ __ __;
   NatMap__Map__Raw__R_add_2 s k' y l -> f1 s k' y l __ __ __;
   NatMap__Map__Raw__R_add_3 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (_NatMap__Map__Raw__coq_R_add_rect k x f f0 f1 f2 l _res r0)}

_NatMap__Map__Raw__coq_R_add_rec :: NatMap__Map__Raw__Coq_key -> a1 -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                    ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                    ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                    a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2)
                                    -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                    ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Map__Raw__Coq_t a1) ->
                                    (NatMap__Map__Raw__R_add a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t a1) ->
                                    (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__R_add a1) -> a2
_NatMap__Map__Raw__coq_R_add_rec =
  _NatMap__Map__Raw__coq_R_add_rect

_NatMap__Map__Raw__add_rect :: NatMap__Map__Raw__Coq_key -> a1 -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                               ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                               () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                               ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                               Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) ->
                               (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__add_rect k x f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> (:) ((,) k x) ([]);
      (:) p l ->
       case p of {
        (,) k' y ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> (:) ((,) k x) s;
          OrderedType.EQ -> (:) ((,) k x) l;
          OrderedType.GT -> (:) ((,) k' y) (_NatMap__Map__Raw__add k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      ([]) -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {f8 = \_ _ -> let {hrec = _NatMap__Map__Raw__add_rect k x f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Map__Raw__add k x s)

_NatMap__Map__Raw__add_rec :: NatMap__Map__Raw__Coq_key -> a1 -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                              ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                              () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                              ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                              Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) ->
                              (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__add_rec =
  _NatMap__Map__Raw__add_rect

_NatMap__Map__Raw__coq_R_add_correct :: NatMap__Map__Raw__Coq_key -> a1 -> (NatMap__Map__Raw__Coq_t a1) ->
                                        (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__R_add a1
_NatMap__Map__Raw__coq_R_add_correct k x s _res =
  _NatMap__Map__Raw__add_rect k x (\y _ z _ -> Logic.eq_rect_r ((:) ((,) k x) ([])) (NatMap__Map__Raw__R_add_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> Logic.eq_rect_r ((:) ((,) k x) y) (NatMap__Map__Raw__R_add_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> Logic.eq_rect_r ((:) ((,) k x) y2) (NatMap__Map__Raw__R_add_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r ((:) ((,) y0 y1) (_NatMap__Map__Raw__add k x y2)) (NatMap__Map__Raw__R_add_3 y y0 y1 y2
      (_NatMap__Map__Raw__add k x y2) (y6 (_NatMap__Map__Raw__add k x y2) __)) z) s _res __

_NatMap__Map__Raw__remove :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__Coq_t a1
_NatMap__Map__Raw__remove k s =
  case s of {
   ([]) -> ([]);
   (:) p l ->
    case p of {
     (,) k' x ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> s;
       OrderedType.EQ -> l;
       OrderedType.GT -> (:) ((,) k' x) (_NatMap__Map__Raw__remove k l)}}}

data NatMap__Map__Raw__R_remove elt =
   NatMap__Map__Raw__R_remove_0 (NatMap__Map__Raw__Coq_t elt)
 | NatMap__Map__Raw__R_remove_1 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_remove_2 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Map__Raw__R_remove_3 (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (NatMap__Map__Raw__Coq_t
                                                                                                           elt) 
 (NatMap__Map__Raw__R_remove elt)

_NatMap__Map__Raw__coq_R_remove_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                        ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                        ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                        a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                        a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                        ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Map__Raw__Coq_t 
                                        a1) -> (NatMap__Map__Raw__R_remove a1) -> a2 -> a2) ->
                                        (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) ->
                                        (NatMap__Map__Raw__R_remove a1) -> a2
_NatMap__Map__Raw__coq_R_remove_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Map__Raw__R_remove_0 s -> f s __;
   NatMap__Map__Raw__R_remove_1 s k' x l -> f0 s k' x l __ __ __;
   NatMap__Map__Raw__R_remove_2 s k' x l -> f1 s k' x l __ __ __;
   NatMap__Map__Raw__R_remove_3 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (_NatMap__Map__Raw__coq_R_remove_rect k f f0 f1 f2 l _res r0)}

_NatMap__Map__Raw__coq_R_remove_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                       ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                       a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () ->
                                       a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Map__Raw__Coq_t a1) ->
                                       (NatMap__Map__Raw__R_remove a1) -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t 
                                       a1) -> (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__R_remove a1) -> a2
_NatMap__Map__Raw__coq_R_remove_rec =
  _NatMap__Map__Raw__coq_R_remove_rect

_NatMap__Map__Raw__remove_rect :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                  ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1))
                                  -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                  (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                  a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 ->
                                  a2) -> (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__remove_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> ([]);
      (:) p l ->
       case p of {
        (,) k' x ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> s;
          OrderedType.EQ -> l;
          OrderedType.GT -> (:) ((,) k' x) (_NatMap__Map__Raw__remove k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      ([]) -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {f8 = \_ _ -> let {hrec = _NatMap__Map__Raw__remove_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Map__Raw__remove k s)

_NatMap__Map__Raw__remove_rec :: NatMap__Map__Raw__Coq_key -> ((NatMap__Map__Raw__Coq_t a1) -> () -> a2) ->
                                 ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1))
                                 -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                 (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                 a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 ->
                                 a2) -> (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__remove_rec =
  _NatMap__Map__Raw__remove_rect

_NatMap__Map__Raw__coq_R_remove_correct :: NatMap__Map__Raw__Coq_key -> (NatMap__Map__Raw__Coq_t a1) ->
                                           (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__R_remove a1
_NatMap__Map__Raw__coq_R_remove_correct k s _res =
  unsafeCoerce _NatMap__Map__Raw__remove_rect k (\y _ z _ ->
    Logic.eq_rect_r ([]) (NatMap__Map__Raw__R_remove_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r y (NatMap__Map__Raw__R_remove_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r y2 (NatMap__Map__Raw__R_remove_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r ((:) ((,) y0 y1) (_NatMap__Map__Raw__remove k y2)) (NatMap__Map__Raw__R_remove_3 y y0 y1 y2
      (_NatMap__Map__Raw__remove k y2) (y6 (_NatMap__Map__Raw__remove k y2) __)) z) s _res __

_NatMap__Map__Raw__elements :: (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__Coq_t a1
_NatMap__Map__Raw__elements m =
  m

_NatMap__Map__Raw__fold :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t a1) -> a2 -> a2
_NatMap__Map__Raw__fold f m acc =
  case m of {
   ([]) -> acc;
   (:) p m' -> case p of {
                (,) k e -> _NatMap__Map__Raw__fold f m' (f k e acc)}}

data NatMap__Map__Raw__R_fold elt a =
   NatMap__Map__Raw__R_fold_0 (NatMap__Map__Raw__Coq_t elt) a
 | NatMap__Map__Raw__R_fold_1 (NatMap__Map__Raw__Coq_t elt) a Prelude.Int elt (([]) ((,) Prelude.Int elt)) a 
 (NatMap__Map__Raw__R_fold elt a)

_NatMap__Map__Raw__coq_R_fold_rect :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                      a1) -> a2 -> () -> a3) -> ((NatMap__Map__Raw__Coq_t a1) -> a2 -> Prelude.Int
                                      -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a2 -> (NatMap__Map__Raw__R_fold
                                      a1 a2) -> a3 -> a3) -> (NatMap__Map__Raw__Coq_t a1) -> a2 -> a2 ->
                                      (NatMap__Map__Raw__R_fold a1 a2) -> a3
_NatMap__Map__Raw__coq_R_fold_rect f f0 f1 _ _ _ r =
  case r of {
   NatMap__Map__Raw__R_fold_0 m acc -> f0 m acc __;
   NatMap__Map__Raw__R_fold_1 m acc k e m' _res r0 ->
    f1 m acc k e m' __ _res r0 (_NatMap__Map__Raw__coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)}

_NatMap__Map__Raw__coq_R_fold_rec :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                     a1) -> a2 -> () -> a3) -> ((NatMap__Map__Raw__Coq_t a1) -> a2 -> Prelude.Int ->
                                     a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a2 -> (NatMap__Map__Raw__R_fold 
                                     a1 a2) -> a3 -> a3) -> (NatMap__Map__Raw__Coq_t a1) -> a2 -> a2 ->
                                     (NatMap__Map__Raw__R_fold a1 a2) -> a3
_NatMap__Map__Raw__coq_R_fold_rec =
  _NatMap__Map__Raw__coq_R_fold_rect

_NatMap__Map__Raw__fold_rect :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> a2
                                -> () -> a3) -> ((NatMap__Map__Raw__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> (([])
                                ((,) Prelude.Int a1)) -> () -> a3 -> a3) -> (NatMap__Map__Raw__Coq_t a1) -> a2 -> a3
_NatMap__Map__Raw__fold_rect f1 f0 f m acc =
  Logic.eq_rect_r
    (case m of {
      ([]) -> acc;
      (:) p m' -> case p of {
                   (,) k e -> _NatMap__Map__Raw__fold f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      ([]) -> f2 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f4 = f3 t0 e l __} in let {hrec = _NatMap__Map__Raw__fold_rect f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (_NatMap__Map__Raw__fold f1 m acc)

_NatMap__Map__Raw__fold_rec :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> a2
                               -> () -> a3) -> ((NatMap__Map__Raw__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> (([])
                               ((,) Prelude.Int a1)) -> () -> a3 -> a3) -> (NatMap__Map__Raw__Coq_t a1) -> a2 -> a3
_NatMap__Map__Raw__fold_rec =
  _NatMap__Map__Raw__fold_rect

_NatMap__Map__Raw__coq_R_fold_correct :: (NatMap__Map__Raw__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Map__Raw__Coq_t
                                         a1) -> a2 -> a2 -> NatMap__Map__Raw__R_fold a1 a2
_NatMap__Map__Raw__coq_R_fold_correct f m acc _res =
  _NatMap__Map__Raw__fold_rect f (\y y0 _ z _ -> Logic.eq_rect_r y0 (NatMap__Map__Raw__R_fold_0 y y0) z)
    (\y y0 y1 y2 y3 _ y5 z _ ->
    Logic.eq_rect_r (_NatMap__Map__Raw__fold f y3 (f y1 y2 y0)) (NatMap__Map__Raw__R_fold_1 y y0 y1 y2 y3
      (_NatMap__Map__Raw__fold f y3 (f y1 y2 y0)) (y5 (_NatMap__Map__Raw__fold f y3 (f y1 y2 y0)) __)) z) m acc _res
    __

_NatMap__Map__Raw__equal :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t
                            a1) -> Prelude.Bool
_NatMap__Map__Raw__equal cmp m m' =
  case m of {
   ([]) -> case m' of {
            ([]) -> Prelude.True;
            (:) _ _ -> Prelude.False};
   (:) p l ->
    case p of {
     (,) x e ->
      case m' of {
       ([]) -> Prelude.False;
       (:) p0 l' ->
        case p0 of {
         (,) x' e' ->
          case OrderedTypeEx._Nat_as_OT__compare x x' of {
           OrderedType.EQ -> (Prelude.&&) (cmp e e') (_NatMap__Map__Raw__equal cmp l l');
           _ -> Prelude.False}}}}}

data NatMap__Map__Raw__R_equal elt =
   NatMap__Map__Raw__R_equal_0 (NatMap__Map__Raw__Coq_t elt) (NatMap__Map__Raw__Coq_t elt)
 | NatMap__Map__Raw__R_equal_1 (NatMap__Map__Raw__Coq_t elt) (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([])
                                                                                                           ((,)
                                                                                                           Prelude.Int
                                                                                                           elt)) 
 Prelude.Int elt (([]) ((,) Prelude.Int elt)) Prelude.Bool (NatMap__Map__Raw__R_equal elt)
 | NatMap__Map__Raw__R_equal_2 (NatMap__Map__Raw__Coq_t elt) (NatMap__Map__Raw__Coq_t elt) Prelude.Int elt (([])
                                                                                                           ((,)
                                                                                                           Prelude.Int
                                                                                                           elt)) 
 Prelude.Int elt (([]) ((,) Prelude.Int elt)) (OrderedType.Compare Prelude.Int)
 | NatMap__Map__Raw__R_equal_3 (NatMap__Map__Raw__Coq_t elt) (NatMap__Map__Raw__Coq_t elt) (NatMap__Map__Raw__Coq_t
                                                                                           elt) (NatMap__Map__Raw__Coq_t
                                                                                                elt)

_NatMap__Map__Raw__coq_R_equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                       (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                       a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                       (NatMap__Map__Raw__R_equal a1) -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                       a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                                       ((,) Prelude.Int a1)) -> () -> (OrderedType.Compare Prelude.Int) -> () -> ()
                                       -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) ->
                                       (NatMap__Map__Raw__Coq_t a1) -> () -> (NatMap__Map__Raw__Coq_t a1) -> () ->
                                       () -> a2) -> (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t 
                                       a1) -> Prelude.Bool -> (NatMap__Map__Raw__R_equal a1) -> a2
_NatMap__Map__Raw__coq_R_equal_rect cmp f f0 f1 f2 _ _ _ r =
  case r of {
   NatMap__Map__Raw__R_equal_0 m m' -> f m m' __ __;
   NatMap__Map__Raw__R_equal_1 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0 (_NatMap__Map__Raw__coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0);
   NatMap__Map__Raw__R_equal_2 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   NatMap__Map__Raw__R_equal_3 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

_NatMap__Map__Raw__coq_R_equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                      (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                      a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                      (NatMap__Map__Raw__R_equal a1) -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                      a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                                      ((,) Prelude.Int a1)) -> () -> (OrderedType.Compare Prelude.Int) -> () -> ()
                                      -> a2) -> ((NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) ->
                                      (NatMap__Map__Raw__Coq_t a1) -> () -> (NatMap__Map__Raw__Coq_t a1) -> () -> ()
                                      -> a2) -> (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) ->
                                      Prelude.Bool -> (NatMap__Map__Raw__R_equal a1) -> a2
_NatMap__Map__Raw__coq_R_equal_rec =
  _NatMap__Map__Raw__coq_R_equal_rect

_NatMap__Map__Raw__equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                 (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                 a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                 ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                 () -> () -> () -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                 (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                 () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () ->
                                 (OrderedType.Compare Prelude.Int) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t
                                 a1) -> (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) -> () ->
                                 (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> (NatMap__Map__Raw__Coq_t 
                                 a1) -> (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__equal_rect cmp f2 f1 f0 f m m' =
  Logic.eq_rect_r
    (case m of {
      ([]) -> case m' of {
               ([]) -> Prelude.True;
               (:) _ _ -> Prelude.False};
      (:) p l ->
       case p of {
        (,) x e ->
         case m' of {
          ([]) -> Prelude.False;
          (:) p0 l' ->
           case p0 of {
            (,) x' e' ->
             case OrderedTypeEx._Nat_as_OT__compare x x' of {
              OrderedType.EQ -> (Prelude.&&) (cmp e e') (_NatMap__Map__Raw__equal cmp l l');
              _ -> Prelude.False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      ([]) -> let {f9 = f3 __} in case m' of {
                                   ([]) -> f9 __;
                                   (:) _ _ -> f8 __};
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          ([]) -> f8 __;
          (:) p0 l0 ->
           case p0 of {
            (,) t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = OrderedTypeEx._Nat_as_OT__compare t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {f14 = \_ _ -> let {hrec = _NatMap__Map__Raw__equal_rect cmp f2 f1 f0 f l l0} in f13 __ __ hrec} in
             case OrderedTypeEx._Nat_as_OT__compare t0 t1 of {
              OrderedType.EQ -> f14 __ __;
              _ -> f12 __}}}}}) (_NatMap__Map__Raw__equal cmp m m')

_NatMap__Map__Raw__equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t 
                                a1) -> (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                () -> () -> () -> a2 -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                (NatMap__Map__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> (OrderedType.Compare
                                Prelude.Int) -> () -> () -> a2) -> ((NatMap__Map__Raw__Coq_t a1) ->
                                (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a1) -> () ->
                                (NatMap__Map__Raw__Coq_t a1) -> () -> () -> a2) -> (NatMap__Map__Raw__Coq_t 
                                a1) -> (NatMap__Map__Raw__Coq_t a1) -> a2
_NatMap__Map__Raw__equal_rec =
  _NatMap__Map__Raw__equal_rect

_NatMap__Map__Raw__coq_R_equal_correct :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Map__Raw__Coq_t a1) ->
                                          (NatMap__Map__Raw__Coq_t a1) -> Prelude.Bool -> NatMap__Map__Raw__R_equal
                                          a1
_NatMap__Map__Raw__coq_R_equal_correct cmp m m' _res =
  _NatMap__Map__Raw__equal_rect cmp (\y y0 _ _ z _ ->
    Logic.eq_rect_r Prelude.True (NatMap__Map__Raw__R_equal_0 y y0) z) (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    Logic.eq_rect_r ((Prelude.&&) (cmp y2 y6) (_NatMap__Map__Raw__equal cmp y3 y7)) (NatMap__Map__Raw__R_equal_1 y
      y0 y1 y2 y3 y5 y6 y7 (_NatMap__Map__Raw__equal cmp y3 y7) (y11 (_NatMap__Map__Raw__equal cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Map__Raw__R_equal_2 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> Logic.eq_rect_r Prelude.False (NatMap__Map__Raw__R_equal_3 y y0 y1 y3) z) m m' _res __

_NatMap__Map__Raw__map :: (a1 -> a2) -> (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__Coq_t a2
_NatMap__Map__Raw__map f m =
  case m of {
   ([]) -> ([]);
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f e)) (_NatMap__Map__Raw__map f m')}}

_NatMap__Map__Raw__mapi :: (NatMap__Map__Raw__Coq_key -> a1 -> a2) -> (NatMap__Map__Raw__Coq_t a1) ->
                           NatMap__Map__Raw__Coq_t a2
_NatMap__Map__Raw__mapi f m =
  case m of {
   ([]) -> ([]);
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f k e)) (_NatMap__Map__Raw__mapi f m')}}

_NatMap__Map__Raw__option_cons :: NatMap__Map__Raw__Coq_key -> (Prelude.Maybe a1) -> (([])
                                  ((,) NatMap__Map__Raw__Coq_key a1)) -> ([]) ((,) NatMap__Map__Raw__Coq_key a1)
_NatMap__Map__Raw__option_cons k o l =
  case o of {
   Prelude.Just e -> (:) ((,) k e) l;
   Prelude.Nothing -> l}

_NatMap__Map__Raw__map2_l :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) ->
                             (NatMap__Map__Raw__Coq_t a1) -> NatMap__Map__Raw__Coq_t a3
_NatMap__Map__Raw__map2_l f m =
  case m of {
   ([]) -> ([]);
   (:) p l ->
    case p of {
     (,) k e ->
      _NatMap__Map__Raw__option_cons k (f (Prelude.Just e) Prelude.Nothing) (_NatMap__Map__Raw__map2_l f l)}}

_NatMap__Map__Raw__map2_r :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) ->
                             (NatMap__Map__Raw__Coq_t a2) -> NatMap__Map__Raw__Coq_t a3
_NatMap__Map__Raw__map2_r f m' =
  case m' of {
   ([]) -> ([]);
   (:) p l' ->
    case p of {
     (,) k e' ->
      _NatMap__Map__Raw__option_cons k (f Prelude.Nothing (Prelude.Just e')) (_NatMap__Map__Raw__map2_r f l')}}

_NatMap__Map__Raw__map2 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) ->
                           (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a2) -> NatMap__Map__Raw__Coq_t
                           a3
_NatMap__Map__Raw__map2 f m =
  case m of {
   ([]) -> _NatMap__Map__Raw__map2_r f;
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       map2_aux m' =
         case m' of {
          ([]) -> _NatMap__Map__Raw__map2_l f m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case OrderedTypeEx._Nat_as_OT__compare k k' of {
              OrderedType.LT ->
               _NatMap__Map__Raw__option_cons k (f (Prelude.Just e) Prelude.Nothing)
                 (_NatMap__Map__Raw__map2 f l m');
              OrderedType.EQ ->
               _NatMap__Map__Raw__option_cons k (f (Prelude.Just e) (Prelude.Just e'))
                 (_NatMap__Map__Raw__map2 f l l');
              OrderedType.GT ->
               _NatMap__Map__Raw__option_cons k' (f Prelude.Nothing (Prelude.Just e')) (map2_aux l')}}}}
      in map2_aux}}

_NatMap__Map__Raw__combine :: (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a2) ->
                              NatMap__Map__Raw__Coq_t ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
_NatMap__Map__Raw__combine m =
  case m of {
   ([]) -> _NatMap__Map__Raw__map (\e' -> (,) Prelude.Nothing (Prelude.Just e'));
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       combine_aux m' =
         case m' of {
          ([]) -> _NatMap__Map__Raw__map (\e0 -> (,) (Prelude.Just e0) Prelude.Nothing) m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case OrderedTypeEx._Nat_as_OT__compare k k' of {
              OrderedType.LT -> (:) ((,) k ((,) (Prelude.Just e) Prelude.Nothing)) (_NatMap__Map__Raw__combine l m');
              OrderedType.EQ -> (:) ((,) k ((,) (Prelude.Just e) (Prelude.Just e')))
               (_NatMap__Map__Raw__combine l l');
              OrderedType.GT -> (:) ((,) k' ((,) Prelude.Nothing (Prelude.Just e'))) (combine_aux l')}}}}
      in combine_aux}}

_NatMap__Map__Raw__fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> (([]) ((,) a1 a2)) -> a3 -> a3
_NatMap__Map__Raw__fold_right_pair f l i =
  List.fold_right (\p -> f (Datatypes.fst p) (Datatypes.snd p)) i l

_NatMap__Map__Raw__map2_alt :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) ->
                               (NatMap__Map__Raw__Coq_t a1) -> (NatMap__Map__Raw__Coq_t a2) -> ([])
                               ((,) NatMap__Map__Raw__Coq_key a3)
_NatMap__Map__Raw__map2_alt f m m' =
  let {m0 = _NatMap__Map__Raw__combine m m'} in
  let {m1 = _NatMap__Map__Raw__map (\p -> f (Datatypes.fst p) (Datatypes.snd p)) m0} in
  _NatMap__Map__Raw__fold_right_pair _NatMap__Map__Raw__option_cons m1 ([])

_NatMap__Map__Raw__at_least_one :: (Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe
                                   ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
_NatMap__Map__Raw__at_least_one o o' =
  case o of {
   Prelude.Just _ -> Prelude.Just ((,) o o');
   Prelude.Nothing -> case o' of {
                       Prelude.Just _ -> Prelude.Just ((,) o o');
                       Prelude.Nothing -> Prelude.Nothing}}

_NatMap__Map__Raw__at_least_one_then_f :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) ->
                                          (Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3
_NatMap__Map__Raw__at_least_one_then_f f o o' =
  case o of {
   Prelude.Just _ -> f o o';
   Prelude.Nothing -> case o' of {
                       Prelude.Just _ -> f o o';
                       Prelude.Nothing -> Prelude.Nothing}}

type NatMap__Map__E__Coq_t = Prelude.Int

_NatMap__Map__E__compare :: Prelude.Int -> Prelude.Int -> OrderedType.Compare Prelude.Int
_NatMap__Map__E__compare x y =
  case PeanoNat._Nat__compare x y of {
   Datatypes.Eq -> OrderedType.EQ;
   Datatypes.Lt -> OrderedType.LT;
   Datatypes.Gt -> OrderedType.GT}

_NatMap__Map__E__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Map__E__eq_dec =
  (Prelude.==)

type NatMap__Map__Coq_key = Prelude.Int

type NatMap__Map__Coq_slist elt =
  NatMap__Map__Raw__Coq_t elt
  -- singleton inductive, whose constructor was Build_slist
  
_NatMap__Map__this :: (NatMap__Map__Coq_slist a1) -> NatMap__Map__Raw__Coq_t a1
_NatMap__Map__this s =
  s

type NatMap__Map__Coq_t elt = NatMap__Map__Coq_slist elt

_NatMap__Map__empty :: NatMap__Map__Coq_t a1
_NatMap__Map__empty =
  _NatMap__Map__Raw__empty

_NatMap__Map__is_empty :: (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__Map__is_empty m =
  _NatMap__Map__Raw__is_empty (_NatMap__Map__this m)

_NatMap__Map__add :: NatMap__Map__Coq_key -> a1 -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__Map__add x e m =
  _NatMap__Map__Raw__add x e (_NatMap__Map__this m)

_NatMap__Map__find :: NatMap__Map__Coq_key -> (NatMap__Map__Coq_t a1) -> Prelude.Maybe a1
_NatMap__Map__find x m =
  _NatMap__Map__Raw__find x (_NatMap__Map__this m)

_NatMap__Map__remove :: NatMap__Map__Coq_key -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__Map__remove x m =
  _NatMap__Map__Raw__remove x (_NatMap__Map__this m)

_NatMap__Map__mem :: NatMap__Map__Coq_key -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__Map__mem x m =
  _NatMap__Map__Raw__mem x (_NatMap__Map__this m)

_NatMap__Map__map :: (a1 -> a2) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a2
_NatMap__Map__map f m =
  _NatMap__Map__Raw__map f (_NatMap__Map__this m)

_NatMap__Map__mapi :: (NatMap__Map__Coq_key -> a1 -> a2) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a2
_NatMap__Map__mapi f m =
  _NatMap__Map__Raw__mapi f (_NatMap__Map__this m)

_NatMap__Map__map2 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Map__Coq_t 
                      a1) -> (NatMap__Map__Coq_t a2) -> NatMap__Map__Coq_t a3
_NatMap__Map__map2 f m m' =
  _NatMap__Map__Raw__map2 f (_NatMap__Map__this m) (_NatMap__Map__this m')

_NatMap__Map__elements :: (NatMap__Map__Coq_t a1) -> ([]) ((,) NatMap__Map__Coq_key a1)
_NatMap__Map__elements m =
  _NatMap__Map__Raw__elements (_NatMap__Map__this m)

_NatMap__Map__cardinal :: (NatMap__Map__Coq_t a1) -> Prelude.Int
_NatMap__Map__cardinal m =
  Datatypes.length (_NatMap__Map__this m)

_NatMap__Map__fold :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Map__Coq_t a1) -> a2 -> a2
_NatMap__Map__fold f m i =
  _NatMap__Map__Raw__fold f (_NatMap__Map__this m) i

_NatMap__Map__equal :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) ->
                       Prelude.Bool
_NatMap__Map__equal cmp m m' =
  _NatMap__Map__Raw__equal cmp (_NatMap__Map__this m) (_NatMap__Map__this m')

type NatMap__Coq_t elt = NatMap__Map__Coq_t elt

_NatMap__P__F__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__P__F__eqb x y =
  case OrderedTypeEx._Nat_as_OT__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

_NatMap__P__F__coq_In_dec :: (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_key -> Prelude.Bool
_NatMap__P__F__coq_In_dec m x =
  let {b = _NatMap__Map__mem x m} in case b of {
                                      Prelude.True -> Prelude.True;
                                      Prelude.False -> Prelude.False}

_NatMap__P__uncurry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
_NatMap__P__uncurry f p =
  f (Datatypes.fst p) (Datatypes.snd p)

_NatMap__P__of_list :: (([]) ((,) NatMap__Map__Coq_key a1)) -> NatMap__Map__Coq_t a1
_NatMap__P__of_list =
  List.fold_right (_NatMap__P__uncurry _NatMap__Map__add) _NatMap__Map__empty

_NatMap__P__to_list :: (NatMap__Map__Coq_t a1) -> ([]) ((,) NatMap__Map__Coq_key a1)
_NatMap__P__to_list =
  _NatMap__Map__elements

_NatMap__P__fold_rec :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) ->
                        ((NatMap__Map__Coq_t a1) -> () -> a3) -> (NatMap__Map__Coq_key -> a1 -> a2 ->
                        (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> () -> () -> () -> a3 -> a3) -> a3
_NatMap__P__fold_rec f i m hempty hstep =
  Logic.eq_rect_r (List.fold_right (_NatMap__P__uncurry f) i (List.rev (_NatMap__Map__elements m)))
    (let {f0 = _NatMap__P__uncurry f} in
     let {l = List.rev (_NatMap__Map__elements m)} in
     let {hstep' = \k e a m' m'' x -> hstep (Datatypes.fst ((,) k e)) (Datatypes.snd ((,) k e)) a m' m'' __ __ __ x}
     in
     Datatypes.list_rect (\_ _ m0 _ -> hempty m0 __) (\a l0 iHl hstep'0 _ m0 _ ->
       case a of {
        (,) k e ->
         hstep'0 k e (List.fold_right f0 i l0) (_NatMap__P__of_list l0) m0 __ __ __
           (iHl (\k0 e0 a0 m' m'' _ _ _ x -> hstep'0 k0 e0 a0 m' m'' __ __ __ x) __ (_NatMap__P__of_list l0) __)}) l
       (\k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) __ m __) (_NatMap__Map__fold f m i)

_NatMap__P__fold_rec_bis :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) ->
                            ((NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> a2 -> () -> a3 -> a3) -> a3 ->
                            (NatMap__Map__Coq_key -> a1 -> a2 -> (NatMap__Map__Coq_t a1) -> () -> () -> a3 -> a3) ->
                            a3
_NatMap__P__fold_rec_bis f i m pmorphism pempty pstep =
  _NatMap__P__fold_rec f i m (\m0 _ -> pmorphism _NatMap__Map__empty m0 i __ pempty) (\k e a m' m'' _ _ _ x ->
    pmorphism (_NatMap__Map__add k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

_NatMap__P__fold_rec_nodep :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) -> a3 ->
                              (NatMap__Map__Coq_key -> a1 -> a2 -> () -> a3 -> a3) -> a3
_NatMap__P__fold_rec_nodep f i m x x0 =
  _NatMap__P__fold_rec_bis f i m (\_ _ _ _ x1 -> x1) x (\k e a _ _ _ x1 -> x0 k e a __ x1)

_NatMap__P__fold_rec_weak :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> ((NatMap__Map__Coq_t a1) ->
                             (NatMap__Map__Coq_t a1) -> a2 -> () -> a3 -> a3) -> a3 -> (NatMap__Map__Coq_key -> a1
                             -> a2 -> (NatMap__Map__Coq_t a1) -> () -> a3 -> a3) -> (NatMap__Map__Coq_t a1) -> a3
_NatMap__P__fold_rec_weak f i x x0 x1 m =
  _NatMap__P__fold_rec_bis f i m x x0 (\k e a m' _ _ x2 -> x1 k e a m' __ x2)

_NatMap__P__fold_rel :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Map__Coq_key -> a1 -> a3 -> a3) -> a2
                        -> a3 -> (NatMap__Map__Coq_t a1) -> a4 -> (NatMap__Map__Coq_key -> a1 -> a2 -> a3 -> () ->
                        a4 -> a4) -> a4
_NatMap__P__fold_rel f g i j m rempty rstep =
  Logic.eq_rect_r (List.fold_right (_NatMap__P__uncurry f) i (List.rev (_NatMap__Map__elements m)))
    (Logic.eq_rect_r (List.fold_right (_NatMap__P__uncurry g) j (List.rev (_NatMap__Map__elements m)))
      (let {l = List.rev (_NatMap__Map__elements m)} in
       let {rstep' = \k e a b x -> rstep k e a b __ x} in
       Datatypes.list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 (Datatypes.fst a) (Datatypes.snd a) (List.fold_right (_NatMap__P__uncurry f) i l0)
           (List.fold_right (_NatMap__P__uncurry g) j l0) __ (iHl (\k e a0 b _ x -> rstep'0 k e a0 b __ x))) l
         (\k e a b _ x -> rstep' k e a b x)) (_NatMap__Map__fold g m j)) (_NatMap__Map__fold f m i)

_NatMap__P__map_induction :: ((NatMap__Map__Coq_t a1) -> () -> a2) -> ((NatMap__Map__Coq_t a1) ->
                             (NatMap__Map__Coq_t a1) -> a2 -> NatMap__Map__Coq_key -> a1 -> () -> () -> a2) ->
                             (NatMap__Map__Coq_t a1) -> a2
_NatMap__P__map_induction x x0 m =
  _NatMap__P__fold_rec (\_ _ _ -> ()) () m x (\k e _ m' m'' _ _ _ x1 -> x0 m' m'' x1 k e __ __)

_NatMap__P__map_induction_bis :: ((NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> () -> a2 -> a2) -> a2 ->
                                 (NatMap__Map__Coq_key -> a1 -> (NatMap__Map__Coq_t a1) -> () -> a2 -> a2) ->
                                 (NatMap__Map__Coq_t a1) -> a2
_NatMap__P__map_induction_bis x x0 x1 m =
  _NatMap__P__fold_rec_bis (\_ _ _ -> ()) () m (\m0 m' _ _ x2 -> x m0 m' __ x2) x0 (\k e _ m' _ _ x2 ->
    x1 k e m' __ x2)

_NatMap__P__cardinal_inv_2 :: (NatMap__Map__Coq_t a1) -> Prelude.Int -> ((,) NatMap__Map__Coq_key a1)
_NatMap__P__cardinal_inv_2 m _ =
  let {l = _NatMap__Map__elements m} in case l of {
                                         ([]) -> Logic.coq_False_rect;
                                         (:) p _ -> p}

_NatMap__P__cardinal_inv_2b :: (NatMap__Map__Coq_t a1) -> ((,) NatMap__Map__Coq_key a1)
_NatMap__P__cardinal_inv_2b m =
  let {n = _NatMap__Map__cardinal m} in
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Logic.coq_False_rect (\x _ -> _NatMap__P__cardinal_inv_2 m x))
    (\n0 -> _NatMap__P__cardinal_inv_2 m n0)
    n

_NatMap__P__filter :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t
                      a1
_NatMap__P__filter f m =
  _NatMap__Map__fold (\k e m0 -> case f k e of {
                                  Prelude.True -> _NatMap__Map__add k e m0;
                                  Prelude.False -> m0}) m _NatMap__Map__empty

_NatMap__P__for_all :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__for_all f m =
  _NatMap__Map__fold (\k e b -> case f k e of {
                                 Prelude.True -> b;
                                 Prelude.False -> Prelude.False}) m Prelude.True

_NatMap__P__exists_ :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__exists_ f m =
  _NatMap__Map__fold (\k e b -> case f k e of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> b}) m Prelude.False

_NatMap__P__partition :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,)
                         (NatMap__Map__Coq_t a1) (NatMap__Map__Coq_t a1)
_NatMap__P__partition f m =
  (,) (_NatMap__P__filter f m) (_NatMap__P__filter (\k e -> Prelude.not (f k e)) m)

_NatMap__P__update :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__P__update m1 m2 =
  _NatMap__Map__fold _NatMap__Map__add m2 m1

_NatMap__P__restrict :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__P__restrict m1 m2 =
  _NatMap__P__filter (\k _ -> _NatMap__Map__mem k m2) m1

_NatMap__P__diff :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__P__diff m1 m2 =
  _NatMap__P__filter (\k _ -> Prelude.not (_NatMap__Map__mem k m2)) m1

_NatMap__P__coq_Partition_In :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) ->
                                NatMap__Map__Coq_key -> Prelude.Bool
_NatMap__P__coq_Partition_In _ m1 _ k =
  _NatMap__P__F__coq_In_dec m1 k

_NatMap__P__update_dec :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_key -> a1 ->
                          Prelude.Bool
_NatMap__P__update_dec _ m' k _ =
  _NatMap__P__F__coq_In_dec m' k

_NatMap__P__filter_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__P__filter_dom f =
  _NatMap__P__filter (\k _ -> f k)

_NatMap__P__filter_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__P__filter_range f =
  _NatMap__P__filter (\_ -> f)

_NatMap__P__for_all_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__for_all_dom f =
  _NatMap__P__for_all (\k _ -> f k)

_NatMap__P__for_all_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__for_all_range f =
  _NatMap__P__for_all (\_ -> f)

_NatMap__P__exists_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__exists_dom f =
  _NatMap__P__exists_ (\k _ -> f k)

_NatMap__P__exists_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__P__exists_range f =
  _NatMap__P__exists_ (\_ -> f)

_NatMap__P__partition_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,)
                             (NatMap__Map__Coq_t a1) (NatMap__Map__Coq_t a1)
_NatMap__P__partition_dom f =
  _NatMap__P__partition (\k _ -> f k)

_NatMap__P__partition_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,) (NatMap__Map__Coq_t a1)
                               (NatMap__Map__Coq_t a1)
_NatMap__P__partition_range f =
  _NatMap__P__partition (\_ -> f)

_NatMap__F__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__F__eqb x y =
  case OrderedTypeEx._Nat_as_OT__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

_NatMap__F__coq_In_dec :: (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_key -> Prelude.Bool
_NatMap__F__coq_In_dec =
  _NatMap__P__F__coq_In_dec

type NatMap__O__ME__TO__Coq_t = Prelude.Int

_NatMap__O__ME__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__ME__eq_dec =
  _NatMap__Map__E__eq_dec

_NatMap__O__ME__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__ME__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False)
    (_NatMap__Map__E__compare x y)

_NatMap__O__ME__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__ME__eqb x y =
  case _NatMap__O__ME__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type NatMap__O__O__MO__TO__Coq_t = Prelude.Int

_NatMap__O__O__MO__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__O__MO__eq_dec =
  _NatMap__Map__E__eq_dec

_NatMap__O__O__MO__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__O__MO__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False)
    (_NatMap__Map__E__compare x y)

_NatMap__O__O__MO__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__O__MO__eqb x y =
  case _NatMap__O__O__MO__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

_NatMap__O__P__F__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__O__P__F__eqb x y =
  case _NatMap__Map__E__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

_NatMap__O__P__F__coq_In_dec :: (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_key -> Prelude.Bool
_NatMap__O__P__F__coq_In_dec m x =
  let {b = _NatMap__Map__mem x m} in case b of {
                                      Prelude.True -> Prelude.True;
                                      Prelude.False -> Prelude.False}

_NatMap__O__P__uncurry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
_NatMap__O__P__uncurry f p =
  f (Datatypes.fst p) (Datatypes.snd p)

_NatMap__O__P__of_list :: (([]) ((,) NatMap__Map__Coq_key a1)) -> NatMap__Map__Coq_t a1
_NatMap__O__P__of_list =
  List.fold_right (_NatMap__O__P__uncurry _NatMap__Map__add) _NatMap__Map__empty

_NatMap__O__P__to_list :: (NatMap__Map__Coq_t a1) -> ([]) ((,) NatMap__Map__Coq_key a1)
_NatMap__O__P__to_list =
  _NatMap__Map__elements

_NatMap__O__P__fold_rec :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) ->
                           ((NatMap__Map__Coq_t a1) -> () -> a3) -> (NatMap__Map__Coq_key -> a1 -> a2 ->
                           (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> () -> () -> () -> a3 -> a3) -> a3
_NatMap__O__P__fold_rec f i m hempty hstep =
  Logic.eq_rect_r (List.fold_right (_NatMap__O__P__uncurry f) i (List.rev (_NatMap__Map__elements m)))
    (let {f0 = _NatMap__O__P__uncurry f} in
     let {l = List.rev (_NatMap__Map__elements m)} in
     let {hstep' = \k e a m' m'' x -> hstep (Datatypes.fst ((,) k e)) (Datatypes.snd ((,) k e)) a m' m'' __ __ __ x}
     in
     Datatypes.list_rect (\_ _ m0 _ -> hempty m0 __) (\a l0 iHl hstep'0 _ m0 _ ->
       case a of {
        (,) k e ->
         hstep'0 k e (List.fold_right f0 i l0) (_NatMap__O__P__of_list l0) m0 __ __ __
           (iHl (\k0 e0 a0 m' m'' _ _ _ x -> hstep'0 k0 e0 a0 m' m'' __ __ __ x) __ (_NatMap__O__P__of_list l0) __)})
       l (\k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) __ m __) (_NatMap__Map__fold f m i)

_NatMap__O__P__fold_rec_bis :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) ->
                               ((NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> a2 -> () -> a3 -> a3) -> a3 ->
                               (NatMap__Map__Coq_key -> a1 -> a2 -> (NatMap__Map__Coq_t a1) -> () -> () -> a3 -> a3)
                               -> a3
_NatMap__O__P__fold_rec_bis f i m pmorphism pempty pstep =
  _NatMap__O__P__fold_rec f i m (\m0 _ -> pmorphism _NatMap__Map__empty m0 i __ pempty) (\k e a m' m'' _ _ _ x ->
    pmorphism (_NatMap__Map__add k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

_NatMap__O__P__fold_rec_nodep :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> (NatMap__Map__Coq_t a1) -> a3 ->
                                 (NatMap__Map__Coq_key -> a1 -> a2 -> () -> a3 -> a3) -> a3
_NatMap__O__P__fold_rec_nodep f i m x x0 =
  _NatMap__O__P__fold_rec_bis f i m (\_ _ _ _ x1 -> x1) x (\k e a _ _ _ x1 -> x0 k e a __ x1)

_NatMap__O__P__fold_rec_weak :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> a2 -> ((NatMap__Map__Coq_t a1) ->
                                (NatMap__Map__Coq_t a1) -> a2 -> () -> a3 -> a3) -> a3 -> (NatMap__Map__Coq_key ->
                                a1 -> a2 -> (NatMap__Map__Coq_t a1) -> () -> a3 -> a3) -> (NatMap__Map__Coq_t 
                                a1) -> a3
_NatMap__O__P__fold_rec_weak f i x x0 x1 m =
  _NatMap__O__P__fold_rec_bis f i m x x0 (\k e a m' _ _ x2 -> x1 k e a m' __ x2)

_NatMap__O__P__fold_rel :: (NatMap__Map__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Map__Coq_key -> a1 -> a3 -> a3) ->
                           a2 -> a3 -> (NatMap__Map__Coq_t a1) -> a4 -> (NatMap__Map__Coq_key -> a1 -> a2 -> a3 ->
                           () -> a4 -> a4) -> a4
_NatMap__O__P__fold_rel f g i j m rempty rstep =
  Logic.eq_rect_r (List.fold_right (_NatMap__O__P__uncurry f) i (List.rev (_NatMap__Map__elements m)))
    (Logic.eq_rect_r (List.fold_right (_NatMap__O__P__uncurry g) j (List.rev (_NatMap__Map__elements m)))
      (let {l = List.rev (_NatMap__Map__elements m)} in
       let {rstep' = \k e a b x -> rstep k e a b __ x} in
       Datatypes.list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 (Datatypes.fst a) (Datatypes.snd a) (List.fold_right (_NatMap__O__P__uncurry f) i l0)
           (List.fold_right (_NatMap__O__P__uncurry g) j l0) __ (iHl (\k e a0 b _ x -> rstep'0 k e a0 b __ x))) l
         (\k e a b _ x -> rstep' k e a b x)) (_NatMap__Map__fold g m j)) (_NatMap__Map__fold f m i)

_NatMap__O__P__map_induction :: ((NatMap__Map__Coq_t a1) -> () -> a2) -> ((NatMap__Map__Coq_t a1) ->
                                (NatMap__Map__Coq_t a1) -> a2 -> NatMap__Map__Coq_key -> a1 -> () -> () -> a2) ->
                                (NatMap__Map__Coq_t a1) -> a2
_NatMap__O__P__map_induction x x0 m =
  _NatMap__O__P__fold_rec (\_ _ _ -> ()) () m x (\k e _ m' m'' _ _ _ x1 -> x0 m' m'' x1 k e __ __)

_NatMap__O__P__map_induction_bis :: ((NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> () -> a2 -> a2) -> a2 ->
                                    (NatMap__Map__Coq_key -> a1 -> (NatMap__Map__Coq_t a1) -> () -> a2 -> a2) ->
                                    (NatMap__Map__Coq_t a1) -> a2
_NatMap__O__P__map_induction_bis x x0 x1 m =
  _NatMap__O__P__fold_rec_bis (\_ _ _ -> ()) () m (\m0 m' _ _ x2 -> x m0 m' __ x2) x0 (\k e _ m' _ _ x2 ->
    x1 k e m' __ x2)

_NatMap__O__P__cardinal_inv_2 :: (NatMap__Map__Coq_t a1) -> Prelude.Int -> ((,) NatMap__Map__Coq_key a1)
_NatMap__O__P__cardinal_inv_2 m _ =
  let {l = _NatMap__Map__elements m} in case l of {
                                         ([]) -> Logic.coq_False_rect;
                                         (:) p _ -> p}

_NatMap__O__P__cardinal_inv_2b :: (NatMap__Map__Coq_t a1) -> ((,) NatMap__Map__Coq_key a1)
_NatMap__O__P__cardinal_inv_2b m =
  let {n = _NatMap__Map__cardinal m} in
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Logic.coq_False_rect (\x _ -> _NatMap__O__P__cardinal_inv_2 m x))
    (\n0 -> _NatMap__O__P__cardinal_inv_2 m n0)
    n

_NatMap__O__P__filter :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) ->
                         NatMap__Map__Coq_t a1
_NatMap__O__P__filter f m =
  _NatMap__Map__fold (\k e m0 -> case f k e of {
                                  Prelude.True -> _NatMap__Map__add k e m0;
                                  Prelude.False -> m0}) m _NatMap__Map__empty

_NatMap__O__P__for_all :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__for_all f m =
  _NatMap__Map__fold (\k e b -> case f k e of {
                                 Prelude.True -> b;
                                 Prelude.False -> Prelude.False}) m Prelude.True

_NatMap__O__P__exists_ :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__exists_ f m =
  _NatMap__Map__fold (\k e b -> case f k e of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> b}) m Prelude.False

_NatMap__O__P__partition :: (NatMap__Map__Coq_key -> a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,)
                            (NatMap__Map__Coq_t a1) (NatMap__Map__Coq_t a1)
_NatMap__O__P__partition f m =
  (,) (_NatMap__O__P__filter f m) (_NatMap__O__P__filter (\k e -> Prelude.not (f k e)) m)

_NatMap__O__P__update :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__O__P__update m1 m2 =
  _NatMap__Map__fold _NatMap__Map__add m2 m1

_NatMap__O__P__restrict :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__O__P__restrict m1 m2 =
  _NatMap__O__P__filter (\k _ -> _NatMap__Map__mem k m2) m1

_NatMap__O__P__diff :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__O__P__diff m1 m2 =
  _NatMap__O__P__filter (\k _ -> Prelude.not (_NatMap__Map__mem k m2)) m1

_NatMap__O__P__coq_Partition_In :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t 
                                   a1) -> NatMap__Map__Coq_key -> Prelude.Bool
_NatMap__O__P__coq_Partition_In _ m1 _ k =
  _NatMap__O__P__F__coq_In_dec m1 k

_NatMap__O__P__update_dec :: (NatMap__Map__Coq_t a1) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_key -> a1 ->
                             Prelude.Bool
_NatMap__O__P__update_dec _ m' k _ =
  _NatMap__O__P__F__coq_In_dec m' k

_NatMap__O__P__filter_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t
                             a1
_NatMap__O__P__filter_dom f =
  _NatMap__O__P__filter (\k _ -> f k)

_NatMap__O__P__filter_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__O__P__filter_range f =
  _NatMap__O__P__filter (\_ -> f)

_NatMap__O__P__for_all_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__for_all_dom f =
  _NatMap__O__P__for_all (\k _ -> f k)

_NatMap__O__P__for_all_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__for_all_range f =
  _NatMap__O__P__for_all (\_ -> f)

_NatMap__O__P__exists_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__exists_dom f =
  _NatMap__O__P__exists_ (\k _ -> f k)

_NatMap__O__P__exists_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> Prelude.Bool
_NatMap__O__P__exists_range f =
  _NatMap__O__P__exists_ (\_ -> f)

_NatMap__O__P__partition_dom :: (NatMap__Map__Coq_key -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,)
                                (NatMap__Map__Coq_t a1) (NatMap__Map__Coq_t a1)
_NatMap__O__P__partition_dom f =
  _NatMap__O__P__partition (\k _ -> f k)

_NatMap__O__P__partition_range :: (a1 -> Prelude.Bool) -> (NatMap__Map__Coq_t a1) -> (,) (NatMap__Map__Coq_t a1)
                                  (NatMap__Map__Coq_t a1)
_NatMap__O__P__partition_range f =
  _NatMap__O__P__partition (\_ -> f)

_NatMap__O__gtb :: ((,) NatMap__Map__Coq_key a1) -> ((,) NatMap__Map__Coq_key a1) -> Prelude.Bool
_NatMap__O__gtb p p' =
  case _NatMap__Map__E__compare (Datatypes.fst p) (Datatypes.fst p') of {
   OrderedType.GT -> Prelude.True;
   _ -> Prelude.False}

_NatMap__O__leb :: ((,) NatMap__Map__Coq_key a1) -> ((,) NatMap__Map__Coq_key a1) -> Prelude.Bool
_NatMap__O__leb p p' =
  Prelude.not (_NatMap__O__gtb p p')

_NatMap__O__elements_lt :: ((,) NatMap__Map__Coq_key a1) -> (NatMap__Map__Coq_t a1) -> ([])
                           ((,) NatMap__Map__Coq_key a1)
_NatMap__O__elements_lt p m =
  List.filter (_NatMap__O__gtb p) (_NatMap__Map__elements m)

_NatMap__O__elements_ge :: ((,) NatMap__Map__Coq_key a1) -> (NatMap__Map__Coq_t a1) -> ([])
                           ((,) NatMap__Map__Coq_key a1)
_NatMap__O__elements_ge p m =
  List.filter (_NatMap__O__leb p) (_NatMap__Map__elements m)

_NatMap__O__max_elt_aux :: (([]) ((,) NatMap__Map__Coq_key a1)) -> Prelude.Maybe ((,) NatMap__Map__Coq_key a1)
_NatMap__O__max_elt_aux l =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) p l0 -> case l0 of {
                ([]) -> Prelude.Just p;
                (:) _ _ -> _NatMap__O__max_elt_aux l0}}

_NatMap__O__max_elt :: (NatMap__Map__Coq_t a1) -> Prelude.Maybe ((,) NatMap__Map__Coq_key a1)
_NatMap__O__max_elt m =
  _NatMap__O__max_elt_aux (_NatMap__Map__elements m)

_NatMap__O__min_elt :: (NatMap__Map__Coq_t a1) -> Prelude.Maybe ((,) NatMap__Map__Coq_key a1)
_NatMap__O__min_elt m =
  case _NatMap__Map__elements m of {
   ([]) -> Prelude.Nothing;
   (:) p _ -> Prelude.Just p}

_NatMap__O__map_induction_max :: ((NatMap__Map__Coq_t a1) -> () -> a2) -> ((NatMap__Map__Coq_t a1) ->
                                 (NatMap__Map__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> () -> () -> a2) ->
                                 (NatMap__Map__Coq_t a1) -> a2
_NatMap__O__map_induction_max x x0 m =
  let {n = _NatMap__Map__cardinal m} in
  Datatypes.nat_rect (\m0 _ -> x m0 __) (\_ iHn m0 _ ->
    case _NatMap__O__max_elt m0 of {
     Prelude.Just p ->
      case p of {
       (,) k e -> x0 (_NatMap__Map__remove k m0) m0 (iHn (_NatMap__Map__remove k m0) __) k e __ __};
     Prelude.Nothing -> x m0 __}) n m __

_NatMap__O__map_induction_min :: ((NatMap__Map__Coq_t a1) -> () -> a2) -> ((NatMap__Map__Coq_t a1) ->
                                 (NatMap__Map__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> () -> () -> a2) ->
                                 (NatMap__Map__Coq_t a1) -> a2
_NatMap__O__map_induction_min x x0 m =
  let {n = _NatMap__Map__cardinal m} in
  Datatypes.nat_rect (\m0 _ -> x m0 __) (\_ iHn m0 _ ->
    case _NatMap__O__min_elt m0 of {
     Prelude.Just p ->
      case p of {
       (,) k e -> x0 (_NatMap__Map__remove k m0) m0 (iHn (_NatMap__Map__remove k m0) __) k e __ __};
     Prelude.Nothing -> x m0 __}) n m __

type NatMap__OTF__TO__Coq_t = Prelude.Int

_NatMap__OTF__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__OTF__eq_dec =
  OrderedTypeEx._Nat_as_OT__eq_dec

_NatMap__OTF__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__OTF__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False)
    (OrderedTypeEx._Nat_as_OT__compare x y)

_NatMap__OTF__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__OTF__eqb x y =
  case _NatMap__OTF__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

_NatMap__canon_map :: (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__canon_map m =
  _NatMap__P__of_list (_NatMap__P__to_list m)

_NatMap__canonicalize_concrete_map :: (NatMap__Map__Coq_t a1) -> NatMap__Map__Coq_t a1
_NatMap__canonicalize_concrete_map m =
  List.fold_left (\acc cur -> case cur of {
                               (,) k v -> _NatMap__Map__add k v acc}) m _NatMap__Map__empty

