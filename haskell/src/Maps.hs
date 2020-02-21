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

type NatMap__Raw__MX__TO__Coq_t = Prelude.Int

_NatMap__Raw__MX__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__MX__eq_dec =
  OrderedTypeEx._Nat_as_OT__eq_dec

_NatMap__Raw__MX__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__MX__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False) (OrderedTypeEx._Nat_as_OT__compare x y)

_NatMap__Raw__MX__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__MX__eqb x y =
  case _NatMap__Raw__MX__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type NatMap__Raw__PX__MO__TO__Coq_t = Prelude.Int

_NatMap__Raw__PX__MO__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__PX__MO__eq_dec =
  OrderedTypeEx._Nat_as_OT__eq_dec

_NatMap__Raw__PX__MO__lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__PX__MO__lt_dec x y =
  OrderedType.coq_Compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ -> Prelude.False) (OrderedTypeEx._Nat_as_OT__compare x y)

_NatMap__Raw__PX__MO__eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__Raw__PX__MO__eqb x y =
  case _NatMap__Raw__PX__MO__eq_dec x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type NatMap__Raw__Coq_key = Prelude.Int

type NatMap__Raw__Coq_t elt = ([]) ((,) Prelude.Int elt)

_NatMap__Raw__empty :: NatMap__Raw__Coq_t a1
_NatMap__Raw__empty =
  ([])

_NatMap__Raw__is_empty :: (NatMap__Raw__Coq_t a1) -> Prelude.Bool
_NatMap__Raw__is_empty l =
  case l of {
   ([]) -> Prelude.True;
   (:) _ _ -> Prelude.False}

_NatMap__Raw__mem :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool
_NatMap__Raw__mem k s =
  case s of {
   ([]) -> Prelude.False;
   (:) p l ->
    case p of {
     (,) k' _ ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> Prelude.False;
       OrderedType.EQ -> Prelude.True;
       OrderedType.GT -> _NatMap__Raw__mem k l}}}

data NatMap__Raw__R_mem elt =
   NatMap__Raw__R_mem_0 (NatMap__Raw__Coq_t elt)
 | NatMap__Raw__R_mem_1 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_mem_2 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_mem_3 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) Prelude.Bool (NatMap__Raw__R_mem elt)

_NatMap__Raw__coq_R_mem_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool -> (NatMap__Raw__R_mem a1) -> a2 -> a2) ->
                                (NatMap__Raw__Coq_t a1) -> Prelude.Bool -> (NatMap__Raw__R_mem a1) -> a2
_NatMap__Raw__coq_R_mem_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Raw__R_mem_0 s -> f s __;
   NatMap__Raw__R_mem_1 s k' _x l -> f0 s k' _x l __ __ __;
   NatMap__Raw__R_mem_2 s k' _x l -> f1 s k' _x l __ __ __;
   NatMap__Raw__R_mem_3 s k' _x l _res r0 -> f2 s k' _x l __ __ __ _res r0 (_NatMap__Raw__coq_R_mem_rect k f f0 f1 f2 l _res r0)}

_NatMap__Raw__coq_R_mem_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                               -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                               (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                               ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool -> (NatMap__Raw__R_mem a1) -> a2 -> a2) ->
                               (NatMap__Raw__Coq_t a1) -> Prelude.Bool -> (NatMap__Raw__R_mem a1) -> a2
_NatMap__Raw__coq_R_mem_rec =
  _NatMap__Raw__coq_R_mem_rect

_NatMap__Raw__mem_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                          (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__mem_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> Prelude.False;
      (:) p l ->
       case p of {
        (,) k' _ ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> Prelude.False;
          OrderedType.EQ -> Prelude.True;
          OrderedType.GT -> _NatMap__Raw__mem k l}}})
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
         let {f8 = \_ _ -> let {hrec = _NatMap__Raw__mem_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Raw__mem k s)

_NatMap__Raw__mem_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                         (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                         ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                         ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__mem_rec =
  _NatMap__Raw__mem_rect

_NatMap__Raw__coq_R_mem_correct :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool -> NatMap__Raw__R_mem a1
_NatMap__Raw__coq_R_mem_correct k s _res =
  unsafeCoerce _NatMap__Raw__mem_rect k (\y _ z _ -> Logic.eq_rect_r Prelude.False (NatMap__Raw__R_mem_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Raw__R_mem_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.True (NatMap__Raw__R_mem_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r (_NatMap__Raw__mem k y2) (NatMap__Raw__R_mem_3 y y0 y1 y2 (_NatMap__Raw__mem k y2) (y6 (_NatMap__Raw__mem k y2) __)) z) s
    _res __

_NatMap__Raw__find :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> Prelude.Maybe a1
_NatMap__Raw__find k s =
  case s of {
   ([]) -> Prelude.Nothing;
   (:) p s' ->
    case p of {
     (,) k' x ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> Prelude.Nothing;
       OrderedType.EQ -> Prelude.Just x;
       OrderedType.GT -> _NatMap__Raw__find k s'}}}

data NatMap__Raw__R_find elt =
   NatMap__Raw__R_find_0 (NatMap__Raw__Coq_t elt)
 | NatMap__Raw__R_find_1 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_find_2 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_find_3 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (Prelude.Maybe elt) (NatMap__Raw__R_find elt)

_NatMap__Raw__coq_R_find_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int ->
                                 a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                 (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe a1) -> (NatMap__Raw__R_find a1) -> a2 -> a2)
                                 -> (NatMap__Raw__Coq_t a1) -> (Prelude.Maybe a1) -> (NatMap__Raw__R_find a1) -> a2
_NatMap__Raw__coq_R_find_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Raw__R_find_0 s -> f s __;
   NatMap__Raw__R_find_1 s k' x s' -> f0 s k' x s' __ __ __;
   NatMap__Raw__R_find_2 s k' x s' -> f1 s k' x s' __ __ __;
   NatMap__Raw__R_find_3 s k' x s' _res r0 -> f2 s k' x s' __ __ __ _res r0 (_NatMap__Raw__coq_R_find_rect k f f0 f1 f2 s' _res r0)}

_NatMap__Raw__coq_R_find_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                                ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe a1) -> (NatMap__Raw__R_find a1) -> a2 -> a2) ->
                                (NatMap__Raw__Coq_t a1) -> (Prelude.Maybe a1) -> (NatMap__Raw__R_find a1) -> a2
_NatMap__Raw__coq_R_find_rec =
  _NatMap__Raw__coq_R_find_rect

_NatMap__Raw__find_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                           (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                           ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                           ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__find_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> Prelude.Nothing;
      (:) p s' ->
       case p of {
        (,) k' x ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> Prelude.Nothing;
          OrderedType.EQ -> Prelude.Just x;
          OrderedType.GT -> _NatMap__Raw__find k s'}}})
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
         let {f8 = \_ _ -> let {hrec = _NatMap__Raw__find_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Raw__find k s)

_NatMap__Raw__find_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                          (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__find_rec =
  _NatMap__Raw__find_rect

_NatMap__Raw__coq_R_find_correct :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> (Prelude.Maybe a1) -> NatMap__Raw__R_find a1
_NatMap__Raw__coq_R_find_correct k s _res =
  unsafeCoerce _NatMap__Raw__find_rect k (\y _ z _ -> Logic.eq_rect_r Prelude.Nothing (NatMap__Raw__R_find_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r Prelude.Nothing (NatMap__Raw__R_find_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r (Prelude.Just y1) (NatMap__Raw__R_find_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r (_NatMap__Raw__find k y2) (NatMap__Raw__R_find_3 y y0 y1 y2 (_NatMap__Raw__find k y2) (y6 (_NatMap__Raw__find k y2) __)) z)
    s _res __

_NatMap__Raw__add :: NatMap__Raw__Coq_key -> a1 -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a1
_NatMap__Raw__add k x s =
  case s of {
   ([]) -> (:) ((,) k x) ([]);
   (:) p l ->
    case p of {
     (,) k' y ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> (:) ((,) k x) s;
       OrderedType.EQ -> (:) ((,) k x) l;
       OrderedType.GT -> (:) ((,) k' y) (_NatMap__Raw__add k x l)}}}

data NatMap__Raw__R_add elt =
   NatMap__Raw__R_add_0 (NatMap__Raw__Coq_t elt)
 | NatMap__Raw__R_add_1 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_add_2 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_add_3 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (NatMap__Raw__Coq_t elt) (NatMap__Raw__R_add
                                                                                                                       elt)

_NatMap__Raw__coq_R_add_rect :: NatMap__Raw__Coq_key -> a1 -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int
                                -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_add a1) -> a2 ->
                                a2) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_add a1) -> a2
_NatMap__Raw__coq_R_add_rect k x f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Raw__R_add_0 s -> f s __;
   NatMap__Raw__R_add_1 s k' y l -> f0 s k' y l __ __ __;
   NatMap__Raw__R_add_2 s k' y l -> f1 s k' y l __ __ __;
   NatMap__Raw__R_add_3 s k' y l _res r0 -> f2 s k' y l __ __ __ _res r0 (_NatMap__Raw__coq_R_add_rect k x f f0 f1 f2 l _res r0)}

_NatMap__Raw__coq_R_add_rec :: NatMap__Raw__Coq_key -> a1 -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int
                               -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                               -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                               (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_add a1) -> a2 ->
                               a2) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_add a1) -> a2
_NatMap__Raw__coq_R_add_rec =
  _NatMap__Raw__coq_R_add_rect

_NatMap__Raw__add_rect :: NatMap__Raw__Coq_key -> a1 -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                          -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                          ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__add_rect k x f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> (:) ((,) k x) ([]);
      (:) p l ->
       case p of {
        (,) k' y ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> (:) ((,) k x) s;
          OrderedType.EQ -> (:) ((,) k x) l;
          OrderedType.GT -> (:) ((,) k' y) (_NatMap__Raw__add k x l)}}})
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
         let {f8 = \_ _ -> let {hrec = _NatMap__Raw__add_rect k x f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Raw__add k x s)

_NatMap__Raw__add_rec :: NatMap__Raw__Coq_key -> a1 -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                         -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                         ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                         ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__add_rec =
  _NatMap__Raw__add_rect

_NatMap__Raw__coq_R_add_correct :: NatMap__Raw__Coq_key -> a1 -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__R_add a1
_NatMap__Raw__coq_R_add_correct k x s _res =
  _NatMap__Raw__add_rect k x (\y _ z _ -> Logic.eq_rect_r ((:) ((,) k x) ([])) (NatMap__Raw__R_add_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r ((:) ((,) k x) y) (NatMap__Raw__R_add_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r ((:) ((,) k x) y2) (NatMap__Raw__R_add_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r ((:) ((,) y0 y1) (_NatMap__Raw__add k x y2)) (NatMap__Raw__R_add_3 y y0 y1 y2 (_NatMap__Raw__add k x y2)
      (y6 (_NatMap__Raw__add k x y2) __)) z) s _res __

_NatMap__Raw__remove :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a1
_NatMap__Raw__remove k s =
  case s of {
   ([]) -> ([]);
   (:) p l ->
    case p of {
     (,) k' x ->
      case OrderedTypeEx._Nat_as_OT__compare k k' of {
       OrderedType.LT -> s;
       OrderedType.EQ -> l;
       OrderedType.GT -> (:) ((,) k' x) (_NatMap__Raw__remove k l)}}}

data NatMap__Raw__R_remove elt =
   NatMap__Raw__R_remove_0 (NatMap__Raw__Coq_t elt)
 | NatMap__Raw__R_remove_1 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_remove_2 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt))
 | NatMap__Raw__R_remove_3 (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) (NatMap__Raw__Coq_t elt) (NatMap__Raw__R_remove
                                                                                                                          elt)

_NatMap__Raw__coq_R_remove_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int ->
                                   a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                   -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                   (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_remove 
                                   a1) -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_remove a1) -> a2
_NatMap__Raw__coq_R_remove_rect k f f0 f1 f2 _ _ r =
  case r of {
   NatMap__Raw__R_remove_0 s -> f s __;
   NatMap__Raw__R_remove_1 s k' x l -> f0 s k' x l __ __ __;
   NatMap__Raw__R_remove_2 s k' x l -> f1 s k' x l __ __ __;
   NatMap__Raw__R_remove_3 s k' x l _res r0 -> f2 s k' x l __ __ __ _res r0 (_NatMap__Raw__coq_R_remove_rect k f f0 f1 f2 l _res r0)}

_NatMap__Raw__coq_R_remove_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int ->
                                  a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1
                                  -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                                  (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_remove a1) -> a2
                                  -> a2) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__R_remove a1) -> a2
_NatMap__Raw__coq_R_remove_rec =
  _NatMap__Raw__coq_R_remove_rect

_NatMap__Raw__remove_rect :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                             (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                             ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                             ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__remove_rect k f2 f1 f0 f s =
  Logic.eq_rect_r
    (case s of {
      ([]) -> ([]);
      (:) p l ->
       case p of {
        (,) k' x ->
         case OrderedTypeEx._Nat_as_OT__compare k k' of {
          OrderedType.LT -> s;
          OrderedType.EQ -> l;
          OrderedType.GT -> (:) ((,) k' x) (_NatMap__Raw__remove k l)}}})
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
         let {f8 = \_ _ -> let {hrec = _NatMap__Raw__remove_rect k f2 f1 f0 f l} in f7 __ __ hrec} in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case OrderedTypeEx._Nat_as_OT__compare k t0 of {
          OrderedType.LT -> f10 __ __;
          OrderedType.EQ -> f9 __ __;
          OrderedType.GT -> f8 __ __}}}) (_NatMap__Raw__remove k s)

_NatMap__Raw__remove_rec :: NatMap__Raw__Coq_key -> ((NatMap__Raw__Coq_t a1) -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 ->
                            (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                            ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([])
                            ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__remove_rec =
  _NatMap__Raw__remove_rect

_NatMap__Raw__coq_R_remove_correct :: NatMap__Raw__Coq_key -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__R_remove a1
_NatMap__Raw__coq_R_remove_correct k s _res =
  unsafeCoerce _NatMap__Raw__remove_rect k (\y _ z _ -> Logic.eq_rect_r ([]) (NatMap__Raw__R_remove_0 y) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r y (NatMap__Raw__R_remove_1 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ z _ ->
    Logic.eq_rect_r y2 (NatMap__Raw__R_remove_2 y y0 y1 y2) z) (\y y0 y1 y2 _ _ _ y6 z _ ->
    Logic.eq_rect_r ((:) ((,) y0 y1) (_NatMap__Raw__remove k y2)) (NatMap__Raw__R_remove_3 y y0 y1 y2 (_NatMap__Raw__remove k y2)
      (y6 (_NatMap__Raw__remove k y2) __)) z) s _res __

_NatMap__Raw__elements :: (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a1
_NatMap__Raw__elements m =
  m

_NatMap__Raw__fold :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2 -> a2
_NatMap__Raw__fold f m acc =
  case m of {
   ([]) -> acc;
   (:) p m' -> case p of {
                (,) k e -> _NatMap__Raw__fold f m' (f k e acc)}}

data NatMap__Raw__R_fold elt a =
   NatMap__Raw__R_fold_0 (NatMap__Raw__Coq_t elt) a
 | NatMap__Raw__R_fold_1 (NatMap__Raw__Coq_t elt) a Prelude.Int elt (([]) ((,) Prelude.Int elt)) a (NatMap__Raw__R_fold elt a)

_NatMap__Raw__coq_R_fold_rect :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> a2 -> () -> a3) ->
                                 ((NatMap__Raw__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a2 ->
                                 (NatMap__Raw__R_fold a1 a2) -> a3 -> a3) -> (NatMap__Raw__Coq_t a1) -> a2 -> a2 -> (NatMap__Raw__R_fold 
                                 a1 a2) -> a3
_NatMap__Raw__coq_R_fold_rect f f0 f1 _ _ _ r =
  case r of {
   NatMap__Raw__R_fold_0 m acc -> f0 m acc __;
   NatMap__Raw__R_fold_1 m acc k e m' _res r0 -> f1 m acc k e m' __ _res r0 (_NatMap__Raw__coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)}

_NatMap__Raw__coq_R_fold_rec :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> a2 -> () -> a3) ->
                                ((NatMap__Raw__Coq_t a1) -> a2 -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a2 ->
                                (NatMap__Raw__R_fold a1 a2) -> a3 -> a3) -> (NatMap__Raw__Coq_t a1) -> a2 -> a2 -> (NatMap__Raw__R_fold 
                                a1 a2) -> a3
_NatMap__Raw__coq_R_fold_rec =
  _NatMap__Raw__coq_R_fold_rect

_NatMap__Raw__fold_rect :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> a2 -> () -> a3) -> ((NatMap__Raw__Coq_t 
                           a1) -> a2 -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a3 -> a3) -> (NatMap__Raw__Coq_t a1) -> a2
                           -> a3
_NatMap__Raw__fold_rect f1 f0 f m acc =
  Logic.eq_rect_r (case m of {
                    ([]) -> acc;
                    (:) p m' -> case p of {
                                 (,) k e -> _NatMap__Raw__fold f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      ([]) -> f2 __;
      (:) p l -> case p of {
                  (,) t0 e -> let {f4 = f3 t0 e l __} in let {hrec = _NatMap__Raw__fold_rect f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (_NatMap__Raw__fold f1 m acc)

_NatMap__Raw__fold_rec :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> a2 -> () -> a3) -> ((NatMap__Raw__Coq_t 
                          a1) -> a2 -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> a3 -> a3) -> (NatMap__Raw__Coq_t a1) -> a2 ->
                          a3
_NatMap__Raw__fold_rec =
  _NatMap__Raw__fold_rect

_NatMap__Raw__coq_R_fold_correct :: (NatMap__Raw__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Raw__Coq_t a1) -> a2 -> a2 -> NatMap__Raw__R_fold 
                                    a1 a2
_NatMap__Raw__coq_R_fold_correct f m acc _res =
  _NatMap__Raw__fold_rect f (\y y0 _ z _ -> Logic.eq_rect_r y0 (NatMap__Raw__R_fold_0 y y0) z) (\y y0 y1 y2 y3 _ y5 z _ ->
    Logic.eq_rect_r (_NatMap__Raw__fold f y3 (f y1 y2 y0)) (NatMap__Raw__R_fold_1 y y0 y1 y2 y3 (_NatMap__Raw__fold f y3 (f y1 y2 y0))
      (y5 (_NatMap__Raw__fold f y3 (f y1 y2 y0)) __)) z) m acc _res __

_NatMap__Raw__equal :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool
_NatMap__Raw__equal cmp m m' =
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
           OrderedType.EQ -> (Prelude.&&) (cmp e e') (_NatMap__Raw__equal cmp l l');
           _ -> Prelude.False}}}}}

data NatMap__Raw__R_equal elt =
   NatMap__Raw__R_equal_0 (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt)
 | NatMap__Raw__R_equal_1 (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) Prelude.Int elt 
 (([]) ((,) Prelude.Int elt)) Prelude.Bool (NatMap__Raw__R_equal elt)
 | NatMap__Raw__R_equal_2 (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt) Prelude.Int elt (([]) ((,) Prelude.Int elt)) Prelude.Int elt 
 (([]) ((,) Prelude.Int elt)) (OrderedType.Compare Prelude.Int)
 | NatMap__Raw__R_equal_3 (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt) (NatMap__Raw__Coq_t elt)

_NatMap__Raw__coq_R_equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                                  ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) ->
                                  () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                  (NatMap__Raw__R_equal a1) -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int
                                  -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () ->
                                  (OrderedType.Compare Prelude.Int) -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t 
                                  a1) -> (NatMap__Raw__Coq_t a1) -> () -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) -> (NatMap__Raw__Coq_t
                                  a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool -> (NatMap__Raw__R_equal a1) -> a2
_NatMap__Raw__coq_R_equal_rect cmp f f0 f1 f2 _ _ _ r =
  case r of {
   NatMap__Raw__R_equal_0 m m' -> f m m' __ __;
   NatMap__Raw__R_equal_1 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0 (_NatMap__Raw__coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0);
   NatMap__Raw__R_equal_2 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   NatMap__Raw__R_equal_3 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

_NatMap__Raw__coq_R_equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                                 ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> ()
                                 -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                                 (NatMap__Raw__R_equal a1) -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int
                                 -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () ->
                                 (OrderedType.Compare Prelude.Int) -> () -> () -> a2) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t 
                                 a1) -> (NatMap__Raw__Coq_t a1) -> () -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) -> (NatMap__Raw__Coq_t 
                                 a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool -> (NatMap__Raw__R_equal a1) -> a2
_NatMap__Raw__coq_R_equal_rec =
  _NatMap__Raw__coq_R_equal_rect

_NatMap__Raw__equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                            ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () ->
                            Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) ->
                            (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                            ((,) Prelude.Int a1)) -> () -> (OrderedType.Compare Prelude.Int) -> () -> () -> a2) -> ((NatMap__Raw__Coq_t 
                            a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                            (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__equal_rect cmp f2 f1 f0 f m m' =
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
              OrderedType.EQ -> (Prelude.&&) (cmp e e') (_NatMap__Raw__equal cmp l l');
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
             let {f14 = \_ _ -> let {hrec = _NatMap__Raw__equal_rect cmp f2 f1 f0 f l l0} in f13 __ __ hrec} in
             case OrderedTypeEx._Nat_as_OT__compare t0 t1 of {
              OrderedType.EQ -> f14 __ __;
              _ -> f12 __}}}}}) (_NatMap__Raw__equal cmp m m')

_NatMap__Raw__equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                           ((NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () ->
                           Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> ((NatMap__Raw__Coq_t a1) ->
                           (NatMap__Raw__Coq_t a1) -> Prelude.Int -> a1 -> (([]) ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> (([])
                           ((,) Prelude.Int a1)) -> () -> (OrderedType.Compare Prelude.Int) -> () -> () -> a2) -> ((NatMap__Raw__Coq_t 
                           a1) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> () -> (NatMap__Raw__Coq_t a1) -> () -> () -> a2) ->
                           (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> a2
_NatMap__Raw__equal_rec =
  _NatMap__Raw__equal_rect

_NatMap__Raw__coq_R_equal_correct :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a1) -> Prelude.Bool ->
                                     NatMap__Raw__R_equal a1
_NatMap__Raw__coq_R_equal_correct cmp m m' _res =
  _NatMap__Raw__equal_rect cmp (\y y0 _ _ z _ -> Logic.eq_rect_r Prelude.True (NatMap__Raw__R_equal_0 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    Logic.eq_rect_r ((Prelude.&&) (cmp y2 y6) (_NatMap__Raw__equal cmp y3 y7)) (NatMap__Raw__R_equal_1 y y0 y1 y2 y3 y5 y6 y7
      (_NatMap__Raw__equal cmp y3 y7) (y11 (_NatMap__Raw__equal cmp y3 y7) __)) z) (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Raw__R_equal_2 y y0 y1 y2 y3 y5 y6 y7 y9) z) (\y y0 y1 _ y3 _ _ z _ ->
    Logic.eq_rect_r Prelude.False (NatMap__Raw__R_equal_3 y y0 y1 y3) z) m m' _res __

_NatMap__Raw__map :: (a1 -> a2) -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a2
_NatMap__Raw__map f m =
  case m of {
   ([]) -> ([]);
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f e)) (_NatMap__Raw__map f m')}}

_NatMap__Raw__mapi :: (NatMap__Raw__Coq_key -> a1 -> a2) -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a2
_NatMap__Raw__mapi f m =
  case m of {
   ([]) -> ([]);
   (:) p m' -> case p of {
                (,) k e -> (:) ((,) k (f k e)) (_NatMap__Raw__mapi f m')}}

_NatMap__Raw__option_cons :: NatMap__Raw__Coq_key -> (Prelude.Maybe a1) -> (([]) ((,) NatMap__Raw__Coq_key a1)) -> ([])
                             ((,) NatMap__Raw__Coq_key a1)
_NatMap__Raw__option_cons k o l =
  case o of {
   Prelude.Just e -> (:) ((,) k e) l;
   Prelude.Nothing -> l}

_NatMap__Raw__map2_l :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Raw__Coq_t a1) -> NatMap__Raw__Coq_t a3
_NatMap__Raw__map2_l f m =
  case m of {
   ([]) -> ([]);
   (:) p l -> case p of {
               (,) k e -> _NatMap__Raw__option_cons k (f (Prelude.Just e) Prelude.Nothing) (_NatMap__Raw__map2_l f l)}}

_NatMap__Raw__map2_r :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Raw__Coq_t a2) -> NatMap__Raw__Coq_t a3
_NatMap__Raw__map2_r f m' =
  case m' of {
   ([]) -> ([]);
   (:) p l' -> case p of {
                (,) k e' -> _NatMap__Raw__option_cons k (f Prelude.Nothing (Prelude.Just e')) (_NatMap__Raw__map2_r f l')}}

_NatMap__Raw__map2 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t 
                      a2) -> NatMap__Raw__Coq_t a3
_NatMap__Raw__map2 f m =
  case m of {
   ([]) -> _NatMap__Raw__map2_r f;
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       map2_aux m' =
         case m' of {
          ([]) -> _NatMap__Raw__map2_l f m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case OrderedTypeEx._Nat_as_OT__compare k k' of {
              OrderedType.LT -> _NatMap__Raw__option_cons k (f (Prelude.Just e) Prelude.Nothing) (_NatMap__Raw__map2 f l m');
              OrderedType.EQ -> _NatMap__Raw__option_cons k (f (Prelude.Just e) (Prelude.Just e')) (_NatMap__Raw__map2 f l l');
              OrderedType.GT -> _NatMap__Raw__option_cons k' (f Prelude.Nothing (Prelude.Just e')) (map2_aux l')}}}}
      in map2_aux}}

_NatMap__Raw__combine :: (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t a2) -> NatMap__Raw__Coq_t ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
_NatMap__Raw__combine m =
  case m of {
   ([]) -> _NatMap__Raw__map (\e' -> (,) Prelude.Nothing (Prelude.Just e'));
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       combine_aux m' =
         case m' of {
          ([]) -> _NatMap__Raw__map (\e0 -> (,) (Prelude.Just e0) Prelude.Nothing) m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case OrderedTypeEx._Nat_as_OT__compare k k' of {
              OrderedType.LT -> (:) ((,) k ((,) (Prelude.Just e) Prelude.Nothing)) (_NatMap__Raw__combine l m');
              OrderedType.EQ -> (:) ((,) k ((,) (Prelude.Just e) (Prelude.Just e'))) (_NatMap__Raw__combine l l');
              OrderedType.GT -> (:) ((,) k' ((,) Prelude.Nothing (Prelude.Just e'))) (combine_aux l')}}}}
      in combine_aux}}

_NatMap__Raw__fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> (([]) ((,) a1 a2)) -> a3 -> a3
_NatMap__Raw__fold_right_pair f l i =
  List.fold_right (\p -> f (Datatypes.fst p) (Datatypes.snd p)) i l

_NatMap__Raw__map2_alt :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Raw__Coq_t a1) -> (NatMap__Raw__Coq_t 
                          a2) -> ([]) ((,) NatMap__Raw__Coq_key a3)
_NatMap__Raw__map2_alt f m m' =
  let {m0 = _NatMap__Raw__combine m m'} in
  let {m1 = _NatMap__Raw__map (\p -> f (Datatypes.fst p) (Datatypes.snd p)) m0} in
  _NatMap__Raw__fold_right_pair _NatMap__Raw__option_cons m1 ([])

_NatMap__Raw__at_least_one :: (Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
_NatMap__Raw__at_least_one o o' =
  case o of {
   Prelude.Just _ -> Prelude.Just ((,) o o');
   Prelude.Nothing -> case o' of {
                       Prelude.Just _ -> Prelude.Just ((,) o o');
                       Prelude.Nothing -> Prelude.Nothing}}

_NatMap__Raw__at_least_one_then_f :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (Prelude.Maybe a1) -> (Prelude.Maybe
                                     a2) -> Prelude.Maybe a3
_NatMap__Raw__at_least_one_then_f f o o' =
  case o of {
   Prelude.Just _ -> f o o';
   Prelude.Nothing -> case o' of {
                       Prelude.Just _ -> f o o';
                       Prelude.Nothing -> Prelude.Nothing}}

type NatMap__E__Coq_t = Prelude.Int

_NatMap__E__compare :: Prelude.Int -> Prelude.Int -> OrderedType.Compare Prelude.Int
_NatMap__E__compare x y =
  case PeanoNat._Nat__compare x y of {
   Datatypes.Eq -> OrderedType.EQ;
   Datatypes.Lt -> OrderedType.LT;
   Datatypes.Gt -> OrderedType.GT}

_NatMap__E__eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
_NatMap__E__eq_dec =
  (Prelude.==)

type NatMap__Coq_key = Prelude.Int

type NatMap__Coq_slist elt = NatMap__Raw__Coq_t elt
  -- singleton inductive, whose constructor was Build_slist
  
_NatMap__this :: (NatMap__Coq_slist a1) -> NatMap__Raw__Coq_t a1
_NatMap__this s =
  s

type NatMap__Coq_t elt = NatMap__Coq_slist elt

_NatMap__empty :: NatMap__Coq_t a1
_NatMap__empty =
  _NatMap__Raw__empty

_NatMap__is_empty :: (NatMap__Coq_t a1) -> Prelude.Bool
_NatMap__is_empty m =
  _NatMap__Raw__is_empty (_NatMap__this m)

_NatMap__add :: NatMap__Coq_key -> a1 -> (NatMap__Coq_t a1) -> NatMap__Coq_t a1
_NatMap__add x e m =
  _NatMap__Raw__add x e (_NatMap__this m)

_NatMap__find :: NatMap__Coq_key -> (NatMap__Coq_t a1) -> Prelude.Maybe a1
_NatMap__find x m =
  _NatMap__Raw__find x (_NatMap__this m)

_NatMap__remove :: NatMap__Coq_key -> (NatMap__Coq_t a1) -> NatMap__Coq_t a1
_NatMap__remove x m =
  _NatMap__Raw__remove x (_NatMap__this m)

_NatMap__mem :: NatMap__Coq_key -> (NatMap__Coq_t a1) -> Prelude.Bool
_NatMap__mem x m =
  _NatMap__Raw__mem x (_NatMap__this m)

_NatMap__map :: (a1 -> a2) -> (NatMap__Coq_t a1) -> NatMap__Coq_t a2
_NatMap__map f m =
  _NatMap__Raw__map f (_NatMap__this m)

_NatMap__mapi :: (NatMap__Coq_key -> a1 -> a2) -> (NatMap__Coq_t a1) -> NatMap__Coq_t a2
_NatMap__mapi f m =
  _NatMap__Raw__mapi f (_NatMap__this m)

_NatMap__map2 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (NatMap__Coq_t a1) -> (NatMap__Coq_t a2) -> NatMap__Coq_t
                 a3
_NatMap__map2 f m m' =
  _NatMap__Raw__map2 f (_NatMap__this m) (_NatMap__this m')

_NatMap__elements :: (NatMap__Coq_t a1) -> ([]) ((,) NatMap__Coq_key a1)
_NatMap__elements m =
  _NatMap__Raw__elements (_NatMap__this m)

_NatMap__cardinal :: (NatMap__Coq_t a1) -> Prelude.Int
_NatMap__cardinal m =
  Datatypes.length (_NatMap__this m)

_NatMap__fold :: (NatMap__Coq_key -> a1 -> a2 -> a2) -> (NatMap__Coq_t a1) -> a2 -> a2
_NatMap__fold f m i =
  _NatMap__Raw__fold f (_NatMap__this m) i

_NatMap__equal :: (a1 -> a1 -> Prelude.Bool) -> (NatMap__Coq_t a1) -> (NatMap__Coq_t a1) -> Prelude.Bool
_NatMap__equal cmp m m' =
  _NatMap__Raw__equal cmp (_NatMap__this m) (_NatMap__this m')

