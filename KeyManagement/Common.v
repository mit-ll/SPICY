Require Import MyPrelude.

(* Syntactic type of types for messages *)
Inductive type :=
| Nat : type
| Unit : type
(* We will definitely need Text, but do we also need special
 * types for, say, keys.  If so, then we most definitely need
 * type to be implemented separately for both Real and Ideal worlds.
 *
 * | Text : type
 *)
| Prod (t1 t2 : type) : type
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat  => nat
  | Unit => unit
  | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end.



(* Exisistential wrapper for stuff, so we can put it in collections *)
Inductive exmsg : Type :=
| Exm {A : Type} (wrapped : A) : exmsg.

(* Labels for the labeled transition system *)
Inductive label  {A} : Type :=
  Silent : label
| Action :  A -> label
.
