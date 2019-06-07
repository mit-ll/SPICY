Require Import
        MyPrelude
        Maps.

Definition user_id              := nat.
Definition user_list (A : Type) := NatMap.t A.

(* Exisistential wrapper for stuff, so we can put it in collections *)
Inductive exmsg : Type :=
| Exm {A : Type} (wrapped : A) : exmsg.

(* Labels for the labeled transition system *)
Inductive label  {A} : Type :=
  Silent : label
| Action :  A -> label
.
