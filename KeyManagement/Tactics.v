From Coq Require Import
     String
     Sumbool
     Eqdep.

Require Import
        MyPrelude.

Set Implicit Arguments.

Ltac split_ands :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac split_ors :=
  repeat match goal with
         | [ H : _ \/ _ |- _ ] => destruct H
         end.

Ltac split_ex :=
  repeat match goal with
         | [ H : exists _, _ |- _ ] => destruct H
         end.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Ltac is_not_var V :=
  first [ is_var V; fail 1
        | idtac ].

Ltac is_not_evar V :=
  first [ is_evar V; fail 1
        | idtac ].

Ltac does_not_unify term1 term2 :=
  first [ unify term1 term2; fail 1
        | idtac ].

Ltac prop_not_exists P :=
  match goal with
  | [ H : P |- _ ] => fail 1
  | _ => idtac
  end.

Ltac prop_not_unifies P :=
  match goal with
  (* | [ H : P |- _ ] => fail 1 *)
  | [ H : ?Q |- _ ] => unify P Q; fail 1
  | _ => idtac
  end.

Ltac assert_if_new P tac :=
  match goal with
  | [ H : P |- _ ] => fail 1
  | _ => assert P by tac
  end.
