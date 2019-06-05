From Coq Require Import
     String
     Sumbool
     Eqdep.

Require Import
        MyPrelude
        Common
        Maps.

Set Implicit Arguments.

Ltac context_map_rewrites :=
  repeat
    match goal with
    | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H
    | [ H : match ?matchee with _ => _ end $? _ = _
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    | [ H : match ?matchee with _ => _ end = _
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    end.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Ltac clean_context :=
  try discriminate;
  repeat
    match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : Some _ = Some _ |- _ ] => invert H
    end.
