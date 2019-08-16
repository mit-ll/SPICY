From Coq Require Import
     String
     Sumbool
     Eqdep.

Require Import
        MyPrelude
        Tactics
        Common
        Maps
        Keys.

Require Import RealWorld.

Set Implicit Arguments.

Ltac solve_findUserKeys_rewrites :=
  repeat
    match goal with
    | [ |- context [RealWorld.user_keys] ] => unfold RealWorld.user_keys
    | [ |- context [ _ $? _] ] => progress clean_map_lookups
    | [ |- context [match _ $? _ with _ => _ end]] => context_map_rewrites
    end; simpl; trivial.

Hint Rewrite @findUserKeys_readd_user_same_keys_idempotent' using solve [ solve_findUserKeys_rewrites ] : find_user_keys.
Hint Rewrite @findUserKeys_readd_user_addnl_keys using solve [ solve_findUserKeys_rewrites ] : find_user_keys.
Hint Rewrite @findUserKeys_readd_user_private_key using solve [ solve_findUserKeys_rewrites ] : find_user_keys.


Ltac clean_context :=
  try discriminate;
  repeat
    match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : Action _ = Action _ |- _ ] => invert H; simpl in *; split_ands
    | [ H : ?x = ?y |- _] => assert (x = y) as EQ by (clear H; trivial); clear H; clear EQ
    end.
