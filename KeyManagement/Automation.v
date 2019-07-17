From Coq Require Import
     String
     Sumbool
     Eqdep.

Require Import
        MyPrelude
        Tactics
        Maps.

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
