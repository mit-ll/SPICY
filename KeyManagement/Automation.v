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

Ltac clean_context :=
  try discriminate;
  repeat
    match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : Action _ = Action _ |- _ ] => invert H; simpl in *; split_ands
    | [ H : ?x = ?y |- _] => assert (x = y) as EQ by (clear H; trivial); clear H; clear EQ
    end.

Ltac simplify_key_merges1 :=
  match goal with
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_chooses_greatest _ _ H1 H2) by trivial; unfold greatest_permission; simpl
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_chooses_greatest _ _ H1 H2) in H3 by trivial; unfold greatest_permission in H3; simpl in *
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) in H3 by trivial
  end.

