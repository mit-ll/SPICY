(* 
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     String
     Sumbool
     Eqdep.

From SPICY Require Import
     MyPrelude
     Tactics
     Common
     Maps
     Keys
     Messages
     RealWorld
     Simulation.

Set Implicit Arguments.

Hint Resolve in_eq in_cons : core.
Remove Hints absurd_eq_true trans_eq_bool : core.

Ltac clean_context :=
  try discriminate;
  repeat
    match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
    | [ H : Action _ = Action _ |- _ ] => invert H; simpl in *; split_ands
    | [ H : Silent _ = Silent _ |- _ ] => invert H
    | [ H : ?x = ?y |- _] => assert (x = y) as EQ by (clear H; trivial); clear H; clear EQ
    end.

Lemma honest_key_honest_keyb :
  forall honestk k,
    honest_key honestk k <-> honest_keyb honestk k = true.
Proof.
  split; unfold honest_keyb; intros.
  - context_map_rewrites; trivial.
  - cases (honestk $? k); subst; try discriminate.
    cases b; try discriminate; econstructor; eauto.
Qed.

Lemma msg_signed_addressed_has_signing_key :
  forall {t} (msg : crypto t) honestk cs,
    msg_honestly_signed honestk cs msg = true
    -> exists k, msg_signing_key cs msg = Some k
           /\ honest_key honestk k.
Proof.
  unfold msg_honestly_signed, msg_signing_key; intros;
    destruct msg; try discriminate;
      cases (cs $? c_id); try discriminate.
  eexists; rewrite honest_key_honest_keyb; eauto.
Qed.

Ltac specialize_simply1 :=
  match goal with
  | [ H : ?arg -> _, ARG : ?arg |- _ ] =>
    match type of arg with
    | Type => fail 1
    | Set => fail 1
    | cipher_id => fail 1
    | user_id => fail 1
    | key_identifier => fail 1
    | nat => fail 1
    | NatMap.Map.key => fail 1
    | _ => specialize (H ARG)
    end

  | [ H : message_no_adv_private ?honk ?cs ?msg , CONTRA : findKeysCrypto ?cs ?msg $? _ = Some true |- _ ] =>
    specialize (H _ _ CONTRA); split_ands; discriminate
  | [ H : forall x, msg_signing_key ?cs ?msg = Some x -> _, ARG : msg_signing_key ?cs ?msg = Some _ |- _ ] =>
    specialize (H _ ARG)
  | [ H : forall x, msg_signing_key ?cs ?msg = Some x -> _, ARG : msg_honestly_signed _ ?cs ?msg = true |- _ ] =>
    generalize (msg_signed_addressed_has_signing_key _ _ _ ARG); intros; split_ex
  | [ H : forall x, Some ?v = Some x -> _ |- _ ] =>
    specialize (H _ (eq_refl (Some v)))
    (* assert (Some v = Some v) as ARG by trivial; specialize (H _ ARG); clear ARG *)
  | [ HK : honest_keyb ?honk ?k = true, H : honest_key ?honk ?k -> _ |- _ ] =>
    assert (honest_key honk k) as HONK by (rewrite honest_key_honest_keyb; assumption); specialize (H HONK); clear HONK
  | [ H : ?arg = ?arg -> _ |- _ ] => specialize (H (eq_refl arg))
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ -> _ ] => intros
  | [ |- _ /\ _ ] => split
  end.

Ltac specialize_simply := repeat specialize_simply1.



Ltac solve_simply1 :=
  match goal with
  | [ H : ?arg -> _, ARG : ?arg |- _ ] =>
    match type of arg with
    | Type => fail 1
    | Set => fail 1
    | cipher_id => fail 1
    | user_id => fail 1
    | key_identifier => fail 1
    | nat => fail 1
    | NatMap.Map.key => fail 1
    | _ => specialize (H ARG)
    end
  | [ H : ?arg = ?arg -> _ |- _ ] => assert (arg = arg) by trivial
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ -> _ ] => intros
  | [ |- _ /\ _ ] => split
  | [ H : _ \/ _ |- _ ] => destruct H
  end.

Ltac solve_simply := repeat solve_simply1.
