(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     Classical
     List.

From SPICY Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     MessagesTheory
     Tactics
     Simulation
     RealWorld
     InvariantsTheory
     SafetyAutomation
     SyntacticallySafe
     AdversarySafety

     ModelCheck.ProtocolFunctions
     ModelCheck.SafeProtocol
     ModelCheck.RealWorldStepLemmas
.

Set Implicit Arguments.

Import RealWorldNotations.
Import SafetyAutomation.

Definition no_resends (sents : sent_nonces) :=
  NoDup sents.

Definition no_resends_U {A B} (U : universe A B) :=
  Forall_natmap (fun u => no_resends u.(sent_nons)) U.(users).

Lemma no_resends_user_step :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc u_id,
          suid = Some u_id
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> no_resends sents'
          -> no_resends sents.
Proof.
  induction 1; inversion 1; inversion 1; unfold no_resends; intros; subst; eauto.

  - eapply IHstep_user in H25; eauto.
  - unfold updateSentNonce in H33.
    destruct msg; eauto.
    cases (cs' $? c_id); eauto.
    destruct (rec_u_id ==n cipher_to_user c); subst; eauto.
    invert H33; eauto.
Qed.

Lemma resend_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> no_resends_U (fst (fst st'))
    -> no_resends_U (fst (fst st)).
Proof.
  induction 1; unfold no_resends_U; rewrite !Forall_natmap_forall; destruct ru, v; simpl in *; intros.

  - invert H; unfold build_data_step in *; simpl in *; dismiss_adv.
  
    destruct (u_id ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H1 k); rewrite add_eq_o in H1 by trivial.
      specialize (H1 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H1 k); rewrite add_neq_o in H1 by congruence.
      destruct userData; eapply silent_step_nochange_other_user with (u_id2 := k) in H4; eauto.
      clean_map_lookups; simpl in *.
      specialize (H1 _ H4); eauto.
      unfold mkULbl in *; destruct lbl; try discriminate; trivial.

  - invert H; unfold build_data_step in *; simpl in *.
    destruct (uid ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H5 k); rewrite add_eq_o in H5 by trivial.
      specialize (H5 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H5 k); rewrite add_neq_o in H5 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H7; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H5 _ H9); eauto.
      specialize (H5 _ H9); eauto.

  - invert H; unfold build_data_step in *; simpl in *.
    destruct (uid ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H4 k); rewrite add_eq_o in H4 by trivial.
      specialize (H4 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H4 k); rewrite add_neq_o in H4 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H5; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H4 _ H8); eauto.
      specialize (H4 _ H8); eauto.
  - invert H; unfold build_data_step in *; simpl in *.
    destruct (uid ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H4 k); rewrite add_eq_o in H4 by trivial.
      specialize (H4 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H4 k); rewrite add_neq_o in H4 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H5; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H4 _ H8); eauto.
      specialize (H4 _ H8); eauto.
Qed.

Lemma resend_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ no_resends_U (fst (fst st))
    -> ~ no_resends_U (fst (fst st')).
Proof.
  unfold not; intros.
  eauto using resend_violation_step'.
Qed.

Lemma resend_violation_steps :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) ^* st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ no_resends_U (fst (fst st))
    -> ~ no_resends_U (fst (fst st')).
Proof.
  induction 1; intros; eauto.

  specialize (adversary_remains_lame_step _ _ _ _ _ H1 H); intros.
  destruct x, y, z; simpl in *.

  generalize H; intros VIOL; eapply resend_violation_step in VIOL; eauto.
Qed.
