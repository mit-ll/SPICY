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
     Automation
     Maps
     Keys
     Messages
     Tactics
     Simulation
     RealWorld
     SyntacticallySafe
     AdversarySafety
     Theory.KeysTheory

     ModelCheck.ModelCheck
     ModelCheck.RealWorldStepLemmas
.

From SPICY Require IdealWorld.

Set Implicit Arguments.

Lemma labels_align_user_step :
    forall {A B} suid (bd bd' : data_step0 A B (Base A)),

      step_user Silent suid bd bd'
      -> forall uid, suid = Some uid
      -> forall cs cs' (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks'
          ks ks' qmsgs qmsgs' mycs mycs' cmd cmd' froms froms' sents sents' cur_n cur_n',

          bd  = (usrs,  adv,  cs,  gks,  ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> bd'  = (usrs',  adv',  cs',  gks',  ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> syntactically_safe_U (mkUniverse usrs adv cs gks)
          -> goodness_predicates (mkUniverse usrs adv cs gks)
          -> message_queues_ok cs usrs gks
          -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
          -> forall usrs'', usrs'' = usrs' $+ (uid, mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n')
          -> forall iu v, labels_align (mkUniverse usrs'' adv' cs' gks', iu, v)
          -> labels_align (mkUniverse usrs adv cs gks, iu, v).
Proof.
  unfold labels_align; intros; subst.
  invert H9.
  unfold build_data_step in H1; simpl in *.
  destruct userData; simpl in *.

  destruct (uid ==n uid0); subst; clean_map_lookups.
  pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H1 H); discriminate.

  generalize H; intros SILENT; eapply silent_step_nochange_other_user in H; eauto.
  unfold syntactically_safe_U in H3;
    specialize (H3 _ _ _ H0 eq_refl); split_ex; simpl in *.
  generalize H1; intros ASTEP; eapply silent_step_then_labeled_step with (uid2 := uid) in H1; eauto.
  split_ex.

  dt x1.

  assert (
      IRS :
        indexedRealStep uid0 (Action ra)
                        {| users := usrs' $+ (uid,
                                              {|
                                                key_heap := ks';
                                                protocol := cmd';
                                                msg_heap := qmsgs';
                                                c_heap := mycs';
                                                from_nons := froms';
                                                sent_nons := sents';
                                                cur_nonce := cur_n' |});
                           adversary := adv';
                           all_ciphers := cs';
                           all_keys := gks' |}
                        
                        (buildUniverse usrs1 adv1 cs1 gks1 uid0 {| key_heap  := ks1
                                                                   ; msg_heap  := qmsgs1
                                                                   ; protocol  := cmd1
                                                                   ; c_heap    := mycs1
                                                                   ; from_nons := froms1
                                                                   ; sent_nons := sents1
                                                                   ; cur_nonce := cur_n1 |}))
    by (econstructor; eauto).

  eapply H8 in IRS; split_ex.
  (do 3 eexists); repeat simple apply conj; eauto.

  unfold goodness_predicates in *; split_ex.
  eapply action_matches_other_user_silent_step_inv; eauto.
Qed.

Lemma alignment_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> syntactically_safe_U (fst (fst st))
    -> goodness_predicates (fst (fst st))
    -> alignment st'
    -> alignment st.
Proof.
  intros.
  unfold alignment in *.
  destruct st as [[ru iu] v].
  destruct st' as [[ru' iu'] v'].
  split_ex; subst.
  invert H; simpl in *; try discriminate; eauto.
  invert H6; dismiss_adv.
  split; trivial.
  
  destruct ru, userData; simpl in *.
  unfold mkULbl in H8; destruct lbl; invert H8.
  eapply labels_align_user_step; eauto.
  trivial.

  unfold goodness_predicates in H2; split_ex; eauto.
 
  Unshelve.
  exact true.
Qed.

Lemma alignment_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> syntactically_safe_U (fst (fst st))
    -> goodness_predicates (fst (fst st))
    -> ~ alignment st
    -> ~ alignment st'.
Proof.
  unfold not; intros.
  eauto using alignment_violation_step'.
Qed.

Lemma alignment_violation_steps :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv)^* st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> goodness_predicates (fst (fst st))
    -> syntactically_safe_U (fst (fst st))
    -> ~ alignment st
    -> ~ alignment st'.
Proof.
  induction 1; intros; eauto.

  assert (LAME : lameAdv b (fst (fst y)).(adversary)) by eauto using adversary_remains_lame_step.
  assert (SS : syntactically_safe_U (fst (fst y)))
    by eauto using syntactically_safe_U_preservation_step.
  assert (GOOD : goodness_predicates (fst (fst y)))
    by eauto using goodness_preservation_step.
  destruct x, y, z; simpl in *.

  generalize H; intros VIOL; eapply alignment_violation_step in VIOL; eauto.
Qed.

Lemma final_alignment_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ returns_align st
    -> ~ returns_align st'.
Proof.
  unfold not; intros.
  unfold returns_align in *.

  invert H; eapply H1; intros; try solve[ exfalso; eauto ].

  clear H1 H2; invert H3.
  - exfalso; eapply H; econstructor 1; eauto.
  - unfold lameAdv in H0; simpl in H0.
    unfold build_data_step in H1
    ; simpl in H1
    ; rewrite H0 in H1
    ; invert H1.
Qed.

Lemma final_alignment_violation_steps :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv)^* st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ returns_align st
    -> ~ returns_align st'.
Proof.
  induction 1; intros; eauto.

  assert (LAME : lameAdv b (fst (fst y)).(adversary)) by eauto using adversary_remains_lame_step.
  destruct x, y, z; simpl in *.

  generalize H; intros VIOL; eapply final_alignment_violation_step in VIOL; eauto.
Qed.
