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
     Theory.KeysTheory
     Messages
     Tactics
     Simulation
     RealWorld
     SyntacticallySafe
     AdversarySafety

     ModelCheck.ModelCheck
     ModelCheck.SafeProtocol
     ModelCheck.RealWorldStepLemmas
.

From SPICY Require IdealWorld.

Set Implicit Arguments.

Lemma silent_step_then_labeled_step :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) uid1 ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ra cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Action ra
      -> suid = Some uid1
      -> usrs $? uid1 = Some {| key_heap := ks;
                               protocol := cmdc;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> forall ctx styp, syntactically_safe uid1 (compute_ids usrs) ctx cmd styp
      -> typingcontext_sound ctx usrs cs uid1
      -> message_queues_ok cs usrs gks
      -> forall uid2 bd2 bd2',
          step_user Silent (Some uid2) bd2 bd2'

          -> forall usrs'' adv'' cs'' gks'' cmd2 cmd2' ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              froms2 froms2' sents2 sents2' cur_n2 cur_n2' usrs''',

            bd2 = (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
            -> bd2' = (usrs'', adv'', cs'', gks'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
            -> uid1 <> uid2
            -> usrs $? uid2 = Some {| key_heap := ks2;
                                     protocol := cmd2;
                                     msg_heap := qmsgs2;
                                     c_heap   := mycs2;
                                     from_nons := froms2;
                                     sent_nons := sents2;
                                     cur_nonce := cur_n2 |}
            -> usrs''' = usrs'' $+ (uid2, {| key_heap := ks2';
                                            protocol := cmd2';
                                            msg_heap := qmsgs2';
                                            c_heap   := mycs2';
                                            from_nons := froms2';
                                            sent_nons := sents2';
                                            cur_nonce := cur_n2' |})
            -> exists bd2'',
                step_user (Action ra) (Some uid1)
                          (usrs''', adv'', cs'', gks'', ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                          bd2''
.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; try discriminate; eauto; clean_context.
  - invert H27.
    eapply IHstep_user in H33; eauto.
    split_ex.
    dt x.
    eexists; econstructor; eauto.
  - generalize H38; intros STEP; eapply silent_step_nochange_other_user with (u_id2 := uid1) in H38; eauto.
    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H1.
    eexists; econstructor; eauto.
    invert H6; [
      econstructor 1
    | econstructor 2
    | econstructor 3]; eauto.

    rewrite Forall_forall in H7 |- *; intros * LIN.
    destruct x.
    assert (List.In (existT _ x c) (msgs__front ++ existT _ t0 msg :: msgs__back))
      as LINMSGS by eauto using in_or_app.
    eapply H7 in LIN.

    unfold message_queues_ok in H37
    ; rewrite Forall_natmap_forall in H37
    ; specialize (H37 _ _ H34)
    ; simpl in H37
    ; unfold message_queue_ok in H37
    ; rewrite Forall_forall in H37
    ; assert (List.In (existT _ t0 msg) (msgs__front ++ existT _ t0 msg :: msgs__back)) as LIN2 by eauto using in_elt
    ; apply H37 in LINMSGS
    ; apply H37 in LIN2
    ; split_ex.
    
    unfold not; intros.
    eapply LIN; clear LIN.
    invert H9; econstructor; eauto.
    eapply H0 in H11; split_ors; eauto.
    specialize (H5 _ eq_refl); contradiction.
    eapply H0 in H11; split_ors; eauto.
    specialize (H5 _ eq_refl); contradiction.

  - generalize H37; intros STEP; eapply silent_step_nochange_other_user with (u_id2 := uid1) in H37; eauto.
    (* eapply step_limited_change_other_user in STEP; eauto; split_ex. *)
    destruct (uid2 ==n rec_u_id); subst; clean_map_lookups;
      eexists; econstructor; eauto.
    2: unfold not; intros INV; invert INV; contradiction.
    4: unfold not; intros INV; invert INV; contradiction.
    3: eapply silent_step_nochange_other_user with (u_id2 := rec_u_id) in STEP; eauto; split_ex.

    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H4.
    unfold typingcontext_sound in *; invert H34; split_ex; process_ctx.
    specialize (H3 _ _ H8); context_map_rewrites; eauto.

    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H4.
    unfold typingcontext_sound in *; invert H34; split_ex; process_ctx.
    specialize (H3 _ _ H8); context_map_rewrites; eauto.
Qed.

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
