(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily reflect the views of the
 * Department of the Air Force.
 *
 * © 2020 Massachusetts Institute of Technology.
 *
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 *
 * The software/firmware is provided to you on an As-Is basis
 *
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)

From Coq Require Import
     Classical
     List.

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     Tactics
     Simulation
     RealWorld
     SyntacticallySafe
     AdversarySafety.

From protocols Require Import
     (* ExampleProtocols *)
     (* ProtocolAutomation *)
     ModelCheck
     SafeProtocol
     RealWorldStepLemmas
.
(* Copy step_usr tactic *)

Require IdealWorld.

Set Implicit Arguments.

(* forall reachable states labels align *)
(* Inductive labels_always_align {A B} : @ModelState A B -> Prop := *)
(* | StepLabelsAlign :  *)
(*     forall st, *)
(*       (forall st', step st st' -> labels_always_align st') *)
(*       -> labels_align st *)
(*       -> labels_always_align st. *)

(* Definition stuck_step_implies_stuck_universe_step {t__hon t__adv} *)
(*            (st : @ModelState t__hon t__adv) : Prop := *)
(*   (forall st', step st st' -> False) *)
(*   -> forall lbl ru', *)
(*     step_universe (fst (fst st)) lbl ru' -> False. *)

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
            (* -> forall ia, action_matches cs gks ra ia *)
            -> exists bd2'',
                step_user (Action ra) (Some uid1)
                          (usrs''', adv'', cs'', gks'', ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                          bd2''
              (* /\ action_matches cs'' gks'' ra ia *)
                  (* ru' = buildUniverse usrs' adv' cs' gks' u_id1 {| key_heap  := ks' *)
                  (*                                                    ; msg_heap  := qmsgs' *)
                  (*                                                    ; protocol  := cmdc' *)
                  (*                                                    ; c_heap    := mycs' *)
                  (*                                                    ; from_nons := froms' *)
                  (*                                                    ; sent_nons := sents' *)
                  (*                                                    ; cur_nonce := cur_n' |} *)
                  (* ->  action_matches ra ru' ia iu. *)
.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; try discriminate; eauto; clean_context.
  - invert H27.
    eapply IHstep_user in H33; eauto.
    split_ex.
    dt x.
    eexists; econstructor; eauto.
  - generalize H36; intros STEP; eapply silent_step_nochange_other_user with (u_id2 := uid1) in H36; eauto.
    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H0.
    eexists; econstructor; eauto.
    invert H6; [
      econstructor 1
    | econstructor 2
    | econstructor 3]; eauto.

  - generalize H36; intros STEP; eapply silent_step_nochange_other_user with (u_id2 := uid1) in H36; eauto.
    (* eapply step_limited_change_other_user in STEP; eauto; split_ex. *)
    destruct (uid2 ==n rec_u_id); subst; clean_map_lookups;
      eexists; econstructor; eauto.
    2: unfold not; intros INV; invert INV; contradiction.
    4: unfold not; intros INV; invert INV; contradiction.
    3: eapply silent_step_nochange_other_user with (u_id2 := rec_u_id) in STEP; eauto; split_ex.

    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H4.
    unfold typingcontext_sound in *; invert H34; split_ex; process_ctx.
    specialize (H3 _ _ H7); context_map_rewrites; eauto.

    eapply step_limited_change_other_user with (u_id2 := uid1) in STEP; eauto; split_ex.
    clear H4.
    unfold typingcontext_sound in *; invert H34; split_ex; process_ctx.
    specialize (H3 _ _ H7); context_map_rewrites; eauto.
Qed.

(* Lemma step_reorder_no_recur : *)
(*   forall A B C lbl1 suid1 uid1 (bd1 bd1' : data_step0 A B C), *)
(*     step_user lbl1 suid1 bd1 bd1' *)
(*     -> suid1 = Some uid1 *)
(*     -> forall D (bd2 bd2' : data_step0 A B D) lbl2 suid2 uid2, *)
(*         step_user lbl2 suid2 bd2 bd2' *)
(*         -> suid2 = Some uid2 *)
(*         -> uid1 <> uid2 *)
(*         -> forall cs cs1' cs2' (usrs usrs1' usrs2' : honest_users A) (adv adv1' adv2' : user_data B) gks gks1' gks2' *)
(*             ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' *)
(*             ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' *)
(*             cmdc1 cmdc2, *)

(*               bd1  = (usrs,   adv,   cs,   gks,   ks1,  qmsgs1,  mycs1,  froms1,  sents1,  cur_n1,  cmd1) *)
(*             -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1') *)
(*             -> bd2  = (usrs,   adv,   cs,   gks,   ks2,  qmsgs2,  mycs2,  froms2,  sents2,  cur_n2,  cmd2) *)
(*             -> bd2' = (usrs2', adv2', cs2', gks2', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2') *)

(*             -> nextAction cmd1 cmd1 *)
(*             -> nextAction cmd2 cmd2 *)
(*             -> nextAction cmdc2 cmd2 *)
(*             (* goodness *) *)
(*             -> goodness_predicates (mkUniverse usrs adv cs gks) *)
(*             -> syntactically_safe_U (mkUniverse usrs adv cs gks) *)
(*             (* allow protocol to freely vary, since we won't be looking at it *) *)
(*             -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1) *)
(*             -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*             -> forall cmdc1' usrs1'',  *)
(*                 usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') *)
(*                 -> usrs1'' $? uid2 = Some {| key_heap := ks2; *)
(*                                             protocol := cmdc2; *)
(*                                             msg_heap := qmsgs2; *)
(*                                             c_heap := mycs2; *)
(*                                             from_nons := froms2; *)
(*                                             sent_nons := sents2; *)
(*                                             cur_nonce := cur_n2 |} *)
(*                 -> exists bd2'', *)
(*                   step_user lbl2 suid2 *)
(*                             (usrs1'', adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2''. *)
(* Proof. *)
(*   (* destruct 1; destruct 2; inversion 3; inversion 1. why not this? too slow? *) *)
(*   intros; cases cmd1; subst. *)
(*   - cases cmd2; invert H1; invert H; clean_map_lookups; simpl. *)
(*   - eapply nextAction_couldBe in H8. contradiction. *)
(*   - cases cmd2; intros; invert H1; invert H; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence. *)
(*       econstructor; eauto. econstructor; eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; intros; invert H1; invert H; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst; destruct (uid0 ==n uid1); subst. *)
(*       * econstructor; eauto. econstructor; eauto. *)
(*       * econstructor; eauto. econstructor; eauto. *)
(*       * econstructor; eauto. econstructor; eauto. congruence. *)
(*       * destruct (uid ==n uid0); subst. econstructor; eauto. econstructor; eauto. congruence.   *)
(*         do 2 (econstructor; eauto). congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. (*; try (econstructor; eauto; econstructor; eauto).S*) *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst; econstructor; eauto; econstructor; eauto; congruence. *)
(*     + destruct (uid ==n uid1); subst; econstructor; eauto; econstructor; eauto; congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor. *)
(*     + destruct (uid1 ==n uid). econstructor; eauto. econstructor; eauto. *)
(*       intros. unfold syntactically_safe_U in H11. split_ex. *)
(*       specialize (H12 uid2). simpl in *. generalize H14. intro H__new. *)
(*       eapply H12 in H14. destruct H14. destruct H0 as [ H__syn H__typ ].  *)
(*       split_ex. (* is it possible to send to yourself? *) *)
(*       simpl in *. unfold typingcontext_sound in *. *)
(*       split_ex. specialize (H2 _ msg0 uid). *)
(*       eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H15. *)
(*       split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto. *)
(*       unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H19 in H4. *)
(*       eauto. eauto. congruence. *)

(*       econstructor; eauto. econstructor; eauto. *)
(*       intros. unfold syntactically_safe_U in H12. split_ex. *)
(*       specialize (H12 uid2). simpl in *. generalize H14. intro H__newer. *)
(*       eapply H12 in H__newer. destruct H__newer. destruct H0 as [ H__syn H__typ ].  *)
(*       split_ex. (* is it possible to send to yourself? *) *)
(*       simpl in *. unfold typingcontext_sound in *. *)
(*       split_ex. specialize (H2 _ msg0 uid). *)
(*       eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H16. *)
(*       split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto. *)
(*       unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H20 in H4. *)
(*       eauto. eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*       unfold not in *. intros.  invert H. *)
(*       * eapply H40. econstructor. *)
(*       * eapply H40. econstructor; try eassumption. destruct (c_id0 ==n c_id); eauto. *)
(*       * eapply H40. invert H6. econstructor; try eassumption. *)
(*         destruct (c_id0 ==n c_id); subst; eauto. *)
(*            unfold goodness_predicates in H11; split_ands.  *)
(*            unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5. simpl in H5. *)
(*            specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5. *)
(*            invert H5. split_ex. specialize (H15 _ eq_refl). tauto. eauto. *)
(*     + econstructor; eauto. *)
(*       eapply StepEncrypt with (c_id1 := next_key (cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (Some uid1, cur_n1) msg))); eauto. *)
(*       clean_map_lookups. eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. *)
(*       eapply StepSign with (c_id1 := next_key (cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (Some uid1, cur_n1) msg))); eauto. *)
(*       clean_map_lookups. eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence. *)
(*       econstructor; eauto. econstructor; eauto. congruence. + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid1 ==n uid). econstructor; eauto. econstructor; eauto. *)
(*       intros. unfold syntactically_safe_U in H11. split_ex. *)
(*       specialize (H12 uid2). simpl in *. generalize H14. intro H__new. *)
(*       eapply H12 in H14. destruct H14. destruct H0 as [ H__syn H__typ ].  *)
(*       split_ex. (* is it possible to send to yourself? *) *)
(*       simpl in *. unfold typingcontext_sound in *. *)
(*       split_ex. specialize (H2 _ msg0 uid). *)
(*       eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H15. *)
(*       split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto. *)
(*       unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H19 in H4. *)
(*       eauto. eauto. congruence. *)

(*       econstructor; eauto. econstructor; eauto. *)
(*       intros. unfold syntactically_safe_U in H12. split_ex. *)
(*       specialize (H12 uid2). simpl in *. generalize H14. intro H__newer. *)
(*       eapply H12 in H__newer. destruct H__newer. destruct H0 as [ H__syn H__typ ].  *)
(*       split_ex. (* is it possible to send to yourself? *) *)
(*       simpl in *. unfold typingcontext_sound in *. *)
(*       split_ex. specialize (H2 _ msg0 uid). *)
(*       eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H16. *)
(*       split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto. *)
(*       unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H20 in H4. *)
(*       eauto. eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*       unfold not in *. intros.  invert H. *)
(*       * eapply H43. econstructor. *)
(*       * eapply H43. invert H6. econstructor; try eassumption. *)
(*         destruct (c_id0 ==n c_id); subst; eauto. *)
(*            unfold goodness_predicates in H11; split_ands.  *)
(*            unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5. simpl in H5. *)
(*            specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5. *)
(*            invert H5. split_ex. specialize (H15 _ eq_refl). tauto. eauto. *)
(*       * eapply H43. invert H6. econstructor; try eassumption. *)
(*         destruct (c_id0 ==n c_id); subst; eauto. *)
(*            unfold goodness_predicates in H11; split_ands.  *)
(*            unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5. *)
(*            specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5. *)
(*            invert H5. split_ex. specialize (H15 _ eq_refl). tauto. *)
(*     + econstructor; eauto.  eapply StepEncrypt with (c_id1 := next_key (cs $+ (c_id, SigCipher k msg_to (Some uid1, cur_n1) msg))); eauto. clean_map_lookups. eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto.  eapply StepSign with (c_id1 := next_key (cs $+ (c_id, SigCipher k msg_to (Some uid1, cur_n1) msg))); eauto. clean_map_lookups. eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence. *)
(*       econstructor; eauto. econstructor; eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence. *)
(*       econstructor; eauto. econstructor; eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. eapply StepGenerateSymKey with *)
(*                                (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := SymKey |}))); eauto. *)
(*       eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. eapply StepGenerateAsymKey with *)
(*                                (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := SymKey |}))); eauto. *)
(*       eapply next_key_not_in. trivial. *)
(*   - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + eapply nextAction_couldBe in H9. contradiction. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence. *)
(*       econstructor; eauto. econstructor; eauto. congruence. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. econstructor; eauto. *)
(*     + econstructor; eauto. eapply StepGenerateSymKey with (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := AsymKey |}))); eauto. *)
(*       eapply next_key_not_in. trivial. *)
(*     + econstructor; eauto. eapply StepGenerateAsymKey with *)
(*                               (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := AsymKey |}))) ; eauto. *)
(*       eapply next_key_not_in. trivial. Unshelve. eauto. eauto. eauto. eauto. eauto. eauto. *)
(*       eauto. eauto. eauto. eauto. *)
(* Qed. *)

(* Hint Resolve step_reorder_no_recur. *)

(* Lemma step_reorder_recur2 : *)
(*   forall A B C lbl1 suid1 uid1 (bd1 bd1' : data_step0 A B C), *)
(*     step_user lbl1 suid1 bd1 bd1' *)
(*     -> suid1 = Some uid1 *)
(*     -> forall D (bd2 bd2' : data_step0 A B D) lbl2 suid2 uid2, *)
(*         step_user lbl2 suid2 bd2 bd2' *)
(*         -> suid2 = Some uid2 *)
(*         -> uid1 <> uid2 *)
(*         -> forall cs cs1' cs2' (usrs usrs1' usrs2' : honest_users A) (adv adv1' adv2' : user_data B) gks gks1' gks2' *)
(*             ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' *)
(*             ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' *)
(*             cmdc1 cmdc2, *)

(*               bd1  = (usrs,   adv,   cs,   gks,   ks1,  qmsgs1,  mycs1,  froms1,  sents1,  cur_n1,  cmd1) *)
(*             -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1') *)
(*             -> bd2  = (usrs,   adv,   cs,   gks,   ks2,  qmsgs2,  mycs2,  froms2,  sents2,  cur_n2,  cmd2) *)
(*             -> bd2' = (usrs2', adv2', cs2', gks2', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2') *)

(*             -> nextAction cmd1 cmd1 *)
(*             (* -> nextAction cmd2 cmd2 *) *)
(*             -> nextAction cmdc2 cmd2 *)
(*             (* goodness *) *)
(*             -> goodness_predicates (mkUniverse usrs adv cs gks) *)
(*             -> syntactically_safe_U (mkUniverse usrs adv cs gks) *)
(*             (* allow protocol to freely vary, since we won't be looking at it *) *)
(*             -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1) *)
(*             -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*             -> forall cmdc1' usrs1'',  *)
(*                 usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') *)
(*                 -> usrs1'' $? uid2 = Some {| key_heap := ks2; *)
(*                                             protocol := cmdc2; *)
(*                                             msg_heap := qmsgs2; *)
(*                                             c_heap := mycs2; *)
(*                                             from_nons := froms2; *)
(*                                             sent_nons := sents2; *)
(*                                             cur_nonce := cur_n2 |} *)
(*                 -> exists bd2'', *)
(*                   step_user lbl2 suid2 *)
(*                             (usrs1'', adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2''. *)
(* Proof. *)
(*   intros; cases cmd1; subst. *)
(*   - induction cmd2; invert H1; invert H; clean_map_lookups; simpl; eauto. *)
(*   - admit. *)
(*     (* induction cmd2; invert H1; invert H; clean_map_lookups; simpl.  *) *)
(*   - induction cmd2; invert H1; invert H; clean_map_lookups; simpl; eauto. *)
(*     + invert H9. admit. *)
(*     + admit. *)
(*     + invert H9. econstructor; eauto. econstructor; eauto. econstructor; eauto. econstructor; eauto. *)
(*     + invert H9. destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. *)
(*       congruence. econstructor; eauto. econstructor; eauto. congruence. econstructor; eauto. *)
(*       econstructor; eauto. 2: congruence.  *)
(*       (* eassumption. econstructor; eauto. econstructor; eauto. *) *)
(* Admitted. *)

(* Lemma step_reorder_recur : *)
(*   forall A B C lbl1 suid1 uid1 (bd1 bd1' : data_step0 A B C), *)
(*     step_user lbl1 suid1 bd1 bd1' *)
(*     -> suid1 = Some uid1 *)
(*     -> forall D (bd2 bd2' : data_step0 A B D) lbl2 suid2 uid2, *)
(*         step_user lbl2 suid2 bd2 bd2' *)
(*         -> suid2 = Some uid2 *)
(*         -> uid1 <> uid2 *)
(*         -> forall cs cs1' cs2' (usrs usrs1' usrs2' : honest_users A) (adv adv1' adv2' : user_data B) gks gks1' gks2' *)
(*             ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' *)
(*             ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' *)
(*             cmdc1 cmdc2, *)

(*               bd1  = (usrs,   adv,   cs,   gks,   ks1,  qmsgs1,  mycs1,  froms1,  sents1,  cur_n1,  cmd1) *)
(*             -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1') *)
(*             -> bd2  = (usrs,   adv,   cs,   gks,   ks2,  qmsgs2,  mycs2,  froms2,  sents2,  cur_n2,  cmd2) *)
(*             -> bd2' = (usrs2', adv2', cs2', gks2', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2') *)

(*             (* -> nextAction cmd1 cmd1 *) *)
(*             (* -> nextAction cmd2 cmd2 *) *)
(*             -> nextAction cmdc2 cmd2 *)
(*             (* goodness *) *)
(*             -> goodness_predicates (mkUniverse usrs adv cs gks) *)
(*             -> syntactically_safe_U (mkUniverse usrs adv cs gks) *)
(*             (* allow protocol to freely vary, since we won't be looking at it *) *)
(*             -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1) *)
(*             -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*             -> forall cmdc1' usrs1'',  *)
(*                 usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') *)
(*                 -> usrs1'' $? uid2 = Some {| key_heap := ks2; *)
(*                                             protocol := cmdc2; *)
(*                                             msg_heap := qmsgs2; *)
(*                                             c_heap := mycs2; *)
(*                                             from_nons := froms2; *)
(*                                             sent_nons := sents2; *)
(*                                             cur_nonce := cur_n2 |} *)
(*                 -> exists bd2'', *)
(*                   step_user lbl2 suid2 *)
(*                             (usrs1'', adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2''. *)
(* Proof. *)
(* Admitted. *)

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
          -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
          -> forall usrs'', usrs'' = usrs' $+ (uid, mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n')
          -> forall iu v, labels_align (mkUniverse usrs'' adv' cs' gks', iu, v)
          -> labels_align (mkUniverse usrs adv cs gks, iu, v).
Proof.
  unfold labels_align; intros; subst.
  invert H8.
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

  eapply H7 in IRS; split_ex.
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
  eapply labels_align_user_step; eauto.
  trivial.

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
