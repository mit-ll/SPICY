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
     ExampleProtocols
     ProtocolAutomation
     ModelCheck
     SafeProtocol
     RealWorldStepLemmas
.
(* Copy step_usr tactic *)

Require IdealWorld.

Set Implicit Arguments.

(* forall reachable states labels align *)
Inductive labels_always_align {A B} : (universe A B * IdealWorld.universe A) -> Prop :=
| StepLabelsAlign : 
    forall st,
      (forall st', step st st' -> labels_always_align st')
      -> labels_align st
      -> labels_always_align st.

Definition stuck_step_implies_stuck_universe_step {t__hon t__adv}
           (st : universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  (forall st', step st st' -> False)
  -> forall lbl ru',
    step_universe (fst st) lbl ru' -> False.


(* Definition almostEqual {A}  (ud ud' : user_data A) := *)
(*   ud = ud' \/ *)
(*   (exists msg, ud =  *)
(*   {| *)
(*   key_heap := key_heap ud'; *)
(*   protocol := protocol ud'; *)
(*   msg_heap := msg_heap ud' ++ [msg]; *)
(*   c_heap := c_heap ud'; *)
(*   from_nons := from_nons ud'; *)
(*   sent_nons := sent_nons ud'; *)
(*   cur_nonce := cur_nonce ud' |}). *)

(* Lemma non_stepped_ud_almost_equal : *)
(*   forall { A B C } suid lbl bd1 bd2, *)
(*     step_user lbl suid bd1 bd2 *)
(*     -> forall (users1 users2 : honest_users A) (adv1 adv2 : user_data B) cs1 cs2 gks1 gks2 *)
(*         stepper ks1 ks2 qmsgs1 qmsgs2 mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2 *)
(*         (cmdc1 cmdc2 : user_cmd C) cmd1, *)
(*       bd1 = (users1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1) *)
(*       -> bd2 = (users2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2) *)
(*       -> suid = Some stepper *)
(*     -> users1 $? stepper = Some {| key_heap := ks1 *)
(*                                ; protocol := cmd1 *)
(*                                ; msg_heap := qmsgs1 *)
(*                                ; c_heap := mycs1 *)
(*                                ; from_nons := froms1 *)
(*                                ; sent_nons := sents1 *)
(*                                ; cur_nonce := cur_n1 |} *)
(*     -> (forall uid ud1 ud2, *)
(*           uid <> stepper *)
(*           -> users1 $? uid = Some ud1 *)
(*           -> users2 $? uid = Some ud2 *)
(*           -> almostEqual ud2 ud1). *)
(* Proof. *)
(*   induct 1; inversion 1; inversion 1; intros; subst; clean_context; clean_map_lookups; eauto; unfold almostEqual; eauto. *)
  
(*   destruct (rec_u_id ==n uid); subst; clean_map_lookups; eauto. *)
(* Qed. *)

(* Lemma different_steps_must_be_by_different_users : *)
(*   forall { A B C } (bd1 bd2 bd__other : data_step0 A B C ) lbl1 lbl2 u_id1 u_id2, *)
(*     (* lameAdv b bd1.(adversary) *) *)
(*     step_user lbl1 (Some u_id1) bd1 bd2 *)
(*     -> step_user lbl2 (Some u_id2) bd1 bd__other *)
(*     -> lbl1 <> lbl2 *)
(*     -> u_id1 <> u_id2. *)
(* Proof. *)
(*   (* inversion 2; inversion 1; intros; subst; eauto. *) *)

(*   (* destruct ru1.  unfold build_data_step in *. destruct userData. destruct userData0. simpl in *. *) *)
(*   (* clean_map_lookups. *) *)
(*   (* destruct ru1. destruct adversary. simpl in *. unfold build_data_step in *. simpl in *. *) *)
(*   (* rewrite H in H8. invert H8. admit. admit. *) *)
(* Admitted. *)



        (* relation between ru__other ru'' : only A and global state are different *)
(* Definition only_global_or_single_user_state_changed {A B C} (bd1 bd2 : data_step0 A B C) (u_id : user_id) := *)
(*   forall u_id' u_d1 u_d2 ru1 ru2, *)
(*     ru1.(users) $? u_id' = Some u_d1 *)
(*     -> bd1 = build_data_step ru1 u_d1 *)
(*     -> ru2.(users) $? u_id' = Some u_d2 *)
(*     -> u_id' <> u_id *)
(*     -> u_d1 = u_d2. *)

(* Lemma silent_leading_step_preserves_action_matches : *)
(*   forall {A B C} (* (ru ru' ru__other : RealWorld.universe A B) *) ra u_id1 u_id2 (bd bd' bd__other : data_step0 A B C), *)
(*     (* ru = buildUniverse_step bd u_id1 *) *)
(*      step_user Silent (Some u_id1) bd bd' *)
(*      (* -> step_universe ru Silent ru' *) *)
(*      (* -> bd = build_data_step  *) *)
(*     -> step_user (Action ra) (Some u_id2) bd bd__other *)
(*     -> forall (users1 users2 : honest_users A) (adv1 adv2 : user_data B) cs1 cs2 gks1 gks2 *)
(*          ks1 ks2 qmsgs1 qmsgs2 mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2 *)
(*         (cmdc1 cmdc2 : user_cmd C), *)
(*       bd = (users1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1) *)
(*       -> bd' = (users2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2) *)
(*     -> exists bd'' , *)
(*         step_user (Action ra) (Some u_id2) bd' bd'' *)
(*         -> only_global_or_single_user_state_changed bd__other bd'' u_id1. *)
(*         (* -> action_matches (buildUniverse_step bd') ra iu ia = action_matches (buildUniverse_step bd'') ra iu ia. *) *)
(* Proof. *)
(*   induction 1; inversion 2; inversion 1; intros; subst; eauto. *)
(*   clear H1. clear H2. eexists.  *)
  
  
(* Lemma silent_step_blah :      *)
(*   forall {A B C} suid lbl bd bd', *)
(*     step_user lbl suid bd bd' *)
(*     -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
(*         (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs' *)
(*         froms froms' sents sents' cur_n cur_n', *)
(*       bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*       -> lbl = Silent *)
(*       -> forall cmdc cmdc' u_id1 u_id2 ud2 usrs'', *)
(*           suid = Some u_id1 *)
(*           -> u_id1 <> u_id2 *)
(*           -> usrs $? u_id1 = Some {| key_heap := ks; *)
(*                                     protocol := cmdc; *)
(*                                     msg_heap := qmsgs; *)
(*                                     c_heap   := mycs; *)
(*                                     from_nons := froms; *)
(*                                     sent_nons := sents; *)
(*                                     cur_nonce := cur_n |} *)
(*           -> usrs $? u_id2 = Some ud2 *)
(*           -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks'; *)
(*                                          protocol := cmdc'; *)
(*                                          msg_heap := qmsgs'; *)
(*                                          c_heap   := mycs'; *)
(*                                          from_nons := froms'; *)
(*                                          sent_nons := sents'; *)
(*                                          cur_nonce := cur_n' |}) *)
(*           -> usrs'' $? u_id2 = Some ud2. *)
(* Proof. *)
(*   induction 1; inversion 1; inversion 1; *)
(*     intros; subst; *)
(*       try discriminate; *)
(*       try solve [ clean_map_lookups; trivial ]. *)
(*   specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _ *)
(*                           _ _ _ _ _ _ _ _ _ _ _ *)
(*                           eq_refl eq_refl eq_refl). *)
(*   specialize (IHstep_user cmdc cmdc'). *)
(*   specialize (IHstep_user _ _ _ _ eq_refl H26 H27 H28 eq_refl). *)
(*   clean_map_lookups; eauto. *)
(* Qed. *)

Lemma syntactically_safe_honest_keys_' :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' (* ctx sty *),

      (* how do I get msg introduced? *)

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall honestk honestk' cmdc cmdc' u_id,
          suid = Some u_id
          (* -> syntactically_safe u_id ctx cmd sty *)
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          (* -> Vjtypechecker_sound ctx honestk cs u_id *)
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmdc';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |})).
          (* -> ks' $k++ findKeysMessage msg $? k__sign = ks' $? k__sign. *)
Proof.
Admitted.

(*
Lemma syntactically_safe_pk_in_message_owned_by_some_honest_user :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty p,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, (Recv p))
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', (Return c_id))

      -> cs' $? c_id = Some (SigEncCipher k__signid k__encid msg_to nonce msg)
-> forall honestk honestk' cmdc cmdc' u_id,
          suid = Some u_id
          -> syntactically_safe u_id ctx cmd sty
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> typechecker_sound ctx honestk cs u_id
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmdc';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |}))

    findKeysMessage msg $? k__sign = Some true ->
    (exists (u : Map.key),
        (forall data__rw data__iw,
            usrs' $? u = Some data__rw
            -> IdealWorld.users ui $? u = Some data__iw
            -> honest_key (findUserKeys usrs') k__sign
            -> key_heap data__rw $? k__sign = Some true))
.*)

Lemma silent_step_message_eq : 
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc cmdc' u_id1 usrs'' t (m__rw : crypto t) m__iw iu ch_id,
          suid = Some u_id1
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> MessageEq.message_eq
              m__rw
              {| users := usrs $+ (u_id1,
                                   {| key_heap := ks;
                                      protocol := cmdc;
                                      msg_heap := qmsgs;
                                      c_heap := mycs;
                                      from_nons := froms;
                                      sent_nons := sents;
                                      cur_nonce := cur_n |});
                 adversary := adv;
                 all_ciphers := cs;
                 all_keys := gks |} m__iw iu ch_id
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> MessageEq.message_eq
              m__rw
              {| users := usrs'' ;
                 adversary := adv';
                 all_ciphers := cs';
                 all_keys := gks' |} m__iw iu ch_id.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst;
    try discriminate;
    try solve [ clean_map_lookups; trivial ]; eauto;
  repeat (match goal with
  | [ H : MessageEq.message_eq _ _ _ _ _ |- _ ] => invert H; [ econstructor 1 | econstructor 2 | econstructor 3]; simpl in *; intros;
                                                   clean_map_lookups; autorewrite with find_user_keys in *
  | [ H : _ $+ (?u_id, _) $? ?u = Some _ |- _ ] => destruct (u_id ==n u); subst; clean_map_lookups; simpl in *
  | [ H : forall _ _ _, _ $+ (?u_id, _) $? _ = _ -> _ -> _ -> _ <-> _ , H2 : ?u_id <> ?u |- _ ] =>
    specialize (H u); eapply H; clean_map_lookups
  | [ H : forall _ _ _ _, _ $+ (_, ?ud) $? _ = _ -> _ -> _ -> _ -> _ <-> _ , H2 : IdealWorld.users _ $? ?u = Some _  |- _ ] =>
    specialize (H u)
  | [ H : forall _ _ _ _, _ $+ (_, ?ud) $? _ = _ -> _ -> _ -> _ -> _ <-> _ , H2 : _ $? ?u = Some {| key_heap := _ |} |- _ ] =>
    specialize (H u); eapply H with (data__rw := ud); clean_map_lookups
  | [ H : forall _ _ _, _ $+ (_, ?ud) $? _ = _ -> _ -> _ -> _ <-> _ , H2 : _ $? ?u = Some {| key_heap := _ |} |- _ ] =>
    specialize (H u); eapply H with (data__rw := ud); clean_map_lookups
  | [ H : forall _ _ _, _ $+ (_, ?ud) $? _ = _ -> _ -> _ -> _ -> _ <-> _ , H2 : _ $? ?u = Some {| key_heap := _ |} |- _ ] =>
    eapply H with (data__rw := ud); clean_map_lookups
  (* | [ H : forall _ _ _, _ $+ (_, _) $? _ = _ -> _ -> _ -> _ <-> _, u : Map.key |- _ ] => specialize (H u) *)
          end); eauto.

  
(* getting new keys out of message *)
  (* *  split; intros. apply merge_perms_split in H4. split_ors. *)
  (* - specialize (H17 u). rewrite add_eq_o in H17. specialize (H17 _ _ eq_refl H5). simpl in H17. *)
  (*   invert H6. apply merge_perms_split in H10. split_ors. *)

  (*   assert (honest_key (findUserKeys usrs') k__sign); eauto. specialize (H17 H10). destruct H17. eapply H11. eauto.  *)
  (*   assert (findUserKeys usrs' $? k__sign = Some true); eauto. eapply findUserKeys_has_private_key_of_user; eauto. *)
  (*   assert (honest_key (findUserKeys usrs') k__sign); eauto. destruct H17; eauto. eauto. *)

  (* - invert H6. *)
        
(*    - assert (findUserKeys usrs' $? k__sign = Some true); eauto.  eapply findUserKeys_has_private_key_of_user; eauto. *)

(*   - specialize (H17 u). rewrite add_eq_o in H17; eauto. specialize (H17 _ _ eq_refl H5). simpl in H17. *)
(*     invert H6. apply merge_perms_split in H10. eauto; split_ors. eapply HonestKey in H6. *)
    
(*     specialize (H17 H6). destruct H17. eapply H10. admit. *)
(*     assert (findUserKeys usrs' $? k__sign = Some true). invert H6. trivial. *)
(*     assert (honest_key (findUserKeys usrs') k__sign); eauto. *)
    

(*     destruct H17; eauto. eauto. *)



(*     destruct H17. eapply HonestKey. trivial. *)
(*     eapply H10. admit *)

    
    
(*     specialize (H17 H4). *)
    

(*     assert (findUserKeys usrs' $? k__sign = Some true); eauto. eapply findUserKeys_has_private_key_of_user; eauto. *)


(*     unfold honest_key. invert H. *)

(*     specialize (H12 H4). solve_perm_merges. *)

(*     assert (honest_key (findUserKeys usrs') k__sign); eauto. specialize (H17 H10). destruct H17. eapply H11. eauto. *)

(*     assert (findUserKeys usrs' $? k__sign = Some true); eauto. eapply findUserKeys_has_private_key_of_user; eauto. *)
(*     assert (honest_key (findUserKeys usrs') k__sign); eauto. destruct H17; eauto. eauto. *)

(*     assert (honest_key (findUserKeys usrs') k__sign); eauto. specialize (H17 H10). destruct H17. admit. *)
(*     destruct H17. invert H4. specialize (H12 H4). solve_perm_merges. *)

(*     solve_perm_merges. eauto. *)



(*     assert (user_cipher_queue_ok cs' (findUserKeys usrs') mycs'0) by admit. unfold user_cipher_queue_ok in H10. rewrite Forall_forall in H10. specialize (H10 _ H7). split_ex; eauto. *)
(*     - admit.  *)
(*     - admit. *)
(*   * admit. (* same as above but u_id1 <> u *) *)
(*   * erewrite cipher_message_keys_already_in_honest; eauto. eapply H17 with (data__rw := {| *)
(*         key_heap := ks0; *)
(*         protocol := cmdc; *)
(*         msg_heap := qmsgs'; *)
(*         c_heap := mycs'0; *)
(*         from_nons := froms'; *)
(*         sent_nons := sents'; *)
(*         cur_nonce := cur_n' |}); clean_map_lookups; eauto. *)
(*     admit. admit. (* also honest key is in heap not message goals *) *)
(*     admit. (* talking about global user heap, is that in scope *) *)
(*     admit. admit. *)
(*   * admit. (* same as above but u_id1 <> u *) *)

(* (* key generation *) *)
(*   * specialize (H12 u). admit. (* adding permission does not violate ksign originally in key_heap *) *)
(*   * admit. (* generate symetric key; ksign is still honest despite new honest key *) *)
(*   * admit. (* same as above but ra is encrypted, different goal *) *)
(*   * admit. (* same as above but u <> u_id *) *)
(*   * admit. (* more add key perm *) *)
(*   * admit. (* another honest key  *) *)
(*   * admit. (* local heap extended with generated key *) *)
(*   * admit. *)
  
(*   Search user_cipher_queues_ok. *)
(*   Search user_cipher_queue_ok. *)
(*   Search encrypted_ciphers_ok. *)
(*   Import SyntacticallySafe. *)
(*   Search encrypted_ciphers_ok. *)
(*   Print syntactically_safe_honest_keys_preservation'. *)
Admitted.

Lemma step_reorder_no_recur :
  forall A B C lbl1 suid1 uid1 (bd1 bd1' : data_step0 A B C),
    step_user lbl1 suid1 bd1 bd1'
    -> suid1 = Some uid1
    -> forall D (bd2 bd2' : data_step0 A B D) lbl2 suid2 uid2,
        step_user lbl2 suid2 bd2 bd2'
        -> suid2 = Some uid2
        -> uid1 <> uid2
        -> forall cs cs1' cs2' (usrs usrs1' usrs2' : honest_users A) (adv adv1' adv2' : user_data B) gks gks1' gks2'
            ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1'
            ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2'
            cmdc1 cmdc2,

              bd1  = (usrs,   adv,   cs,   gks,   ks1,  qmsgs1,  mycs1,  froms1,  sents1,  cur_n1,  cmd1)
            -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
            -> bd2  = (usrs,   adv,   cs,   gks,   ks2,  qmsgs2,  mycs2,  froms2,  sents2,  cur_n2,  cmd2)
            -> bd2' = (usrs2', adv2', cs2', gks2', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

            -> nextAction cmd1 cmd1
            -> nextAction cmd2 cmd2
            -> nextAction cmdc2 cmd2
            (* goodness *)
            -> goodness_predicates (mkUniverse usrs adv cs gks)
            -> syntactically_safe_U (mkUniverse usrs adv cs gks)
            (* allow protocol to freely vary, since we won't be looking at it *)
            -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
            -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> forall cmdc1' usrs1'', 
                usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1')
                -> usrs1'' $? uid2 = Some {| key_heap := ks2;
                                            protocol := cmdc2;
                                            msg_heap := qmsgs2;
                                            c_heap := mycs2;
                                            from_nons := froms2;
                                            sent_nons := sents2;
                                            cur_nonce := cur_n2 |}
                -> exists bd2'',
                  step_user lbl2 suid2
                            (usrs1'', adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2''.
Proof.
  (* destruct 1; destruct 2; inversion 3; inversion 1. why not this? too slow? *)
  intros; cases cmd1; subst.
  - cases cmd2; invert H1; invert H; clean_map_lookups; simpl.
  - eapply nextAction_couldBe in H8. contradiction.
  - cases cmd2; intros; invert H1; invert H; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence.
      econstructor; eauto. econstructor; eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; intros; invert H1; invert H; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst; destruct (uid0 ==n uid1); subst.
      * econstructor; eauto. econstructor; eauto.
      * econstructor; eauto. econstructor; eauto.
      * econstructor; eauto. econstructor; eauto. congruence.
      * destruct (uid ==n uid0); subst. econstructor; eauto. econstructor; eauto. congruence.  
        do 2 (econstructor; eauto). congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl. (*; try (econstructor; eauto; econstructor; eauto).S*)
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst; econstructor; eauto; econstructor; eauto; congruence.
    + destruct (uid ==n uid1); subst; econstructor; eauto; econstructor; eauto; congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor.
    + destruct (uid1 ==n uid). econstructor; eauto. econstructor; eauto.
      intros. unfold syntactically_safe_U in H11. split_ex.
      specialize (H12 uid2). simpl in *. generalize H14. intro H__new.
      eapply H12 in H14. destruct H14. destruct H0 as [ H__syn H__typ ]. 
      split_ex. (* is it possible to send to yourself? *)
      simpl in *. unfold typingcontext_sound in *.
      split_ex. specialize (H2 _ msg0 uid).
      eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H15.
      split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto.
      unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H19 in H4.
      eauto. eauto. congruence.

      econstructor; eauto. econstructor; eauto.
      intros. unfold syntactically_safe_U in H12. split_ex.
      specialize (H12 uid2). simpl in *. generalize H14. intro H__newer.
      eapply H12 in H__newer. destruct H__newer. destruct H0 as [ H__syn H__typ ]. 
      split_ex. (* is it possible to send to yourself? *)
      simpl in *. unfold typingcontext_sound in *.
      split_ex. specialize (H2 _ msg0 uid).
      eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H16.
      split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto.
      unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H20 in H4.
      eauto. eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
      unfold not in *. intros.  invert H.
      * eapply H40. econstructor.
      * eapply H40. econstructor; try eassumption. destruct (c_id0 ==n c_id); eauto.
      * eapply H40. invert H6. econstructor; try eassumption.
        destruct (c_id0 ==n c_id); subst; eauto.
           unfold goodness_predicates in H11; split_ands. 
           unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5. simpl in H5.
           specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5.
           invert H5. split_ex. specialize (H15 _ eq_refl). tauto. eauto.
    + econstructor; eauto.
      eapply StepEncrypt with (c_id1 := next_key (cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (Some uid1, cur_n1) msg))); eauto.
      clean_map_lookups. eapply next_key_not_in. trivial.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto.
      eapply StepSign with (c_id1 := next_key (cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (Some uid1, cur_n1) msg))); eauto.
      clean_map_lookups. eapply next_key_not_in. trivial.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence.
      econstructor; eauto. econstructor; eauto. congruence. + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid1 ==n uid). econstructor; eauto. econstructor; eauto.
      intros. unfold syntactically_safe_U in H11. split_ex.
      specialize (H12 uid2). simpl in *. generalize H14. intro H__new.
      eapply H12 in H14. destruct H14. destruct H0 as [ H__syn H__typ ]. 
      split_ex. (* is it possible to send to yourself? *)
      simpl in *. unfold typingcontext_sound in *.
      split_ex. specialize (H2 _ msg0 uid).
      eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H15.
      split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto.
      unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H19 in H4.
      eauto. eauto. congruence.

      econstructor; eauto. econstructor; eauto.
      intros. unfold syntactically_safe_U in H12. split_ex.
      specialize (H12 uid2). simpl in *. generalize H14. intro H__newer.
      eapply H12 in H__newer. destruct H__newer. destruct H0 as [ H__syn H__typ ]. 
      split_ex. (* is it possible to send to yourself? *)
      simpl in *. unfold typingcontext_sound in *.
      split_ex. specialize (H2 _ msg0 uid).
      eapply syntactically_safe_na in H10; eauto. split_ex. invert H4. eapply H2 in H16.
      split_ex. subst. destruct (c_id ==n x0); clean_map_lookups; eauto.
      unfold keys_mine, findKeysCrypto in *. intros. clean_map_lookups. eapply H20 in H4.
      eauto. eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
      unfold not in *. intros.  invert H.
      * eapply H43. econstructor.
      * eapply H43. invert H6. econstructor; try eassumption.
        destruct (c_id0 ==n c_id); subst; eauto.
           unfold goodness_predicates in H11; split_ands. 
           unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5. simpl in H5.
           specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5.
           invert H5. split_ex. specialize (H15 _ eq_refl). tauto. eauto.
      * eapply H43. invert H6. econstructor; try eassumption.
        destruct (c_id0 ==n c_id); subst; eauto.
           unfold goodness_predicates in H11; split_ands. 
           unfold message_queues_ok in H5. rewrite Forall_natmap_forall in H5.
           specialize (H5 _ _ H14). unfold message_queue_ok in H5; simpl in H5.
           invert H5. split_ex. specialize (H15 _ eq_refl). tauto.
    + econstructor; eauto.  eapply StepEncrypt with (c_id1 := next_key (cs $+ (c_id, SigCipher k msg_to (Some uid1, cur_n1) msg))); eauto. clean_map_lookups. eapply next_key_not_in. trivial.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto.  eapply StepSign with (c_id1 := next_key (cs $+ (c_id, SigCipher k msg_to (Some uid1, cur_n1) msg))); eauto. clean_map_lookups. eapply next_key_not_in. trivial.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence.
      econstructor; eauto. econstructor; eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence.
      econstructor; eauto. econstructor; eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. eapply StepGenerateSymKey with
                               (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := SymKey |}))); eauto.
      eapply next_key_not_in. trivial.
    + econstructor; eauto. eapply StepGenerateAsymKey with
                               (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := SymKey |}))); eauto.
      eapply next_key_not_in. trivial.
  - cases cmd2; invert H; invert H1; clean_map_lookups; simpl.
    + eapply nextAction_couldBe in H9. contradiction.
    + eapply nextAction_couldBe in H9. contradiction.
    + econstructor; eauto. econstructor; eauto.
    + destruct (uid ==n uid1); subst. econstructor; eauto. econstructor; eauto. congruence.
      econstructor; eauto. econstructor; eauto. congruence.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. econstructor; eauto.
    + econstructor; eauto. eapply StepGenerateSymKey with (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := AsymKey |}))); eauto.
      eapply next_key_not_in. trivial.
    + econstructor; eauto. eapply StepGenerateAsymKey with
                              (k_id1 := next_key (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := AsymKey |}))) ; eauto.
      eapply next_key_not_in. trivial. Unshelve. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto.
Qed.

(* Lemma step_reorder : *)
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

(*             (* -> nextAction cmd1 cmdc1 *)            -> nextAction cmd2 cmdc2 *)
(*             (* goodness *) *)
(*             (* allow protocol to freely vary, since we won't be looking at it *) *)
(*             -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1) *)
(*             -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*             -> forall cmdc1' usrs1'' usr2', *)
(*                 usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') *)
(*                 -> usrs1'' $? uid2 = Some usr2' *)
(*                 -> exists bd2'', *)
(*                   step_user lbl2 suid2 *)
(*                             (build_data_step (mkUniverse usrs1'' adv1' cs1' gks1') usr2') bd2''. *)
(* Proof. *)
(*   induction 1; inversion 5; inversion 1; intros. *)
(*   - admit. (* cmd1 = Bind cmd cmd *) *)
(*   - admit. (* cmd1 = Bind (Return v) cmd *) *)
(*   - invert H0. (* cmd1 = Gen *) *)
(*     + unfold build_data_step. simpl. clean_context. (* cmd2 = Gen *) clean_map_lookups. simpl in *. *)
(*       assert (cmd2 = Bind cmd0 cmd3). invert H41; eauto. rewrite H in H29. invert H29. eexists. admit. *)
(*     (* + assert (cmd2 = Bind cmd0 cmd3). invert H41; eauto. rewrite H in H29. *) *)
(*     (*     clean_map_lookups. admit. (* cmd2 = Bind cmd cmd *) *) *)
(*     + admit. (* cmd2 = Bind (Return v) cmd *) *)
(*     + unfold build_data_step. simpl. clean_context. (* cmd2 = Gen *) clean_map_lookups. simpl in *. *)
(*       assert (cmd2 = Gen). invert H41; eauto. rewrite H in H29. invert H29. eexists. econstructor. eexists. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Recv pat). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Recv pat). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Send rec_u_id msg). invert H35; eauto. rewrite H0 in H29. invert H29. eexists. unfold updateSentNonce in H37. simpl in H37. *)
(*       (* eapply StepSend. *) admit. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = SignEncrypt k__signid k__encid msg_to msg). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Decrypt (SignedCiphertext c_id)). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Sign k_id msg_to msg). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = Verify k_id (SignedCiphertext c_id)). invert H35; eauto. rewrite H in H29. invert H29. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = GenerateSymKey usage). invert H35; eauto. rewrite H in H29. invert H29. *)
(*       eexists. econstructor; eauto. invert H35. clean_context. clean_map_lookups. admit. *)
(*     + unfold build_data_step. simpl. clean_context. clean_map_lookups. simpl. *)
(*       assert (cmd2 = GenerateAsymKey usage). invert H35; eauto. rewrite H in H29. invert H29. *)
(*       eexists. econstructor; eauto. invert H35. clean_context. clean_map_lookups. admit. *)
(*   -  *)
(* Admitted. *)

(*   Lemma commutes_sound_recur_cmd1' : *)
(*     forall {A B C D} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B C), *)

(*       step_user lbl1 suid1 bd1 bd1' *)
(*       -> suid1 = Some u_id1 *)
(*       -> forall (bd2 bd2' : data_step0 A B D) lbl2 suid2 u_id2, *)

(*           step_user lbl2 suid2 bd2 bd2' *)
(*           -> suid2 = Some u_id2 *)
(*           -> u_id1 <> u_id2 *)

(*           -> forall cs cs1 cs' (usrs1 usrs1' usrs2 usrs2' : honest_users A) (adv adv1 adv' : user_data B) gks gks1 gks' *)
(*               ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' *)
(*               ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' *)
(*               cmdc1 cmdc1' cmdc2 qmsgs2'', *)

(*               bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1) *)
(*               -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1') *)
(*               -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2'', mycs2, froms2, sents2, cur_n2, cmd2) *)
(*               -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2') *)
(*               (* allow protocol to freely vary, since we won't be looking at it *) *)
(*               -> usrs1 $? u_id1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1) *)
(*               -> usrs1 $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*               -> usrs1' $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2'' mycs2 froms2 sents2 cur_n2) *)
(*               -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') *)
(*               -> encrypted_ciphers_ok (findUserKeys usrs1) cs gks *)
(*               -> message_queues_ok cs usrs1 gks *)
(*               -> keys_and_permissions_good gks usrs1 adv.(key_heap) *)
(*               -> user_cipher_queues_ok cs (findUserKeys usrs1) usrs1 *)
(*               (* -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1 *) *)
(*               (* -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2 *) *)
                                  
(*               (* no recursion *) *)
(*               (* -> nextAction cmd1 cmd1 *) *)
(*               -> not (nextAction cmd2 cmd2) *)
(*               (* -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n <> Send x m) *) *)


(*               -> forall bd3 cmdc2', *)
(*                   bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) *)
(*                   -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3, *)
(*                       step_user lbl3 suid2 bd3 bd3' *)
(*                       /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2') *)
(*                       /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2') *)
(*                       /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1) *)
(*                       /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1') *)
(*                       /\ step_user lbl4 suid1 bd4 bd4' *)
(*                       /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') =  *)
(*                           usrs2' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs2' mycs2' froms2' sents2' cur_n2') ) *)
(*   . *)
(*   Proof. *)
(*     induction 1; inversion 5; inversion 1 *)
(*     ; intros. *)
(*     - invert H1. *)
(*     Admitted. *)

(* Lemma step_step_recurse_ok : *)
(*   forall A B C lbl1 suid1 bd1 bd1', *)
(*     step_user lbl1 suid1 bd1 bd1' *)
(*     -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
(*         (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs' *)
(*         froms froms' sents sents' cur_n cur_n' uid1, *)
(*       bd1 = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*       -> bd1' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*       -> suid1 = Some uid1 *)
(*       -> forall cmdc cmdc', *)
(*           usrs $? uid1 = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n) *)
(*       -> forall D ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd1 (cmd2 : << D >> -> user_cmd (Base A)) uid2, *)
(*           usrs $? uid2 = Some (mkUserData ks2 (Bind cmd1 cmd2) qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*       -> uid1 <> uid2 *)
(*       -> forall bd2' lbl2 , *)
(*           step_user lbl2 (Some uid2) (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, Bind cmd1 cmd2) bd2' *)
(*           -> exists lbl3 bd3 qmsgs3, *)
(*             usrs' $? uid2 = *)
(*             Some *)
(*               {| key_heap := ks2; *)
(*                  protocol := Bind cmd1 cmd2; *)
(*                  msg_heap := qmsgs3; *)
(*                  c_heap := mycs2; *)
(*                  from_nons := froms2; *)
(*                  sent_nons := sents2; *)
(*                  cur_nonce := cur_n2 |} *)
(*             -> step_user lbl3 (Some uid2) *)
(*                         (usrs' $+ (uid1, *)
(*                                    {| *)
(*                                      key_heap := ks'; *)
(*                                      protocol := cmdc'; *)
(*                                      msg_heap := qmsgs'; *)
(*                                      c_heap := mycs'; *)
(*                                      from_nons := froms'; *)
(*                                      sent_nons := sents'; *)
(*                                      cur_nonce := cur_n' |}), adv', cs', gks', ks2, qmsgs3, mycs2, froms2, sents2, cur_n2, Bind cmd1 cmd2) bd3. *)
(* Proof. *)
(*   induction 1; inversion 1; inversion 1; intros; subst; eauto. *)
(*   - induction H27. *)
(*     + admit. *)
(*     + admit. *)
(*     + do 3 eexists. intros.  *)
(* Admitted. *)


(* Lemma step_then_step : *)
(*   forall A B C lbl1 suid1 bd1 bd1', *)
(*     step_user lbl1 suid1 bd1 bd1' *)
(*     -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
(*         (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs' *)
(*         froms froms' sents sents' cur_n cur_n' uid1, *)
(*       bd1 = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*       -> bd1' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*       -> suid1 = Some uid1 *)
(*       -> forall cmdc cmdc', *)
(*           usrs $? uid1 = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n) *)
(*       -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2 uid2, *)
(*           usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2) *)
(*       -> uid1 <> uid2 *)
(*       -> forall bd2' lbl2 , *)
(*           step_user lbl2 (Some uid2) (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2' *)
(*       -> exists lbl3 bd3 qmsgs3, *)
(*             usrs' $? uid2 = Some (mkUserData ks2 cmd2 qmsgs3 mycs2 froms2 sents2 cur_n2) *)
(*           -> step_user lbl3 (Some uid2) (usrs' $+ (uid1, (mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n')), *)
(*                                         adv', cs', gks', ks2, qmsgs3, mycs2, froms2, sents2, cur_n2, cmd2) bd3. *)
(* Proof. *)
(*   induction 1; inversion 1; inversion 1; intros; subst; eauto. *)
(*   - invert H27.  *)
(*     (* + destruct cmd1. *) *)
(*     (*   *do 3 eexists; intros; econstructor 2; eauto. *) *)
(*     (*   * admit. *) *)
(*     (*   * exists lbl2. do 2 eexists. intros. econstructor. admit. *) *)
(*     (*   * admit. *) *)
(*     (*   * admit *) *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   - invert H27. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   - invert H35. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*       (* Verify? *)  *)
(*   - invert H31. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   (* send *) *)
(*   - invert H35.  *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. admit. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*       (* sign enc*) *)
(*   - invert H37. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. admit. admit. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   - invert H36. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   (* sign *) *)
(*   - invert H35. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. admit. admit. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   - invert H31. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*   (* gen keys *) *)
(*   - invert H31. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. admit. (* gks *) *)
(*     + do 3 eexists; intros; econstructor; eauto. admit. *)
(*   - invert H31. *)
(*     + admit. *)
(*     + do 3 eexists; intros; econstructor 2; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. *)
(*     + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. *)
(*      do 3 eexists; intros; econstructor; eauto. *)
(*     + do 3 eexists; intros; econstructor; eauto. admit. (* gks *) *)
(*     + do 3 eexists; intros; econstructor; eauto. admit.  *)
(* Admitted. *)



(* Lemma labels_align_silent_step' : *)
(*   forall A B C suid lbl bd bd', *)

(*     step_user lbl suid bd bd' *)

(*     -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
(*         (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs' *)
(*         froms froms' sents sents' cur_n cur_n' uid, *)

(*       bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*       -> suid = Some uid *)
(*       -> forall cmdc, *)
(*           usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n) *)

(*       -> forall cmdc' iu, *)
(*           labels_align ({| *)
(*                          users := usrs $+ (uid, *)
(*                                            {| *)
(*                                              key_heap := ks'; *)
(*                                              protocol := cmdc'; *)
(*                                              msg_heap := qmsgs'; *)
(*                                              c_heap := mycs'; *)
(*                                              from_nons := froms'; *)
(*                                              sent_nons := sents'; *)
(*                                              cur_nonce := cur_n' |}); *)
(*                          adversary := adv'; *)
(*                          all_ciphers := cs'; *)
(*                          all_keys := gks' |}, iu) *)
(*        -> labels_align ({| *)
(*                          users := usrs; *)
(*                          adversary := adv; *)
(*                          all_ciphers := cs; *)
(*                          all_keys := gks |}, iu). *)
(* Proof. *)
(*   induction 1; inversion 1; inversion 1; intros; subst; eauto. *)
(*   - admit. *)
(*   - unfold labels_align in *; intros. *)
(*     invert H1; simpl in *. *)
(*     destruct userData; unfold build_data_step in *; simpl in *. *)

(* Admitted. *)


(* Lemma alignment_violation_step' : *)
(*   forall t__hon t__adv st st', *)
(*     @step t__hon t__adv st st' *)
(*     (* -> lameAdv b (fst st).(adversary) *) *)
(*     -> labels_always_align st' *)
(*     -> labels_always_align st. *)
(* Proof. *)

(*   induct 1; intros; *)
(*     match goal with *)
(*     | [ H : labels_always_align _ |- _ ] => invert H *)
(*     end. *)
(*   - econstructor; intros. *)
(*     * econstructor; intros. *)
(*       ** admit. *)
(*       ** admit. *)
(*     * invert H. *)
(*       2:admit. (* adversary step, so ignore *) *)
(*       unfold buildUniverse in *. *)
(*       admit. *)

(*   -  *)
(*   (* we know that we have stepped from (ru,iu) to (ru',iu).  we know that if the user *)
(*    * that stepped was the one from H, then we can use H1 to discharge. *)
(*    * However, if it was another user, stepping from (ru,iu) to st', then *)
(*    * we need to know that the other user wouldn't have messed us up if it went first, but we *)
(*    * know that to be true because of H2 (labels_align (ru',iu)), but we will need to prove that *)
(*    * as a lemma  *) *)


(* Admitted. *)

(* Lemma alignment_violation_step : *)
(*   forall t__hon t__adv st st' b, *)
(*     @step t__hon t__adv st st' *)
(*     -> lameAdv b (fst st).(adversary) *)
(*     -> ~ labels_always_align st *)
(*     -> ~ labels_always_align st'. *)
(* Proof. *)
(*   unfold not; intros. *)
(*   eauto using alignment_violation_step'. *)
(* Qed. *)

(* Lemma alignment_violation_steps : *)
(*   forall t__hon t__adv st st' b, *)
(*     (@step t__hon t__adv)^* st st' *)
(*     -> lameAdv b (fst st).(adversary) *)
(*     -> ~ labels_always_align st *)
(*     -> ~ labels_always_align st'. *)
(* Proof. *)
(*   induction 1; intros; eauto. *)

(*   assert (LAME : lameAdv b (fst y).(adversary)) by eauto using adversary_remains_lame_step. *)
(*   destruct x, y, z; simpl in *. *)

(*   generalize H; intros VIOL; eapply alignment_violation_step in VIOL; eauto. *)
(* Qed. *)
