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

Require IdealWorld.

Set Implicit Arguments.

(* forall reachable states labels align *)
Inductive labels_always_align {A B} : @ModelState A B -> Prop :=
| StepLabelsAlign : 
    forall st,
      (forall st', step st st' -> labels_always_align st')
      -> labels_align st
      -> labels_always_align st.

Definition stuck_step_implies_stuck_universe_step {t__hon t__adv}
           (st : @ModelState t__hon t__adv) : Prop :=
  (forall st', step st st' -> False)
  -> forall lbl ru',
    step_universe (fst (fst st)) lbl ru' -> False.


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

Lemma step_step_recurse_ok :
  forall A B C lbl1 suid1 bd1 bd1',
    step_user lbl1 suid1 bd1 bd1'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid1,
      bd1 = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd1' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid1 = Some uid1
      -> forall cmdc cmdc',
          usrs $? uid1 = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
      -> forall D ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd1 (cmd2 : << D >> -> user_cmd (Base A)) uid2,
          usrs $? uid2 = Some (mkUserData ks2 (Bind cmd1 cmd2) qmsgs2 mycs2 froms2 sents2 cur_n2)
      -> uid1 <> uid2
      -> forall bd2' lbl2 ,
          step_user lbl2 (Some uid2) (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, Bind cmd1 cmd2) bd2'
          -> exists lbl3 bd3 qmsgs3,
            usrs' $? uid2 =
            Some
              {| key_heap := ks2;
                 protocol := Bind cmd1 cmd2;
                 msg_heap := qmsgs3;
                 c_heap := mycs2;
                 from_nons := froms2;
                 sent_nons := sents2;
                 cur_nonce := cur_n2 |}
            -> step_user lbl3 (Some uid2)
                        (usrs' $+ (uid1,
                                   {|
                                     key_heap := ks';
                                     protocol := cmdc';
                                     msg_heap := qmsgs';
                                     c_heap := mycs';
                                     from_nons := froms';
                                     sent_nons := sents';
                                     cur_nonce := cur_n' |}), adv', cs', gks', ks2, qmsgs3, mycs2, froms2, sents2, cur_n2, Bind cmd1 cmd2) bd3.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto.
  - induction H27.
    + admit.
    + admit.
    + do 3 eexists. intros. 
Admitted.


Lemma step_then_step :
  forall A B C lbl1 suid1 bd1 bd1',
    step_user lbl1 suid1 bd1 bd1'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid1,
      bd1 = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd1' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid1 = Some uid1
      -> forall cmdc cmdc',
          usrs $? uid1 = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
      -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2 uid2,
          usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
      -> uid1 <> uid2
      -> forall bd2' lbl2 ,
          step_user lbl2 (Some uid2) (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) bd2'
      -> exists lbl3 bd3 qmsgs3,
            usrs' $? uid2 = Some (mkUserData ks2 cmd2 qmsgs3 mycs2 froms2 sents2 cur_n2)
          -> step_user lbl3 (Some uid2) (usrs' $+ (uid1, (mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n')),
                                        adv', cs', gks', ks2, qmsgs3, mycs2, froms2, sents2, cur_n2, cmd2) bd3.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto.
  - invert H27. 
    (* + destruct cmd1. *)
    (*   *do 3 eexists; intros; econstructor 2; eauto. *)
    (*   * admit. *)
    (*   * exists lbl2. do 2 eexists. intros. econstructor. admit. *)
    (*   * admit. *)
    (*   * admit *)
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  - invert H27.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  - invert H35.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
      (* Verify? *) 
  - invert H31.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  (* send *)
  - invert H35. 
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto. admit.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
      (* sign enc*)
  - invert H37.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. admit. admit.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  - invert H36.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  (* sign *)
  - invert H35.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto. admit. admit.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  - invert H31.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto.
  (* gen keys *)
  - invert H31.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto. admit. (* gks *)
    + do 3 eexists; intros; econstructor; eauto. admit.
  - invert H31.
    + admit.
    + do 3 eexists; intros; econstructor 2; eauto.
    + do 3 eexists; intros; econstructor; eauto.
    + destruct (rec_u_id ==n uid1); subst. do 3 eexists; intros. econstructor; eauto.
     do 3 eexists; intros; econstructor; eauto.
    + do 3 eexists; intros; econstructor; eauto. admit. (* gks *)
    + do 3 eexists; intros; econstructor; eauto. admit. 
Admitted.



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


Lemma labels_align_user_step :
    forall {A B} suid (bd bd' : data_step0 A B (Base A)),

      step_user Silent suid bd bd'
      -> forall uid, suid = Some uid
      -> forall cs cs' (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks'
          ks ks' qmsgs qmsgs' mycs mycs' cmd cmd' froms froms' sents sents' cur_n cur_n',

          bd  = (usrs,  adv,  cs,  gks,  ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> bd'  = (usrs',  adv',  cs',  gks',  ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> syntactically_safe_U (mkUniverse usrs adv cs gks)
          -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
          -> forall usrs'', usrs'' = usrs' $+ (uid, mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n')
          -> forall iu v, labels_align (mkUniverse usrs'' adv' cs' gks', iu, v)
          -> labels_align (mkUniverse usrs adv cs gks, iu, v).
Proof.
  unfold labels_align; intros; subst.
  invert H7.
  unfold build_data_step in H1; simpl in *.
  destruct userData; simpl in *.

  destruct (uid ==n uid0); subst; clean_map_lookups.
  pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H1 H); discriminate.

  generalize H; intros SILENT; eapply silent_step_nochange_other_user in H; eauto.
  unfold syntactically_safe_U in H3;
    specialize (H3 _ _ _ H0 eq_refl); split_ex; simpl in *.
  eapply silent_step_then_labeled_step with (uid2 := uid) in H1; eauto.
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

  eapply H6 in IRS; split_ex.
  (do 3 eexists); repeat simple apply conj; eauto.

  (* action_matches silent step inv *)
  admit.
Admitted.

Lemma alignment_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> syntactically_safe_U (fst (fst st))
    -> alignment st'
    -> alignment st.
Proof.
  intros.
  unfold alignment in *.
  destruct st as [[ru iu] v].
  destruct st' as [[ru' iu'] v'].
  split_ex; subst.
  invert H; eauto.
  simpl in H0; 
    invert H4; dismiss_adv.
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
