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
     AdversarySafety.

From protocols Require Import
     ExampleProtocols
     ModelCheck
     ProtocolAutomation
     PartialOrderReduction
     SafeProtocol.

From protocols Require Sets.

Require IdealWorld.

Set Implicit Arguments.

Definition almostEqual {A}  (ud ud' : user_data A) :=
  ud = ud' \/
  (exists msg, ud = 
  {|
  key_heap := key_heap ud';
  protocol := protocol ud';
  msg_heap := msg_heap ud' ++ [msg];
  c_heap := c_heap ud';
  from_nons := from_nons ud';
  sent_nons := sent_nons ud';
  cur_nonce := cur_nonce ud' |}).

Lemma non_stepped_ud_almost_equal :
  forall { A B C } suid lbl bd1 bd2,
    step_user lbl suid bd1 bd2
    -> forall (users1 users2 : honest_users A) (adv1 adv2 : user_data B) cs1 cs2 gks1 gks2
        stepper ks1 ks2 qmsgs1 qmsgs2 mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2
        (cmdc1 cmdc2 : user_cmd C) cmd1,
      bd1 = (users1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1)
      -> bd2 = (users2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2)
      -> suid = Some stepper
    -> users1 $? stepper = Some {| key_heap := ks1
                               ; protocol := cmd1
                               ; msg_heap := qmsgs1
                               ; c_heap := mycs1
                               ; from_nons := froms1
                               ; sent_nons := sents1
                               ; cur_nonce := cur_n1 |}
    -> (forall uid ud1 ud2,
          uid <> stepper
          -> users1 $? uid = Some ud1
          -> users2 $? uid = Some ud2
          -> almostEqual ud2 ud1).
Proof.
  induct 1; inversion 1; inversion 1; intros; subst; clean_context; clean_map_lookups; eauto;
    unfold almostEqual; eauto.
  
  destruct (rec_u_id ==n uid); subst; clean_map_lookups; eauto.
Qed.

Lemma different_steps_must_be_by_different_users :
  forall { A B C } (bd1 bd2 bd__other : data_step0 A B C ) lbl1 lbl2 u_id1 u_id2,
    (* lameAdv b bd1.(adversary) *)
    step_user lbl1 (Some u_id1) bd1 bd2
    -> step_user lbl2 (Some u_id2) bd1 bd__other
    -> lbl1 <> lbl2
    -> u_id1 <> u_id2.
Proof.
  (* inversion 2; inversion 1; intros; subst; eauto. *)

  (* destruct ru1.  unfold build_data_step in *. destruct userData. destruct userData0. simpl in *. *)
  (* clean_map_lookups. *)
  (* destruct ru1. destruct adversary. simpl in *. unfold build_data_step in *. simpl in *. *)
  (* rewrite H in H8. invert H8. admit. admit. *)
Admitted.



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
  
  
Lemma silent_step_blah :     
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc cmdc' u_id1 u_id2 ud2 usrs'',
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some ud2
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> usrs'' $? u_id2 = Some ud2.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst;
      try discriminate;
      try solve [ clean_map_lookups; trivial ].
  specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _
                          _ _ _ _ _ _ _ _ _ _ _
                          eq_refl eq_refl eq_refl).
  specialize (IHstep_user cmdc cmdc').
  specialize (IHstep_user _ _ _ _ eq_refl H26 H27 H28 eq_refl).
  clean_map_lookups; eauto.
Qed.

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
    try solve [ clean_map_lookups; trivial ]; eauto.
  - invert H26; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; intros; clean_map_lookups;
      autorewrite with find_user_keys in *; simpl in *; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * autorewrite with find_user_keys in *.  simpl.
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto.
      destruct data__rw.
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := key_heap;
                            protocol := cmdc;
                            msg_heap := msg_heap;
                            c_heap := c_heap;
                            from_nons := from_nons;
                            sent_nons := sent_nons;
                            cur_nonce := cur_nonce |}) .
      clean_map_lookups; eauto. assumption. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto.
      eapply H11 with (data__rw :=
                         {| key_heap := key_heap;
                            protocol := protocol;
                            msg_heap := msg_heap;
                            c_heap := c_heap;
                            from_nons := from_nons;
                            sent_nons := sent_nons;
                            cur_nonce := cur_nonce |}); eauto.
     
      eapply H
    autorewrite with find_user_keys in *. destruct data__rw. simpl.
    specialize (H11 u).
    destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto.
    eapply H11 with (data__rw :=
    {| key_heap := key_heap;
    protocol := cmdc;
    msg_heap := msg_heap;
    c_heap := c_heap;
    from_nons := from_nons;
    sent_nons := sent_nons;
    cur_nonce := cur_nonce |}) .
    clean_map_lookups; eauto. assumption. assumption.
Admitted.

Lemma silent_step_then_labeled_step : 
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) u_id1 cmdc cmdc'
        ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' suid2 lbl2,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> usrs $? u_id1 = Some {| key_heap := ks;
                                protocol := cmdc;
                                msg_heap := qmsgs;
                                c_heap   := mycs;
                                from_nons := froms;
                                sent_nons := sents;
                                cur_nonce := cur_n |}
      -> forall D bd2 bd2',
          step_user lbl2 suid2 bd2 bd2'
          -> forall cmdc2 u_id2 ru ia iu ra
              (cmd2 cmd2' : user_cmd D) ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              froms2 froms2' sents2 sents2' cur_n2 cur_n2',
            suid = Some u_id1
            -> suid2 = Some u_id2
            -> lbl2 = Action ra
            -> bd2 = (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
            -> bd2' = (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
            -> u_id1 <> u_id2
            -> ru = buildUniverse usrs adv cs gks u_id1 {| key_heap  := ks
                                                          ; msg_heap  := qmsgs
                                                          ; protocol  := cmdc
                                                          ; c_heap    := mycs
                                                          ; from_nons := froms
                                                          ; sent_nons := sents
                                                          ; cur_nonce := cur_n |}
            -> action_matches ra ru ia iu
            -> usrs $? u_id2 = Some {| key_heap := ks2;
                                      protocol := cmdc2;
                                      msg_heap := qmsgs2;
                                      c_heap   := mycs2;
                                      from_nons := froms2;
                                      sent_nons := sents2;
                                      cur_nonce := cur_n2 |}
            -> forall ru',
                  (* step_user (Action ra) (Some u_id2) *)
                  (*           (usrs'', adv', cs', gks', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) *)
                  (*           bd2'' *)
                  ru' = buildUniverse usrs' adv' cs' gks' u_id1 {| key_heap  := ks'
                                                                     ; msg_heap  := qmsgs'
                                                                     ; protocol  := cmdc'
                                                                     ; c_heap    := mycs'
                                                                     ; from_nons := froms'
                                                                     ; sent_nons := sents'
                                                                     ; cur_nonce := cur_n' |}
                  ->  action_matches ra ru' ia iu.
Proof.
  induction 6; inversion 4; inversion 1; intros; subst; try discriminate; clean_context.
  - specialize (IHstep_user _ _ H).
    specialize (IHstep_user _ _ _ _ _ cmdc' eq_refl eq_refl H3).
    specialize (IHstep_user _ _ _ _ _ _ _ _ _ _
                            _ _ _ _ _ _ _ _ _ _
                            eq_refl eq_refl eq_refl eq_refl eq_refl H21 eq_refl H34 H35).
    eapply IHstep_user; eauto.
  - generalize H; intros STEP1.
    eapply silent_step_blah in H; eauto.
    clean_map_lookups.
    invert H41; eauto.
    econstructor; eauto.
    invert H1.
    unfold buildUniverse in *; simpl in *.
    eapply silent_step_message_eq with (u_id3 := u_id1); eauto.
  - generalize H; intros STEP1.
    eapply silent_step_blah in H; eauto.
    clean_map_lookups.
    invert H41; eauto.
    eapply Out; eauto.
    invert H2.
    unfold buildUniverse in *; simpl in *.
    eapply silent_step_message_eq with (u_id3 := u_id1); eauto.
    Unshelve.
    all: try discriminate; eauto.
Qed.



(*   inversion 1;  intros; subst; eauto; simpl in *. *)
(*   (* inversion 3; inversion 2;  intros; subst; eauto; simpl in *.  *) *)
(*   (* eexists. destruct (nextStep cmd). *) *)
(*   (* invert H13. destruct iu; simpl in *. econstructor. *) *)
(*   (* eauto. eauto. eauto.  *) *)
(* Admitted. *)


Lemma alignment_preservation_step :
  forall t__hon t__adv st st',
    @step t__hon t__adv st st'
    (* -> lameAdv b (fst st).(adversary) *)
    -> labels_align st'
    -> labels_align st.
Proof.

  induct 1; unfold labels_align.
  - intros.  eapply silent_leading_step_preserves_action_matches in H. eexists. eexists. eexists.
    
  (*   eapply silent_leading_step_preserves_action_matches; eauto.  *)
  (*   eapply silent_leading_step_preserves_action_matches in H. *)
  (*   invert H. invert H1. shelve. shelve. *)
  (* - intros. invert H. *)

  (*   invert H. invert H0. *)

 (*   specialize (H0 _ ra). admit. *)
  (* - intros. *)
  (*   eapply H0. invert H1. invert H. eapply H0. specialize (H0 _ _ H1). *)


  (*   intro. intro ru''. intros. specialize (H0 ru'' ra). invert H.    admit. admit. *)
          
  (* - intro. intro ru''. intro ra'. specialize (H3 ru'' ra').  *)
Admitted.


Lemma alignment_perservation_steps :
  forall t__hon t__adv st st' ,
    (@step t__hon t__adv)^* st st'
    (* -> lameAdv b (fst st).(adversary) *)
    -> labels_align st'
    -> labels_align st.
(* a user either has only changed in that it has new messages or a user already had label alignment in st *)
Proof.
  induct 1; eauto using alignment_preservation_step.
Qed.



