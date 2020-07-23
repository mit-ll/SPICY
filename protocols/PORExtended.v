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
     Morphisms
     JMeq
     Program.Equality
     List.

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     MessageEq
     MessageEqTheory
     Tactics
     Simulation
     RealWorld
     InvariantsTheory
     AdversaryUniverse
     AdversarySafety
     SafetyAutomation
     SyntacticallySafe
     UsersTheory.

From protocols Require Import
     RealWorldStepLemmas
     ExampleProtocols
     ModelCheck
     ProtocolAutomation
     SafeProtocol
     (* LabelsAlign *)
     NoResends
     PartialOrderReduction
.

Import SafetyAutomation.

Definition stuck_model_step_user_stuck_user {t__hon t__adv}
           (st : universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  forall uid u,
    (fst st).(users) $? uid = Some u
    -> (forall st', model_step_user uid st st' -> False)
    -> (forall lbl bd, step_user lbl (Some uid) (build_data_step (fst st) u) bd -> False). 


Definition try_this {t__hon t__adv}
           (st : universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  (forall uid st', model_step_user uid st st' -> False)
  -> (forall uid u lbl bd, (fst st).(users) $? uid = Some u -> step_user lbl (Some uid) (build_data_step (fst st) u) bd -> False). 

Lemma user_step_label_deterministic :
  forall A B C lbl1 lbl2 bd bd1' bd2' suid,
    @step_user A B C lbl1 suid bd bd1'
    -> step_user lbl2 suid bd bd2'
    -> lbl1 = lbl2.
Proof.
  induction 1; invert 1;
    subst;
    eauto;
    repeat
      match goal with
      | [ H : _ = _ |- _ ] => invert H; try contradiction
      end;
    eauto.

  invert H.
  invert H6.
Qed.

Lemma syntactically_safe_U_preservation_step :
  forall t__hon t__adv (st st' : universe t__hon t__adv * IdealWorld.universe t__hon),
    step st st'
    -> goodness_predicates (fst st)
    -> syntactically_safe_U (fst st)
    -> syntactically_safe_U (fst st').
Proof.
  inversion 1; intros; subst; simpl in *; eapply syntactically_safe_U_preservation_stepU; eauto.
Qed.

Lemma syntactically_safe_U_preservation_steps :
  forall t__hon t__adv st st',
    (@step t__hon t__adv) ^* st st'
    -> goodness_predicates (fst st)
    -> syntactically_safe_U (fst st)
    -> syntactically_safe_U (fst st').
Proof.
  induction 1; intros; eauto.
  eapply IHtrc; eauto using syntactically_safe_U_preservation_step, goodness_preservation_step.
Qed.

(* Lemma try_this_implies_labels_align : *)
(*   forall t__hon t__adv st, *)
(*     @try_this t__hon t__adv st *)
(*     -> labels_align st. *)
(* Proof. *)
(*   unfold try_this, labels_align; *)
(*     destruct st as [ru iu]; intros. *)

(*   invert H0. *)

(*   destruct (classic (exists st, model_step_user u_id (ru,iu) st)). *)
(*   - split_ex. *)
(*     invert H0; *)
(*       destruct ru, userData, userData0; *)
(*       unfold build_data_step in *; *)
(*       simpl in *; *)
(*       clean_map_lookups. *)

(*     + admit. *)
(*     + destruct (x ==n u_id); subst; clean_map_lookups; eauto. *)
(*       admit. (* easy *) *)
      

(*     + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6); discriminate. *)
(*     + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6). *)
(*       invert H0. *)
(*       (do 3 eexists); repeat simple apply conj; eauto. *)

(*   - assert (forall st', ~ model_step_user u_id (ru,iu) st') by eauto using all_not_not_ex. *)
(*     eapply H in H3; eauto. *)
(*     contradiction. *)
(* Qed. *)


Lemma stuck_model_step_user_stuck_user_implies_labels_align :
  forall t__hon t__adv st,
    @stuck_model_step_user_stuck_user t__hon t__adv st
    -> labels_align st.
Proof.
  unfold stuck_model_step_user_stuck_user, labels_align;
    destruct st as [ru iu]; intros.

  invert H0.
  specialize (H _ _ H1).

  destruct (classic (exists st, model_step_user u_id (ru,iu) st)).
  - split_ex.
    invert H0;
      destruct ru, userData, userData0;
      unfold build_data_step in *;
      simpl in *;
      clean_map_lookups.

    + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6); discriminate.
    + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6).
      invert H0.
      (do 3 eexists); repeat simple apply conj; eauto.

  - assert (forall st', ~ model_step_user u_id (ru,iu) st') by eauto using all_not_not_ex.
    eapply H in H3; eauto.
    contradiction.
Qed.

Lemma step_reorder :
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

            (* allow protocol to freely vary, since we won't be looking at it *)
            -> usrs $? uid1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
            -> usrs $? uid2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> forall cmdc1' usrs1'' usr2',
                usrs1'' = usrs1' $+ (uid1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1')
                -> usrs1'' $? uid2 = Some usr2'
                -> exists bd2'',
                  step_user lbl2 suid2
                            (build_data_step (mkUniverse usrs1'' adv1' cs1' gks1') usr2') bd2''.
Proof.
Admitted.

Lemma step_reorder_simple :
  forall t__hon t__adv uid uid' u u' U bd' lbl1 lbl2
    (usrs : honest_users t__hon) (adv : user_data t__adv) cs gks ks qmsgs mycs froms sents cur_n cmd,
    
    step_user lbl1 (Some uid) (build_data_step  U u) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,cur_n,cmd)
    -> U.(users) $? uid = Some u
    -> U.(users) $? uid' = Some u'
    -> step_user lbl2 (Some uid') (build_data_step  U u') bd'
    -> uid <> uid'
    -> forall usrs' u'', usrs' = usrs $+ (uid, mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> usrs' $? uid' = Some u''
    -> exists bd'',
        step_user lbl2 (Some uid')
                  (build_data_step (mkUniverse usrs' adv cs gks) u'') bd''.
Proof.
  intros;
    destruct U, u, u';
    dt bd';
    unfold build_data_step in *;
    simpl in *;
    eapply step_reorder with (suid1 := Some uid) (suid2 := Some uid'); eauto.
Qed.

Lemma input_action_msg_queue :
  forall t__hon t__adv t lbl suid bd bd',
    step_user lbl suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid a,

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> lbl = Action a
      -> forall t__m (msg : crypto t__m) pat froms'', a = Input msg pat froms''
      -> froms'' = froms
        /\ (exists qmsgs'', qmsgs = (existT _ _ msg) :: qmsgs'')
        /\ (exists t__m pat, nextAction cmd (@Recv t__m pat)
                   /\ msg_accepted_by_pattern cs suid froms pat msg)
.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; try discriminate; eauto.

  assert (froms'' = froms0 /\
          (exists qmsgs'' : list {x : type & crypto x}, qmsgs0 = existT crypto t__m msg :: qmsgs'') /\
          (exists (t__m0 : type) (pat0 : msg_pat), nextAction cmd1 (@Recv t__m0 pat0)
            /\ msg_accepted_by_pattern cs0 (Some uid) froms0 pat0 msg)) by eauto.
  split_ex; subst.
  repeat simple apply conj; eauto.
  (do 2 eexists); split; eauto; econstructor; eauto.
  invert H32; eauto.

  repeat simple apply conj; eauto.
  (do 2 eexists); split; eauto; econstructor; eauto.
Qed.

Lemma output_action_msg_queue :
  forall t__hon t__adv t lbl suid bd bd',
    step_user lbl suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid a,

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> lbl = Action a
      -> forall t__m (msg : crypto t__m) sents'' to from, a = Output msg from to sents''
      -> sents'' = sents
      /\ from = Some uid
      /\ exists rec_u_id rec_u,
          nextAction cmd (Send rec_u_id msg)
          /\ to = Some rec_u_id
          /\ usrs $? rec_u_id = Some rec_u
          /\ rec_u_id <> uid.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; try discriminate; eauto.

  assert (sents'' = sents0 /\
          from = Some uid /\
          (exists (rec_u_id : user_id) (rec_u : user_data A),
              nextAction cmd1 (Send rec_u_id msg)
              /\ to = Some rec_u_id /\ usrs0 $? rec_u_id = Some rec_u /\ rec_u_id <> uid)) by eauto.
  split_ex; subst.
  repeat simple apply conj; eauto.
  (do 2 eexists); repeat simple apply conj; eauto.
  econstructor; eauto.

  invert H32.
  repeat simple apply conj; eauto.
  (do 2 eexists); repeat simple apply conj; eauto.
  econstructor; eauto.
  unfold not; intros; subst; contradiction.
Qed.


Lemma unpack_keyperms :
  forall honestk cs uid froms t cid c (msg : crypto t) qmsgs,
    clean_messages honestk cs (Some uid) froms ((existT _ _ msg) :: qmsgs) =
     (existT _ _ msg) :: clean_messages honestk cs (Some uid) (cipher_nonce c :: froms) qmsgs
    -> cs $? cid = Some c
    -> msg = SignedCiphertext cid
    -> key_perms_from_message_queue cs honestk (existT _ _ msg :: qmsgs) uid froms $0 =
      (findKeysCrypto cs msg) $k++ (key_perms_from_message_queue cs honestk qmsgs uid (cipher_nonce c :: froms) $0).
Proof.
  unfold key_perms_from_message_queue; intros; subst.
  rewrite H; simpl.
  rewrite !key_perms_from_message_queue_notation.
  rewrite key_perms_from_message_queue_pull_merge.
  rewrite merge_perms_sym; trivial.
Qed.

Lemma user_step_label_deterministic' :
  forall t t__hon t__adv suid lbl bd bd',

    step_user lbl suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid uid',

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> uid' <> uid
      -> forall cmd1, usrs $? uid = Some (mkUserData ks cmd1 qmsgs mycs froms sents n)
      -> forall ud, usrs $? uid' = Some ud
      -> forall lbl' bd'', step_user lbl' (Some uid') (build_data_step (mkUniverse usrs adv cs gks) ud) bd''
      -> forall usrs'' cmdc, usrs'' = usrs' $+ (uid, mkUserData ks' cmdc qmsgs' mycs' froms' sents' n')
      -> forall ud', usrs' $? uid' = Some ud'
      -> forall lbl'' bd''', step_user lbl'' (Some uid') (build_data_step (mkUniverse usrs'' adv' cs' gks') ud') bd'''
      -> lbl' = lbl''.
Proof.
  intros; subst; clean_map_lookups.
  dt bd''; dt bd'''.
  pose proof (step_reorder _ _ _ _ _ _ _ _ H eq_refl _ _ _ _ _ _ H6 eq_refl).
  destruct ud; simpl in *.
  eapply impact_from_other_user_step with (u_id2 := uid') in H; eauto; split_ex.
  clean_map_lookups; subst.
  
  eapply H0 with (cmdc1' := cmdc) in H4; eauto; clear H0.

  2 : unfold build_data_step; simpl; eauto.

  split_ex; unfold build_data_step in *; simpl in *.

  eapply user_step_label_deterministic in H9; eauto.
Qed.

Lemma action_matches_addnl_cipher_inp :
  forall cs cid c gks ia t c_id c' pat froms,
    ~ In cid cs
    -> cs $? c_id = Some c'
    -> action_matches (cs $+ (cid,c)) gks (Input (@SignedCiphertext t c_id) pat froms) ia
    -> action_matches cs gks (Input (@SignedCiphertext t c_id) pat froms) ia.
Proof.
  intros * NIN CS AM;
    invert AM;
    destruct (cid ==n cid0); subst;
      match goal with
      | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
      end;
      clean_map_lookups;
      [ econstructor 1 | econstructor 2];
      eauto.
Qed.

Lemma action_matches_addnl_cipher_out :
  forall cs cid c gks ia t c_id c' to from sents,
    ~ In cid cs
    -> cs $? c_id = Some c'
    -> action_matches (cs $+ (cid,c)) gks (Output (@SignedCiphertext t c_id) to from sents) ia
    -> action_matches cs gks (Output (@SignedCiphertext t c_id) to from sents) ia.
Proof.
  intros * NIN CS AM;
    invert AM;
    destruct (cid ==n cid0); subst;
      match goal with
      | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
      end;
      clean_map_lookups;
      [ econstructor 3 | econstructor 4];
      eauto.
Qed.

(* Lemma action_matches_addnl_key : *)
(*   forall cs gks kid k ia t (msg : crypto t) pat froms, *)
(*     ~ In kid gks *)
(*     -> match msg with *)
(*       | Content _ => False *)
(*       | SignedCiphertext cid =>  *)
(*     -> (forall kid' kp, findKeysCrypto cs msg $? kid' = Some kp -> gks $? kid' <> None) *)
(*     -> action_matches cs (gks $+ (kid,k)) (Input msg pat froms) ia *)
(*     -> action_matches cs gks (Input msg pat froms) ia. *)
(* Proof. *)
(*   intros * NIN FIND AM; *)
(*     invert AM; *)
(*     unfold findKeysCrypto in FIND; *)
(*     context_map_rewrites. *)

(*   eapply InpSig; eauto using message_content_eq_addnl_key_inv. *)
(*   eapply InpEnc; eauto using message_content_eq_addnl_key_inv. *)


  
(*     destruct (kid ==n kid0); subst; *)
(*       match goal with *)
(*       | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H *)
(*       end; *)
(*       clean_map_lookups; *)
(*       [ econstructor 1 | econstructor 2]; *)
(*       eauto. *)
(* Qed. *)


Lemma no_model_step_other_user_silent_step' :
  forall t t__hon t__adv suid lbl bd bd',

    step_user lbl suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid uid' iu,

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> lbl = Silent
      -> message_queues_ok cs usrs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> keys_and_permissions_good gks usrs adv.(key_heap)
      -> syntactically_safe_U (mkUniverse usrs adv cs gks)
      -> forall ctx styp uids, syntactically_safe uid uids ctx cmd styp
      -> typingcontext_sound ctx usrs cs uid
      -> uids = compute_ids usrs
      -> forall cmdc, usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents n)
      -> forall ud', usrs $? uid' = Some ud'
      -> forall lbl' bd'', step_user lbl' (Some uid') (build_data_step (mkUniverse usrs adv cs gks) ud') bd''
      -> uid <> uid'
      -> forall cmdc ,
        (forall st', model_step_user
                  uid' 
                  (mkUniverse usrs adv cs gks, iu)
                  st' -> False)
      -> (forall st', model_step_user
                  uid'
                  (mkUniverse (usrs' $+ (uid, mkUserData ks' cmdc qmsgs' mycs' froms' sents' n'))
                              adv' cs' gks', iu)
                  st' -> False).
Proof.
  Local Ltac solve_model_step_block stp :=
    repeat
      match goal with
      | [ H : model_step_user _ _ _ |- _ ] => 
        invert H; unfold build_data_step in *; simpl in *; clean_map_lookups
      | [ H1 : step_user ?lbl (Some ?uid) (?usrs,_,_,_,_,_,_,_,_,_,_) ?bd,
          H2 : step_user ?lbl__known (Some ?uid) (?usrs $+ (_,_),_,_,_,_,_,_,_,_,_,_) _ |- _ ] => 
        is_var lbl;
        dt bd;
        assert (lbl = lbl__known) by 
            (clean_map_lookups;
             eapply (user_step_label_deterministic' _ _ _ _ _ _ _ stp);
             eauto; unfold build_data_step; simpl; eauto); subst
        (* assert (lbl = lbl__known) by admit; subst *)
      | [ H : (forall _, model_step_user ?uid ({| users := ?usrs |},_) _ -> False),
          STP : step_user ?lbl (Some ?uid) (?usrs,_,_,_,_,_,_,_,_,_,_) _
          |- False ] =>
        is_not_var lbl;
        eapply H;
        match lbl with
        | Silent => econstructor 1
        | Action _ => econstructor 2
        end; unfold build_data_step, buildUniverse; simpl; eauto
      (* | [ H : action_matches ?a _ _ _ |- action_matches ?a _ _ _ ] => *)
      (*   solve [ invert H; [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4 ]; eauto 3 ] *)
      end.

  intros * STEP;
    generalize STEP;
    induction 1; inversion 1; inversion 1;
      try solve [ invert 8; intros; eauto ];
      intros; subst; eauto; clean_context;
        solve_model_step_block STEP.

  - destruct userData; simpl in *.
    destruct ra.
    
    + eapply input_action_msg_queue in H45; eauto; split_ex; subst.
      msg_queue_prop.
      generalize (H39 _ _ _ H44 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H7; eauto; split_ex.
      assert (msg_pattern_safe (findUserKeys usrs') x0)
        by (unfold typingcontext_sound in *; split_ex; invert H7; process_ctx; eauto).
      assert (msg_honestly_signed (findUserKeys usrs') cs0 msg0 = true) by eauto.
      unfold msg_honestly_signed, msg_signing_key in H18;
        destruct msg0;
        try discriminate;
        cases (cs0 $? c_id0);
        try discriminate;
        destruct c;
        eauto using action_matches_addnl_cipher_inp.
    + eapply output_action_msg_queue in H45; eauto; split_ex; subst.
      generalize (H39 _ _ _ H44 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H7; eauto; split_ex.
      unfold typingcontext_sound in *; split_ex; invert H7; process_ctx.
      eauto using action_matches_addnl_cipher_out.

  - destruct userData; simpl in *.
    destruct ra.
    
    + eapply input_action_msg_queue in H43; eauto; split_ex; subst.
      msg_queue_prop.
      generalize (H37 _ _ _ H42 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H5; eauto; split_ex.
      assert (msg_pattern_safe (findUserKeys usrs') x0)
        by (unfold typingcontext_sound in *; split_ex; invert H5; process_ctx; eauto).
      assert (msg_honestly_signed (findUserKeys usrs') cs0 msg0 = true) by eauto.
      unfold msg_honestly_signed, msg_signing_key in H16;
        destruct msg0;
        try discriminate;
        cases (cs0 $? c_id0);
        try discriminate;
        destruct c;
        eauto using action_matches_addnl_cipher_inp.
    + eapply output_action_msg_queue in H43; eauto; split_ex; subst.
      generalize (H37 _ _ _ H42 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H5; eauto; split_ex.
      unfold typingcontext_sound in *; split_ex; invert H5; process_ctx.
      eauto using action_matches_addnl_cipher_out.

  - destruct userData, ra; simpl in *.

    Import ProtocolAutomation.
    Import SimulationAutomation.

    + eapply input_action_msg_queue in H39; eauto; split_ex; subst.
      msg_queue_prop.
      generalize (H33 _ _ _ H38 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H2; eauto; split_ex.
      assert (msg_pattern_safe (findUserKeys usrs') x0)
        by (unfold typingcontext_sound in *; split_ex; invert H2; process_ctx; eauto).
      assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.

      unfold msg_honestly_signed, msg_signing_key in H13.
      invert H8;
        clean_map_lookups;
        encrypted_ciphers_prop;
        eauto using message_content_eq_addnl_key_inv;
        keys_and_permissions_prop.

      eapply InpEnc; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.

    + eapply output_action_msg_queue in H39; eauto; split_ex; subst.
      generalize (H33 _ _ _ H38 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H2; eauto; split_ex.
      unfold typingcontext_sound in *; split_ex; invert H2; process_ctx.

      invert H8;
        clean_map_lookups;
        encrypted_ciphers_prop;
        eauto using message_content_eq_addnl_key_inv;
        keys_and_permissions_prop;
        invert H14;
        clean_map_lookups.

      eapply OutSig; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.

      eapply OutEnc; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.
    
  - destruct userData, ra; simpl in *.

    Import ProtocolAutomation.
    Import SimulationAutomation.

    + eapply input_action_msg_queue in H39; eauto; split_ex; subst.
      msg_queue_prop.
      generalize (H33 _ _ _ H38 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H2; eauto; split_ex.
      assert (msg_pattern_safe (findUserKeys usrs') x0)
        by (unfold typingcontext_sound in *; split_ex; invert H2; process_ctx; eauto).
      assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.

      unfold msg_honestly_signed, msg_signing_key in H13.
      invert H8;
        clean_map_lookups;
        encrypted_ciphers_prop;
        eauto using message_content_eq_addnl_key_inv;
        keys_and_permissions_prop.

      eapply InpEnc; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.

    + eapply output_action_msg_queue in H39; eauto; split_ex; subst.
      generalize (H33 _ _ _ H38 eq_refl); intro; split_ex; simpl in *.
      eapply syntactically_safe_na in H2; eauto; split_ex.
      unfold typingcontext_sound in *; split_ex; invert H2; process_ctx.

      invert H8;
        clean_map_lookups;
        encrypted_ciphers_prop;
        eauto using message_content_eq_addnl_key_inv;
        keys_and_permissions_prop;
        invert H14;
        clean_map_lookups.

      eapply OutSig; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.

      eapply OutEnc; eauto;
        repeat 
          match goal with
          | [ |- content_eq _ _ _ ] =>
            eapply message_content_eq_addnl_key_inv; eauto; intros
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
            eapply H in ARG; split_ex
          | [ PHG : permission_heap_good ?gks ?honk, LK : ?honk $? ?k = Some _ |- ?gks $? ?k <> None ] =>
            let GKS := fresh "GKS" in
            unfold not; intros GKS; eapply PHG in LK; split_ex; clean_map_lookups
          end.
Qed.

Lemma no_model_step_other_user_silent_step :
  forall t__hon t__adv uid uid' u u' U bd' lbl
    (usrs : honest_users t__hon) (adv : user_data t__adv)  cs gks ks qmsgs mycs froms sents cur_n cmd iu,
    
    step_user Silent (Some uid) (build_data_step  U u) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,cur_n,cmd)
    -> U.(users) $? uid = Some u
    -> U.(users) $? uid' = Some u'
    -> step_user lbl (Some uid') (build_data_step  U u') bd'
    -> uid <> uid'
    -> goodness_predicates U
    -> syntactically_safe_U U
    -> (forall st', model_step_user uid' (U, iu) st' -> False)
    -> (forall st', model_step_user uid'
                  (mkUniverse (usrs $+ (uid, mkUserData ks cmd qmsgs mycs froms sents cur_n))
                              adv cs gks, iu)
                  st' -> False).

Proof.
  unfold goodness_predicates; intros; split_ex.
  generalize (H5 _ _ _ H0 eq_refl); intros; split_ex.
  destruct u , u', U; simpl in *;
    eapply no_model_step_other_user_silent_step' with (uid := uid) (uid' := uid'); try reflexivity; simpl; eauto; simpl.
Qed.

Notation "p1 @@ p2" := (IdealWorld.construct_permission p1 p2) (left associativity, at level 20).

Section IdealWorldLemmas.
  Import IdealWorld.

  Inductive perm_ge : permission -> permission -> Prop :=
  | Owner : forall p,
      perm_ge (true @@ true) p
  | None : forall p,
      perm_ge p (false @@ false)
  | Same : forall b1 b2,
      b1 <> b2
      -> perm_ge (b1 @@ b2) (b1 @@ b2)
  .

End IdealWorldLemmas.

Lemma no_model_step_other_user_labeled_step :
  forall t t__hon t__adv suid lbl bd bd',

    step_user lbl suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid uid'
        ra ia iu iu' iu'',

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> lbl = Action ra
      -> forall cmdc, usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents n)
      -> forall ud', usrs $? uid' = Some ud'
      -> forall lbl' bd'', step_user lbl' (Some uid') (build_data_step (mkUniverse usrs adv cs gks) ud') bd''
      (* arguments to fill out label alignment for uid step above *)                                  
      -> (istepSilent) ^* iu iu'
      -> IdealWorld.lstep_universe iu' (Action ia) iu''
      -> action_matches cs gks ra ia
      -> uid <> uid'
      -> forall cmdc,
        (forall st', model_step_user
                  uid' 
                  (mkUniverse usrs adv cs gks, iu)
                  st' -> False)
      -> (forall st', model_step_user
                  uid'
                  (mkUniverse (usrs' $+ (uid, mkUserData ks' cmdc qmsgs' mycs' froms' sents' n'))
                              adv' cs' gks', iu'')
                  st' -> False).
Proof.

  intros * STEP;
    generalize STEP;
    induction 1; inversion 1; inversion 1;
      intros; subst; eauto; clean_context.

  - solve_model_step_block STEP.

    invert H8.
    + econstructor 1; eauto.
      assert (ia = IdealWorld.Input m__iw ch_id cs1 ps) by admit; eauto.
      admit.

      invert H13; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
        intros;
        autorewrite with find_user_keys in *; eauto;
          specialize (H15 u); destruct (u ==n uid); subst; clean_map_lookups; eauto 8.

      (* including message heap keys helps here 
       * still worried aobut progression of ideal world, though
       *)
      admit.
      admit.
      admit.
      admit.

    + econstructor 2; eauto.
      assert (ia = IdealWorld.Output m__iw ch_id cs1 ps) by admit; eauto.

      invert H12; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
        intros;
        autorewrite with find_user_keys in *; eauto;
          specialize (H14 u); destruct (u ==n uid); subst; clean_map_lookups; eauto 8.

      (* including message heap keys helps here 
       * still worried aobut progression of ideal world, though
       *)
      admit.
      admit.
      admit.
      admit.

  - destruct (rec_u_id ==n uid'); subst; clean_map_lookups;
      solve_model_step_block STEP; simpl in *.

    + dt bd'';
        destruct ud';
        simpl in *.

      assert (lbl' = Silent) by 
          (clean_map_lookups;
           eapply (user_step_label_deterministic' _ _ _ _ _ _ _ STEP);
           eauto; unfold build_data_step; simpl; eauto); subst.
      
      eapply H40; econstructor 1; unfold build_data_step, buildUniverse; simpl; eauto; simpl.

    + dt bd'';
        destruct ud';
        simpl in *.

      assert (lbl' = Action ra) by 
          (clean_map_lookups;
           eapply (user_step_label_deterministic' _ _ _ _ _ _ _ STEP);
           eauto; unfold build_data_step; simpl; eauto); subst.
      
      eapply H40; econstructor 2; unfold build_data_step, buildUniverse; simpl; eauto; simpl.

      invert H11.
      * econstructor 1; eauto.
        assert (ia = IdealWorld.Input m__iw ch_id cs1 ps) by admit; eauto.
        admit.
        
        invert H16; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
          intros;
          autorewrite with find_user_keys in *; eauto;
            specialize (H18 u); destruct (u ==n uid); subst; clean_map_lookups; eauto 8.

        all: admit.

      * admit.

    + dt bd'';
        destruct userData;
        simpl in *.

      assert (lbl' = Silent) by
          ( clean_map_lookups;
            eapply (user_step_label_deterministic' _ _ _ _ _ _ _ STEP) with (uid' := uid');
            eauto; unfold build_data_step; simpl; eauto); subst.
      
      eapply H40; econstructor 1; unfold build_data_step, buildUniverse; simpl; eauto; simpl.

    + dt bd'';
        destruct userData;
        simpl in *.

      assert (lbl' = Action ra) by
          ( clean_map_lookups;
            eapply (user_step_label_deterministic' _ _ _ _ _ _ _ STEP) with (uid' := uid');
            eauto; unfold build_data_step; simpl; eauto); subst.

      eapply H40; econstructor 2; unfold build_data_step, buildUniverse; simpl; eauto; simpl.
      
Admitted.

Lemma stuck_model_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> goodness_predicates (fst st)
    -> syntactically_safe_U (fst st)
    -> stuck_model_step_user_stuck_user st'
    -> stuck_model_step_user_stuck_user st.
Proof.
  unfold stuck_model_step_user_stuck_user; intros.

  invert H; simpl in *.

  - invert H7; dismiss_adv.
    simpl in *.

    destruct (u_id ==n uid); subst; clean_map_lookups.
    + eapply H5.
      econstructor; eauto.

    + generalize H8; intros OUSTEP.
      destruct ru, u, userData; simpl in *.
      unfold build_data_step in OUSTEP; simpl in *.
      eapply impact_from_other_user_step in OUSTEP; eauto; split_ex.

      specialize (H3 uid).
      rewrite add_neq_o in H3 by auto.
      specialize (H3 _ H7); simpl in H3.

      generalize (no_model_step_other_user_silent_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8 H H4 H6 n H1 H2 H5);
        intros NOMODEL.

      assert (OU : usrs $+ (u_id, mkUserData ks cmd qmsgs mycs froms sents cur_n) $? uid =
                   Some (mkUserData key_heap protocol (msg_heap ++ x) c_heap from_nons sent_nons cur_nonce))
        by (clean_map_lookups; trivial).

      generalize (step_reorder_simple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8 H H4 H6 n _ _ eq_refl OU);
        intros;
        split_ex.

      eapply H3 in NOMODEL; try contradiction; eauto.

  (* labeled case -- this will perhaps be a bit more difficult because of the ideal world *)
  - invert H7.
    simpl in *.
    (* unfold buildUniverse, build_data_step in *; simpl in *. *)

    destruct (u_id ==n uid); subst; clean_map_lookups.
    + eapply H5.
      econstructor 2; eauto.
    + generalize H9; intros OUSTEP.

      destruct ru, u; simpl in *.
      eapply impact_from_other_user_step in OUSTEP; eauto; split_ex.

      specialize (H1 uid).
      rewrite add_neq_o in H1 by auto.
      specialize (H1 _ H5); simpl in H1.

      destruct userData; simpl in *.
      pose proof (no_model_step_other_user_labeled_step
                    _ _ _ _ _ _ _ H9
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ra ia iu iu' iu''
                    eq_refl eq_refl eq_refl eq_refl _ H _ H2 _ _ H4 H6 H7 H8 n cmd H3) as NOMODEL.
      specialize (H1 NOMODEL).

      dt bd.
      pose proof (step_reorder _ _ _ _ _ _ _ _ H9 eq_refl _ _ _ _ _ _ H4 eq_refl) as REORDER.
      generalize H; intros USR; eapply REORDER in USR; eauto; clear REORDER.
      split_ex.
      unfold build_data_step in H7; simpl in H7.
      eapply H1; eauto.

Admitted.

Lemma stuck_model_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> ~ stuck_model_step_user_stuck_user st
    -> ~ stuck_model_step_user_stuck_user st'.
Proof.
  unfold not; intros.
  eauto using stuck_model_violation_step'.
Qed.

    




Module Type SyntacticallySafeProtocol.

  Parameter t__hon : type.
  Parameter t__adv : type.
  Parameter b : << Base t__adv >>.
  Parameter iu0 : IdealWorld.universe t__hon.
  Parameter ru0 : RealWorld.universe t__hon t__adv.

  Notation SYS := (S ru0 iu0).

  Axiom U_good : universe_starts_sane b ru0.
  Axiom universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0 /\ syntactically_safe_U ru0.

  Axiom safe_invariant : invariantFor
                           SYS
                           (fun st => no_resends_U (fst st)
                                 /\ stuck_model_step_user_stuck_user st ).

End SyntacticallySafeProtocol.

Module ProtocolSimulates (Proto : SyntacticallySafeProtocol).
  Import Proto.

  Lemma no_resends_inv : invariantFor SYS (fun st => no_resends_U (fst st)).
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder idtac ]. Qed.

  Lemma stuck_not_misaligned_inv : invariantFor SYS stuck_model_step_user_stuck_user.
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder eauto ]. Qed.

  Hint Resolve no_resends_inv stuck_not_misaligned_inv.

  Definition reachable_from := (fun ru iu ru' iu' => SYS.(Step)^* (ru, iu) (ru', iu')).
  (* Definition reachable_froms := (fun st st' => reachable_from (fst st) (snd st) (fst st') (snd st')). *)
  Definition reachable := (fun ru iu => reachable_from ru0 iu0 ru iu).
  (* Definition reachables := (fun st => reachable (fst st) (snd st)). *)

  Tactic Notation "invar" constr(invar_lem) :=
    eapply use_invariant
    ; [ eapply invar_lem
      | eauto
      |]
    ; simpl
    ; eauto.

  Tactic Notation "invar" :=
    eapply use_invariant
    ; [ eauto .. |]
    ; simpl
    ; eauto.


  Inductive R :
    RealWorld.simpl_universe t__hon
    -> IdealWorld.universe t__hon
    -> Prop :=
  | RStep : forall ru iu,
      SYS.(Step) ^* (ru0,iu0) (ru,iu)
      -> R (@RealWorld.peel_adv _ t__adv ru) iu.

  Lemma single_step_stays_lame :
    forall st st',
      SYS.(Step) st st'
      -> lameAdv b (adversary (fst st))
      -> lameAdv b (adversary (fst st')).
  Proof.
    intros.
    invert H;
      simpl in *;
      eauto using universe_step_preserves_lame_adv.
  Qed.
  
  Lemma always_lame' :
    forall st st',
      SYS.(Step) ^* st st'
      -> forall (ru ru' : RealWorld.universe t__hon t__adv) (iu iu' : IdealWorld.universe t__hon),
          st = (ru,iu)
        -> st' = (ru',iu')
        -> lameAdv b (adversary ru)
        -> lameAdv b (adversary ru').
  Proof.
    unfold SYS; simpl; intros *; intro H.
    eapply trc_ind with (P:=fun st st' => lameAdv b (adversary (fst st)) -> lameAdv b (adversary (fst st'))) in H;
      intros;
      subst;
      simpl in *;
      eauto.
  Qed.

  Lemma always_lame :
    forall (ru ru' : RealWorld.universe t__hon t__adv) (iu iu' : IdealWorld.universe t__hon),
      lameAdv b (adversary ru)
      -> SYS.(Step) ^* (ru,iu) (ru',iu')
      -> lameAdv b (adversary ru').
  Proof.
    intros; eauto using always_lame'.
  Qed.

  Hint Resolve always_lame : safe.

  Lemma lame_adv_no_impact_silent_step' :
    forall A B C u_id bd bd',
      step_user Silent (Some u_id) bd bd'
      -> forall (usrs usrs' : honest_users A) (adv adv' advx : user_data B) (cmd cmd' : user_cmd C)
          cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n',
        bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
        -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
        -> exists advx',
            step_user Silent (Some u_id)
                      (usrs,advx,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                      (usrs',advx',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd').
  Proof.
    induction 1; inversion 1; inversion 1;
      intros;
      repeat match goal with
             | [ H : (_,_,_,_,_,_,_,_,_,_,_) = _ |- _ ] => invert H
             end;
      try solve [eexists; subst; econstructor; eauto].

    specialize (IHstep_user _ _ _ _ advx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); split_ex.
    eexists; eapply StepBindRecur; eauto.
  Qed.

  Lemma lame_adv_no_impact_silent_step :
    forall A B C u_id
      (usrs usrs' : honest_users A) (adv adv' advx : user_data B) (cmd cmd' : user_cmd C)
      cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n',
      step_user Silent (Some u_id)
                (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> exists advx',
        step_user Silent (Some u_id)
                  (usrs,advx,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                  (usrs',advx',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd').
  Proof.
    intros; eauto using lame_adv_no_impact_silent_step'.
  Qed.

  Lemma lame_adv_no_impact_labeled_step' :
    forall A B C u_id bd bd' a__r,
      step_user (Action a__r) (Some u_id) bd bd'
      -> forall (usrs usrs' : honest_users A) (adv adv' advx : user_data B) (cmd cmd' : user_cmd C)
          cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n',
        bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
        -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
        -> exists advx',
            step_user (Action a__r) (Some u_id)
                      (usrs,advx,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                      (usrs',advx',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd').
  Proof.
    induction 1; inversion 1; inversion 1;
      intros;
      repeat match goal with
             | [ H : (_,_,_,_,_,_,_,_,_,_,_) = _ |- _ ] => invert H
             end;
      try solve [eexists; subst; econstructor; eauto].

    specialize (IHstep_user _ _ _ _ advx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); split_ex.
    eexists; eapply StepBindRecur; eauto.
  Qed.

  Lemma lame_adv_no_impact_labeled_step :
    forall A B C u_id a__r
      (usrs usrs' : honest_users A) (adv adv' advx : user_data B) (cmd cmd' : user_cmd C)
      cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n',
      step_user (Action a__r) (Some u_id)
                (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> exists advx',
        step_user (Action a__r) (Some u_id)
                  (usrs,advx,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                  (usrs',advx',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd').
  Proof.
    intros; eauto using lame_adv_no_impact_labeled_step'.
  Qed.

  Lemma reachable_from_silent_step :
    forall iu (ru U U' : RealWorld.universe t__hon t__adv),
      SYS.(Step) ^* (ru0,iu0) (ru,iu)
      -> step_universe U Silent U'
      -> lameAdv b U.(adversary)
      -> ru.(users) = U.(users)
      -> ru.(all_ciphers) = U.(all_ciphers)
      -> ru.(all_keys) = U.(all_keys)
      -> exists U'',
          step_universe ru Silent U''
          /\ peel_adv U' = peel_adv U''.
  Proof.
    intros.
    assert (lameAdv b ru.(adversary))
      by (pose proof U_good; unfold universe_starts_sane, adversary_is_lame in *; split_ands; eauto with safe).
    
    destruct ru; destruct U; simpl in *; subst.
    invert H0.
    - destruct userData; unfold build_data_step in *; simpl in *.

      eapply lame_adv_no_impact_silent_step in H3; split_ex.
      eexists; split.
      eapply StepUser; unfold build_data_step; eauto; simpl in *.
      unfold buildUniverse, peel_adv; simpl; trivial.
      
    - unfold lameAdv, build_data_step in *; simpl in *.
      rewrite H1 in H2.
      invert H2.
  Qed.
  
  Lemma reachable_from_labeled_step :
    forall iu (ru U U' : RealWorld.universe t__hon t__adv) a__r,
      SYS.(Step) ^* (ru0,iu0) (ru,iu)
      -> step_universe U (Action a__r) U'

      -> lameAdv b U.(adversary)
      -> ru.(users) = U.(users)
      -> ru.(all_ciphers) = U.(all_ciphers)
      -> ru.(all_keys) = U.(all_keys)
      -> exists U'',
          step_universe ru (Action a__r) U''
          /\ peel_adv U' = peel_adv U''.
  Proof.
    intros.
    assert (lameAdv b ru.(adversary))
      by (pose proof U_good; unfold universe_starts_sane, adversary_is_lame in *; split_ands; eauto with safe).
    
    destruct ru; destruct U; simpl in *; subst.
    invert H0.

    destruct userData; unfold build_data_step in *; simpl in *.

    eapply lame_adv_no_impact_labeled_step in H3; split_ex.
    eexists; split.
    eapply StepUser; unfold build_data_step; eauto; simpl in *.
    unfold buildUniverse, peel_adv; simpl; trivial.
  Qed.

  Lemma simsilent : simulates_silent_step (lameAdv b) R.
  Proof.
    hnf
    ; intros * REL UOK AUOK LAME * STEP
    ; invert REL.

    generalize (reachable_from_silent_step _ _ _ _ H3 STEP LAME H H1 H2);
      intros; split_ex.

    eexists; split; eauto.
    rewrite H4.
    econstructor.

    eapply trcEnd_trc.
    generalize (trc_trcEnd H3); intros.
    econstructor; eauto.
    unfold SYS; simpl.
    econstructor; eauto.
    
  Qed.

  Lemma message_eq_adv_change :
    forall {t t1 t2} (m__rw : crypto t) (m__iw : IdealWorld.message.message t)
      (U U' : RealWorld.universe t1 t2) (U__i : IdealWorld.universe t1) ch_id,
      message_eq m__rw U m__iw U__i ch_id
      -> users U = users U'
      -> all_ciphers U = all_ciphers U'
      -> all_keys U = all_keys U'
      -> message_eq m__rw U' m__iw U__i ch_id.
  Proof.
    intros * MEQ RWU RWC RWK.
    invert MEQ; [ econstructor 1 | econstructor 2 ]
    ; rewrite <- ?RWU, <- ?RWC, <- ?RWK
    ; eauto.
  Qed.

  Hint Resolve message_eq_adv_change : safe.
  Hint Constructors action_matches : safe.
  
  Lemma action_matches_adv_change :
    forall {t1 t2} (U U' : RealWorld.universe t1 t2) (U__i : IdealWorld.universe t1) a__r a__i,
      action_matches a__r U a__i U__i
      -> users U = users U'
      -> all_ciphers U = all_ciphers U'
      -> all_keys U = all_keys U'
      -> action_matches a__r U' a__i U__i.
  Proof.
    intros * AM RWU RWC RWK.
    invert AM; eauto with safe.
  Qed.

  Lemma simlabeled : simulates_labeled_step (lameAdv b) R.
  Proof.
    hnf
    ; intros * REL UOK AUOK LAME * STEP
    ; invert REL.

    generalize (reachable_from_labeled_step _ _ _ _ _ H3 STEP LAME H H1 H2);
      intros; split_ex.

    pose proof stuck_not_misaligned_inv.
    unfold invariantFor, SYS in H5; simpl in H5.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto.
    specialize (H5 _ ARG _ H3).
    apply stuck_model_step_user_stuck_user_implies_labels_align in H5.

    specialize (H5 _ _ H0); split_ex; rewrite H4; (do 3 eexists);
      repeat simple apply conj; eauto.

    - invert H7; eauto with safe.
      
    - econstructor.

      eapply trcEnd_trc.
      generalize (trc_trcEnd H3); intros.
      econstructor; eauto.
      unfold SYS; simpl.
      econstructor; eauto.
  Qed.

  Lemma ss_implies_next_safe :
    forall t (cmd : user_cmd t) uid ctx uids sty cs,
      syntactically_safe uid uids ctx cmd sty
      -> forall A B (usrs usrs' : honest_users A) (adv adv' : user_data B) cmd'
          cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' lbl,
        step_user lbl (Some uid)
                  (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                  (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
        -> typingcontext_sound ctx usrs cs uid
        -> uids = compute_ids usrs
        -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
        -> (forall r, cmd__n <> Return r)
        -> no_resends sents'
        -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H1; eauto.
      invert H4.
      eapply IHcmd in H7; eauto.
      eapply H7 in H11; eauto.

      invert H11; trivial.

    - unfold typingcontext_sound in *; split_ex; invert H.
      apply H2 in H11; split_ex; subst.
      apply H1 in H10.
      unfold msg_honestly_signed, msg_signing_key,
             msg_to_this_user, msg_destination_user,
             msgCiphersSignedOk, honest_keyb;
        context_map_rewrites.
      destruct ( cipher_to_user x0 ==n cipher_to_user x0 ); try contradiction.
      repeat simple apply conj; eauto.
      econstructor; eauto.
      unfold msg_honestly_signed, msg_signing_key, honest_keyb;
        context_map_rewrites;
        trivial.
      (do 2 eexists); repeat simple apply conj; eauto.
      invert H0.
      unfold no_resends, updateSentNonce in H5; context_map_rewrites.
      destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
      invert H5; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H12 in H; split_ex; subst; eauto.
  Qed.

  Lemma ss_implies_next_safe_not_send :
    forall t (cmd : user_cmd t) {A} (usrs : honest_users A) uid uids ctx sty cs froms sents,
      syntactically_safe uid uids ctx cmd sty
      -> typingcontext_sound ctx usrs cs uid
      -> uids = compute_ids usrs
      -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
      -> (forall t__msg recuid (msg : crypto t__msg), cmd__n ~= Send recuid msg -> False)
      -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H3; eauto.
      eapply IHcmd with (froms := froms) (sents := sents) in H11; eauto.
      eapply na_deterministic in H9; eauto; split_ex; subst.
      invert H2.
      eapply H11 in H6; eauto.

    - invert H2.
      exfalso.
      eapply H3; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H10 in H; split_ex; subst; eauto.
  Qed.

  Lemma ss_implies_next_safe_not_send' :
    forall t (cmd : user_cmd t) uid uids ctx sty A (usrs : honest_users A) cs froms sents,
      syntactically_safe uid uids ctx cmd sty
      -> typingcontext_sound ctx usrs cs uid
      -> uids = compute_ids usrs
      -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
      -> match cmd__n with
        | Send recuid msg => t__n = Base Unit /\ (cmd__n ~= Send recuid msg -> False)
        | _ => False
        end
      -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H3; eauto.
      eapply IHcmd with (froms := froms) (sents := sents) in H11; eauto.
      eapply na_deterministic in H9; eauto; split_ex; subst.
      invert H2.
      eapply H11 in H6; eauto.

    - invert H2; split_ex.
      exfalso.
      eapply H2; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H10 in H; split_ex; subst; eauto.
  Qed.

  Lemma model_step_implies_step :
    forall t__hon t__adv uid st st',
      @model_step_user t__hon t__adv uid st st'
      -> step st st'.
  Proof.
    intros * MS.
    invert MS; intros.
    - econstructor 1.
      econstructor; eauto.
    - econstructor 2; eauto.
      econstructor; eauto.
  Qed.

  Lemma step_na_recur :
    forall t t__n (cmd : user_cmd t) (cmd__n : user_cmd t__n),
      nextAction cmd cmd__n
      -> forall A B suid lbl bd bd',

        step_user lbl suid bd bd'

        -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
            cmd__n' ks ks' qmsgs qmsgs' mycs mycs'
            froms froms' sents sents' cur_n cur_n',

          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n)
          -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n')
          -> exists bd'',
              step_user lbl suid (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) bd''.
  Proof.
    induct 1; intros; subst;
      eauto.

    eapply IHnextAction in H0; eauto. split_ex.
    simpl.

    Set Printing Implicit.
    
    dt x; eexists; eapply StepBindRecur; eauto.

  Qed.

  Lemma simsafe : honest_actions_safe t__adv R.
  Proof.
    hnf
    ; intros * REL UOK AUOK
    ; invert REL.

    pose proof no_resends_inv.
    unfold invariantFor, SYS in H0; simpl in H0.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by auto.
    specialize (H0 _ ARG).

    pose proof universe_starts_safe; simpl in *; split_ex.
    assert (syntactically_safe_U ru).
    change (syntactically_safe_U (fst (ru,U__i))).
    assert (goodness_predicates (fst (ru0, iu0))).
    unfold goodness_predicates, adv_goodness , adv_universe_ok, universe_ok,
           adv_message_queue_ok, adv_cipher_queue_ok in *; intuition idtac.
    1-2:simpl.

    rewrite Forall_forall in H15 |- *; intros * LIN; eapply H15 in LIN; destruct x; intuition idtac.
    eapply H27 in H26; split_ex; intuition eauto.

    rewrite Forall_forall in H13 |- *; intros * LIN; eapply H13 in LIN; split_ex; intuition eauto.
    eapply syntactically_safe_U_preservation_steps; eauto.
    
    unfold syntactically_safe_U in *; simpl in *.
    unfold honest_cmds_safe; intros; subst.
    destruct u; simpl.
    generalize H9; intros USRS; rewrite <- H in USRS.
    specialize (H7 _ _ _ USRS eq_refl); split_ex; simpl in *.

    rename U__i into iu.
    red. intros.

    destruct (classic (exists st', model_step_user u_id (ru,iu) st')).
    - split_ex.
      rename x1 into st'.
      pose proof (model_step_implies_step _ _ _ _ _ H11) as STEP.
      assert (STEPS' : (@step t__hon t__adv) ^* (ru,iu) st') by (eauto using TrcFront).
      pose proof (trc_trans H3 STEPS') as STEPS.

      specialize (H0 _ STEPS); unfold no_resends_U in H0.
      destruct st' as [ru1 iu1]; simpl in *.

      rewrite <- H, <- H1.
      destruct (classic (exists r, cmd__n = Return r)); split_ex; subst; eauto.
      assert (forall r, cmd__n <> Return r) by eauto using all_not_not_ex.

      rewrite Forall_natmap_forall in H0.
      
      destruct ru; invert H11;
        unfold build_data_step in *;
        clean_map_lookups;
        simpl in *;
        eapply ss_implies_next_safe; eauto.

      all: 
        specialize (H0 u_id); rewrite add_eq_o in H0 by trivial;
        specialize (H0 _ eq_refl);
        eauto.

    - eapply syntactically_safe_na in H7; eauto; split_ex.
      rewrite <- H, <- H1.
      unfold typingcontext_sound in *; split_ex.
      invert H7; subst; process_ctx; eauto.

      + eapply nextAction_couldBe in H10; eauto.
      + apply H16 in H14; split_ex; subst; eauto.
      + exfalso.
        assert (forall st', model_step_user u_id (ru,iu) st' -> False) by eauto using not_ex_all_not.
        pose proof stuck_not_misaligned_inv as NOTMISAL.
        specialize (NOTMISAL _ ARG _ H3).
        eapply NOTMISAL in H14.
        2: simpl; exact USRS.
        
        unfold build_data_step in *; simpl in *.
        assert (STEP : exists lbl bd,
                   step_user lbl
                             (Some u_id)
                             (users ru, adversary ru, all_ciphers ru, all_keys ru,
                              key_heap, msg_heap, c_heap, from_nons, sent_nons, cur_nonce,
                              Send (cipher_to_user x2) (@SignedCiphertext t0 x1)) bd).

        (* generalize (syntactically_safe_na _ _ _ _ H7 _ _ _ _ H4); intros; split_ex. *)
        unfold typingcontext_sound in *; split_ex.
        (do 2 eexists); econstructor; clean_map_lookups; simpl in *; eauto.
        context_map_rewrites; eauto.
        unfold not; intros INV; invert INV; contradiction.
        
        split_ex.

        assert (forall st', model_step_user u_id (ru,iu) st' -> False) by eauto using not_ex_all_not.
        eapply NOTMISAL in H20; eauto.
        unfold build_data_step in H20; simpl in H20; eauto.

        dt x5; eapply step_na_recur in H10; eauto; split_ex; eauto.
  Qed.

  Hint Resolve simsilent simlabeled simsafe : safe.

  Lemma proto_lamely_refines :
    refines (lameAdv b) ru0 iu0.
  Proof.
    exists R; unfold simulates.

    pose proof safe_invariant.
    pose proof universe_starts_safe; split_ands.
    
    unfold invariantFor in H; simpl in H.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto.
    specialize (H _ ARG); clear ARG.

    Hint Constructors R : safe.

    unfold simulates_silent_step, simulates_labeled_step;
      intuition eauto with safe.

  Qed.

  Hint Resolve proto_lamely_refines : safe.

  Lemma proto_starts_ok : universe_starts_ok ru0.
  Proof.
    pose proof universe_starts_safe.
    pose proof U_good.
    unfold universe_starts_ok; intros.
    unfold universe_ok, adv_universe_ok, universe_starts_sane in *; split_ands.
    intuition eauto.
  Qed.

  Hint Resolve proto_starts_ok : safe.

  Theorem protocol_with_adversary_could_generate_spec :
    forall U__ra advcode acts__r,
      U__ra = add_adversary ru0 advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate iu0 acts__i
          /\ traceMatches acts__r acts__i.
  Proof.
    intros.
    pose proof U_good as L; unfold universe_starts_sane, adversary_is_lame in L; split_ands.
    eapply refines_could_generate; eauto with safe.
  Qed.

End ProtocolSimulates.
