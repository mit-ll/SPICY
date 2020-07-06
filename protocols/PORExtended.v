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
     UsersTheory.

From protocols Require Import
     RealWorldStepLemmas
     ExampleProtocols
     ModelCheck
     ProtocolAutomation
     SafeProtocol
     SyntacticallySafe
     LabelsAlign
     PartialOrderReduction
.

Definition stuck_model_step_user_stuck_user {t__hon t__adv}
           (st : universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  forall uid u,
    (fst st).(users) $? uid = Some u
    -> (forall st', model_step_user uid st st' -> False)
    -> (forall lbl bd, step_user lbl (Some uid) (build_data_step (fst st) u) bd -> False).


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

    + admit.  (* contradiction based on steps being deterministic *)
    + 




  - assert (forall st', ~ model_step_user u_id (ru,iu) st') by eauto using all_not_not_ex.
    eapply H in H3; eauto.
    contradiction.
Qed.
  


Lemma stuck_other_step_not_unstuck :
  forall t__hon t__adv uid st st',
    @model_step_user t__hon t__adv uid st st'
    -> forall uid' lbl u bd,
      (fst st).(users) $? uid' = Some u
      -> step_user lbl (Some uid') (build_data_step (fst st) u) bd
      -> uid <> uid'
      -> (forall st'', model_step_user uid' st st'' -> False)
      -> (forall st'', model_step_user uid' st' st'' -> False).
Proof.
  intros.
  invert H;
    unfold build_data_step, buildUniverse in *; simpl in *.

  - 
  
  invert H; invert H2;
    unfold build_data_step, buildUniverse in *; simpl in *;
      clean_map_lookups.
  - destruct ru , userData, userData0; simpl in *.


    assert (exists m, users $? uid' =
                 Some
                   {|
                     key_heap := key_heap0;
                     protocol := protocol0;
                     msg_heap := msg_heap0 ++ m;
                     c_heap := c_heap0;
                     from_nons := from_nons0;
                     sent_nons := sent_nons0;
                     cur_nonce := cur_nonce0 |}).
    eapply step_back_into_other_user with (u_id1 := uid) in H4; eauto.
    split_ors; split_ex; eauto.

    2: {
      simpl.
    



Lemma stuck_other_step_not_unstuck :
  forall t__hon t__adv t suid bd bd',

    step_user Silent suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid ru iu,

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> forall cmda1, usrs $? uid = Some (mkUserData ks cmda1 qmsgs mycs froms sents n)
      -> ru = {| users := usrs; adversary := adv; all_ciphers := cs ; all_keys := gks |}
      -> forall ru' uid' cmda,
          uid <> uid'
          -> (forall st, model_step_user uid' (ru,iu) st -> False)
          -> ru' = buildUniverse_step (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmda) uid
          -> (forall st, model_step_user uid' (ru',iu) st -> False).
Proof.
  induction 1; inversion 1; inversion 1; intros; subst;
    eauto.

  admit.
  admit.

  unfold buildUniverse_step in *; simpl in *.
    


Lemma stuck_step_implies_stuck_universe_step_labels_align :
  forall t__hon t__adv st,
    @stuck_step_implies_stuck_universe_step t__hon t__adv st
    -> labels_align st.
Proof.
  destruct st as [ru iu].
  unfold stuck_step_implies_stuck_universe_step, labels_align; intros.

  destruct (classic (forall st', step (ru,iu) st' -> False)).
  - exfalso; eauto.
  - eapply not_all_not_ex in H1; split_ex.
    

Admitted.

Lemma stuck_step_trsys_implies_labels_align :
  forall t__hon t__adv st st',
    (@step t__hon t__adv) ^* st st'
    -> forall ru0 iu0,
      st = (ru0,iu0)
      -> invariantFor (@S t__hon t__adv ru0 iu0) stuck_step_implies_stuck_universe_step
      -> labels_align st'.
Proof.
  induction 1; intros; subst; eauto.
  - unfold invariantFor in *; simpl in *; intros.
    assert (ARG : (ru0,iu0) = (ru0,iu0) \/ False) by eauto.
    specialize (H0 _ ARG); clear ARG.
    assert (STEP : (@step t__hon t__adv) ^* (ru0,iu0) (ru0,iu0)) by eauto.
    apply H0 in STEP.
    apply stuck_step_implies_stuck_universe_step_labels_align in STEP.
    unfold labels_align in STEP; eauto.

  - destruct y as [ru1 iu1].
    assert (STEP : (@step t__hon t__adv) ^* (ru0,iu0) (ru1,iu1)) by (eapply TrcFront; eauto).
    assert (INIT : (ru0,iu0) = (ru0,iu0) \/ False ) by eauto.

    assert (INV : invariantFor (S ru1 iu1) stuck_step_implies_stuck_universe_step).
    unfold invariantFor; simpl; intros.
    destruct H1; try contradiction; subst.
    eapply trc_trans in H3; eauto.
    eapply H2; simpl; eauto.

    eapply IHtrc in INV; eauto.
Qed.

Lemma stuck_step_violation_implies_alignment_violation :
  forall t__hon t__adv st,
    ~ @stuck_step_implies_stuck_universe_step t__hon t__adv st
    -> ~ labels_align st.
Proof.
  unfold stuck_step_implies_stuck_universe_step, labels_align; intros.
  destruct st as [ru iu]; simpl in *.
  unfold not; intros.
  eapply H; intros; clear H.
  destruct lbl.
  - eapply H1; econstructor; eauto.
  - generalize H2; intros; eapply H0 in H2; split_ex.
    eapply H1; econstructor 2; eauto.
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
                                 /\ stuck_step_implies_stuck_universe_step st ).

End SyntacticallySafeProtocol.

Module ProtocolSimulates (Proto : SyntacticallySafeProtocol).
  Import Proto.

  Lemma no_resends_inv : invariantFor SYS (fun st => no_resends_U (fst st)).
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder idtac]. Qed.

  Lemma stuck_not_misaligned_inv : invariantFor SYS stuck_step_implies_stuck_universe_step.
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder idtac]. Qed.

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

    admit.
    (* pose proof labels_align_inv. *)
    (* unfold invariantFor, SYS in H5; simpl in H5. *)
    (* assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto. *)
    (* specialize (H5 _ ARG _ H3 _ _ H0). *)

    (* split_ex. *)
    (* do 3 eexists; rewrite H4; repeat apply conj; eauto. *)
    (* - invert H7; eauto with safe. *)
      
    (* - econstructor. *)

    (*   eapply trcEnd_trc. *)
    (*   generalize (trc_trcEnd H3); intros. *)
    (*   econstructor; eauto. *)
    (*   unfold SYS; simpl. *)
    (*   econstructor; eauto. *)
  Admitted.

  (* Lemma honest_cmds_safe_adv_change : *)
  (*   forall {t1 t2} (U U' : RealWorld.universe t1 t2), *)
  (*     honest_cmds_safe U *)
  (*     -> users U = users U' *)
  (*     -> all_ciphers U = all_ciphers U' *)
  (*     -> all_keys U = all_keys U' *)
  (*     -> honest_cmds_safe U'. *)
  (* Proof. *)
  (*   intros * HCS RWU RWC RWK. *)
  (*   unfold honest_cmds_safe in * *)
  (*   ; intros *)
  (*   ; rewrite <- ?RWU, <- ?RWC, <- ?RWK in * *)
  (*   ; eauto. *)
  (* Qed. *)

  (* Hint Resolve honest_cmds_safe_adv_change : safe. *)

  Require Import Coq.Program.Equality.

  Lemma foo :
    forall A B t (cmd : user_cmd t) (usrs : honest_users A) (adv : user_data B) cs gks
      uid ks qmsgs mycs froms sents n,
        (forall lbl bd, ~ step_user lbl (Some uid) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd) bd)
        -> forall t__n cmd1 (cmd2 : <<t__n>> -> user_cmd t),
        cmd = Bind cmd1 cmd2
        -> forall lbl' bd',
          ~ step_user lbl' (Some uid) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd1) bd'.
  Admitted.

  Hint Resolve foo : core.
    

  (* Lemma predicates_imply_next_cmd_safe_no_step' : *)
  (*   forall A B t (cmd : user_cmd t) (usrs : honest_users A) (adv : user_data B) cs gks *)
  (*     uid ks qmsgs mycs froms sents n ctx styp, *)
  (*     syntactically_safe uid ctx cmd styp *)
  (*     -> typingcontext_sound ctx (findUserKeys usrs) cs uid *)
  (*     -> (forall usrs' adv' cs' gks' ks' qmsgs' mycs' froms' sents' n' cmd' lbl, *)
  (*           ~ step_user lbl (Some uid) *)
  (*             (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd) *)
  (*             (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')) *)
  (*     -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd. *)
  (* Proof. *)
  (*   dependent induction cmd; *)
  (*     unfold next_cmd_safe; intros; *)
  (*       match goal with *)
  (*       | [ H : nextAction _ _ |- _ ] => invert H *)
  (*       end; *)
  (*       eauto. *)

  (*   - invert H0. *)
  (*     eapply IHcmd *)
  (*         (* (bd := (usrs0, adv0, cs0, gks0, ks0, qmsgs0, mycs0, froms0, sents0, cur_n, cmd0)) *) *)
  (*       in H10; eauto.  *)
  (*     apply H10 in H7; eauto. *)
  (*     intros; eauto. *)
  (*     unfold not; intros. *)
  (*     eapply H2. *)
  (*     admit. *)
    
    (* forall A B C lbl suid bd bd', *)
    (*   step_user lbl suid bd bd' *)
    (*   -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd C) *)
    (*       cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' u_id, *)
    (*     suid = Some u_id *)
    (*     -> bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd) *)
    (*     -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd') *)
    (*     -> no_resends sents' *)
    (*     -> forall ctx styp, syntactically_safe u_id ctx cmd styp *)
    (*     -> typingcontext_sound ctx (findUserKeys usrs) cs u_id *)
    (*     -> forall cmdc, usrs $? u_id = Some {| key_heap := ks; *)
    (*                                      protocol := cmdc; *)
    (*                                      msg_heap := qmsgs; *)
    (*                                      c_heap   := mycs; *)
    (*                                      from_nons := froms; *)
    (*                                      sent_nons := sents; *)
    (*                                      cur_nonce := n |} *)
    (*     -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd. *)


  
  (* Lemma predicates_imply_next_cmd_safe_step : *)
  (*   forall A B C lbl suid bd bd', *)
  (*     step_user lbl suid bd bd' *)
  (*     -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd C) *)
  (*         cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' u_id, *)
  (*       suid = Some u_id *)
  (*       -> bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd) *)
  (*       -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd') *)
  (*       -> no_resends sents' *)
  (*       -> forall ctx styp, syntactically_safe u_id ctx cmd styp *)
  (*       -> typingcontext_sound ctx (findUserKeys usrs) cs u_id *)
  (*       -> forall cmdc, usrs $? u_id = Some {| key_heap := ks; *)
  (*                                        protocol := cmdc; *)
  (*                                        msg_heap := qmsgs; *)
  (*                                        c_heap   := mycs; *)
  (*                                        from_nons := froms; *)
  (*                                        sent_nons := sents; *)
  (*                                        cur_nonce := n |} *)
  (*       -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd. *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 1; *)
  (*     unfold next_cmd_safe; intros; subst; *)
  (*       match goal with *)
  (*       | [ H : nextAction _ _ |- _ ] => invert H *)
  (*       end; *)
  (*       match goal with *)
  (*       | [ H : syntactically_safe _ _ _ _  |- _ ] => *)
  (*         invert H; unfold typingcontext_sound in *; split_ex *)
  (*       end; *)
  (*       eauto. *)

  (*   - eapply IHstep_user in H6; eauto. *)
  (*     invert H3; eauto. *)
  (*   - invert H5; eauto. *)
  (*   - eapply H4 in H12; split_ex; subst; clear H4. *)
  (*     clean_context. *)
  (*     invert H10. *)
  (*     apply H in H14. *)
  (*     unfold msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user, honest_keyb; *)
  (*       context_map_rewrites; *)
  (*       destruct (cipher_to_user x0 ==n cipher_to_user x0); *)
  (*       try contradiction. *)
  (*     repeat simple apply conj; eauto. *)

  (*     econstructor; eauto. *)

  (*     unfold msg_honestly_signed, msg_signing_key, honest_keyb; *)
  (*       context_map_rewrites; *)
  (*       trivial. *)

  (*     (do 2 eexists); repeat simple apply conj; eauto. *)
      
  (*     unfold no_resends in H22. *)
  (*     invert H22; eauto. *)

  (*   - intros. *)
  (*     eapply H14 in H5; split_ex; subst; split; eauto. *)
  (* Qed. *)
  
      
  Lemma simsafe : honest_actions_safe t__adv R.
  Proof.
    hnf
    ; intros * REL UOK AUOK
    ; invert REL.

    pose proof no_resends_inv.
    unfold invariantFor, SYS in H0; simpl in H0.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by auto.
    specialize (H0 _ ARG); clear ARG.

    assert (syntactically_safe_U ru) by admit.
    unfold syntactically_safe_U in *; simpl in *.
    unfold honest_cmds_safe; intros; subst.
    destruct u; simpl.
    generalize H6; intros USRS; rewrite <- H in USRS.
    specialize (H4 _ _ USRS); split_ex; simpl in *.

    rename U__i into iu.
    destruct (classic (exists st', step (ru,iu) st')).
    - split_ex.
      rename x1 into st'.
      assert (STEP : (@step t__hon t__adv) ^* (ru,iu) st') by (eauto using TrcFront).
      pose proof (trc_trans H3 STEP) as STEPS.

      specialize (H0 _ STEPS); unfold no_resends_U in H0.
      
      (* rewrite Forall_natmap_forall in H0; specialize (H0 _ _ USRS); simpl in H0. *)
      (* eapply predicates_imply_next_cmd_safe; eauto. *)
      admit.
    - admit.


    (* pose proof safety_inv. *)
    (* unfold invariantFor, SYS in H0; simpl in H0. *)
    (* assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto. *)
    (* specialize (H0 _ ARG _ H3). *)
    (* unfold safety in *; eauto with safe. *)

  Admitted.

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

