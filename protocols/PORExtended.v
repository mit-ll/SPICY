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

    + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6); discriminate.
    + pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H2 H6).
      invert H0.
      (do 3 eexists); repeat simple apply conj; eauto.

  - assert (forall st', ~ model_step_user u_id (ru,iu) st') by eauto using all_not_not_ex.
    eapply H in H3; eauto.
    contradiction.
Qed.


Lemma no_model_step_other_user_silent_step :
  forall t t__hon t__adv suid bd bd',

    step_user Silent suid bd bd'
    
    -> forall (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) (cmd cmd' : user_cmd t)
        cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' uid uid' iu,

      bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
      -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> suid = Some uid
      -> forall st', model_step_user uid (mkUniverse usrs adv cs gks, iu) st'
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
  induct 1; inversion 1; inversion 1; intros; subst; eauto;
    clean_context.

  - invert H27; unfold build_data_step in *; simpl in *.
    admit.
    
  

Admitted.

Lemma stuck_model_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> stuck_model_step_user_stuck_user st'
    -> stuck_model_step_user_stuck_user st.
Proof.
  unfold stuck_model_step_user_stuck_user; intros.

  invert H; simpl in *.

  - invert H5; dismiss_adv.
    unfold buildUniverse, build_data_step in *; simpl in *.

    destruct (u_id ==n uid); subst; clean_map_lookups.
    + eapply H3.
      econstructor; eauto.
    + generalize H6; intros OUSTEP.
      destruct ru, u; simpl in *.
      eapply impact_from_other_user_step in OUSTEP; eauto; split_ex.

      specialize (H1 uid).
      rewrite add_neq_o in H1 by auto.
      specialize (H1 _ H5); simpl in H1.

      (* pose proof (no_model_step_other_user_silent_step *)
      (*               _ _ _ _ _ H6 *)
      (*               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ *)
      (*               eq_refl eq_refl eq_refl n H3) as NOMODEL. *)
      (* specialize (H1 NOMODEL). *)
      (* eapply H1. *)

      (* Need lemma for :
       *   if I can step now
       *   and other user silently steps instead 
       *   then I can still step in the new universe *)

      admit.

  (* labeled case -- this will perhaps be a bit more difficult because of the ideal world *)
  - invert H5.
    unfold buildUniverse, build_data_step in *; simpl in *.

    destruct (u_id ==n uid); subst; clean_map_lookups.
    + eapply H3.
      econstructor 2; eauto.
    + admit.

  
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
    forall t (cmd : user_cmd t) uid ctx sty honestk cs froms sents,
      syntactically_safe uid ctx cmd sty
      -> typingcontext_sound ctx honestk cs uid
      -> forall A B (usrs usrs' : honest_users A) (adv adv' : user_data B) cmd'
          cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms' sents' n n' lbl,
          step_user lbl (Some uid)
                    (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                    (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
          -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
          -> (forall r, cmd__n <> Return r)
          -> no_resends sents'
          -> next_cmd_safe honestk cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H2; eauto.
      invert H3.
      eapply IHcmd in H8; eauto.
      eapply H8 in H10; eauto.

      invert H3. invert H7. specialize (H4 a0); contradiction.

    - unfold typingcontext_sound in *; split_ex; invert H.
      apply H5 in H12; split_ex; subst.
      apply H0 in H10.
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
      invert H1.
      unfold no_resends, updateSentNonce in H4; context_map_rewrites.
      destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
      invert H4; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H14 in H; split_ex; subst; eauto.
  Qed.

  Lemma ss_implies_next_safe_not_send :
    forall t (cmd : user_cmd t) uid ctx sty honestk cs froms sents,
      syntactically_safe uid ctx cmd sty
      -> typingcontext_sound ctx honestk cs uid
      -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
      -> (forall t__msg recuid (msg : crypto t__msg), cmd__n ~= Send recuid msg -> False)
      -> next_cmd_safe honestk cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H2; eauto.
      eapply IHcmd in H11; eauto.
      eapply na_deterministic in H8; eauto; split_ex; subst.
      invert H2.
      eapply H11 in H6; eauto.

    - invert H1.
      exfalso.
      eapply H2; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H12 in H; split_ex; subst; eauto.

      Unshelve.
      eauto.
  Qed.

  Lemma ss_implies_next_safe_not_send' :
    forall t (cmd : user_cmd t) uid ctx sty honestk cs froms sents,
      syntactically_safe uid ctx cmd sty
      -> typingcontext_sound ctx honestk cs uid
      -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
      -> match cmd__n with
        | Send recuid msg => t__n = Base Unit /\ (cmd__n ~= Send recuid msg -> False)
        | _ => False
        end
      -> next_cmd_safe honestk cs uid froms sents cmd.
  Proof.
    induct cmd;
      unfold next_cmd_safe; intros;
        match goal with
        | [ H : nextAction _ _ |- _ ] => invert H
        end; eauto;
          try solve [ unfold typingcontext_sound in *; split_ex;
                      match goal with
                      | [ H : syntactically_safe _ _ _ _ |- _ ] => invert H
                      end; eauto ].

    - invert H0.
      invert H2; eauto.
      eapply IHcmd in H11; eauto.
      eapply na_deterministic in H8; eauto; split_ex; subst.
      invert H2.
      eapply H11 in H6; eauto.

    - invert H1.
      exfalso.
      eapply H2; eauto.
      
    - unfold typingcontext_sound in *; split_ex; invert H; eauto.
      intros.
      apply H12 in H; split_ex; subst; eauto.

      Unshelve.
      eauto.
  Qed.

  (* Lemma ss_implies_next_safe_not_send : *)
  (*   forall t__hon t__adv (usrs : honest_users t__hon)  (cmd : user_cmd t) uid ctx sty honestk cs froms sents, *)
  (*     syntactically_safe uid ctx cmd sty *)
  (*     -> typingcontext_sound ctx honestk cs uid *)
  (*     -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n *)
  (*     -> next_cmd_safe honestk cs uid froms sents cmd. *)
  (* Proof. *)
  (*   induct cmd; *)
  (*     unfold next_cmd_safe; intros; *)
  (*       match goal with *)
  (*       | [ H : nextAction _ _ |- _ ] => invert H *)
  (*       end; eauto; *)
  (*         try solve [ unfold typingcontext_sound in *; split_ex; *)
  (*                     match goal with *)
  (*                     | [ H : syntactically_safe _ _ _ _ |- _ ] => invert H *)
  (*                     end; eauto ]. *)

  (*   - invert H0. *)
  (*     invert H2; eauto. *)
  (*     eapply IHcmd in H11; eauto. *)
  (*     eapply na_deterministic in H8; eauto; split_ex; subst. *)
  (*     invert H2. *)
  (*     eapply H11 in H6; eauto. *)

  (*   - invert H1. *)
  (*     exfalso. *)
  (*     eapply H2; eauto. *)
      
  (*   - unfold typingcontext_sound in *; split_ex; invert H; eauto. *)
  (*     intros. *)
  (*     apply H12 in H; split_ex; subst; eauto. *)

  (*     Unshelve. *)
  (*     eauto. *)
  (* Qed. *)

  

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

  Import RealWorldNotations.

  Lemma StepBindRecur' :
    forall {B r r'} (usrs usrs' : honest_users r') (adv adv' : user_data B)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' sents sents' cur_n cur_n'
      (cmd1 cmd1' : user_cmd r) (cmd2 : <<r>> -> user_cmd (Base r')) bd bd',

      step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd1)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd1')
      -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Bind cmd1 cmd2)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', Bind cmd1' cmd2)
      -> forall lbl' suid',
          lbl' = lbl
          -> suid' = u_id
          -> step_user lbl u_id bd bd'.
  Proof.
    intros; subst; eapply StepBindRecur; eauto.
  Qed.

  (* Lemma step_na_not_return : *)
  (*   forall t t__n (cmd : user_cmd t) (cmd__n : user_cmd t__n), *)
  (*     nextAction cmd cmd__n *)
                 
  (*     -> forall A B uid lbl bd bd' cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
  (*         cmd__n' ks ks' qmsgs qmsgs' mycs mycs' *)
  (*         froms froms' sents sents' cur_n cur_n' , *)

  (*       step_user lbl (Some uid) bd bd' *)
  (*       -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n) *)
  (*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n') *)
  (*       -> exists f cmd', *)
  (*           cmd = f cmd__n *)
  (*           /\ cmd' = f cmd__n' *)
  (*           /\ forall lbl1 suid1 (usrs1 usrs1' : honest_users A) (adv1 adv1' : user_data B) *)
  (*               cs1 cs1' gks1 gks1' *)
  (*               ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd__n'' *)
  (*               froms1 froms1' sents1 sents1' cur_n1 cur_n1', *)

  (*               step_user lbl1 suid1 *)
  (*                         (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n) *)
  (*                         (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n'') *)
  (*               -> step_user lbl1 suid1 *)
  (*                           (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, f cmd__n) *)
  (*                           (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', f cmd__n''). *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 1; intros; subst. *)
  (*   - invert H. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - clean_context. *)
  (*     eapply IHnextAction in H0; eauto; split_ex; subst. *)
  (*     exists (fun CD => x <- x CD; c2 x). *)
  (*     eexists; subst; repeat simple apply conj; intros; eauto. *)
  (*     eapply StepBindRecur'. *)
  (*     remember (Some uid) as suid. *)
  (*     match goal with *)
  (*     | [ |- step_user _ _ ?bd1 ?bd2 ] => *)
  (*       remember bd1 as bbd1; *)
  (*         remember bd2 as bbd2 *)
  (*     end. *)

  
  (* Lemma step_na_not_return : *)
  (*   forall t t__n (cmd : user_cmd t) (cmd__n : user_cmd t__n), *)
  (*     nextAction cmd cmd__n *)
                 
  (*     -> forall A B uid lbl bd bd' cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
  (*         cmd__n' ks ks' qmsgs qmsgs' mycs mycs' *)
  (*         froms froms' sents sents' cur_n cur_n' , *)

  (*       step_user lbl (Some uid) bd bd' *)
  (*       -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n) *)
  (*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n') *)
  (*       -> exists f cmd', *)
  (*           cmd = f cmd__n *)
  (*           /\ cmd' = f cmd__n' *)
  (*           /\ step_user lbl (Some uid) *)
  (*                       (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, f cmd__n) *)
  (*                       (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', f cmd__n'). *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 1; intros; subst. *)
  (*   - invert H. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; eauto. *)
  (*   - clean_context. *)
  (*     eapply IHnextAction in H0; eauto; split_ex; subst. *)
  (*     exists (fun CD => x <- x CD; c2 x). *)
  (*     eexists; subst; repeat simple apply conj; eauto. *)
  (*     eapply StepBindRecur'. *)
  (*     remember (Some uid) as suid. *)
  (*     match goal with *)
  (*     | [ |- step_user _ _ ?bd1 ?bd2 ] => *)
  (*       remember bd1 as bbd1; *)
  (*         remember bd2 as bbd2 *)
  (*     end. *)

      
  (*     eapply StepBindRecur' with (cmd1 := x c) (cmd1' :=  x cmd__n') (cmd2 := c2). *)
    


  (* Lemma step_na_not_return : *)
  (*   forall {A B C} suid lbl bd bd', *)

  (*     step_user lbl suid bd bd' *)

  (*     -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
  (*         (cmd__n cmd__n' : user_cmd C) (cmd : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs' *)
  (*         froms froms' sents sents' cur_n cur_n', *)

  (*       bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n) *)
  (*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n') *)
  (*       -> nextAction cmd cmd__n *)
  (*       -> exists f cmd', *)
  (*           (* step_user lbl suid *) *)
  (*           (*           (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n) *) *)
  (*           (*           (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n') *) *)
  (*             cmd = f cmd__n *)
  (*           /\ cmd' = f cmd__n' *)
  (*           /\ step_user lbl suid *)
  (*                       (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, f cmd__n) *)
  (*                       (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', f cmd__n'). *)
  (* Proof. *)
  (*   Hint Constructors step_user syntactically_safe : core. *)

  (*   induction 1; inversion 1; inversion 1; intros; subst. *)

  (*   - eapply nextAction_couldBe in H13; contradiction. *)
  (*   - eapply nextAction_couldBe in H12; contradiction. *)
  (*   -  *)


  (*   - eapply IHstep_user in H28; eauto. *)
  (*     split_ex. *)
  (*     exists (fun CD => x <- x CD; cmd2 x). *)
  (*     eexists; subst; repeat simple apply conj; eauto. *)
      
  (*   - invert H27. *)
  (*     unfold not in *; exfalso; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (*   - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto. *)
  (* Qed. *)


  Lemma simsafe : honest_actions_safe t__adv R.
  Proof.
    hnf
    ; intros * REL UOK AUOK
    ; invert REL.

    pose proof no_resends_inv.
    unfold invariantFor, SYS in H0; simpl in H0.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by auto.
    specialize (H0 _ ARG).

    assert (syntactically_safe_U ru) by admit.
    unfold syntactically_safe_U in *; simpl in *.
    unfold honest_cmds_safe; intros; subst.
    destruct u; simpl.
    generalize H6; intros USRS; rewrite <- H in USRS.
    specialize (H4 _ _ USRS); split_ex; simpl in *.

    rename U__i into iu.
    red. intros.

    destruct (classic (exists st', model_step_user u_id (ru,iu) st')).
    - split_ex.
      rename x1 into st'.
      pose proof (model_step_implies_step _ _ _ _ _ H8) as STEP.
      assert (STEPS' : (@step t__hon t__adv) ^* (ru,iu) st') by (eauto using TrcFront).
      pose proof (trc_trans H3 STEPS') as STEPS.

      specialize (H0 _ STEPS); unfold no_resends_U in H0.
      destruct st' as [ru1 iu1]; simpl in *.

      rewrite <- H, <- H1.
      destruct (classic (exists r, cmd__n = Return r)); split_ex; subst; eauto.
      assert (forall r, cmd__n <> Return r) by eauto using all_not_not_ex.

      rewrite Forall_natmap_forall in H0.
      
      destruct ru; invert H8;
        unfold build_data_step in *;
        clean_map_lookups;
        simpl in *;
        eapply ss_implies_next_safe; eauto.

      specialize (H0 u_id); rewrite add_eq_o in H0 by trivial;
        specialize (H0 _ eq_refl);
        eauto.

      specialize (H0 u_id); rewrite add_eq_o in H0 by trivial;
        specialize (H0 _ eq_refl);
        eauto.

    - dependent destruction cmd__n; eauto.
      + eapply nextAction_couldBe in H7; contradiction.
      + exfalso.
        assert (forall st', model_step_user u_id (ru,iu) st' -> False) by eauto using not_ex_all_not.
        pose proof stuck_not_misaligned_inv as NOTMISAL.
        specialize (NOTMISAL _ ARG _ H3).
        eapply NOTMISAL in H9.
        2: simpl; exact USRS.

        
        unfold build_data_step in *; simpl in *.
        assert (STEP : exists lbl bd,
                   step_user lbl
                             (Some u_id)
                             (users ru, adversary ru, all_ciphers ru, all_keys ru,
                              key_heap, msg_heap, c_heap, from_nons, sent_nons, cur_nonce, Send uid msg) bd).
        (do 2 eexists).
        econstructor; eauto.

        unfold typingcontext_sound in *.
        

        
        eapply step_na_not_return in H7; eauto.
        
        eapply H9.
        unfold build_data_step; simpl.

        


    - destruct (classic (forall t__msg recuid (msg : crypto t__msg), cmd__n ~= Send recuid msg -> False)).
      + eapply ss_implies_next_safe_not_send; eauto.
        rewrite <- H, <- H1; assumption.
      + dependent destruction cmd__n; eauto.

      

    - destruct (classic (match cmd__n with
                         | Send recuid msg => B = Base Unit /\ (cmd__n ~= Send recuid msg -> False)
                         | _ => False
                         end)).

      + eapply ss_implies_next_safe_not_send; eauto.
        rewrite <- H, <- H1; assumption.
        dependent destruction cmd__n; try contradiction.
        split_ands; eauto.

      + dependent destruction cmd__n; eauto.
        * eapply nextAction_couldBe in H7; contradiction.
        * exfalso.
          eapply H9.
          split; intros; eauto.
          invert
        
        


      
    - destruct (classic (forall t__msg recuid (msg : crypto t__msg), cmd__n ~= Send recuid msg -> False)).
      + eapply ss_implies_next_safe_not_send; eauto.
        rewrite <- H, <- H1; assumption.

      + exfalso.
        eapply H9.
        intros.
        invert H10.

        
        
      

      dependent destruction cmd__n; auto.
      apply nextAction_couldBe in H7; contradiction.
      eapply ss_implies_next_safe in H7; eauto.

      
      (* rewrite Forall_natmap_forall in H0; *)
      (*   specialize (H0 _ _ USRS). *)
      (* invert H8; simpl in *. *)
      (* eapply ss_implies_next_safe; eauto. *)
      (* unfold next_cmd_safe; intros. *)

      (* induct H8; eauto. *)
      (* admit. *)
      (* invert H4. *)
      (* eapply IHnextAction in H15; eauto. *)
      

      (* generalize H8; intros NA; apply nextAction_couldBe in NA. *)
      (* dependent destruction protocol; try contradiction; eauto. *)
      admit.

    - 



      
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

  (* Lemma foo : *)
  (*   forall A B t (cmd : user_cmd t) (usrs : honest_users A) (adv : user_data B) cs gks *)
  (*     uid ks qmsgs mycs froms sents n, *)
  (*       (forall lbl bd, ~ step_user lbl (Some uid) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd) bd) *)
  (*       -> forall t__n cmd1 (cmd2 : <<t__n>> -> user_cmd t), *)
  (*       cmd = Bind cmd1 cmd2 *)
  (*       -> forall lbl' bd', *)
  (*         ~ step_user lbl' (Some uid) (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd1) bd'. *)
  (* Admitted. *)

  (* Hint Resolve foo : core. *)

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

