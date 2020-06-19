(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
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
     Lists.List.

From KeyManagement
     Require Import
        MyPrelude
        Maps
        Keys
        Messages
        MessageEq
        Tactics
        Simulation
        RealWorld
        AdversarySafety.

From protocols
     Require Import
        ModelCheck.

Require Sets IdealWorld.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Definition adversary_is_lame {B : type} (b : << Base B >>) (adv : user_data B) : Prop :=
    adv.(key_heap) = $0
  /\ adv.(msg_heap) = []
  /\ adv.(c_heap) = []
  /\ lameAdv b adv.

Definition universe_starts_sane {A B : type} (b : << Base B >>) (U : universe A B) : Prop :=
  let honestk := findUserKeys U.(users)
  in  (forall u_id u, U.(users) $? u_id = Some u -> u.(RealWorld.msg_heap) = [])
      /\ ciphers_honestly_signed honestk U.(RealWorld.all_ciphers)
      /\ keys_honest honestk U.(RealWorld.all_keys)
      /\ adversary_is_lame b U.(adversary).

(* 
 * Our definition of a Safe Protocol.  For now, we assume a pretty boring initial
 * adversary state.  The constraints could be relaxed a bit, but it is unclear that
 * there is really any purpose in doing so.
 *)
Module Type SafeProtocol.

  Parameter A B : type.
  Parameter U__i : IdealWorld.universe A.
  Parameter U__r : universe A B.
  Parameter b : << Base B >>.
  Parameter R : simpl_universe A -> IdealWorld.universe A -> Prop.

  Axiom U_good : universe_starts_sane b U__r.

  Axiom R_silent_simulates : simulates_silent_step (lameAdv b) R.
  Axiom R_loud_simulates : simulates_labeled_step (lameAdv b) R.
  Axiom R_honest_actions_safe : honest_actions_safe B R.
  Axiom universe_starts_safe : R (peel_adv U__r) U__i /\ universe_ok U__r /\ adv_universe_ok U__r.

End SafeProtocol.

(*
 * A Functor which lifts any 'SafeProtocol' into the state we really want,
 * namely a universe where there is an adversary executing arbitrary code.
 * This lifting is basically provided by the top level proofs of
 * AdversarySafety.
 *)

Module AdversarySafeProtocol ( Proto : SafeProtocol ).
  Import Proto.

  Hint Resolve
       R_silent_simulates
       R_loud_simulates
       R_honest_actions_safe.

  Lemma proto_lamely_refines :
    refines (lameAdv b) U__r U__i.
  Proof.
    exists R; unfold simulates.
    pose proof universe_starts_safe.
    intuition eauto.
  Qed.

  Hint Resolve proto_lamely_refines.

  Lemma proto_starts_ok : universe_starts_ok U__r.
  Proof.
    pose proof universe_starts_safe.
    pose proof U_good.
    unfold universe_starts_ok; intros.
    unfold universe_ok, adv_universe_ok, universe_starts_sane in *; split_ands.
    intuition eauto.
  Qed.

  Hint Resolve proto_starts_ok.

  Theorem protocol_with_adversary_could_generate_spec :
    forall U__ra advcode acts__r,
      U__ra = add_adversary U__r advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate U__i acts__i
          /\ traceMatches acts__r acts__i.
  Proof.
    intros.
    pose proof U_good as L; unfold universe_starts_sane, adversary_is_lame in L; split_ands.
    eapply refines_could_generate; eauto.
  Qed.
  
End AdversarySafeProtocol.

Section SafeProtocolLemmas.

  Import RealWorld.

  Lemma adversary_is_lame_adv_univ_ok_clauses :
    forall A B (U : universe A B) b,
      universe_starts_sane b U
      -> permission_heap_good U.(all_keys) U.(adversary).(key_heap)
      /\ message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
      /\ adv_cipher_queue_ok U.(all_ciphers) U.(users) U.(adversary).(c_heap)
      /\ adv_message_queue_ok U.(users) U.(all_ciphers) U.(all_keys) U.(adversary).(msg_heap)
      /\ adv_no_honest_keys (findUserKeys U.(users)) U.(adversary).(key_heap).
  Proof.
    unfold universe_starts_sane, adversary_is_lame; intros; split_ands.
    repeat match goal with
           | [ H : _ (adversary _) = _ |- _ ] => rewrite H; clear H
           end.
    repeat (simple apply conj); try solve [ econstructor; clean_map_lookups; eauto ].

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      specialize (H _ _ H2); rewrite H; econstructor.
    - unfold adv_no_honest_keys; intros.
      cases (findUserKeys (users U) $? k_id); eauto.
      destruct b0; eauto.
      right; right; apply conj; eauto.
      clean_map_lookups.

      Unshelve.
      exact (MkCryptoKey 1 Encryption SymKey).
  Qed.

End SafeProtocolLemmas.

Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Inductive step (t__hon t__adv : type) :
  (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> Prop :=
| RealSilent : forall ru ru' iu,
    RealWorld.step_universe ru Silent ru' -> step (ru, iu) (ru', iu)
| BothLoud : forall ru ru' ra ia iu iu' iu'',
    RealWorld.step_universe ru (Action ra) ru'
    -> istepSilent^* iu iu'
    -> IdealWorld.lstep_universe iu' (Action ia) iu''
    -> action_matches ra ru ia iu'
    -> step (ru, iu) (ru', iu'').

Definition lift_fst {A B C} (f : A -> C) : (A * B) -> C :=
  fun p => f (fst p).

Definition safety {t__hon t__adv} (st : RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  let (ru, iu) := st
  in  honest_cmds_safe ru.

Definition labels_align {t__hon t__adv} (st : RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) : Prop :=
  let (ru, iu) := st
  in  forall ru' ra,
      RealWorld.step_universe ru (Action ra) ru'
      -> exists ia iu' iu'',
        (istepSilent)^* iu iu'
        /\ IdealWorld.lstep_universe iu' (Action ia) iu''
        /\ action_matches ra ru ia iu'.

Definition S {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) :=
  {| Initial := {(ru0, iu0)};
     Step    := @step t__hon t__adv |}.
  
Module Type AutomatedSafeProtocol.

  Parameter t__hon : type.
  Parameter t__adv : type.
  Parameter b : << Base t__adv >>.
  Parameter iu0 : IdealWorld.universe t__hon.
  Parameter ru0 : RealWorld.universe t__hon t__adv.

  Notation SYS := (S ru0 iu0).

  Axiom U_good : universe_starts_sane b ru0.
  Axiom universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0.

  Axiom safe_invariant : invariantFor
                           SYS
                           (fun st => safety st
                                 /\ labels_align st ).

End AutomatedSafeProtocol.

Section RealWorldLemmas.

  Import
    RealWorld
    RealWorldNotations.

  Lemma universe_predicates_preservation :
    forall {A B} (U U' : universe A B) lbl,
      universe_ok U
      -> adv_universe_ok U
      -> honest_cmds_safe U
      -> step_universe U lbl U'
      -> universe_ok U'
      /\ adv_universe_ok U'.
  Proof.
    intros * UOK AUOK HCS STEP.
    destruct lbl;
      intuition eauto.

    unfold adv_universe_ok in *; split_ands; 
      eapply honest_labeled_step_univ_ok;
      eauto using honest_cmds_implies_safe_actions.
  Qed.

  Lemma universe_step_preserve_lame_adv' :
    forall A B C lbl u_id bd bd',
      step_user lbl (Some u_id) bd bd'
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd C) ud
          cs cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n',
        usrs $? u_id = Some ud
        -> bd = (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
        -> bd' = (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
        -> adv.(protocol) = adv'.(protocol).
  Proof.
    induction 1; inversion 2; inversion 1;
      intros;
      repeat match goal with
             | [ H : (_,_,_,_,_,_,_,_,_,_,_) = _ |- _ ] => invert H
             end;
      eauto.
  Qed.

  Lemma universe_step_preserves_lame_adv :
    forall {t__h t__a} (U U' : universe t__h t__a) lbl b,
      lameAdv b U.(adversary)
      -> step_universe U lbl U'
      -> lameAdv b U'.(adversary).
  Proof.
    intros.
    invert H0;
      unfold buildUniverse, buildUniverseAdv, build_data_step, lameAdv in *; simpl.

    - destruct U; destruct userData; simpl in *.
      specialize (universe_step_preserve_lame_adv' H2 H1 eq_refl eq_refl); intros; eauto.
      destruct adversary; destruct adv; simpl in *; subst; trivial.
    - rewrite H in *; invert H1.
  Qed.
  
End RealWorldLemmas.

Module ProtocolSimulates (Proto : AutomatedSafeProtocol).
  Import Proto Simulation.

  Lemma safety_inv : invariantFor SYS safety.
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder idtac]. Qed.

  Lemma labels_align_inv : invariantFor SYS labels_align.
  Proof. eapply invariant_weaken; [ apply safe_invariant | firstorder idtac]. Qed.

  Hint Resolve safety_inv labels_align_inv.

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

    destruct x; destruct y; simpl in *.
    apply single_step_stays_lame in H0; eauto.
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

      (* -> step_universe U (Action a__r) U' *)
      (* -> istepSilent^* U__i U__i' *)
      (* -> IdealWorld.lstep_universe U__i' (Action a__i) U__i'' *)
      (* -> action_matches a__r ru' a__i U__i'' *)

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

    generalize (reachable_from_silent_step H3 STEP LAME H H1 H2);
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

    generalize (reachable_from_labeled_step H3 STEP LAME H H1 H2);
      intros; split_ex.

    pose proof labels_align_inv.
    unfold invariantFor, SYS in H5; simpl in H5.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto.
    specialize (H5 _ ARG _ H3 _ _ H0).

    split_ex.
    do 3 eexists; rewrite H4; repeat apply conj; eauto.
    - invert H7; eauto with safe.
      
    - econstructor.

      eapply trcEnd_trc.
      generalize (trc_trcEnd H3); intros.
      econstructor; eauto.
      unfold SYS; simpl.
      econstructor; eauto.
  Qed.

  Lemma honest_cmds_safe_adv_change :
    forall {t1 t2} (U U' : RealWorld.universe t1 t2),
      honest_cmds_safe U
      -> users U = users U'
      -> all_ciphers U = all_ciphers U'
      -> all_keys U = all_keys U'
      -> honest_cmds_safe U'.
  Proof.
    intros * HCS RWU RWC RWK.
    unfold honest_cmds_safe in *
    ; intros
    ; rewrite <- ?RWU, <- ?RWC, <- ?RWK in *
    ; eauto.
  Qed.

  Hint Resolve honest_cmds_safe_adv_change : safe.

  Lemma simsafe : honest_actions_safe t__adv R.
  Proof.
    hnf
    ; intros * REL UOK AUOK
    ; invert REL.

    pose proof safety_inv.
    unfold invariantFor, SYS in H0; simpl in H0.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto.
    specialize (H0 _ ARG _ H3).
    unfold safety in *; eauto with safe.
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
