(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     Keys
     Automation
     Tactics
     Simulation
     SyntacticallySafe
     AdversaryUniverse

     ModelCheck.Commutation
     ModelCheck.ModelCheck
     ModelCheck.ProtocolFunctions
     ModelCheck.SilentStepElimination
     ModelCheck.SteppingTactics
     ModelCheck.InvariantSearch
     ModelCheck.UniverseInversionLemmas
.

From protocols Require Import
     SecureDNS.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

Set Implicit Arguments.

Open Scope protocol_scope.

Module SecureDNSProtocolSecure <: AutomatedSafeProtocolSS.

  Import SecureDNSProtocol.

  (* Some things may need to change here.  t__hon is where we place the 
   * type that the protocol computes.  It is set to Nat now, because we
   * return a natual number.
   *)
  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b    := tt.

  (* These two variables hook up the starting points for both specification and
   * implementation universes.  If you followed the template above, this shouldn't
   * need to be changed.
   *)
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start.

  Import Gen Tacs.

  (* These are here to help the proof automation.  Don't change. *)
  #[export] Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  #[export] Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
    : core.

  Lemma realServerbrt_bodybrt :
    forall t n (cmd : RealWorld.user_cmd t),
      boundRunningTime cmd n
      -> forall (tv : RealWorld.denote t) n__iter,
        exists n__server, boundRunningTime (realServer n__iter tv cmd) n__server.
  Proof.
    induction n__iter; intros.
    - rewrite realserver_done.
      eexists; find_runtime.
    - erewrite unroll_realserver_step; eauto.
      split_ex.
      eexists; find_runtime.
      
      Unshelve.
      exact 0.
  Qed.

  Lemma finitelyRuns : exists n, runningTimeMeasure ru0 n.
  Proof.
    autounfold; simpl.
    repeat 
      match goal with
      | [ |- context [realServer _ _ ?cmd] ] =>
        match goal with
        | [ H : exists _, boundRunningTime cmd _ |- _ ] => fail 1
        | _ => let BRT := fresh "BRT" in
              assert (exists n, boundRunningTime cmd n) as BRT by (eexists; simpl; find_runtime)
        end
      end
    ; split_ex
    ; repeat
        match goal with
        | [ H : boundRunningTime ?cmd _ |- context [ realServer ?n ?dv ?cmd ] ] =>
          pose proof (realServerbrt_bodybrt H dv n); clear H
        end
    ; split_ex.
    
    eexists; econstructor; simpl; find_runtime; eauto.

    Unshelve.
    all: exact 0.
  Qed.

  Lemma realServerss_bodyss :
    forall t uid uids ctx (cmd : RealWorld.user_cmd (RealWorld.Base t)) cs (usrs : RealWorld.honest_users t) sty,
      syntactically_safe uid uids ctx cmd sty
      -> typingcontext_sound ctx usrs cs uid
      -> forall tv n,
          exists sty__s ctx__s,
            List.Forall (fun styp => List.In styp ctx__s) ctx
            /\ syntactically_safe uid uids ctx__s (realServer n tv cmd) sty__s
            /\ typingcontext_sound ctx__s usrs cs uid.
  Proof.
    induct n; intros.
    - rewrite realserver_done.
      (do 2 eexists); eauto.
    - erewrite unroll_realserver_step; eauto.
      split_ex.
      (do 2 eexists); repeat simple apply conj; eauto.
      econstructor; intros; eauto using syntactically_safe_add_ctx.
  Qed.

  Lemma typechecks : syntactically_safe_U ru0.
  Proof.
    unfold syntactically_safe_U; intros.
    autounfold
    ; subst
    ; simpl in *.

    unfold compute_ids; simpl.
    
    focus_user; simpl
    ; try solve [ do 2 eexists; split
                  ; [ unshelve (repeat typechecks1)
                      ; match goal with
                        | [ |- bool ] => exact true
                        | [ |- list safe_typ ] => exact []
                        end
                    | repeat verify_context_soundness ] ].

    match goal with
    | [ |- exists _ _, syntactically_safe ?uid ?uids _ (realServer ?n ?tv ?cmd) _
               /\ typingcontext_sound _ ?usrs ?cs ?uid ] =>
      assert (exists sty ctx, syntactically_safe uid uids ctx cmd sty
                         /\ typingcontext_sound ctx usrs cs uid)
    end.

    do 2 eexists; split
    ; [ unshelve (repeat typechecks1)
        ; match goal with
          | [ |- bool ] => exact true
          | [ |- list safe_typ ] => exact []
          end
      | repeat verify_context_soundness ].

    split_ex.

    match goal with
    | [ SS : syntactically_safe _ _ _ ?cmd _, TCS : typingcontext_sound _ _ _ _
        |- context [ realServer ?n ?tv ?cmd ] 
      ] =>
      pose proof ( realServerss_bodyss SS TCS tv n)
      ; clear SS TCS
      ; split_ex
    end
    ; (do 2 eexists); split; eauto.

    Unshelve.
    all: exact true.
  Qed.
    
  Lemma summarizable : exists summaries, summarize_univ ru0 summaries.
  Proof.
    autounfold; unfold summarize_univ; simpl; intros.
    unshelve (
        eexists; intros; focus_user; simpl
        ; (exists useless_summary; split; [ build_summary |]; eauto using useless_summary_summarizes)
      ) ; exact $0.
  Qed.
    
  Lemma lameness : @lameAdv t__adv b (RealWorld.adversary ru0).
  Proof.
    unfold lameAdv; autounfold; simpl; eauto.
  Qed.

  Set Ltac Profiling.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @stepSS t__hon t__adv  |}
      (@noresends_inv t__hon t__adv).
  Proof.
    unfold invariantFor
    ; unfold Initial, Step
    ; intros
    ; simpl in *
    ; split_ors
    ; try contradiction
    ; subst.

    autounfold in H0
    ; unfold fold_left, fst, snd in *.

    time (
        repeat transition_system_step
      ).

    Unshelve.
    all: exact 0 || auto.
  Qed.

  Show Ltac Profile.
  (* Show Ltac Profile "churn2". *)
  
  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - focus_user; auto.
    - econstructor.
    - unfold AdversarySafety.keys_honest; rewrite Forall_natmap_forall; intros.
      unfold mkrUsr; simpl.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; simpl in *; eauto.
    - unfold lameAdv; simpl; eauto.
  Qed.

  Lemma universe_starts_safe : universe_ok ru0.
  Proof.
    pose proof (adversary_is_lame_adv_univ_ok_clauses U_good).
    
    unfold universe_ok
    ; autounfold
    ; simpl
    ; intuition eauto
    .

    - econstructor; eauto.
    - unfold keys_and_permissions_good; solve_simple_maps; intuition eauto.
      solve_simple_maps; eauto.

      rewrite Forall_natmap_forall; intros.

      solve_simple_maps; simpl
      ; unfold permission_heap_good; intros;
        solve_simple_maps; solve_concrete_maps; eauto.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      focus_user
      ; simpl in *; econstructor; eauto.

    - unfold honest_nonces_ok, honest_user_nonces_ok, honest_nonces_ok
      ; repeat simple apply conj
      ; intros
      ; clean_map_lookups
      ; intros
      ; focus_user
      ; try contradiction; try discriminate; simpl;
        repeat (apply conj); intros; clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      focus_user;
        subst;
        simpl in *;
        clean_map_lookups;
        unfold mkrUsr; simpl; 
          rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty;
          eauto;
          simpl in *;
          solve_concrete_perm_merges;
          solve_concrete_maps;
          solve_simple_maps;
          eauto.
  Qed.

End SecureDNSProtocolSecure.
