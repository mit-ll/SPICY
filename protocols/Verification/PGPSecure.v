(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Lia.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse

     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ModelCheck
     ModelCheck.ProtocolFunctions
     ModelCheck.SilentStepElimination
     ModelCheck.InvariantSearch
.

From protocols Require Import
     PGP.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

Set Implicit Arguments.

Open Scope protocol_scope.

Module PGPProtocolSecure <: AutomatedSafeProtocolSS.

  Import PGPProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start.

  Import Gen Tacs SetLemmas.

  #[export] Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.

  Lemma next_key_natmap_exists :
    forall {V} (m : NatMap.t V),
    exists k, m $? k = None.
  Proof.
    intros.
    exists (next_key m); eauto using Maps.next_key_not_in.
  Qed.

  Lemma next_key_chmap_exists :
    forall {V} (m : ChMap.t V),
    exists k, m #? (# k) = None.
  Proof.
    intros.
    exists (next_key_nat m); eauto using next_key_not_in.
  Qed.

  Set Ltac Profiling.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @stepSS t__hon t__adv  |}
      (@safety_inv t__hon t__adv).
      (* (fun st => safety st /\ alignment st /\ returns_align st). *)
  Proof.
    unfold invariantFor
    ; unfold Initial, Step
    ; intros
    ; sets_invert.

    autounfold in H0
    ; unfold fold_left, fst, snd in *.
    unfold real_users, ideal_users, mkrUsr, userProto, userKeys, userId, mkiUsr in *; uf; rwuf.

    (* Ltac invSS1 := *)
    (*   discriminate *)
    (*   || match goal with *)
    (*     | [ STEP : (stepSS (t__adv := _)) ^* (?U,_,_) _ *)
    (*       , IRS : indexedRealStep ?uid Silent ?U ?RU *)
    (*       , P : (forall _ _, _ > ?uid -> _) *)
    (*         |- _ ] => *)

    (*       pose proof (ssteps_inv_silent' STEP eq_refl IRS P) *)
    (*       ; clear STEP IRS P RU *)
    (*       ; split_ex *)

    (*     | [ STEP : (stepSS (t__adv := _)) ^* (?ru,?iu,?b) _ *)
    (*       , P : (forall _ _, ~ indexedRealStep _ Silent _  _) *)
    (*         |- _ ] => *)

    (*       progress ( unfold not in P ) *)

    (*     | [ STEP : (stepSS (t__adv := _)) ^* (?ru,?iu,?b) (_,_,_) *)
    (*       , P : (forall _ _, indexedRealStep _ Silent _ _ -> False) *)
    (*         |- _ ] => *)

    (*       concrete ru *)
    (*       ; match goal with *)
    (*         | [ LA : labels_align (?ru,?iu,?b) |- _ ] => *)
    (*           let PROOF := fresh "PROOF" in *)
    (*           pose proof (ssteps_inv_labeled P STEP LA eq_refl ) as PROOF *)
    (*           ; clear STEP P LA *)
    (*           ; destruct PROOF *)
    (*           ; repeat cleanup1 *)
    (*           (* ; repeat cleanup1 *) *)
    (*           ; split_ex *)
    (*           ; subst *)

    (*         | _ => *)
    (*           idtac "proving alignment 4" *)
    (*           ; assert (labels_align (ru,iu,b)) by ((repeat prove_alignment1); eauto) *)
    (*         end *)
    (*     | [ STEP : (stepSS (t__adv := _)) ^* ?st ?st' *)
    (*       , P : (forall _ _, indexedRealStep _ Silent _ _ -> False) *)
    (*         |- _ ] => *)

    (*       match st with *)
    (*       | (_,_,_) => idtac *)
    (*       | _ => destruct st as [[?ru ?iu] ?b] *)
    (*       end *)
    (*       ; match st' with *)
    (*         | (_,_,_) => idtac *)
    (*         | _ => destruct st' as [[?ru' ?iu'] ?b'] *)
    (*         end *)

    (*     | [ H : (stepSS (t__adv := _)) ^* (?U,_,_) _ |- _ ] => *)
    (*       match U with *)
    (*       | {| RealWorld.users := ?usrs |} => *)
    (*         find_silent U usrs *)
    (*       end *)

    (*     | [ IMS : indexedModelStep ?uid (?U,_,_) _ *)
    (*               , IRS : indexedRealStep ?uid _ ?U _ *)
    (*         |- _ ] => clear IMS *)

    (*     | [ H : action_matches _ _ _ _ |- _] => invert H *)
    (*     | [ H : forall _ _ _, _ -> _ -> _ -> _ <-> _ |- _ ] => clear H *)
    (*     | [ H : forall _ _ _ _, _ -> _ -> _ -> _ -> _ <-> _ |- _ ] => clear H *)
    (*     | [ H : (forall _ _ _, indexedRealStep _ _ ?ru _ -> *)
    (*                       exists _ _ _, (indexedIdealStep _ _) ^* ?iu _ /\ _) |- _ ] => *)
    (*       clear H *)

    (*     | [H : indexedRealStep _ _ _ _ |- _ ] => *)
    (*       invert H *)
    (*     | [H : RealWorld.step_universe _ ?u _ _ |- _] => *)
    (*       concrete u; chu *)
    (*     | [H : RealWorld.step_user _ None _ _ |- _] => *)
    (*       invert H *)
    (*     | [H : RealWorld.step_user _ _ ?u _ |- _] => *)
    (*       concrete u; chu *)

    (*     | [ H : indexedIdealStep _ _ _ _ |- _ ] => istep (* run _after_ real steps *) *)
                                                   
    (*     (* | [ H : _ ^* (?ru,?iu,_) _ |- _ ] => concrete ru; concrete iu; invert H *) *)

    (*     | [ |- safety_inv (?ru,_,_) ] => *)
    (*       concrete ru; solve [ finish_invariant ] *)

    (*     | [ H : _ \/ _ |- _ ] => destruct H; split_ex; subst *)
    (*     end. *)

    (* Ltac do_trsys_step := invSS1; (repeat cleanup1). *)

    (* Ltac transition_system_step := *)
    (*   rwuf; do_trsys_step; canonicalize context. *)

    (* repeat transition_system_step. *)

    Ltac prove_gt_pred :=
      intros
      ; simpl in *
      ; repeat 
          match goal with
          | [ H : context [ _ $+ (_,_) $- _ ] |- _ ] =>
            repeat (
                (rewrite map_add_remove_neq in H by congruence)
                || (rewrite map_add_remove_eq in H by trivial)
                || (rewrite remove_empty in H)
              )
          | [ H : _ $+ (?uid,_) $? ?uid' = Some _ |- _ ] =>
            destruct (uid ==n uid'); subst; clean_map_lookups; try lia
          | [ H : NoSilent ?uid ?U |- ~ indexedRealStep ?uid _ ?U _ ] =>
            idtac "admitting " uid; admit (* unfold not; intros; rstep *)
          end.

    Ltac assert_gt_pred U uid :=
      let P := fresh "P"
      in assert (forall uid' ud' U', U.(RealWorld.users) $? uid' = Some ud'
                                -> uid' > uid
                                -> ~ indexedRealStep uid' Silent U U') as P by prove_gt_pred
         ; pose proof (upper_users_cant_step_rewrite P); clear P
    .

    Ltac assert_no_silents U :=
      let P := fresh "P"
      in assert (forall uid U', ~ indexedRealStep uid Silent U U') as P by admit
    .

    Ltac getNextAction p :=
      match p with
      | RealWorld.Bind ?n _ => getNextAction n
      | ?n                  => idtac n
      end.

    Ltac assertSilentStatus uid U p :=
      match p with
      | RealWorld.Bind ?n _ => assertSilentStatus uid U n
      | RealWorld.Send _ _  => assert (NoSilent uid U) by (econstructor; unfold not; intros; rstep)
      | RealWorld.Recv _    => assert (NoSilent uid U) by (econstructor; unfold not; intros; rstep)
      | ?n                  => assert (exists U', indexedRealStep uid Silent U U') by solve_indexedRealStep
      end.

    Ltac find_silent U us :=
      let MAX := fresh "MEQ"
      in  remember (O.max_elt us) eqn:MAX
          ; unfold O.max_elt in MAX
          ; simpl in MAX
          ; match type of MAX with
            | _ = Some (?uid,?u) =>
              idtac "Processing uid: " uid;
              let p := (eval simpl in u.(RealWorld.protocol))
              in 
                 assertSilentStatus uid U p
                 ; match goal with
                   | [ H : NoSilent uid _ |- _ ] => idtac "found " uid; find_silent U (us $- uid)
                   | _ => idtac "asserting gt " uid; assert_gt_pred U uid
                   end
                 ; idtac "here" (* assert_no_silents U *)
              (* ( ( assert (exists U', indexedRealStep uid Silent U U') by solve_indexedRealStep *)
              (*     ; assert_gt_pred U uid) *)
              (*   || find_silent U (us $- uid) *)
                   (* ) || assert_no_silents U *)
            | _ => idtac "weird"; assert_no_silents U
            end
          ; subst; split_ex
    .

    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.

    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step.
    transition_system_step. 

    match goal with
    | [ H : (stepSS (t__adv := _)) ^* (?U,_,_) _ |- _ ] =>
      match U with
      | {| RealWorld.users := ?usrs |} =>
        find_silent U usrs
      end
    end.

    match goal with
    | [ H : NoSilent _ ?U |- _ ] =>
      assert (forall uid U', ~ indexedRealStep uid Silent U U')
    end.

    intros.

    intros; prove_gt_pred.
    unfold not; intros.
    invert H3.

    transition_system_step.
    transition_system_step.
    transition_system_step.

    
      time (
          repeat transition_system_step
        ).

      Unshelve.
      all: eauto.
  Qed.

  Show Ltac Profile.
      
  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - focus_user; auto.
    - econstructor.
    - unfold AdversarySafety.keys_honest; rewrite Forall_natmap_forall; intros.
      unfold mkrUsr; simpl.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto.
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

End PGPProtocolSecure.
