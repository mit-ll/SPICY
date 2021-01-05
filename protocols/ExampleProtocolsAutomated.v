(*
 * © 2019 Massachusetts Institute of Technology.
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
     Common
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse

     ModelCheck.ModelCheck
     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
.

From protocols Require Import
     ExampleProtocols.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Import SimulationAutomation.

From Frap Require Import Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Module SimplePingProtocolSecure <: AutomatedSafeProtocol.

  Import SignPingSendProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start startAdv.

  Import Gen Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start mkiU real_univ_start mkrU mkrUsr startAdv : core.

  Section Test.
    Section RW.
      Import RealWorld.
      Import RealWorldNotations.
      
      Definition testU :=
        mkrU $0 $0 $0
             (* user A *)
             ( n  <- Gen; Return n )
             (* user B *)
             ( @Return (Base Nat) 1 ) startAdv.

      Definition testU' y :=
        mkrU $0 $0 $0
             (* user A *)
             ( n  <- Return y; Return n )
             (* user B *)
             ( @Return (Base Nat) 1 ) startAdv.

    End RW.

    Section IW.
      Import IdealWorld.
      Import IdealNotations.
      
      Definition testI :=
        mkiU #0 $0 $0
             (* user A *)
             ( n <- Gen; Return n)
             (* user B *)
             ( ret 1 ).
    End IW.

    Lemma sets_test1 :
      { (false,false,false) } \cap { (true,false,false) } = { }.
    Proof.
      sets.
    Qed.

    Lemma sets_test2 :
      { (testU, testI, true) } \cap { (testU, testI, false) } = { }.
    Proof.
      sets.
    Qed.

    (* Lemma sets_test3 : *)
    (*   { ([, testI, true) } \cap { (testU, testI, false) } = { }. *)
    (* Proof. *)
    (*   sets. *)
    (* Qed. *)
  End Test.

  Import RealWorld.
      
  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ alignment st /\ returns_align st).
  Proof.
    eapply invariant_weaken.

    - apply multiStepClosure_ok; simpl.

      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      (* time(gen). *)
      
    - intros.
      simpl in *; repeat simple apply conj.
      
      + sets_invert; unfold safety;
          split_ex; simpl in *; subst;
            autounfold with *;
            try solve [ solve_honest_actions_safe
                        ; clean_map_lookups; eauto 8 ].

      + sets_invert;
          unfold alignment; split_ex; subst; split; trivial; repeat prove_alignment1; eauto 3.

      + sets_invert
        ; autounfold with *
        ; split_ex
        ; simpl in *
        ; subst
        ; unfold returns_align; intros
        ; intros
        ; find_step_or_solve
        .

        Unshelve.
        all: exact 0 || auto.
  Qed.

  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - solve_perm_merges; eauto.
    - econstructor.
    - unfold AdversarySafety.keys_honest, KEYS; rewrite Forall_natmap_forall; intros.
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
    - unfold keys_and_permissions_good, KEYS; solve_simple_maps; intuition eauto.
      solve_simple_maps; eauto.

      rewrite Forall_natmap_forall; intros.
      solve_simple_maps; simpl
      ; unfold permission_heap_good; intros;
        solve_concrete_maps; eauto.

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
        solve_perm_merges;
        solve_concrete_maps;
        solve_simple_maps;
        eauto.

  Qed.


End SimplePingProtocolSecure.

Module SimpleEncProtocolSecure <: AutomatedSafeProtocol.

  Import EncPingSendProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start startAdv.

  Import Gen Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start mkiU real_univ_start mkrU : core.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ alignment st /\ returns_align st).
  Proof.
    eapply invariant_weaken.

    - apply multiStepClosure_ok; simpl.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.

    - intros.
      simpl in *; repeat simple apply conj.
      
      + sets_invert; unfold safety;
          split_ex; simpl in *; subst;
            autounfold with *;
            solve_honest_actions_safe;
            clean_map_lookups; eauto 8.
        
      + sets_invert;
          unfold alignment; split_ex; subst; split; trivial; repeat prove_alignment1; eauto 3.

      + sets_invert
        ; autounfold with *
        ; split_ex
        ; simpl in *
        ; subst
        ; unfold returns_align; intros
        ; intros
        ; find_step_or_solve
        .

        Unshelve.
        all: exact 0 || auto.
  Qed.

  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - solve_perm_merges; eauto.
    - econstructor.
    - unfold AdversarySafety.keys_honest, KEYS; rewrite Forall_natmap_forall; intros.
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
    - unfold keys_and_permissions_good, KEYS; solve_simple_maps; intuition eauto.
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
        solve_perm_merges;
        solve_concrete_maps;
        solve_simple_maps;
        eauto.

  Qed.

End SimpleEncProtocolSecure.
