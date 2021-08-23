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
     AdversaryUniverse

     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ModelCheck
     ModelCheck.ProtocolFunctions
     ModelCheck.SilentStepElimination
     ModelCheck.InvariantSearch
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

From Frap Require Import Sets.

Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module MyProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.

  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, [])).

    Notation PERMS1 := ($0 $+ (pCH12, owner) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, owner)).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        (* User 1 Specification *)
        mkiUsr USR1 PERMS1
                (
                  ret 1
                )
        ;

      (* User 2 Specification *)
      mkiUsr USR2 PERMS2
              (
                ret 1
              )
      ].

    (* This is where the entire specification universe gets assembled.  It is unlikely anything
     * will need to change here.
     *)
    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.

    (* Key management needs to be bootstrapped.  Since all honest users must only send signed
     * messages, we need some way of initially distributing signing keys in order to be able
     * to begin secure communication.  This is analagous in the real world where we need to 
     * have some sort of trust relationship in order to distribute trusted keys.
     * 
     * Here, each user has a public asymmetric signing key.
     *)
    Notation KID1 := 0.
    Notation KID2 := 1.

    Notation KEYS := [ skey KID1 ; skey KID2 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, false)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, true)).

    Notation real_users :=
      [
        (* User 1 implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      ret 1
                    )
        ; 

      (* User 2 implementation *)
      MkRUserSpec USR2 KEYS2
                  (
                    ret 1
                  ) 
      ].

    (* Here is where we put the implementation universe together.  Like above, it is 
     * unlikely anything will need to change here.
     *)
    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  (* These are here to help the proof automation.  Don't change. *)
  #[export] Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  #[export] Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl).
  
End MyProtocol.

Module MyProtocolSecure <: AutomatedSafeProtocolSS.

  Import MyProtocol.

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

  Import Gen Tacs SetLemmas.

  (* These are here to help the proof automation.  Don't change. *)
  #[export] Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  #[export] Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
    : core.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @stepSS t__hon t__adv  |}
      (@safety_inv t__hon t__adv).
  Proof.
    unfold invariantFor
    ; unfold Initial, Step
    ; intros
    ; sets_invert.

    invert H0.
    - autounfold; finish_invariant.
    - autounfold in H
      ; unfold fold_left, fst, snd in *.

      time (
          repeat transition_system_step
        ).

      Unshelve.
      all: exact 0  || auto.
  Qed.
  
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
          solve_concrete_perm_Merges;
          solve_concrete_maps;
          solve_simple_maps;
          eauto.
  Qed.

End MyProtocolSecure.
