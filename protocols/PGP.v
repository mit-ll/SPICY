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
     List.

Require Import
        MyPrelude
        Maps
        ChMaps
        Messages
        ModelCheck
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol
        ProtocolFunctions.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module PGPProtocol.

  (* User ids *)
  Notation USR1 := 0.
  Notation USR2 := 1.

  Section IW.
    Import IdealWorld.

    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).

    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, [])).

    Notation PERMS1 := ($0 $+ (pCH12, owner) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, writer)).

    Definition ideal_users :=
      [
        (mkiUsr USR1 PERMS1 
                ( m1 <- @Recv Access CH21
                  ; m2 <- @Recv Nat (getPerm m1 #& pCH21)
                  ; @Return (Base Nat) (extractContent m2)
        )) ;
      (mkiUsr USR2 PERMS2
              ( chid <- CreateChannel
                ; _ <- Send (sharePerm chid owner) CH21
                ; n <- Gen
                ; _ <- Send (Content n) (chid #& pCH21)
                ; @Return (Base Nat) n
      ))
      ].

    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.
    Import RealWorld.message.

    Notation KID1 := 0.
    Notation KID2 := 1.
    Notation KID3 := 2.

    Notation KEYS := [ skey KID1 ; skey KID2 ; ekey KID3 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, false) $+ (KID3, true)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, true) $+ (KID3, false)).

    Definition real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( c1 <- @Recv Access (SignedEncrypted KID2 KID3 true)
                      ; m1 <- Decrypt c1
                      ; c2 <- @Recv Nat (SignedEncrypted KID2 (getKey m1) true)
                      ; m2 <- Decrypt c2
                      ; @Return (Base Nat) (extractContent m2)) ;

      MkRUserSpec USR2 KEYS2
                  ( kp <- GenerateSymKey Encryption
                    ; c1 <- SignEncrypt KID2 KID3 USR1 (sharePrivKey kp)
                    ; _  <- Send USR1 c1
                    ; n  <- Gen
                    ; c2 <- SignEncrypt KID2 (fst kp) USR1 (Content n)
                    ; _  <- Send USR1 c2
                    ; @Return (Base Nat) n )
      ].

    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl).
  
End PGPProtocol.

Module PGPProtocolSecure <: AutomatedSafeProtocol.

  Import PGPProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start.

  Import Gen Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.

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

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ alignment st ).
  Proof.
    eapply invariant_weaken.

    - eapply multiStepClosure_ok; simpl.
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
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      
    - intros.
      simpl in *.

      sets_invert; split_ex;
        simpl in *; autounfold with core;
          subst; simpl;
            unfold safety, alignment;
            ( split;
            [ try solve [ solve_honest_actions_safe; clean_map_lookups; eauto 8 ]
            | try solve [ simpl; split; trivial; intros; rstep; subst; solve_labels_align ]
            ]).
      
      Unshelve.
      all: auto.

  Qed.

  (* Show Ltac Profile. *)
  (* Show Ltac Profile "churn2". *)
  
  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - solve_perm_merges; eauto.
    - econstructor.
    - unfold AdversarySafety.keys_honest; rewrite Forall_natmap_forall; intros.
      econstructor; unfold mkrUsr; simpl.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto.
      solve_perm_merges.
    - unfold lameAdv; simpl; eauto.
  Qed.

  Lemma univ_ok_start : universe_ok ru0.
  Proof.
    autounfold; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start : adv_universe_ok ru0.
  Proof.
    autounfold; unfold adv_universe_ok; eauto.
    unfold keys_and_permissions_good.
    pose proof (adversary_is_lame_adv_univ_ok_clauses U_good).

    intuition eauto;
      simpl in *.

    - solve_simple_maps; eauto.
    - rewrite Forall_natmap_forall; intros.
      solve_simple_maps; simpl;
        unfold permission_heap_good; intros;
          solve_simple_maps; eauto.

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
  
  Lemma universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0.
  Proof.
    repeat (simple apply conj);
      eauto using univ_ok_start, adv_univ_ok_start.
  Qed.
  

End PGPProtocolSecure.

(*
 * 1) make protocols  518.64s user 0.45s system 99% cpu 8:39.13 total  ~ 6.2GB
 * 2) add cleanup of chmaps to close:
 *    make protocols  414.45s user 0.43s system 99% cpu 6:54.90 total  ~ 5.6GB
 *
 *
 *)
