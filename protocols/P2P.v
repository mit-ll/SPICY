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

From KeyManagement Require Import
        MyPrelude
        Maps
        ChMaps
        Messages
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse.

From protocols Require Import
        ModelCheck
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol
        ProtocolFunctions
        SilentStepElimination.

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

Module P2PProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  Notation USR3 := 2.

  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH13 := 0.
    Notation pCH23 := 1.

    Notation pCH1  := 4.
    Notation pCH2  := 5.
    Notation pCH3  := 6.
    Notation pCH__from3  := 7.

    Notation CH13 := (# pCH13).
    Notation CH23 := (# pCH23).

    (* Encryption Channelse *)
    Notation CH1  := (# pCH1).
    Notation CH2  := (# pCH2).
    Notation CH3  := (# pCH3).

    (* Authenticity Channel *)
    Notation CH__from3  := (# pCH__from3).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0
                            #+ (CH13, []) #+ (CH23, [])
                            #+ (CH1, []) #+ (CH2, []) #+ (CH3, [])
                          ).

    Notation PERMS1 := ($0 $+ (pCH13, writer) $+ (pCH1, owner) $+ (pCH2, writer) $+ (pCH3, writer) $+ (pCH__from3, reader) ).
    Notation PERMS2 := ($0 $+ (pCH23, writer) $+ (pCH1, writer) $+ (pCH2, owner) $+ (pCH3, writer) $+ (pCH__from3, reader) ).
    Notation PERMS3 := ($0 $+ (pCH13, reader) $+ (pCH23, reader) $+ (pCH3, owner)).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        mkiUsr USR1 PERMS1
               ( _ <- Send (MsgPair (sharePerm pCH1 writer) (sharePerm pCH2 writer)) CH13 (* please send generate a new key for me and pCH2 to speak over *)
                 ; m <- @Recv Access (pCH1 #& pCH__from3)
                 ; n <- Gen
                 ; _ <- Send (Content n) (getPerm m #& pCH2)
                 ; @Return (Base Nat) n
               )
        ; 

      mkiUsr USR2 PERMS2
             ( p <- @Recv Access (pCH2 #& pCH__from3)
               ; m <- @Recv Nat (getPerm p #& pCH2)
               ; @Return (Base Nat) (extractContent m)
             )
        ; 

      mkiUsr USR3 PERMS3
             ( m <- @Recv (TPair Access Access) CH13
               ; ch <- CreateChannel
               ; _ <- Send (sharePerm ch owner) (getPerm (msgSnd m) #& pCH__from3)
               ; _ <- Send (sharePerm ch owner) (getPerm (msgFst m) #& pCH__from3)
               ; @Return (Base Nat) 1
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
    Import RealWorld.message.

    (* Key management needs to be bootstrapped.  Since all honest users must only send signed
     * messages, we need some way of initially distributing signing keys in order to be able
     * to begin secure communication.  This is analagous in the real world where we need to 
     * have some sort of trust relationship in order to distribute trusted keys.
     * 
     * Here, each user has a public asymmetric signing key.
     *)
    Notation KID__s1 := 0.
    Notation KID__e1 := 1.
    Notation KID__s2 := 2.
    Notation KID__e2 := 3.
    Notation KID__s3 := 4.
    Notation KID__e3 := 5.

    Notation KEYS := [ skey KID__s1 ; ekey KID__e1 
                       ; skey KID__s2 ; ekey KID__e2
                       ; skey KID__s3 ; ekey KID__e3 ].

    Notation KEYS1 := ($0 $+ (KID__s1, true) $+ (KID__e1, true) $+ (KID__s2, false) $+ (KID__e2, false) $+ (KID__s3, false) $+ (KID__e3, false) ).
    Notation KEYS2 := ($0 $+ (KID__s2, true) $+ (KID__e2, true) $+ (KID__s1, false) $+ (KID__e1, false) $+ (KID__s3, false) $+ (KID__e3, false) ).
    Notation KEYS3 := ($0 $+ (KID__s3, true) $+ (KID__e3, true) $+ (KID__s2, false) $+ (KID__e2, false) $+ (KID__s1, false) $+ (KID__e1, false) ).

    Notation real_users :=
      [
        (* User 1 implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      c1 <- SignEncrypt KID__s1 KID__e3 USR3 (MsgPair (Permission (KID__e1, false)) (Permission (KID__e2, false)))
                      ; _ <- Send USR3 c1
                      ; c2 <- @Recv Access (SignedEncrypted KID__s3 KID__e1 true)
                      ; m1 <- Decrypt c2
                      ; n <- Gen
                      ; c3 <- SignEncrypt KID__s1 (getKey m1) USR2 (Content n)
                      ; _ <- Send USR2 c3
                      ; @Return (Base Nat) n
                    )
        ; 

      (* User 2 implementation *)
      MkRUserSpec USR2 KEYS2
                  (
                    c1 <- @Recv Access (SignedEncrypted KID__s3 KID__e2 true)
                    ; m1 <- Decrypt c1
                    ; c2 <- @Recv Nat (SignedEncrypted KID__s3 (getKey m1) true)
                    ; m2 <- Decrypt c2
                    ; @Return (Base Nat) (extractContent m2)
                  )
        ; 

      (* User 2 implementation *)
      MkRUserSpec USR3 KEYS3
                  (
                    c1 <- @Recv (TPair Access Access) (SignedEncrypted KID__s1 KID__e3 true)
                    ; m1 <- Decrypt c1
                    ; ky <- GenerateSymKey Encryption
                    ; c2 <- SignEncrypt KID__s3 (getKey (msgSnd m1)) USR2 (sharePrivKey ky)
                    ; c3 <- SignEncrypt KID__s3 (getKey (msgFst m1)) USR1 (sharePrivKey ky)
                    ; _ <- Send USR2 c2
                    ; _ <- Send USR1 c3
                    ; @Return (Base Nat) 1
                  )
      ].

    (* Here is where we put the implementation universe together.  Like above, it is 
     * unlikely anything will need to change here.
     *)
    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  (* These are here to help the proof automation.  Don't change. *)
  Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl).
  
End P2PProtocol.

Module P2PProtocolSecure <: AutomatedSafeProtocolSS.

  Import P2PProtocol.

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
  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
    : core.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @stepSS t__hon t__adv  |}
      (fun st => safety st /\ alignment st ).
  Proof.
    eapply invariant_weaken.

    - eapply multiStepClosure_ok; simpl.
      (* Calls to gen1 will need to be addded here until the model checking terminates. *)
      autounfold in *.
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
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      
    (* The remaining parts of the proof script shouldn't need to change. *)
    - intros.
      simpl in *.

      sets_invert; split_ex;
        simpl in *; autounfold with core;
          subst; simpl;
            unfold safety, alignment;
            ( split;
            [ solve_honest_actions_safe; clean_map_lookups; eauto 8
            | simpl; split; trivial; intros; rstep; subst; solve_labels_align
            ]).

       Local Ltac merge_perms_helper :=
        repeat match goal with
               | [ |- _ = _ ] => reflexivity
               | [ |- _ $? _ = _ ] => solve_concrete_maps
               end.

      Ltac finish_off1 :=
        match goal with
        | [ H : _ $k++ _ $? ?kid = Some _  |- _ ] =>
          apply merge_perms_split in H
          ; destruct H
        | [ |- _ $k++ _ $? _ = Some _ ] =>
          solve [ erewrite merge_perms_adds_ks1; (swap 2 4; merge_perms_helper) ]
          || solve [ erewrite merge_perms_adds_ks2; (swap 2 4; merge_perms_helper) ]
          || solve [ erewrite merge_perms_chooses_greatest; swap 1 4; eauto; clean_map_lookups]
        | [ H : context [ _ $+ (?k1,_) $? ?k2] |- _ ] =>
          progress (
              repeat (
                  (rewrite add_neq_o in H by solve_simple_ineq)
                  || (rewrite add_eq_o in H by trivial)
                  || (rewrite lookup_empty_none in H)
            ))
        | [ |- _ $? _ = _ ] =>
          progress solve_concrete_maps
        | [ |- context [ _ $k++ _ ] ] =>
          progress solve_concrete_perm_merges
        end.

      all: try solve [ repeat finish_off1].

      Unshelve.

      all: try discriminate.
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
  

End P2PProtocolSecure.