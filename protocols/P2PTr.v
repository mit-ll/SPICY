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

     ModelCheck.ModelCheck
     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
     ModelCheck.SilentStepElimination
     ModelCheck.InvariantSearch
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

From Frap Require Import Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module P2PProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  Notation SRV  := 2.

  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH1 := 0.
    Notation pCH2 := 1.

    Notation pCH__s1 := 2.
    Notation pCH1s := 3.
    Notation pCH__s2 := 4.
    Notation pCH2s := 5.

    Notation CH1  := (# pCH1).
    Notation CH2  := (# pCH2).
    Notation CH__s1 := (# pCH__s1).
    Notation CH1s := (# pCH1s).
    Notation CH__s2 := (# pCH__s2).
    Notation CH2s := (# pCH2s).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs :=
      (#0
        #+ (CH1, []) #+ (CH2, []) #+ (CH__s1, []) #+ (CH__s2, []) #+ (CH1s, []) #+ (CH2s, [])
      ).

    Notation PERMS1 := ($0 $+ (pCH1, owner) $+ (pCH__s1, reader) $+ (pCH1s, writer)).
    Notation PERMS2 := ($0 $+ (pCH2, owner) $+ (pCH__s2, reader) $+ (pCH2s, writer)).
    Notation PERMS__s := ($0 $+ (pCH1, reader) $+ (pCH2, reader)
                         $+ (pCH__s1, writer) $+ (pCH1s, reader)
                         $+ (pCH__s2, writer) $+ (pCH2s, reader)
                       ).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        mkiUsr USR1 PERMS1
               ( _ <- Send (Content USR2) CH1s
                 ; m <- @Recv (TPair Access Access) CH__s1
                 ; n <- Gen
                 ; let ch := getPerm (msgSnd m)
                   in _ <- Send (Content n) (pCH1 #& ch)
                 ; @Return (Base Nat) n
               )
        ; 

      mkiUsr USR2 PERMS2
               ( _ <- Send (Content USR1) CH2s
                 ; m <- @Recv (TPair Access Access) CH__s2
                 ; n <- Gen
                 ; let ch := getPerm (msgSnd m)
                   in  m <- @Recv Nat (pCH1 #& ch)
                 ; @Return (Base Nat) (extractContent m)
               )
        ; 

      mkiUsr SRV PERMS__s
             ( m1 <- @Recv Nat CH1s
               ; m2 <- @Recv Nat CH2s
               ; ch <- CreateChannel
               ; _ <- Send (MsgPair (sharePerm pCH1 reader) (sharePerm ch owner)) CH__s2
               ; _ <- Send (MsgPair (sharePerm pCH2 reader) (sharePerm ch owner)) CH__s1
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
    Notation KID__ss := 4.
    Notation KID__es := 5.

    Notation KEYS := [ skey KID__s1 ; ekey KID__e1
                       ; skey KID__s2 ; ekey KID__e2
                       ; skey KID__ss ; ekey KID__es ].

    Notation KEYS1 := ($0 $+ (KID__s1, true) $+ (KID__e1, true) $+ (KID__ss, false) $+ (KID__es, false)).
    Notation KEYS2 := ($0 $+ (KID__s2, true) $+ (KID__e2, true) $+ (KID__ss, false) $+ (KID__es, false)).
    Notation KEYS__s := ($0
                        $+ (KID__s1, false) $+ (KID__e1, false)
                        $+ (KID__s2, false) $+ (KID__e2, false)
                        $+ (KID__ss, true) $+ (KID__es, true)).

    Notation real_users :=
      [
        (* User 1 implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      c1 <- SignEncrypt KID__s1 KID__es SRV (Content USR2)
                      ; _ <- Send SRV c1
                      ; c2 <- @Recv (TPair Access Access) (SignedEncrypted KID__ss KID__e1 true)
                      ; m1 <- Decrypt c2
                      ; n <- Gen
                      ; c3 <- SignEncrypt KID__s1 (getKey (msgSnd m1)) USR2 (Content n)
                      ; _ <- Send USR2 c3
                      ; @Return (Base Nat) n
                    )
        ; 

      (* User 2 implementation *)
      MkRUserSpec USR2 KEYS2
                    (
                      c1 <- SignEncrypt KID__s2 KID__es SRV (Content USR1)
                      ; _ <- Send SRV c1
                      ; c2 <- @Recv (TPair Access Access) (SignedEncrypted KID__ss KID__e2 true)
                      ; m1 <- Decrypt c2
                      ; c3 <- @Recv Nat (SignedEncrypted (getKey (msgFst m1)) (getKey (msgSnd m1)) true)
                      ; m2 <- Decrypt c3
                      ; @Return (Base Nat) (extractContent m2)
                    )
        ; 

      (* Server implementation *)
      MkRUserSpec SRV KEYS__s
                  (
                    c1 <- @Recv Nat (SignedEncrypted KID__s1 KID__es true)
                    ; c2 <- @Recv Nat (SignedEncrypted KID__s2 KID__es true)
                    ; m1 <- Decrypt c1
                    ; m2 <- Decrypt c2
                    ; ky <- GenerateKey SymKey Encryption
                    ; c3 <- SignEncrypt KID__ss KID__e1 USR1 (MsgPair (Permission (KID__s2, false)) (sharePrivKey ky))
                    ; c4 <- SignEncrypt KID__ss KID__e2 USR2 (MsgPair (Permission (KID__s1, false)) (sharePrivKey ky))
                    ; _ <- Send USR2 c4
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
  #[export] Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  #[export] Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl) : core.
  
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
    - finish_invariant.
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
    - solve_perm_merges; eauto.
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
          solve_perm_merges;
          solve_concrete_maps;
          solve_simple_maps;
          eauto.
  Qed.

End P2PProtocolSecure.
