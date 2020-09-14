(* remember to add key for signing for all valid server users *)
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

Module MyProtocol.

  Notation USR__A := 0.
  Notation USR__B := 1.
  Notation SERVER := 2.

  Section IW.
    Import IdealWorld.

    (* Initial communication channels so each user can talk directly to the other *)
    Notation pCHS := 0.
    Notation pCHA := 1.
    Notation pCHB := 2.
    Notation CHS  := (# pCHS).
    Notation CHA  := (# pCHA).
    Notation CHB  := (# pCHB).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0 #+ (CHS, []) #+ (CHA, []) #+ (CHB, [])).

    Notation PERMS__S := ($0 $+ (pCHS, owner) $+ (pCHA, writer) $+ (pCHB, writer)).
    Notation PERMS__A := ($0 $+ (pCHS, owner) $+ (pCHA, owner)).
    Notation PERMS__B := ($0 $+ (pCHS, owner) $+ (pCHB, owner)).

    Definition Iserver_db := ($0
                            $+ (USR__A, (Permission {| ch_perm := writer ; ch_id := pCHA|}))
                            $+ (USR__B, (Permission {| ch_perm := writer ; ch_id := pCHB|}))).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Definition ideal_users : list (user_id * user Nat) :=
      [
       mkiUsr USR__A PERMS__A
              (
                _ <- Send (MsgPair (Content pCHA) (Content USR__B)) CHS
                ; B <- @Recv Access CHS
                ; m <- Gen
                ; _ <- Send (Content m) (# match B with Permission b => b.(ch_id)  end)
                    (* should this be an intersection? *)
                ; @Return (Base Nat) m
              )
        ;


      mkiUsr USR__B PERMS__B
              (
                m <- @Recv Nat CHB
                ; @Return (Base Nat) (match m with Content m' => m' end)
              )
        ;
      (* User 2 Specification *)
      (* can I repeat this or does it need to finish? *)
      mkiUsr SERVER PERMS__S
              (
                m__r <- @Recv (TPair Nat Nat) CHS
                ; _ <- match Iserver_db $? (extractContent (msgSnd m__r)) with 
                      | Some p => Send p (# (extractContent (msgFst m__r)))
                      | _ => @Return (Base Unit) tt
                      end
                ; @Return (Base Nat) 1
              )
      ].

    (* This is where the entire specification universe gets assembled.  It is unlikely anything *)
    (*  * will need to change here. *)
    Definition ideal_univ_start := mkiU empty_chs ideal_users.

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
    Notation KID__A := 0.
    Notation KID__B := 1.
    Notation KID__S := 2.


    Notation KEYS := [ (MkCryptoKey KID__A Encryption AsymKey) ;
                         (MkCryptoKey KID__B Encryption AsymKey) ;
                         (MkCryptoKey KID__S Signing SymKey) ].

    Notation KEYS__A := ($0 $+ (KID__A, true) $+ (KID__S, true)).
    Notation KEYS__B := ($0 $+ (KID__B, true) $+ (KID__S, true)).
    Notation KEYS__S := ($0 $+ (KID__S, true) $+ (KID__A, false) $+ (KID__B, false)).

    Notation Rserver_db := ($0 $+ (USR__A, KID__A) $+ (USR__B, KID__B)).

    Definition real_users : list (@RUserSpec Nat) :=
    (* Notation real_users := *)
      [
        (* User 1 implementation *)
        MkRUserSpec USR__A KEYS__A
                    (
                      m1 <- Sign KID__A SERVER (MsgPair (message.Content USR__A) (message.Content USR__B))
                      ; _ <- Send SERVER m1
                      ; c <- @Recv (Access) (Signed KID__S true)
                      ; m2 <- Verify KID__S c
                      ; k <- @Return (Base Nat) (fst (extractPermission (snd m2)))
                      ; g <- Gen
                      ; m3 <- SignEncrypt KID__A k USR__B (message.Content g)
                      ; _ <- Send USR__B m3
                      ; @Return (Base Nat) g
                    )
        ; 
(* User 2 implementation *)
      MkRUserSpec USR__B KEYS__B
                  (
                    c <- @Recv (Nat) (SignedEncrypted KID__S KID__B true)
                    ; m <- Decrypt c
                    ; @Return (Base Nat) (extractContent m)
                  ) 
        ; 
(* User 2 implementation *)
      MkRUserSpec SERVER KEYS__S
                  (
                    p__r <- @Recv (TPair Nat Nat) (Signed KID__S true)
                    ; m__r <- Verify KID__S p__r
                    ; m__s <- match Rserver_db $? (extractContent (msgSnd (snd m__r))) with 
                          | Some p => Sign KID__S (extractContent (msgFst (snd m__r))) (message.Permission (p, false))
                          | _ => Sign KID__S (extractContent (msgFst (snd m__r))) (message.Permission (KID__S, false))
                          end
                    ; _ <- Send (extractContent (msgFst (snd m__r))) m__s

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
  
End MyProtocol.

Module MyProtocolSecure <: AutomatedSafeProtocol.

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
  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
       real_users
    : core.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ alignment st ).
  Proof.
    eapply invariant_weaken.

    - eapply multiStepClosure_ok; simpl.
      (* Calls to gen1 will need to be addded here until the model checking terminates. *)
      gen1.
      gen1.
      
    (* The remaining parts of the proof script shouldn't need to change. *)
    - intros.
      simpl in *.

      sets_invert; split_ex;
        simpl in *; autounfold with core.
          subst; simpl;
            unfold safety, labels_align;
            ( split;
            [ solve_honest_actions_safe; clean_map_lookups; eauto 8
            | intros; rstep; subst; solve_labels_align
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
      cases (USR1 ==n k); cases (USR2 ==n k);
        subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold honest_nonces_ok; intros.
      unfold honest_nonce_tracking_ok.

      destruct (u_id ==n USR1); destruct (u_id ==n USR2);
        destruct (rec_u_id ==n USR1); destruct (rec_u_id ==n USR2);
          subst; try contradiction; try discriminate; clean_map_lookups; simpl;
            repeat (apply conj); intros; clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      destruct (u_id ==n USR1);
        destruct (u_id ==n USR2);
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
  

End MyProtocolSecure.
