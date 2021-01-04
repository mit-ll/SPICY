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
        ModelCheck.SilentStepElimination.

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
      (fun st => safety st /\ alignment st /\ returns_align st).
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

      sets_invert; split_ex
      ; simpl in *; autounfold with core
      ; subst; simpl
      ; unfold safety, alignment, returns_align
      ; ( repeat simple apply conj
          ; [ solve_honest_actions_safe; clean_map_lookups; eauto 8
            | trivial
            | unfold labels_align; intros; rstep; subst; solve_labels_align
            | try solve [ intros; find_step_or_solve ] 
        ]).

      all: idtac "sets inverted".

      Ltac solve_merges1 :=
        match goal with
        | [ H : Some _ = Some _ |- _ ] => apply some_eq_inv in H; subst
        | [ H : Some _ = None |- _ ] => discriminate H
        | [ H : None = Some _ |- _ ] => discriminate H
        | [ H : ?ks $? ?k = _ |- _ ] =>
          progress (
              repeat (
                  (rewrite add_eq_o in H by trivial)
                  || (rewrite add_neq_o in H by congruence)
                  || (rewrite lookup_empty_none in H by congruence)
                )
            )
        | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] =>
          destruct (k1 ==n k2); subst
        | [ H : _ $k++ _ $? _ = None  |- _ ] =>
          apply merge_perms_no_disappear_perms in H
          ; destruct H
        | [ H : _ $k++ _ $? ?kid = Some _  |- _ ] =>
          apply merge_perms_split in H
          ; destruct H
        | [ |- context [ ?kss1 $k++ ?kss2 $? ?ky ] ] =>
          has_key kss1 ky; has_key kss2 ky
          ; erewrite merge_perms_chooses_greatest
              with (ks1 := kss1) (ks2 := kss2) (k := ky) (k' := ky)
        | [ |- context [ ?kss1 $k++ ?kss2 $? ?ky ] ] =>
          has_key kss1 ky
          ; erewrite merge_perms_adds_ks1
              with (ks1 := kss1) (ks2 := kss2) (k := ky)
          ; try reflexivity
        | [ |- context [ ?kss1 $k++ ?kss2 $? ?ky ] ] =>
          has_key kss2 ky
          ; erewrite merge_perms_adds_ks2
              with (ks1 := kss1) (ks2 := kss2) (k := ky)
          ; try reflexivity
        | [ |- context [ ?kss1 $k++ ?kss2 $? ?ky ] ] =>
          erewrite merge_perms_adds_no_new_perms
            with (ks1 := kss1) (ks2 := kss2) (k := ky)
        | [ |- ?ks $? ?k = _ ] =>
          progress (
              repeat (
                  (rewrite add_eq_o by trivial)
                  || (rewrite add_neq_o by congruence)
                  || (rewrite lookup_empty_none by congruence)
                )
            ) 
        end.

      all : try solve [ repeat solve_merges1; try reflexivity; simpl; trivial ].

      Unshelve.
      all: exact 0  || auto.

      all: idtac "type checking".

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
