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

Module SecureDNSProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  Notation USR3 := 2.

  Parameter names : NatMap.t nat.
  
  (* Notation names := *)
  (*   ( $0 $+ (0,10) *)
  (*        $+ (1,11) *)
  (*        $+ (2,12) *)
  (*        $+ (3,13) *)
  (*        $+ (4,14) *)
  (*   ). *)

  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation pCH23 := 2.
    Notation pCH32 := 3.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).
    Notation CH23  := (# pCH23).
    Notation CH32  := (# pCH32).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, []) #+ (CH23, []) #+ (CH32, [])).

    Notation PERMS1 := ($0 $+ (pCH12, writer) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, writer) $+ (pCH23, writer) $+ (pCH32, reader)).
    Notation PERMS3 := ($0 $+ (pCH23, reader) $+ (pCH32, writer)).

    Fixpoint idealServer (n : nat) {t} (r : << t >>) (c : cmd t) : cmd t :=
      match n with
      | 0   => @Return t r
      | S i => (r' <- c ; idealServer i r' c)
      end.

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        (* Authorative DNS Server Specification *)
        mkiUsr USR1 PERMS1
               (
                 @idealServer 1 (Base Nat) 1
                              (
                                m <- @Recv Nat CH21
                                ; let ip := match names $? extractContent m with
                                            | None   => 0
                                            | Some a => a
                                            end
                                  in
                                  _ <- Send (Content ip) CH12
                                ; @Return (Base Nat) ip
                              )
               )
        ;

      (* Secure DNS Cache Specification *)
      mkiUsr USR2 PERMS2
             (
               req <- @Recv Nat CH32
               ; _ <- Send (Content (extractContent req)) CH21
               ; ip1 <- @Recv Nat CH12
               ; _ <- Send (Content (extractContent ip1)) CH23
               ; @Return (Base Nat) (extractContent ip1)
             )
        ;

      (* DNS Client Specification *)
      mkiUsr USR3 PERMS3
             (
               _ <- Send (Content 0) CH32
               ; ip1 <- @Recv Nat CH23
               ; @Return (Base Nat) (extractContent ip1)
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
    Notation KID3 := 2.
    Notation KID4 := 3.
    Notation KID5 := 4.
    Notation KID6 := 5.

    Notation KEYS := [ skey KID1 ; ekey KID2 ; skey KID3 ; ekey KID4 ; skey KID5 ; ekey KID6 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, true) $+ (KID3, false) $+ (KID4, false)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, false)
                        $+ (KID3, true) $+ (KID4, true)
                        $+ (KID5, false) $+ (KID6, false)).
    Notation KEYS3 := ($0 $+ (KID3, false) $+ (KID4, false) $+ (KID5, true) $+ (KID6, true)).

    Fixpoint realServer (n : nat) {t} (r : << t >>) (c : user_cmd t) : user_cmd t :=
      match n with
      | 0   => @Return t r
      | S i => (r' <- c ; realServer i r' c)
      end.

    Notation real_users :=
      [
        (* Authoritative DNS server implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      @realServer 1 (Base Nat) 1
                                  ( c <- @Recv Nat (SignedEncrypted KID3 KID2 true)
                                    ; m <- Decrypt c
                                    ; let ip := match names $? (extractContent m) with
                                                | None   => 0
                                                | Some a => a
                                                end
                                      in ipC <- SignEncrypt KID1 KID4 USR2 (message.Content ip)
                                    ; _ <- Send USR2 ipC
                                    ; @Return (Base Nat) ip
                                  )
                    )
        ;

      (* Secure DNS Cache implementation *)
      MkRUserSpec USR2 KEYS2
                  (
                    reqc <- @Recv Nat (SignedEncrypted KID5 KID4 true)
                    ; req <- Decrypt reqc
                    ; c1 <- SignEncrypt KID3 KID2 USR1 (message.Content (extractContent req))
                    ; _ <- Send USR1 c1
                    ; hostC <- @Recv Nat (SignedEncrypted KID1 KID4 true)
                    ; host <- Decrypt hostC
                    ; c2 <- SignEncrypt KID3 KID6 USR3 (message.Content (extractContent host))
                    ; _ <- Send USR3 c2
                    ; @Return (Base Nat) (extractContent host)
                  ) 
        ;

      (* DNS Client implementation *)
      MkRUserSpec USR3 KEYS3
                  (
                    c <- SignEncrypt KID5 KID4 USR2 (message.Content 0)
                    ; _ <- Send USR2 c
                    ; hostC <- @Recv Nat (SignedEncrypted KID3 KID6 true)
                    ; host <- Decrypt hostC
                    ; @Return (Base Nat) (extractContent host)
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
  
End SecureDNSProtocol.

Module SecureDNSProtocolSecure <: AutomatedSafeProtocol.

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

  Import Gen Tacs SetLemmas.

  Ltac gen1' :=
    simplify
    ; tidy
    ; idtac "rstep start"
    ; rstep
    ; idtac "istep start"
    ; istep
    ; idtac "istep done"
    ; subst
    ; canonicalize users
    ; idtac "close start"
    ; repeat close
    ; idtac "close done"
  .

  Ltac msc_st1 := unfold oneStepClosure_new  (* ; repeat gen1' *).
  Ltac msc_st2 :=
    simplify
    ; sets
    ; split_ex
    ; propositional
    ; repeat match goal with
             | [H : (?x1, ?y1) = ?p |- _] =>
               match p with
               | (?x2, ?y2) =>
                 tryif (concrete x2; concrete y2)
                 then let H' := fresh H
                      in assert (H' : (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2)
                        by equality
                         ; propositional
                         ; discriminate
                 else invert H
               | _ => invert H
               end
             end.

  
  Ltac mscalt' :=
    eapply msc_step_alt
    ; [ solve[ msc_st1; repeat gen1' ]
      | solve[ msc_st2 | eapply intersect_empty_l ]
      | rewrite ?union_empty_r ].

  Ltac mscalt :=
    match goal with
    | [|- multiStepClosure _ (_ \cup ?wl) ?wl _] => mscalt'
    end.

  Ltac gen1 :=
    match goal with
    | [|- multiStepClosure _ _ { } _] =>
      eapply MscDone
    | [|- multiStepClosure _ {(_, _)} {(_, _)} _] =>
      eapply MscStep
      ; [ solve[ apply oneStepClosure_grow; gen1' ]
        | simplify; simpl_sets (sets; tidy)]
    | [|- multiStepClosure _ (_ \cup ?wl) ?wl _] => mscalt'
    end.


  (* These are here to help the proof automation.  Don't change. *)
  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
    : core.

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

      eapply msc_step_alt.
      + unfold oneStepClosure_new; repeat gen1'.



        | solve[ simplify
                 ; sets
                 ; split_ex
                 ; propositional
                 ; repeat match goal with
                          | [H : (?x1, ?y1) = ?p |- _] =>
                            match p with
                            | (?x2, ?y2) =>
                              tryif (concrete x2; concrete y2)
                              then let H' := fresh H
                                   in assert (H' : (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2)
                                     by equality
                                      ; propositional
                                      ; discriminate
                              else invert H
                            | _ => invert H
                            end
                          end
               | eapply intersect_empty_l]
        | rewrite ?union_empty_r ]


      
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
      (* 129 *)
            ( split;
            [ solve_honest_actions_safe; clean_map_lookups; eauto 8
            | simpl; split; trivial; intros; rstep; subst; solve_labels_align
            ]).

      all: simpl; solve_honest_actions_safe.

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
      simpl in *; solve_perm_merges.
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
  

End SecureDNSProtocolSecure.
