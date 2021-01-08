(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List.

Require Import
        MyPrelude
        Maps
        ChMaps
        Messages
        ModelCheck
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol
        ProtocolFunctions
        PartialOrderReduction.

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

Module ShareSecretProtocol.

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
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, owner)).

    Notation ideal_users :=
      [
        (mkiUsr USR1 PERMS1 
                ( chid <- CreateChannel
                  ; _ <- Send (Permission {| ch_perm := writer ; ch_id := chid |}) CH12
                  ; m <- @Recv Nat (chid #& pCH21)
                  ; @Return (Base Nat) (extractContent m)
        )) ;
      (mkiUsr USR2 PERMS2
              ( m <- @Recv Access CH12
                ; n <- Gen
                ; _ <- let chid := ch_id (extractPermission m)
                      in  Send (Content n) (chid #& pCH21)
                ; @Return (Base Nat) n
      ))
      ].

    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.

    Notation KID1 := 0.
    Notation KID2 := 1.

    Notation KEYS := [ skey KID1 ; skey KID2 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, false)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, true)).

    Notation real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( kp <- GenerateAsymKey Encryption
                      ; c1 <- Sign KID1 USR2 (Permission (fst kp, false))
                      ; _  <- Send USR2 c1
                      ; c2 <- @Recv Nat (SignedEncrypted KID2 (fst kp) true)
                      ; m  <- Decrypt c2
                      ; @Return (Base Nat) (extractContent m) ) ;

      MkRUserSpec USR2 KEYS2
                  ( c1 <- @Recv Access (Signed KID1 true)
                    ; v  <- Verify KID1 c1
                    ; n  <- Gen
                    ; c2 <- SignEncrypt KID2 (fst (extractPermission (snd v))) USR1 (message.Content n)
                    ; _  <- Send USR1 c2
                    ; @Return (Base Nat) n)
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
  
End ShareSecretProtocol.

Module ShareSecretProtocolSecure <: AutomatedSafeProtocol.

  Import ShareSecretProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start.

  Import Gen Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start real_univ_start : core.
  Hint Unfold
       mkiU mkiUsr mkrU mkrUsr
       mkKeys
    : core.

  (* Section Summary. *)
  (*   Import RealWorld. *)

  (*   Ltac build_summary proto s := *)
  (*     match proto with *)
  (*     | Send ?uid _ => constr:({| sending_to := s.(sending_to) \cup { uid } |}) *)
  (*     | Bind ?cmd1 ?cmd2 => *)
  (*       let s1 := build_summary cmd1 s *)
  (*       in  build_summary (cmd2 ?v) s1 *)
  (*     | _ => s *)
  (*     end. *)

  (*   Check build_summary (@Return (Base Nat) 1) {| sending_to := { } |}. *)
      

  (*   Fixpoint build_summary {t} (proto : RealWorld.user_cmd t) (s : summary ) : summary := *)
  (*     match proto with *)
  (*     | Send uid m => {| sending_to := s.(sending_to) \cup { uid } |} *)
  (*     | Bind cmd1 cmd2 => *)
  (*       let s1 := build_summary cmd1 *)
  (*       in  let s2 := build_summary (cmd2 v) *)
  (*           in   *)
  (*     | _ => s *)
  (*     end. *)


  (* Record summary := { sending_to : Sets.set user_id }. *)

  (* Inductive summarize : forall {t}, user_cmd t -> summary -> Prop := *)
  (* | SumReturn : forall t r s, *)
  (*     summarize (@Return t r) s *)
  (* | SumGen : forall s, *)
  (*     summarize Gen s *)
  (* | SumSend : forall {t} (msg : crypto t) uid s, *)
  (*     Sets.In uid s.(sending_to) *)
  (*     -> summarize (Send uid msg) s *)
  (* | SumRecv : forall t pat s, *)
  (*     summarize (@Recv t pat) s *)
  (* | SumSignEncrypt : forall t k__s k__e u_id (msg : message t)s , *)
  (*     summarize (SignEncrypt k__s k__e u_id msg) s *)
  (* | SumDecrypt : forall t (msg : crypto t) s, *)
  (*     summarize (Decrypt msg) s *)
  (* | SumSign : forall t k u_id (msg : message t) s, *)
  (*     summarize (Sign k u_id msg) s *)
  (* | SumVerify : forall t k (msg : crypto t) s, *)
  (*     summarize (Verify k msg) s *)
  (* | SumGenSymKey : forall usg s, *)
  (*     summarize (GenerateSymKey usg) s *)
  (* | SumGenAsymKey : forall usg s, *)
  (*     summarize (GenerateAsymKey usg) s *)
  (* | SumBind : forall t1 t2 (c1 : user_cmd t1) (c2 : << t1 >> -> user_cmd t2) s, *)
  (*     summarize c1 s *)
  (*     -> (forall r__v, summarize (c2 r__v) s) *)
  (*     -> summarize (Bind c1 c2) s *)
  (* . *)
  
  Ltac build_summary proto s :=
    match proto with
    | RealWorld.Send ?uid _ =>
      let s1 := constr:({| sending_to := s.(sending_to) \cup { uid } |}) in eval simpl in s1
    | RealWorld.Bind ?cmd1 ?cmd2 =>
      match cmd2 with
      | (fun v:?V => ?CMD) =>
        let s1 := build_summary cmd1 s
        in  let s2 := build_summary CMD s1
            in eval simpl in s2
      (* | _ => *)
      (*   constr:({| sending_to := s.(sending_to) \cup { 2000 } |}) *)
      end
    | _ => s
    end.

  (* Import RealWorld. *)
  (* Import RealWorld.RealWorldNotations. *)



  (* let s := build_summary (@Return (Base Nat) 1) constr:({| sending_to := { } |}) *)
  (* in  idtac s. *)

  (* let s := build_summary ( Send 0 (Content (message.Content 100)) ) *)
  (*                        constr:({| sending_to := { } |}) *)
  (* in  idtac s. *)
  

  (* let s := build_summary ( _ <- Send 0 (Content (message.Content 100)); @Return (Base Unit) tt) *)
  (*                        constr:({| sending_to := { } |}) *)
  (* in  idtac s. *)


  (* Lemma build_summary_summarizes : *)
  (*   forall t (proto : RealWorld.user_cmd t) s, *)
  (*     s = build_summary proto {| sending_to := { } |} *)
  (*     -> summarize proto s. *)
      
  
  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0, true)}; Step := @stepC t__hon t__adv  |}
      (fun st => safety st /\ alignment st ).
  Proof.
    eapply invariant_weaken.

    - eapply multiStepClosure_ok; simpl.

      eapply MscStep.
      
      apply oneStepClosure_grow; gen1'.


      simplify
      ; repeat tidy'
      ; tidy
      ; rstep
      ; istep
      ; subst
      ; canonicalize users.

      clear H1; close.
      clear H1; close.
      
      ; repeat close.

      simpl in H2; split_ex; subst.
      invert H2.
      invert H8.

      (* unfold summarize_univ in H1. *)
      (* autounfold in H1; simpl in H1. *)
      (* specialize (H1 0); *)
      (*   rewrite !add_neq_o in H1 by congruence; *)
      (*   rewrite !add_eq_o in H1 by trivial; simpl in H1. *)
      (* specialize (H1 _ {| sending_to := { } |} eq_refl); simpl in H1. *)


      match goal with
      | [ H : (forall _ _, ~ indexedRealStep ?uid _ ?ru _)
            \/ (exists _ _, ?uid <> _ /\ _ $? _ = Some _ /\ (forall _, ?sums $? _ = Some _ -> commutes ?proto _ -> False))
        , S : summarize_univ ?ru ?sums
          |- _ ] =>
        ( (assert (exists lbl ru', indexedRealStep uid lbl ru ru') by solve_indexedRealStep )
        ; (assert (exists uid2 ud2, uid <> uid2
                               /\ ru.(RealWorld.users) $? uid2 = Some ud2
                               /\ (forall s, summaries $? uid2 = Some s -> commutes proto s)) by non_commuters ))
        ; discharge_nextStep2 (* clear this goal since the preconditions weren't satisfied *)
      end.

      admit.
      admit.
      



      repeat 
      match goal with
      end.
        
      specialize (H1 _ _ {| sending_to := { } |} H6); split_ex.
      specialize (H7 _ H1); simpl in H7; contradiction.
      
      match goal with
      | [ H : (forall _ _, ~ indexedRealStep ?uid _ ?ru _), ARG : indexedRealStep ?uid _ ?ru _ |- _ ] =>
        eapply H in ARG; contradiction
      | [ H : (forall _, ?sums $? _ = Some _ -> commutes ?proto _ -> False),
        ARG : (forall _, ?sums $? _ = Some _ -> commutes ?proto _) |- _ ] =>
        eapply H in ARG
      end.
      
      (* specialize (H1 0); *)
      (*   autounfold in H1; *)
      (*   simpl in H1; *)
      (*   rewrite !add_neq_o in H1 by congruence; *)
      (*   rewrite !add_eq_o in H1 by trivial; *)
      (*   specialize (H1 _ {| sending_to := { } |} eq_refl); *)
      (*   simpl in H1; *)
      (*   split_ex. *)

      exists 0; eexists; repeat simple apply conj; [
        congruence
      | solve [ autounfold; simpl; clean_map_lookups; trivial ]
      | intros; simpl
      ]; match goal with
         | [ |- False ] => idtac 1
         end.

      | intros; invert_commutes ].

      exists 0; eexists; repeat simple apply conj; [
        congruence
      | solve [ autounfold; simpl; clean_map_lookups; trivial ]
      | intros; invert_commutes ].



      simplify
      ; tidy
      ; rstep
      ; istep
      ; subst
      ; canonicalize users
      ; repeat close.
      


      
        
         
      simplify
      ; repeat tidy'
      ; tidy
      ; repeat tidy'
      ; idtac "rstep start"
      ; rstep
      ; idtac "istep start"
      ; istep
      ; idtac "istep done"
      ; subst
      ; canonicalize users
      ; idtac "close start"
      ; repeat close
      ; idtac "close done".




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
    ; idtac "close done".
      
      invert H0.
      invert H1.
      invert H.

      
      simplify; simpl_sets (sets; tidy)]




      
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
            [ solve_honest_actions_safe; clean_map_lookups; eauto 8
            | split; trivial; intros; rstep; subst; solve_labels_align
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
  

End ShareSecretProtocolSecure.

(*
 * 1) make protocols  518.64s user 0.45s system 99% cpu 8:39.13 total  ~ 6.2GB
 * 2) add cleanup of chmaps to close:
 *    make protocols  414.45s user 0.43s system 99% cpu 6:54.90 total  ~ 5.6GB
 *
 *
 *)
