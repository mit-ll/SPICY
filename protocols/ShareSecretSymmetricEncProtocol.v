(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019-2020 Massachusetts Institute of Technology.
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

Module ShareSecretSymmetricEncProtocol.

  (* User ids *)
  Notation USR1 := 0.
  Notation USR2 := 1.

  
  Section IW_Simple.
    Import IdealWorld.

    Notation perms_CH := 0.
    Notation CH := (Single perms_CH).

    Notation empty_chs := (#0 #+ (CH, [])).

    Definition PERMS := $0 $+ (perms_CH, {| read := true; write := true |}).

    Definition simple_users :=
      [
        (mkiUsr USR1 PERMS 
                (
                  n <- Gen
                  ; _ <- Send (Content n) CH
                  ; @Return (Base Nat) n
        ));
        (mkiUsr USR2 PERMS
                ( m <- @Recv Nat CH
                ; @Return (Base Nat) (extractContent m)))
        ].

    Definition simple_univ_start :=
      mkiU empty_chs simple_users.

  End IW_Simple.

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
                  ; _ <- Send (sharePerm chid writer) CH12
                  ; m <- @Recv Access (chid #& pCH21)
                  ; n <- Gen
                  ; _ <- Send (Content n) (getPerm m #& pCH12)
                  ; @Return (Base Nat) n
        )) ;
      (mkiUsr USR2 PERMS2
              ( m <- @Recv Access CH12
                ; chid <- CreateChannel
                ; _ <- Send (sharePerm chid owner) (getPerm m #& pCH21)
                ; m <- @Recv Nat (chid #& pCH12)
                ; @Return (Base Nat) (extractContent m)
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

    Definition real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( kp <- GenerateAsymKey Encryption
                      ; c1 <- Sign KID1 USR2 (sharePubKey kp)
                      ; _  <- Send USR2 c1
                      ; c2 <- @Recv Access (SignedEncrypted KID2 (fst kp) true)
                      ; m  <- Decrypt c2
                      ; n  <- Gen
                      ; c3 <- SignEncrypt KID1 (getKey m) USR2 (message.Content n)
                      ; _  <- Send USR2 c3
                      ; @Return (Base Nat) n) ;

      MkRUserSpec USR2 KEYS2
                  ( c1 <- @Recv Access (Signed KID1 true)
                    ; v  <- Verify KID1 c1
                    ; kp <- GenerateSymKey Encryption
                    ; c2 <- SignEncrypt KID2 (getKey (snd v)) USR1 (sharePrivKey kp)
                    ; _  <- Send USR1 c2
                    ; c3 <- @Recv Nat (SignedEncrypted KID1 (fst kp) true)
                    ; m  <- Decrypt c3
                    ; @Return (Base Nat) (extractContent m) )
      ].

    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  Hint Unfold
       simple_univ_start
       ideal_univ_start
       real_univ_start
    : user_build.

  Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl).
  
End ShareSecretSymmetricEncProtocol.

Section IW_Simple_Refinement.
  Import IdealWorld
         ShareSecretSymmetricEncProtocol
         Tacs
         Gen.

  Lemma iw_simpl_steps_to_end : forall n,
      exists su,
        trc3 lstep_universe (fun _ => True) simple_univ_start su
        /\ (forall l su', ~ lstep_universe su l su')
        /\ (forall uid ud,
              simple_univ_start.(users) $? uid = Some ud
              -> exists ud',
                su.(users) $? uid = Some ud'
                /\ ud'.(protocol) = Return n).
  Proof.
    intros
    ; unfold simple_univ_start, mkiUsr, mkiU, simple_users
    ; simpl.

    eexists; repeat simple apply conj.
    - eapply Trc3Front; trivial.

      Ltac stpu uid :=
        eapply LStepUser' with (u_id := uid);
        [ simpl; clean_map_lookups; trivial
        | eapply LStepBindRecur; econstructor; eauto
        | reflexivity ].

      Ltac stpu' uid :=
        eapply LStepUser' with (u_id := uid);
        [ simpl; clean_map_lookups; trivial
        | eapply LStepBindProceed; trivial
        | reflexivity ].

      stpu 0.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Front; trivial.
      stpu' 0.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Front; trivial.
      stpu 0.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Front; trivial.
      stpu' 0.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Front; trivial.
      stpu 1.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Front; trivial.
      stpu' 1.
      simpl; canonicalize iusers; simpl.
      eapply Trc3Refl.

      Unshelve.
      eassumption.

    - unfold not; intros.
      invert H; simpl in *.
      destruct (u_id ==n 1)
      ; [ | destruct (u_id ==n 0)]
      ; subst; clean_map_lookups
      ; invert H5.

    - simpl; intros.
      destruct (uid ==n 1)
      ; [ | destruct (uid ==n 0)]
      ; subst; clean_map_lookups
      ; trivial.

      eexists; simpl; split; [ reflexivity | ]; eauto.
      eexists; simpl; split; [ reflexivity | ]; eauto.
  Qed.

  Inductive R__ii :
    IdealWorld.universe Nat -> IdealWorld.universe Nat
    -> Prop :=
  | BeforeDone : forall iu',
      trc3 IdealWorld.lstep_universe (fun _ => True) ideal_univ_start iu'
      -> forall l iu'', lstep_universe iu' l iu''
      -> R__ii iu' simple_univ_start
  | Done : forall su' iu',
      trc3 IdealWorld.lstep_universe (fun _ => True) ideal_univ_start iu'
      -> (forall l iu'', ~ lstep_universe iu' l iu'')
      -> trc3 IdealWorld.lstep_universe (fun _ => True) simple_univ_start su'
      -> (forall l su'', ~ lstep_universe su' l su'')
      -> R__ii iu' su'.

  Inductive KEEP {A} : universe A -> universe A -> universe A -> Prop :=
    K : forall l u u' u'',
      trc3 lstep_universe (fun _ => True) u u'
      -> lstep_universe u' l u''
      -> KEEP u u' u''.

  Theorem ii_correct :
    ii_simulates R__ii ideal_univ_start simple_univ_start.
  Proof.
    unfold ii_simulates, ii_step, simple_univ_start, ideal_univ_start, mkiUsr, mkiU, simple_users
    ; simpl
    ; split; intros.

    Ltac process_ideal_ctx1 := 
      match goal with
      | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
        is_var k2
        ; destruct (k1 ==n k2); subst
        ; clean_map_lookups

      | [ H : context [ addMsg ] |- _ ] =>
        unfold addMsg in H
        ; simpl in H
      | [ H : context [ $0 $? _ ] |- _ ] =>
        rewrite lookup_empty_none in H
      | [ H : context [ #0 #? _ ] |- _ ] =>
        rewrite ChMaps.ChMap.lookup_empty_none in H
      | [ H : context [ _ #+ (_,_) #? _ ] |- _ ] =>
        (rewrite ChMaps.ChMap.F.add_neq_o in H by congruence)
        || (rewrite ChMaps.ChMap.F.add_eq_o in H by trivial)
      | [ H : None = Some _ |- _ ] =>
        discriminate H
      | [ H : Some _ = None |- _ ] =>
        discriminate H
      end
      || ( progress ( (repeat equality1); subst ) ).

    Ltac id_step :=
      simpl
      ; match goal with
        | [ |- lstep_user _ _ (_, _ <- Return _; _ , _ ) _ ] =>
          eapply LStepBindProceed
        | [ |- lstep_user _ _ (_, _ <- _; _ , _ ) _ ] =>
          eapply LStepBindRecur
        | [ |- lstep_user _ _ (_,_,_) _ ] =>
          econstructor
        end.

    Ltac solve_ideal_step_stuff2 :=
      match goal with
      | [ |- context [ _ $? _ ] ] =>
        progress clean_map_lookups
      | [ |- context [ perm_intersection ] ] =>
        unfold perm_intersection; simpl
      end.

    Ltac univ_user_step uid :=
      eapply LStepUser' with (u_id := uid)
      ; [ simpl; clean_map_lookups; trivial
        | ( repeat id_step ); repeat ( solve_ideal_step_stuff1 || solve_ideal_step_stuff2 ); eauto
        | reflexivity
        ].

    Ltac so_is uid := (do 2 eexists); univ_user_step uid.

    Ltac do_step1 :=
      match goal with

      | [ STEP : lstep_user ?uid _ ?u _ |- _ ] =>
        is_not_var uid
        ; is_not_var u
        ; invert STEP
        ; repeat (equality1 || solve_ideal_step_stuff1 || (progress subst))
                 
      | [ STEP : lstep_user ?uid _ ?u _
        , USR : _ $? ?uid = Some _ |- _ ] =>

        is_var uid
        ; is_not_var u
        ; simpl in USR
        ; destruct (uid ==n 1); destruct (uid ==n 0); subst
        ; clean_map_lookups
        ; simpl in STEP

      | [ STEP : lstep_universe ?u _ _ |- _ ] =>
        is_not_var u; invert STEP

      end.

    Ltac finish := 
      match goal with
      | [ H : KEEP ?u1 ?u2 ?u3 |- context [ R__ii ?u3 _ ] ] =>
        invert H
        ; match goal with
          | [ TRC : trc3 _ ?p ?u1 ?u2, STEP : lstep_universe ?u2 _ ?u3 |- _ ] =>
            assert (trc3 lstep_universe p u1 u3)
              by (eapply trc3_trans; [ eassumption |]; eapply trc3_one; eauto 2)
            ; clear TRC
          end
        ; repeat (
              discriminate
              || do_step1
            )
      end
      ; ( eexists; repeat simple apply conj
          ; [ eapply Trc3Refl
            | unfold ii_final_labels_align; intros
            | solve [ econstructor 1
                      ; unfold ideal_univ_start, mkiU, mkiUsr; simpl in *; eauto 2
                      ; repeat process_ideal_ctx1
                      ; try solve [ univ_user_step 0 ]
                      ; try solve [ univ_user_step 1 ]
                    ] 
            ]
          ; exfalso
          ; match goal with
            | [ H : forall _ _, ~ lstep_universe ?u _ _ |- _ ] =>
              let STEP := fresh "STEP"
              in  assert (exists lbl u', lstep_universe u lbl u')
                as STEP by ( solve [ so_is 0 ] || solve [ so_is 1] )
                  ; destruct STEP as [?lbl [?u' STEP]]
                  ; eapply H in STEP
                  ; contradiction
            end)
    .

    Ltac find_step1 :=
      do_step1 ||
      match goal with

      | [ STEP : lstep_universe ?u _ _
        , TRC : trc3 lstep_universe _ _ ?u |- _ ] =>
        invert TRC

      | [ H : KEEP _ _ ?u |- exists _, _ /\ (ii_final_labels_align ?u _) /\ _ ] =>
        solve [ finish ]

      end.

    
    Ltac simple_ideal :=
      match goal with
      | [ H : context [ users _ ] |- _ ] =>
        progress ( simpl in H )
      | [ H : context [ channel_vector _ ] |- _ ] =>
        progress ( simpl in H )
      | [ H : context [ {| users := ?us |}] |- _ ] =>
        progress ( canonicalize_concrete_map  us )
      | [ |- context [ {| users := ?us |}] ] =>
        progress ( canonicalize_concrete_map  us )
      end.

    Ltac find_step :=
      ( progress ( repeat process_ideal_ctx1 ))
      || discriminate
      || simple_ideal
      || find_step1.

    

    - invert H.
      + assert (KEEP ideal_univ_start U__i U__i').
        econstructor; eauto.
        clear H0.

        do 175 (try find_step).

        Ltac f' := 
          match goal with
          | [ H : Return _ = Return ?r
                  , F : (forall _ _, _ $? _ = Some _ -> exists _, _ /\ _)
              |- exists _, users _ $? _ = Some _ /\ protocol _  = Return ?r ] =>
            rewrite <- H
            ; idtac H F
            ; eapply F
            ; clean_map_lookups
            ; reflexivity
          end.

        Ltac f :=
          match goal with
          | [ H : KEEP ?u1 ?u2 ?u3 |- context [ R__ii ?u3 _ ] ] =>
            invert H
            ; match goal with
              | [ TRC : trc3 _ ?p ?u1 ?u2, STEP : lstep_universe ?u2 _ ?u3 |- _ ] =>
                assert (trc3 lstep_universe p u1 u3)
                  by (eapply trc3_trans; [ eassumption |]; eapply trc3_one; eauto 2)
                ; clear TRC
              end
            ; repeat (
                  discriminate
                  || do_step1
                )
          end
          ; simpl
          ; repeat simple_ideal
          ; match goal with
            | [ H : trc3 _ _ _ {| users := _ $+ (_, {| protocol := Return ?n |}) |} |- _ ] =>
              idtac n
              ; pose proof (iw_simpl_steps_to_end n)
              ; split_ex
            end
          ; assert (exists ud, simple_univ_start.(users) $? 0 = Some ud)
            by ( eexists; unfold simple_univ_start; simpl; clean_map_lookups; reflexivity )
          ; assert (exists ud, simple_univ_start.(users) $? 1 = Some ud)
            by ( eexists; unfold simple_univ_start; simpl; clean_map_lookups; reflexivity )
          ; split_ex
          ; eexists; repeat simple apply conj
          ; [ eassumption
            | unfold ii_final_labels_align; intros
              ; (do 2 eexists); eauto
              ; repeat simple apply conj
              ; [ apply Trc3Refl
                | auto 2
                | simpl; intros
                  ; match goal with
                    | [ H : _ $? ?uid = Some ?ud, P : protocol ?ud = Return _ |- _ ] =>
                      destruct (uid ==n 0); destruct (uid ==n 1); subst; clean_map_lookups
                    end
                  ; simpl in *
                  ; f'
                ]

            | solve [ econstructor 2
                      ; try eassumption
                      ; unfold not; intros; repeat find_step
                    ] 
            ].

        f.

        all : try solve [ f ].

        Unshelve.
        all: auto.

      + eapply H2 in H0; contradiction.

    - econstructor.
      eapply Trc3Refl.
      univ_user_step 0.

  Qed.
        

End IW_Simple_Refinement.

Module ShareSecretProtocolSecure <: AutomatedSafeProtocol.

  Import ShareSecretSymmetricEncProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition su0  := simple_univ_start.
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
      (fun st => safety st /\ alignment st /\ returns_align st).
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

      Unshelve.
      all: exact 0 || auto.

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
  

End ShareSecretProtocolSecure.

(*
 * 1) make protocols  518.64s user 0.45s system 99% cpu 8:39.13 total  ~ 6.2GB
 * 2) add cleanup of chmaps to close:
 *    make protocols  414.45s user 0.43s system 99% cpu 6:54.90 total  ~ 5.6GB
 *
 *
 *)
