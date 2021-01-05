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
     ModelCheck
     Common
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse

     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
.

From SPICY Require IdealWorld RealWorld.

From protocols Require Import
     ShareSecretProtocolSymmetricEnc.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

From Frap Require Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

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
