(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Eqdep
     Lia
.

From SPICY Require Import
     MyPrelude
     AdversaryUniverse
     Automation
     Common
     Keys
     Maps
     Messages
     MessageEq
     RealWorld
     Simulation
     Tactics

     Theory.KeysTheory

     ModelCheck.ModelCheck
     ModelCheck.SafeProtocol
     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolFunctions
     ModelCheck.PartialOrderReduction
     ModelCheck.SilentStepElimination
.

From SPICY Require
     IdealWorld
     RealWorld
     ChMaps
.

From Frap Require 
     Sets
.

Import ChMaps.ChMapNotation
       ChMaps.ChNotation.

Set Implicit Arguments.

Module SimulationAutomation.

  Hint Constructors RealWorld.msg_accepted_by_pattern : core.

  Module T.
    Import RealWorld.

    Lemma message_match_not_match_pattern_different :
      forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) cs suid froms pat,
        ~ msg_accepted_by_pattern cs suid froms pat msg1
        -> msg_accepted_by_pattern cs suid froms pat msg2
        -> existT _ _ msg1 <> existT _ _ msg2.
    Proof.
      intros.
      unfold not; intros.
      generalize (projT1_eq H1); intros EQ; simpl in EQ; subst.
      eapply inj_pair2 in H1; subst.
      contradiction.
    Qed.

    Lemma message_queue_split_head :
      forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) qmsgs qmsgs1 qmsgs2
        cs suid froms pat,

        existT _ _ msg2 :: qmsgs = qmsgs1 ++ existT _ _ msg1 :: qmsgs2
        -> msg_accepted_by_pattern cs suid froms pat msg1
        -> ~ msg_accepted_by_pattern cs suid froms pat msg2
        -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs suid froms pat msg') qmsgs1
        -> exists qmsgs1',
            qmsgs1 = (existT _ _ msg2) :: qmsgs1'.
    Proof.
      intros.
      destruct qmsgs1.
      - rewrite app_nil_l in H.
        eapply message_match_not_match_pattern_different in H0; eauto.
        invert H; contradiction.

      - rewrite <- app_comm_cons in H.
        invert H; eauto.
    Qed.

    Lemma message_queue_solve_head :
      forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) qmsgs qmsgs1 qmsgs2
        cs suid froms pat,

        existT _ _ msg2 :: qmsgs = qmsgs1 ++ existT _ _ msg1 :: qmsgs2
        -> msg_accepted_by_pattern cs suid froms pat msg1
        -> msg_accepted_by_pattern cs suid froms pat msg2
        -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs suid froms pat msg') qmsgs1
        -> qmsgs1 = []
          /\ qmsgs2 = qmsgs
          /\ existT _ _ msg1 = existT _ _ msg2.
    Proof.
      intros.
      subst.
      destruct qmsgs1.

      rewrite app_nil_l in H
      ; invert H
      ; eauto.

      exfalso.
      rewrite <- app_comm_cons in H.
      invert H; eauto.
      invert H2; contradiction.
    Qed.

    Ltac pr_message cs uid froms pat msg :=
      (assert (msg_accepted_by_pattern cs uid froms pat msg)
        by (econstructor; eauto))
      || (assert (~ msg_accepted_by_pattern cs uid froms pat msg)
          by (let MA := fresh "MA" in  unfold not; intros MA; invert MA; clean_map_lookups)).

    Ltac cleanup_msg_queue :=
      repeat (
          invert_base_equalities1 ||
          match goal with
          | [ H : context [ (_ :: _) ++ _ ] |- _ ] =>
            rewrite <- app_comm_cons in H
          end ).

    Ltac process_message_queue :=
      cleanup_msg_queue;
      match goal with
      | [ H : (existT _ _ ?m) :: ?msgs = ?msgs1 ++ (existT _ _ ?msg) :: ?msgs2,
              M : msg_accepted_by_pattern ?cs ?suid ?froms ?pat ?msg
          |- _ ] =>

        pr_message cs suid froms pat m
        ; match goal with
          | [ MSA : msg_accepted_by_pattern cs suid froms pat m
                    , HD : Forall _ msgs1
              |- _ ] =>
            idtac "solving " H M MSA HD
            ; pose proof (message_queue_solve_head _ H M MSA HD)
            ; split_ex; subst
            ; cleanup_msg_queue; subst
          | [ MSA : ~ msg_accepted_by_pattern cs suid froms pat m
                    , HD : Forall _ msgs1
              |- _ ] =>
            idtac "splitting"
            ; pose proof (message_queue_split_head _ H M MSA HD)
            ; split_ex; subst
            ; invert HD
            ; cleanup_msg_queue; subst
            ; process_message_queue (* recurse *)
          end
      end.

    Ltac step_usr_hyp H cmd :=
      match cmd with
      | Return _ => apply step_user_inv_ret in H; contradiction
      | Bind _ _ => apply step_user_inv_bind in H; split_ands; split_ors; split_ands; subst; try discriminate
      | Gen => apply step_user_inv_gen in H
      | Send _ _ => apply step_user_inv_send in H
      | Recv _ => apply step_user_inv_recv in H; split_ex; subst; process_message_queue
      | SignEncrypt _ _ _ _ => apply step_user_inv_enc in H
      | Decrypt _ => apply step_user_inv_dec in H
      | Sign _ _ _ => apply step_user_inv_sign in H
      | Verify _ _ => apply step_user_inv_verify in H
      | GenerateKey _ _ => apply step_user_inv_genkey in H
      | _ => idtac "***Missing inversion: " cmd; invert H
      end; split_ex; subst.

    Lemma inv_univ_silent_step :
      forall t__hon t__adv ru ru' suid b,
        lameAdv b ru.(RealWorld.adversary)
        -> @RealWorld.step_universe t__hon t__adv suid ru Silent ru'
        -> exists uid ud usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
            ru.(RealWorld.users) $? uid = Some ud
            /\ step_user Silent (Some uid)
                        (build_data_step ru ud)
                        (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
            /\ ru' = buildUniverse usrs adv cs gks uid {| key_heap    := ks
                                                         ; msg_heap  := qmsgs
                                                         ; protocol  := cmd
                                                         ; c_heap    := mycs
                                                         ; from_nons := froms
                                                         ; sent_nons := sents
                                                         ; cur_nonce := cur_n |}.
    Proof.
      intros * LAME STEP
      ; invert STEP.

      - unfold mkULbl in H2
        ; destruct lbl
        ; try discriminate
        ; eauto 20.

      - unfold lameAdv in LAME.
        unfold build_data_step in H
        ; rewrite LAME in H
        ; invert H.
    Qed.

    Lemma inv_univ_labeled_step :
      forall t__hon t__adv ru ru' suid uid a,
        @RealWorld.step_universe t__hon t__adv suid ru (Action (uid,a)) ru'
        -> exists ud usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
          ru.(RealWorld.users) $? uid = Some ud
          /\ suid = Some uid
          /\ step_user (@Action RealWorld.action a) (Some uid)
                      (build_data_step ru ud)
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          /\ ru' = buildUniverse usrs adv cs gks uid {| key_heap    := ks
                                                       ; msg_heap  := qmsgs
                                                       ; protocol  := cmd
                                                       ; c_heap    := mycs
                                                       ; from_nons := froms
                                                       ; sent_nons := sents
                                                       ; cur_nonce := cur_n |}.
    Proof.
      intros * STEP
      ; invert STEP.

      unfold mkULbl in H2
      ; destruct lbl
      ; try discriminate.

      invert H2; eauto 20.
    Qed.

    Ltac rw_step1 :=
      match goal with

      (* Only take a user step if we have chosen a user *)
      | [ H : RealWorld.step_user _ (Some ?u) _ _ |- _ ] =>
        progress simpl in H
      | [ H : RealWorld.step_user _ (Some ?u) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u;
        step_usr_hyp H cmd

      | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,_,_,_,RealWorld.protocol ?adv) _
        , LAME : lameAdv _ ?adv |- _ ] => pose proof (adv_no_step LAME STEP); contradiction

      | [ H : RealWorld.step_user _ _ (build_data_step _ _) _ |- _ ] =>
        unfold build_data_step in H; autounfold with user_build in H; simpl in H

      | [ |- context [RealWorld.buildUniverse _ _ _ _ _ _] ] =>
        unfold RealWorld.buildUniverse

      | [ H: step_universe _ ?U Silent _ |- _ ] =>
        is_not_var U
        ; eapply inv_univ_silent_step in H
        ; eauto
        ; split_ex
        ; subst

      | [ H: step_universe _ ?U (Action _) _ |- _ ] =>
        is_not_var U
        ; eapply inv_univ_labeled_step in H
        ; eauto
        ; split_ex
        ; subst
      end.

    Ltac prove_alignment1 :=
      equality1 ||
      match goal with
      | [ |- labels_align _ ] => unfold labels_align; intros
      | [ H : _ \/ False |- _ ] =>
        destruct H; [|contradiction]
      | [ H : _ \/ ?r |- _ ] =>
        destruct H
      | [ H : indexedRealStep _ _ _ _ |- _ ] => invert H
      | [ H : users _ $? _ = Some _ |- _ ] =>
        progress (autounfold in H; simpl in H)
      (* | [ H : _ $+ (_,_) $? _ = Some _ |- _ ] => progress clean_map_lookups *)
      | [ H : _ $+ (?k1,_) $? ?k2 = Some _ |- _ ] => destruct (k1 ==n k2); subst
      | [ H : step_user (Action _) (Some ?uid) _ _ |- _ ] =>
        progress (autounfold in H; unfold RealWorld.build_data_step in H; simpl in H)
      | [ H : step_user _ (Some ?u) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u; is_not_evar u;
        step_usr_hyp H cmd
      | [ |- exists _ _ _, _ ] => simpl; (do 3 eexists); repeat simple apply conj
      end.
      (* || equality1. *)
    
    Lemma label_align_step_split :
      forall t__hon t__adv st st',
        @step t__hon t__adv st st'
        -> labels_align st
        -> forall ru ru' iu iu' b b' a,
            st = (ru,iu,b)
            -> st' = (ru',iu',b')
            -> lameAdv a ru.(adversary)
            -> b = b'
              /\ exists uid,
                ( indexedRealStep uid Silent ru ru' /\ iu = iu' )
                \/ exists iu0 ra ia, 
                  indexedRealStep uid (Action ra) ru ru'
                  /\ (indexedIdealStep uid Silent) ^* iu iu0
                  /\ indexedIdealStep uid (Action ia) iu0 iu'
                  /\ action_matches (all_ciphers ru) (all_keys ru) (uid,ra) ia.
    Proof.
      intros.
      subst; invert H; try contradiction.

      - invert H2;
          try 
            match goal with
            | [ H : Silent = mkULbl ?lbl _ |- _ ] => unfold mkULbl in H; destruct lbl; try discriminate
            end;
          split; eexists; left; eauto.
        unfold build_data_step in *; unfold lameAdv in H3; rewrite H3 in *.
        invert H.
      - split; eexists; right; eauto 10.

        Unshelve.
        auto.
    Qed.

    Lemma label_align_indexedModelStep_split :
      forall t__hon t__adv st st' uid,
        @indexedModelStep t__hon t__adv uid st st'
        -> labels_align st
        -> forall ru ru' iu iu' b b' a,
            st = (ru,iu,b)
            -> st' = (ru',iu',b')
            -> lameAdv a ru.(adversary)
            -> b = b'
              /\ ( (indexedRealStep uid Silent ru ru' /\ iu = iu')
                \/ (exists iu0 ra ia, 
                  indexedRealStep uid (Action ra) ru ru'
                  /\ (indexedIdealStep uid Silent) ^* iu iu0
                  /\ indexedIdealStep uid (Action ia) iu0 iu'
                  /\ action_matches (all_ciphers ru) (all_keys ru) (uid,ra) ia)).
    Proof.
      intros;
        subst; invert H; try contradiction; eauto 12.
    Qed.


  End T.

  Import T.
  Export T.

  Ltac fill_unification_var_ineq uni v :=
    match goal with
    | [ H : ?uni' = v -> False |- _ ] => unify uni uni'
    | [ H : v = ?uni' -> False |- _ ] => unify uni uni'
    end.

  Ltac solve_simple_ineq :=
    repeat
      match goal with
      | [ |- ?kid1 <> ?kid2 ] =>
          congruence
        || (is_evar kid1; fill_unification_var_ineq kid1 kid2)
        || (is_evar kid2; fill_unification_var_ineq kid2 kid1)
        || (is_not_var kid1; progress unfold kid1)
        || (is_not_var kid2; progress unfold kid2)
      end.

  Ltac solve_concrete_maps1 :=
    clean_map_lookups1
    || ChMaps.ChMap.clean_map_lookups1
    || match goal with
      (* | [ H : Some _ = Some _ |- _ ] => invert H *)
      (* | [ H : Some _ = None |- _ ] => discriminate *)
      (* | [ H : None = Some _ |- _ ] => discriminate *)
      | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H; simpl in H

      | [ H : ?m $? _ = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m #? _ = _ |- _ ] => progress (unfold m in H)
      | [ |- context [ ?m $? _ ] ] => progress (unfold m)
      | [ |- context [ ?m #? _ ] ] => progress (unfold m)
                                             
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] =>
        progress ( repeat ( rewrite add_neq_o in H by solve_simple_ineq ) )
      | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- _ ] =>
        progress ( repeat ( rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq ) )
      | [ |- context [ _ $+ (?kid2,_) $? ?kid1 ] ] =>
        progress ( repeat ( rewrite add_neq_o by solve_simple_ineq ) )
      | [ |- context [ _ #+ (?kid2,_) #? ?kid1 ] ] =>
        progress ( repeat ( rewrite ChMaps.ChMap.F.add_neq_o by solve_simple_ineq ) )

      | [ H : In ?k ?m -> False |- _ ] =>
        is_not_var k;
        assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; repeat solve_concrete_maps1);
        contradiction
      | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
      | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
      | [ |- ~ In _ _ ] => rewrite not_find_in_iff; try eassumption
      | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H

      | [ H : ChMaps.ChMap.Map.In ?k ?m -> False |- _ ] =>
        is_not_var k
        ; assert (ChMaps.ChMap.Map.In k m)
          by (clear H; rewrite ChMaps.ChMap.F.in_find_iff; unfold not; intros; repeat solve_concrete_maps1)
        ; contradiction
      | [ H : ChMaps.ChMap.Map.In _ _ |- _ ] => rewrite ChMaps.ChMap.F.in_find_iff in H
      | [ H : ~ ChMaps.ChMap.Map.In _ _ |- _ ] => rewrite ChMaps.ChMap.F.not_find_in_iff in H
      | [ |- ~ ChMaps.ChMap.Map.In _ _ ] => rewrite ChMaps.ChMap.F.not_find_in_iff; try eassumption
      | [ H : ChMaps.ChMap.Map.In ?x ?xs -> False |- _ ] =>
        change (ChMaps.ChMap.Map.In x xs -> False) with (~ ChMaps.ChMap.Map.In x xs) in H

      | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)

      | [ |- _ $+ (?k1,_) $? ?k2 = _ ] =>
        is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2)
        ; destruct (k1 ==n k2); subst; try contradiction

      | [ |- _ #+ (?k1,_) #? ?k2 = _ ] =>
        is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2)
        ; destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst; try contradiction
                                           
      | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)

      | [ |- _ = _ ] => reflexivity
      | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros
      | [ |- _ #+ (_,_) = _ ] => apply ChMaps.ChMap.map_eq_Equal; unfold ChMaps.ChMap.Map.Equal; intros

      | [ |- Some _ = Some _ ] => f_equal
      | [ |- {| RealWorld.key_heap := _ |} = _ ] => f_equal
      | [ |- _ $? _ = _ ] => eassumption
      | [ |- _ #? _ = _ ] => eassumption

                             
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ $+ (_,_) $? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "destructing1 " k1 k2; destruct (k1 ==n k2); subst
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- (match _ $+ (_,_) $? _ with _ => _ end) $? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "destructing2 " k1 k2; destruct (k1 ==n k2); subst
      | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- _ #+ (_,_) #? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "#destructing1 " k1 k2; destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst
      | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- (match _ #+ (_,_) #? _ with _ => _ end) #? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "#destructing2 " k1 k2; destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst
      end.

  Ltac solve_concrete_maps := repeat solve_concrete_maps1.

  Ltac churn2 :=
    (repeat equality1); subst; rw_step1; intuition idtac; split_ex; intuition idtac; subst; try discriminate; solve_concrete_maps.

  Ltac churn :=
    repeat churn2.

  Ltac i_single_silent_step :=
      eapply IdealWorld.LStepBindProceed
    || eapply IdealWorld.LStepGen
    || eapply IdealWorld.LStepCreateChannel
  .

  Ltac r_single_silent_step :=
      eapply RealWorld.StepBindProceed
    || eapply RealWorld.StepGen
    (* || eapply RealWorld.StepRecvDrop *)
    || eapply RealWorld.StepEncrypt
    || eapply RealWorld.StepDecrypt
    || eapply RealWorld.StepSign
    || eapply RealWorld.StepVerify
    || eapply RealWorld.StepGenerateKey
  .

  Ltac pick_user uid :=
    match goal with
    | [ |- _ $? ?euid = Some _ ] => unify euid uid
    end; reflexivity.

  Ltac istep_univ uid :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..];
      (try eapply @eq_refl); (try f_equal); simpl.
  Ltac rstep_univ uid :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick_user uid | ..]; (try eapply @eq_refl); simpl.

  Ltac rw H :=
    (rewrite ChMaps.ChMap.F.add_neq_o in H by congruence)
    || (rewrite ChMaps.ChMap.F.add_eq_o in H by congruence).

  Ltac solve_ideal_step_stuff1 :=
    match goal with
    | [ H : context [ _ #+ (_,_) #? _ ] |- _ ] => progress (repeat rw H)
    | [ Heq : ?k = _, H : _ #+ (?k1,_) #? ?k2 = None |- _ ] =>
      match k2 with
      | # k => idtac k
      | _ => fail 1
      end;
      assert (k1 <> k2)
        by (destruct (ChMaps.ChMap.F.eq_dec k1 k2); clear Heq; try assumption;
            unfold ChMaps.ChannelType.eq in *; subst; ChMaps.ChMap.clean_map_lookups);
      ChMaps.ChMap.clean_map_lookups
    | [ H : # ?x = # ?y -> False |- _ ] => assert (x <> y) by congruence; clear H
    | [ |- Forall _ _ ] => econstructor
    | [ |- {| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _] => smash_universe; solve_concrete_maps
    | [ |- _ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}] => smash_universe; solve_concrete_maps
    | [ |- IdealWorld.screen_msg _ _ ] => econstructor
    | [ |- IdealWorld.permission_subset _ _ ] => econstructor
    | [ |- IdealWorld.check_perm _ _ _ ] => unfold IdealWorld.check_perm
    | [ |- ?m #? (# ?k) = None ] =>
      solve [ is_evar k; unify k (ChMaps.next_key_nat m); apply ChMaps.next_key_not_in; trivial ]
    | [ |- context [ ChMaps.next_key_nat ?m ]] =>
      match goal with
      | [ |- context [ IdealWorld.addMsg ] ] => unfold IdealWorld.addMsg; simpl
      | _ => 
        idtac "posing"
        ; pose proof (ChMaps.next_key_not_in m _ eq_refl)
        ; let k := fresh "k" in
          let Heq := fresh "Heq"
          in remember (ChMaps.next_key_nat m) as k eqn:Heq
      end
    (* | [ |- context [ match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end ] ] => *)
    (*   rewrite add_eq_o by trivial *)
    | [ |- context [ match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end] ] =>
      progress (
          repeat (
              ( rewrite add_eq_o by trivial)
              || (rewrite add_neq_o by solve_simple_ineq)
            )
        )
    | [ |- context [ #0 #? _ ]] => rewrite ChMaps.ChMap.lookup_empty_none
    | [ |- _ = _ ] => subst; reflexivity
    | [ |- context [ _ $? _ ] ] => progress solve_concrete_maps
    | [ |- context [ _ #? _ ] ] => progress solve_concrete_maps
    | [ H : match _ $+ (?k1,_) $? ?k2 with _ => _ end |- _ ] =>
      try (
          progress (
              repeat ((  rewrite add_eq_o in H by trivial)
                      || (rewrite add_neq_o in H by solve_simple_ineq)
                      || (rewrite lookup_empty_none in H))
        ))
      || destruct (k1 ==n k2); subst
    end; simpl.

  Ltac solve_ideal_step_stuff := repeat solve_ideal_step_stuff1.

  Ltac isilent_step_univ uid :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
    ((eapply IdealWorld.LStepBindRecur; i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2  ])
     || (i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2 ])).
  Ltac rsilent_step_univ uid :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
      ((eapply RealWorld.StepBindRecur; r_single_silent_step) || r_single_silent_step).

  Ltac single_silent_multistep usr_step := eapply TrcFront; [usr_step |]; simpl.
  Ltac single_silent_multistep3 usr_step := eapply Trc3Front; swap 1 2; [usr_step |..]; simpl; trivial.
  
  Ltac real_single_silent_multistep uid := single_silent_multistep3 ltac:(rsilent_step_univ uid).
  Ltac ideal_single_silent_multistep uid := single_silent_multistep ltac:(isilent_step_univ uid).

  Ltac figure_out_ideal_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        let p1 := constr:(IdealWorld.protocol usr1) in
        let p2 := constr:(IdealWorld.protocol usr2) in
        does_not_unify p1 p2; step_tac u
      end
    end.

  Ltac figure_out_real_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        let p1 := constr:(RealWorld.protocol usr1) in
        let p2 := constr:(RealWorld.protocol usr2) in
        does_not_unify p1 p2; step_tac u
      end
    end.

  Remove Hints TrcRefl TrcFront Trc3Refl Trc3Front : core.
  Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl : core.

  Remove Hints
         eq_sym (* includes_lookup *)
         trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat : core.

  Hint Constructors action_matches : core.
  Hint Resolve IdealWorld.LStepSend IdealWorld.LStepRecv' : core.

  Lemma TrcRefl' :
    forall {A} (R : A -> A -> Prop) x1 x2,
      x1 = x2 ->
      trc R x1 x2.
  Proof.
    intros. subst. apply TrcRefl.
  Qed.

  Lemma Trc3Refl' :
    forall {A B} (R : A -> B -> A -> Prop) x1 x2 P,
      x1 = x2 ->
      trc3 R P x1 x2.
  Proof.
    intros. subst. apply Trc3Refl.
  Qed.
  
  Ltac solve_refl :=
    solve [
        eapply TrcRefl
      | eapply TrcRefl'; simpl; eauto ].

  Ltac solve_refl3 :=
    solve [
        eapply Trc3Refl
      | eapply Trc3Refl'; simpl; smash_universe; solve_concrete_maps ].

  Ltac simpl_real_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ RealWorld.buildUniverse ] ] => progress (unfold RealWorld.buildUniverse; simpl)
      | [ |- context [ {| RealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      (* | [ |- context [ RealWorld.mkUniverse ?usrs _ _ _] ] => canonicalize_map usrs *)
      end.

  Ltac simpl_ideal_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ {| IdealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      end.

  Ltac rss_clean uid := real_single_silent_multistep uid; [ solve [eauto 3] .. |].

  Ltac ideal_silent_multistep :=
    simpl_ideal_users_context;
    match goal with
    | [ |- istepSilent ^* ?U1 ?U2 ] =>
      is_not_evar U1; is_not_evar U2;
      first [
          solve_refl
        | figure_out_ideal_user_step ideal_single_silent_multistep U1 U2 ]
    end.

  Ltac single_step_ideal_universe :=
    simpl_ideal_users_context;
    match goal with
    | [ |- IdealWorld.lstep_universe _ ?U1 _ ?U2] =>
      match U1 with
      | IdealWorld.construct_universe _ ?usrs1 =>
        match U2 with
        | IdealWorld.construct_universe _ ?usrs2 =>
          figure_out_ideal_user_step istep_univ usrs1 usrs2
        end
      end
    end.

  Ltac single_labeled_ideal_step uid :=
    eapply IdealWorld.LStepUser' with (u_id := uid);
    [ solve [ solve_concrete_maps ] | simpl | reflexivity ];
    eapply IdealWorld.LStepBindRecur;
    ( (eapply IdealWorld.LStepRecv'; solve [ solve_ideal_step_stuff ])
      || (eapply IdealWorld.LStepSend; solve [ solve_ideal_step_stuff ])).

  Ltac step_each_ideal_user U :=
    match U with
    | ?usrs $+ (?AB,_) =>
      idtac "stepping " AB; (single_labeled_ideal_step AB || step_each_ideal_user usrs)
    end.

  (* TODO: during canonicalization, cleanup the channels map *)
  Local Ltac blah1 :=
    match goal with
    | [ |- context [ IdealWorld.addMsg ]] => unfold IdealWorld.addMsg; simpl
    | [ |- context [ ?m #? _ ]] => progress unfold m
    | [ |- context [ _ #+ (?k1,_) #? ?k1 ]] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- context [ _ #+ (?k1,_) #? ?k2 ]] => rewrite ChMaps.ChMap.F.add_neq_o by congruence
    end.

  Ltac step_ideal_user :=
    match goal with
    | [ |- IdealWorld.lstep_universe _ _ (Action _) ?U' ] =>
      is_evar U'; simpl_ideal_users_context; (repeat blah1);
      match goal with
      | [ |- IdealWorld.lstep_universe
            {| IdealWorld.users := ?usrs; IdealWorld.channel_vector := _ |} _ _ ] =>
        step_each_ideal_user usrs
      end
    end.

  Ltac idealUserSilentStep :=
    (eapply IdealWorld.LStepBindRecur; i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2  ])
    || (i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2 ]).

  Ltac indexedIdealSilentStep :=
    econstructor; simpl; [ solve [ clean_map_lookups; trivial ]
                         | solve [ idealUserSilentStep ]
                         | reflexivity ].

  Ltac solve_indexed_silent_multistep :=
    simpl_ideal_users_context;
    eapply TrcFront; [ indexedIdealSilentStep |].

  Ltac unBindi :=
    match goal with
    | [ |- IdealWorld.lstep_user _ (Action _) (_,IdealWorld.Bind _ _,_) _ ] =>
      eapply IdealWorld.LStepBindRecur
    end.

  Ltac ideal_user_labeled_step :=
    simpl
    ; repeat unBindi
    ; match goal with
      | [ |- IdealWorld.lstep_user _ (Action _) (_,IdealWorld.Recv _,_) _ ] =>
        eapply IdealWorld.LStepRecv'; solve_ideal_step_stuff
      | [ |- IdealWorld.lstep_user _ (Action _) (_,IdealWorld.Send _ _,_) _ ] =>
        eapply IdealWorld.LStepSend; solve_ideal_step_stuff
      end.
  
  Ltac indexedIdealStep :=
    match goal with
    | [ |- indexedIdealStep _ (Action _) _ ?U' ] =>
      is_evar U'; simpl_ideal_users_context; (repeat blah1);
      econstructor; simpl; [ solve [ clean_map_lookups; trivial ]
                           | ideal_user_labeled_step
                           | reflexivity ]
    end.

  Hint Extern 1 ((indexedIdealStep _ Silent) ^* _ _) =>
    repeat solve_indexed_silent_multistep; solve_refl : core.

  Hint Extern 1 (indexedIdealStep _ (Action _) _ _) => indexedIdealStep : core.

  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_multistep : core.

  Hint Extern 1 ({| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _) => smash_universe; solve_concrete_maps : core.
  Hint Extern 1 (_ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}) => smash_universe; solve_concrete_maps : core.

  Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => step_ideal_user : core.
  
  Hint Extern 1 (List.In _ _) => progress simpl : core.
  Hint Extern 1 (~ In ?k ?m) =>
     solve_concrete_maps : core.

  Hint Extern 1 (action_adversary_safe _ _ _ = _) => unfold action_adversary_safe; simpl : core.
  Hint Extern 1 (IdealWorld.screen_msg _ _) => econstructor; progress simpl : core.

  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl : core.

  Hint Extern 1 (_ $+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  Hint Extern 1 (_ $? _ = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  Hint Extern 1 (_ #+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress ChMaps.m_equal) || (progress ChMaps.ChMap.clean_map_lookups) : core.
  Hint Extern 1 (_ #? _ = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress ChMaps.m_equal) || (progress ChMaps.ChMap.clean_map_lookups) : core.

  Local Ltac merge_perms_helper :=
    repeat match goal with
           | [ |- _ = _ ] => reflexivity
           | [ |- _ $? _ = _ ] => solve_concrete_maps
           end.
  
  Ltac solve_action_matches1 :=
    match goal with
    | [ |- content_eq _ _ _ ] => progress simpl
    | [ |- action_matches _ _ _ _ ] => progress simpl_real_users_context
    | [ |- action_matches _ _ _ _ ] => progress simpl_ideal_users_context
    | [ H : ?cs $? ?cid = Some (SigCipher _ _ _ _ )
        |- action_matches ?cs _ (_,RealWorld.Output (SignedCiphertext ?cid) _ _ _) _ ] => eapply OutSig
    | [ H : ?cs $? ?cid = Some (SigEncCipher _ _ _ _ _ )
        |- action_matches ?cs _ (_,RealWorld.Output (SignedCiphertext ?cid) _ _ _) _ ] => eapply OutEnc
    | [ H : ?cs $? ?cid = Some (SigCipher _ _ _ _ )
        |- action_matches ?cs _ (_,RealWorld.Input (SignedCiphertext ?cid) _ _) _ ] => eapply InpSig
    | [ H : ?cs $? ?cid = Some (SigEncCipher _ _ _ _ _ )
        |- action_matches ?cs _ (_,RealWorld.Input (SignedCiphertext ?cid) _ _) _ ] => eapply InpEnc
    | [ |- action_matches ?cs _ (_,RealWorld.Output (SignedCiphertext ?cid) _ _ _) _ ] =>
      match cs with
      | context [ _ $+ (cid, SigCipher _ _ _ _)] => eapply OutSig
      | context [_ $+ (cid, SigEncCipher _ _ _ _ _)] => eapply OutEnc
      end
    | [ |- action_matches ?cs _ (_,RealWorld.Input (SignedCiphertext ?cid) _ _) _ ] =>
      match cs with
      | context[ _ $+ (cid, SigCipher _ _ _ _)] => eapply InpSig
      | context[ _ $+ (cid, SigEncCipher _ _ _ _ _)] => eapply InpEnc
      end
    | [ H : _ $+ (?k1,_) $? ?k2 = Some ?d__rw |- context [ RealWorld.key_heap ?d__rw $? _ = Some _ ] ] =>
      is_var d__rw; is_var k2; is_not_var k1;
      destruct (k1 ==n k2); subst; clean_map_lookups; simpl
    | [ H : ?P $? _ = Some {| IdealWorld.read := _; IdealWorld.write := _ |} |- _ ] =>
      simpl in *; unfold P in H; solve_concrete_maps
    | [ |- _ $? _ = Some _ ] => progress solve_concrete_maps
    | [ |- context [ IdealWorld.addMsg ]] => unfold IdealWorld.addMsg; simpl
    | [ |- context [ ?m #? _ ]] => progress unfold m
    | [ |- context [ _ #+ (?k1,_) #? ?k1 ]] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- context [ _ #+ (?k1,_) #? ?k2 ]] => rewrite ChMaps.ChMap.F.add_neq_o by congruence
    | [ |- context [ IdealWorld.perm_intersection ] ] =>
      unfold IdealWorld.perm_intersection; simpl
    | [ H : _ $k++ _ $? _ = Some ?b |- context [ ?b ]] =>
      solve [ solve_perm_merges; solve_concrete_maps ]
    | [ |- _ $k++ _ $? _ = Some _ ] =>
      solve [ erewrite merge_perms_adds_ks1; (swap 2 4; merge_perms_helper) ]
      || solve [ erewrite merge_perms_adds_ks2; (swap 2 4; merge_perms_helper) ]
    | [ H : match _ $+ (?k1,_) $? ?k1 with _ => _ end = _ |- _ ] =>
      rewrite add_eq_o in H by trivial
    | [ H : match _ $+ (?k1,_) $? ?k2 with _ => _ end = _ |- _ ] =>
      rewrite add_neq_o in H by congruence
    | [ |- _ <-> _ ] => split
    | [ |- _ -> _ ] => intros
    | [ |- _ = _ ] => reflexivity
    | [ |- _ /\ _ ] => split
    | [ |- context [ _ $? _ ]] =>
      progress (
          repeat (
              (rewrite add_eq_o by trivial)
              || (rewrite add_neq_o by congruence)
              || (rewrite lookup_empty_none by congruence)
            )
        )
    end; split_ex; simpl in *.

  Hint Extern 1 (action_matches _ _ _ _) =>
    repeat (solve_action_matches1)
  ; NatMap.clean_map_lookups
  ; ChMaps.ChMap.clean_map_lookups : core.

  Hint Resolve
       findUserKeys_foldfn_proper
       findUserKeys_foldfn_transpose : core.
  
  Lemma findUserKeys_add_reduce :
    forall {A} (usrs : RealWorld.honest_users A) u_id ks p qmsgs mycs froms sents cur_n,
      ~ In u_id usrs
      -> RealWorld.findUserKeys (usrs $+ (u_id, {| RealWorld.key_heap := ks;
                                      RealWorld.protocol := p;
                                      RealWorld.msg_heap := qmsgs;
                                      RealWorld.c_heap := mycs;
                                      RealWorld.from_nons := froms;
                                      RealWorld.sent_nons := sents;
                                      RealWorld.cur_nonce := cur_n |})) = RealWorld.findUserKeys usrs $k++ ks.
  Proof.
    intros.
    unfold RealWorld.findUserKeys.
    rewrite fold_add; eauto.
  Qed.

  Lemma findUserKeys_empty_is_empty :
    forall A, @RealWorld.findUserKeys A $0 = $0.
  Proof. trivial. Qed.
  
  Hint Constructors RealWorld.msg_pattern_safe : core.

  Lemma reduce_merge_perms :
    forall perms1 perms2 kid perm1 perm2,
        perm1 = match perms1 $? kid with
                | Some p => p
                | None => false
                end
      -> perm2 = match perms2 $? kid with
                | Some p => p
                | None => false
                end
      -> (perms1 $? kid = None -> perms2 $? kid = None -> False)
      -> perms1 $k++ perms2 $? kid = Some (perm1 || perm2).
  Proof.
    intros; solve_perm_merges; subst; eauto.
    - rewrite orb_false_r; auto.
    - exfalso; eauto.
  Qed.
  
  Ltac solve_concrete_perm_merges :=
    repeat 
      match goal with
      | [ |- context [true || _]  ] => rewrite orb_true_l
      | [ |- context [_ || true]  ] => rewrite orb_true_r
      | [ |- context [$0 $k++ _] ] => rewrite merge_perms_left_identity
      | [ |- context [_ $k++ $0] ] => rewrite merge_perms_right_identity
      | [ |- context [_ $k++ _]  ] => erewrite reduce_merge_perms by (clean_map_lookups; eauto)
      end; trivial.

  Ltac simplify_terms :=
    unfold RealWorld.msg_honestly_signed
         , RealWorld.msg_signing_key
         , RealWorld.msg_to_this_user
         , RealWorld.msg_destination_user
         , RealWorld.cipher_signing_key
         , RealWorld.honest_keyb
         , RealWorld.cipher_nonce
         , add_key_perm.

  Ltac assert_lkp ks k tac :=
    let ev' := fresh "ev"
    in  evar (ev' : option bool);
        let ev := eval unfold ev' in ev'
          in (clear ev'
              ; match ks with
                | ?ks1 $k++ ?ks2 => assert (ks $? k = ev) by tac
                | _ => assert (ks $? k = ev) by tac
                end).

  Ltac bldLkup ks k tac :=
    match goal with
    | [ H : ks $? k = ?ans |- _ ] => idtac (* idtac "done with: " ks *)
    | _ => 
      match ks with
      | ?ks1 $k++ ?ks2 => (* idtac "splitting: " ks1 " and " ks2; *) bldLkup ks1 k tac; bldLkup ks2 k tac
      | _ => idtac (* "will build: " ks *)
      end; assert_lkp ks k tac
    end.

  Ltac prove_lookup :=
    solve [
        repeat
          match goal with
          | [ |- None = _ ] => reflexivity
          | [ |- Some _ = _ ] => reflexivity
          | [ |- $0 $? _ = _ ] => rewrite lookup_empty_none
          | [ |- ?ks $+ (?k1,_) $? ?k2 = _ ] =>
            (rewrite add_eq_o by trivial)
            || (rewrite add_neq_o by auto 2)
            || fail 2
          | [ |- ?m $? _ = _ ] => progress (unfold m)
          | [ H1 : ?ks1 $? ?kid = Some _
                   , H2 : ?ks2 $? ?kid = Some _ |- ?ks1 $k++ ?ks2 $? ?kid = _ ]
            => rewrite (merge_perms_chooses_greatest _ _ H1 H2) by trivial; unfold greatest_permission; simpl
          | [ H1 : ?ks1 $? ?kid = Some _
                   , H2 : ?ks2 $? ?kid = None |- ?ks1 $k++ ?ks2 $? ?kid = _ ]
            => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) by trivial
          | [ H1 : ?ks1 $? ?kid = None
                   , H2 : ?ks2 $? ?kid = Some _ |- ?ks1 $k++ ?ks2 $? ?kid = _ ]
            => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) by trivial
          | [ H1 : ?ks1 $? ?kid = None
                   , H2 : ?ks2 $? ?kid = None |- ?ks1 $k++ ?ks2 $? ?kid = _ ]
            => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) by trivial
          | [ H : ?ks1 $? ?kid = _ |- ?ks1 $k++ ?ks2 $? ?kid = _ ] =>
            assert_lkp ks2 kid prove_lookup
          | [ H : ?ks2 $? ?kid = _ |- ?ks1 $k++ ?ks2 $? ?kid = _ ] =>
            assert_lkp ks1 kid prove_lookup
          | [ |- ?ks1 $k++ ?ks2 $? ?kid = _ ] =>
            assert_lkp ks1 kid prove_lookup
            ; assert_lkp ks2 kid prove_lookup
          end
      ].

  Ltac solve_merges :=
    repeat
      match goal with
      | [ |- context [true || _]  ] => rewrite orb_true_l
      | [ |- context [_ || true]  ] => rewrite orb_true_r
      | [ |- context [ _ $k++ $0 ] ] => rewrite merge_perms_right_identity
      | [ |- context [ $0 $k++ _ ] ] => rewrite merge_perms_left_identity
      | [ RW : ?ks $? ?k = _ |- context [ ?ks $? ?k ] ] => rewrite RW
      | [ |- context [ ?ks $? ?k ] ] => (* idtac "building: " ks; *) bldLkup ks k prove_lookup
      end; trivial.

  Lemma reduce_merge_perms_r :
    forall perms1 perms2 kid p2,
      perms1 $? kid = None
      -> perms1 $k++ (perms2 $+ (kid,p2)) = perms1 $+ (kid,p2) $k++ (perms2 $- kid).
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros.
    cases (perms1 $? y);
      cases (perms2 $? y);
      destruct (kid ==n y); subst;
        clean_map_lookups.

    - erewrite !merge_perms_chooses_greatest; try reflexivity; clean_map_lookups; eauto.

    - erewrite merge_perms_adds_ks1 with (ks1 := perms1) (ks2 := perms2 $+ (kid, p2)); eauto.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (kid, p2)) (ks2 := perms2 $- kid); eauto.

    - erewrite merge_perms_adds_ks2 with (ks1 := perms1) (ks2 := perms2 $+ (y, p2)); eauto.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (y, p2)) (ks2 := perms2 $- y); eauto.

    - erewrite merge_perms_adds_ks2 with (ks1 := perms1) (ks2 := perms2 $+ (kid, p2) ); eauto.
      erewrite merge_perms_adds_ks2 with (ks1 := perms1 $+ (kid, p2)) (ks2 := perms2 $- kid); eauto.

    - erewrite merge_perms_adds_ks2 with (ks1 := perms1); eauto; clean_map_lookups; try reflexivity.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (y, p2)) (ks2 := perms2 $- y); eauto.

    - rewrite !merge_perms_adds_no_new_perms; eauto.

  Qed.

  Lemma reduce_merge_perms_both :
    forall perms1 perms2 kid p1 p2,
      perms1 $? kid = Some p1
      -> perms1 $k++ (perms2 $+ (kid,p2)) = perms1 $+ (kid,greatest_permission p1 p2) $k++ (perms2 $- kid).
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros.
    cases (perms1 $? y);
      cases (perms2 $? y);
      destruct (kid ==n y); subst;
        clean_map_lookups.

    - erewrite merge_perms_chooses_greatest; eauto; clean_map_lookups; try reflexivity.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (y, greatest_permission b p2)) (ks2 := perms2 $- y); eauto.

    - erewrite !merge_perms_chooses_greatest; try reflexivity; clean_map_lookups; trivial.

    - erewrite merge_perms_chooses_greatest; eauto; clean_map_lookups; try reflexivity.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (y, greatest_permission b p2)) (ks2 := perms2 $- y); eauto.

    - erewrite merge_perms_adds_ks1 with (ks1 := perms1) (ks2 := perms2 $+ (kid, p2)); eauto.
      erewrite merge_perms_adds_ks1 with (ks1 := perms1 $+ (kid, greatest_permission p1 p2)) (ks2 := perms2 $- kid); eauto.

    - erewrite merge_perms_adds_ks2 with (ks1 := perms1) (ks2 := perms2 $+ (kid, p2)); eauto.
      erewrite merge_perms_adds_ks2 with (ks1 := perms1 $+ (kid, greatest_permission p1 p2)) (ks2 := perms2 $- kid); eauto.

    - rewrite !merge_perms_adds_no_new_perms; eauto.

  Qed.

  Ltac xx := clean_map_lookups;
             try match goal with
                 | [ |- $0 $? _ = _ ] => rewrite lookup_empty_none
                 end;
             eauto.

  Ltac find_merge_rewrite ks1 ks2 :=
    match ks1 with
    | ?ks1' $k++ ?ks2' =>
      find_merge_rewrite ks1' ks2'
    | _ => match ks2 with
          | ?ks $+ (?k,?p) =>
            assert_lkp ks1 k xx
            ; match goal with
              | [ H : ks1 $? k = ?opt |- _ ] =>
                match opt with
                | Some ?p' =>
                  rewrite reduce_merge_perms_both with (perms1 := ks1) (perms2 := ks) (kid := k) (p1 := p') (p2 := p)
                | None =>
                  rewrite reduce_merge_perms_r with (perms1 := ks1) (perms2 := ks) (kid := k) (p2 := p)
                end
              end
          end
    end.

  Lemma remove_empty :
    forall k V, (@empty V) $- k = $0.
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros; eauto.
  Qed.

  Ltac elim_removes1 :=
    (rewrite !map_add_remove_eq by trivial)
    || (rewrite !map_add_remove_neq by eauto)
    || (rewrite !remove_empty).

  Ltac elim_removes := repeat elim_removes.

  Ltac reduce_merges :=
    repeat
      match goal with
      | [ |- context [true || _]  ] => rewrite orb_true_l
      | [ |- context [_ || true]  ] => rewrite orb_true_r
      | [ |- context [ _ $k++ $0 ] ] => rewrite merge_perms_right_identity
      | [ |- context [ $0 $k++ _ ] ] => rewrite merge_perms_left_identity
      | [ |- context [ _ $- _ ]] => elim_removes1
      | [ |- context [ ?ks1 $k++ ?ks2 ]] =>
        find_merge_rewrite ks1 ks2
      | [ RW : ?ks $? ?k = _ |- context [ ?ks $? ?k ] ] => rewrite RW
      end; trivial.

  Ltac has_key ks k :=
    match ks with
    | context [ _ $+ (k,_) ] => idtac
    end.
  
  Ltac solve_merges1 :=
    match goal with
    | [ H : Some _ = Some _ |- _ ] => injection H; subst
    | [ H : Some _ = None |- _ ] => discriminate H
    | [ H : None = Some _ |- _ ] => discriminate H
    | [ H : findKeysMessage _ $? _ = _ |- _ ] => progress (simpl in H)
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
    | [ |- _ = _ ] => (progress simpl) || reflexivity
    end.

  Ltac solve_honest_actions_safe1 :=
    solve_merges1 ||
    match goal with
    | [ H : _ = {| RealWorld.users := _;
                   RealWorld.adversary := _;
                   RealWorld.all_ciphers := _;
                   RealWorld.all_keys := _ |} |- _ ] => invert H

    | [ |- honest_cmds_safe _ ] => unfold honest_cmds_safe; intros; simpl in *
    | [ |- next_cmd_safe _ _ _ _ _ _ ] => unfold next_cmd_safe; intros
    | [ H : _ $+ (?id1,_) $? ?id2 = _ |- _ ] => is_var id2; destruct (id1 ==n id2); subst; clean_map_lookups
    | [ H : nextAction _ _ |- _ ] => invert H

    | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H; simpl in H
    | [ |- context [ RealWorld.findUserKeys ?usrs ] ] => canonicalize_map usrs
    | [ |- context [ RealWorld.findUserKeys _ ] ] =>
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty by eauto
    | [ H : RealWorld.findKeysMessage _ $? _ = _ |- _ ] => progress (simpl in H)
    | [ |- (_ -> _) ] => intros
    | [ |- context [ _ $+ (_,_) $? _ ] ] => progress clean_map_lookups
    | [ |- RealWorld.msg_pattern_safe _ _ ] => econstructor
    | [ |- RealWorld.honest_key _ _ ] => econstructor
    (* | [ |- context [_ $k++ _ ] ] => progress reduce_merges *)
    (* | [ |- context [_ $k++ _ $? _ ] ] => progress solve_merges *)
    | [ |- context [ ?m $? _ ] ] => unfold m
    | [ |- Forall _ _ ] => econstructor
    | [ |- exists x y, (_ /\ _)] => (do 2 eexists); repeat simple apply conj; eauto 2
    | [ |- _ /\ _ ] => repeat simple apply conj
    | [ |- ~ List.In _ _ ] => progress simpl
    | [ |- ~ (_ \/ _) ] => unfold not; intros; split_ors; subst; try contradiction
    | [ H : (_,_) = (_,_) |- _ ] => invert H
    end.

  Ltac solve_honest_actions_safe :=
    repeat (solve_honest_actions_safe1 || (progress simplify_terms) (* ; simpl; cbn *)).

  Ltac solve_labels_align :=
    (do 3 eexists); repeat (simple apply conj);
    [ solve [ eauto ]
    | indexedIdealStep; simpl
    | subst; repeat solve_action_matches1; clean_map_lookups; ChMaps.ChMap.clean_map_lookups
    ]; eauto; simpl; eauto.

End SimulationAutomation.

Import SimulationAutomation Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Ltac univ_equality1 :=
  match goal with
  | [ |- _ = _ ] => reflexivity
  | [ |- _ /\ _ ] => repeat simple apply conj
  | [ |- (_,_) = (_,_) ] => rewrite pair_equal_spec
  | [ |- {| RealWorld.users := _ |} = _ ] => eapply real_univ_eq_fields_eq
  | [ |- {| IdealWorld.users := _ |} = _ ] => eapply ideal_univ_eq_fields_eq
  end
  || ( progress m_equal )
  || ( progress ChMaps.m_equal ).

Ltac univ_equality := progress (repeat univ_equality1).

Ltac sets0 := Sets.sets ltac:(simpl in *
                              ; intuition (subst; auto; try congruence; try univ_equality; try linear_arithmetic)).
Ltac sets' :=
  propositional;
  try match goal with
      | [ |- @eq (?T -> Prop) _ _ ] =>
        change (T -> Prop) with (set T)
      end;
  try match goal with
      | [ |- @eq (set _) _ _ ] =>
        let x := fresh "x" in
        apply sets_equal; intro x;
        repeat match goal with
               | [ H : @eq (set _) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H;
                                               apply eq_iff in H
               end
      end; sets0;
  try match goal with
      | [ H : @eq (set ?T) _ _, x : ?T |- _ ] =>
        repeat match goal with
               | [ H : @eq (set T) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H;
                                               apply eq_iff in H
               end;
        solve [ sets0 ]
      end.

Tactic Notation "sets" := sets'.

Module SetLemmas.
  Lemma setminus_empty_subtr : forall {A} (s : set A),
      s \setminus {} = s.
  Proof. sets. Qed.

  Lemma setminus_empty_minu : forall {A} (s : set A),
      {} \setminus s = {}.
  Proof. sets. Qed.

  Lemma setminus_self : forall {A} (s : set A),
      s \setminus s = {}.
  Proof. sets. Qed.

  Lemma setminus_other : forall {A} (s1 s2 : set A),
      s1 \cap s2 = {} -> s1 \setminus s2 = s1.
  Proof. sets. Qed.

  Lemma setminus_distr_subtr : forall {A} (s1 s2 s3 : set A),
      (s1 \cup s2) \setminus s3 = (s1 \setminus s3) \cup (s2 \setminus s3).
  Proof. sets. Qed.

  Lemma setminus_distr_minu : forall {A} (s1 s2 s3 : set A),
      s1 \setminus (s2 \cup s3) = (s1 \setminus s2) \cap (s1 \setminus s3).
  Proof. sets. Qed.

  Lemma union_self : forall {A} (s : set A),
      s \cup s = s.
  Proof. sets. Qed.

  Lemma  union_self_thru : forall {A} (s1 s2 : set A), s1 \cup (s1 \cup s2) = s1 \cup s2.
  Proof. sets. Qed.

  Lemma union_empty_r : forall {A} (s : set A),
      s \cup {} = s.
  Proof. sets. Qed.

  Lemma union_empty_l : forall {A} (s : set A),
      {} \cup s = s.
  Proof. sets. Qed.

  Lemma intersect_self : forall {A} (s : set A),
      s \cap s = s.
  Proof. sets. Qed.

  Lemma intersect_empty_r : forall {A} (s : set A),
      s \cap {} = {}.
  Proof. sets. Qed.

  Lemma intersect_empty_l : forall {A} (s : set A),
      {} \cap s = {}.
  Proof. sets. Qed.
End SetLemmas.

Module Tacs.
  Import SetLemmas.

  Ltac simpl_sets1 disj_tac :=
    match goal with
    | [|- context[?s' \cup ?s']] =>
      rewrite union_self
        with (s := s')
    | [|- context[?s1' \cup (?s1' \cup ?s2')]] =>
      rewrite union_self_thru
        with (s1 := s1') (s2 := s2')
    | [|- context[?s' \cup {}]] =>
      rewrite union_empty_r
        with (s := s')
    | [|- context[{} \cup ?s']] =>
      rewrite union_empty_l
        with (s := s')
    | [|- context[?s' \cap ?s']] =>
      rewrite intersect_self
        with (s := s')
    | [|- context[?s' \cap {}]] =>
      rewrite intersect_empty_r
        with (s := s')
    | [|- context[{} \cap ?s']] =>
      rewrite intersect_empty_l
        with (s := s')
    | [|- context[?s' \setminus ?s']] =>
      rewrite setminus_self
        with (s := s')
    | [|- context[?s' \setminus {}]] =>
      rewrite setminus_empty_subtr
        with (s := s')
    | [|- context[{} \setminus ?s']] =>
      rewrite setminus_empty_minu
        with (s := s')
    | [|- context[(?s1' \cup ?s2') \setminus ?s3']] =>
      rewrite setminus_distr_subtr
        with (s1 := s1') (s2 := s2') (s3 := s3')
    | [|- context[?s1' \setminus (?s2' \cup ?s3')]] =>
      rewrite setminus_distr_minu
        with (s1 := s1') (s2 := s2') (s3 := s3')
    | [|- context[?s1' \setminus ?s2']] =>
      rewrite setminus_other
        with (s1 := s1') (s2 := s2') by disj_tac
    end.

  Ltac sets_invert :=
    repeat match goal with
           | [H : (_ \cup _) _ |- _] => invert H
           | [H : (_ \cap _) _ |- _] => invert H
           | [H : [_ | _] _ |- _] => invert H
           | [H : (_ \setminus _) _ |- _] => invert H
           | [H : _ \in _ |- _] => invert H
           | [H : (complement _) _ |- _] => invert H
           | [H : { } _ |- _] => invert H
           | [H : { _ } _ |- _] => invert H
           | [H : _ \/ False |- _ ] => destruct H; [ | contradiction]
           end.

  Ltac case_lookup H :=
    match type of H with
    | ?m $? ?k = Some ?v =>
      let t := type of v in
      repeat match m with
             | context[add ?k' ?v' _ ] =>
               let t' := type of v'
               in unify t t'
                  ; match goal with
                    | [e : k = k' |- _] => fail 2
                    | [n : k <> k' |- _] => fail 2
                    | _ => destruct (k ==n k')
                    end
             end
      ; subst
      ; simpl in *
      ; clean_map_lookups
      ; simpl in *
    end.

  Lemma map_sym : forall {v} (m : NatMap.t v) k1 k2 v1 v2,
      k1 <> k2
      -> m $+ (k1, v1) $+ (k2, v2) = m $+ (k2, v2) $+ (k1, v1).
  Proof. intros; maps_equal. Qed.

  Ltac reorder_usrs n :=
    repeat match n with
           | context[add ?a ?va (add ?b ?vb ?rest)] =>
             match eval cbv in (Nat.leb a b) with
               | true =>
                 rewrite map_sym
                   with (m := rest) (k1 := b) (k2 := a) (v1 := vb) (v2 := va)
                   by auto
             end
           end.

  Tactic Notation "simpl_sets" := repeat (simpl_sets1 ltac:(shelve)).
  Tactic Notation "simpl_sets" tactic(disj_tac) := repeat (simpl_sets1 ltac:(disj_tac)).

  Tactic Notation "ifnot" tactic(t) "at" int_or_var(lvl) := tryif t then fail lvl else idtac.
  Tactic Notation "ifnot" tactic(t) := ifnot t at 0.
  Tactic Notation "concrete" constr(x) "at" int_or_var(lvl) :=
    (ifnot (is_var x) at lvl); (ifnot (is_evar x) at lvl).
  Tactic Notation "concrete" constr(x) := concrete x at 0.
  Tactic Notation "concrete" "iuniv" constr(u) :=
    match u with
    | {| IdealWorld.channel_vector := ?cv
         ; IdealWorld.users := ?usrs |} =>
      concrete cv; concrete usrs
    end.
  Tactic Notation "concrete" "iproc" constr(p) :=
    match p with
    | (IdealWorld.protocol ?p) => concrete p at 1
    | _ => concrete p at 1
    end.

  Tactic Notation "canonicalize" "rusers" :=
    repeat match goal with
           | [|- context[{| RealWorld.users := ?usrs
                           ; RealWorld.adversary := _
                           ; RealWorld.all_ciphers := _
                           ; RealWorld.all_keys := _ |}]] =>
             progress canonicalize_concrete_map usrs
           end.

  Tactic Notation "canonicalize" "iusers" :=
    repeat match goal with
           | [|- context[{| IdealWorld.channel_vector := _
                           ; IdealWorld.users := ?usrs |}]] =>
             progress canonicalize_concrete_map usrs
           end.

  Tactic Notation "canonicalize" "users" :=
    canonicalize rusers; canonicalize iusers.

End Tacs.

Import Tacs.

Module Gen.
  Import
    SetLemmas.

  Hint Unfold oneStepClosure oneStepClosure_current oneStepClosure_new : osc.

  Lemma oneStepClosure_grow : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
      (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
      -> oneStepClosure sys inv1 (inv1 \cup inv2).
  Proof. sets; repeat autounfold with osc in *; propositional; eauto. Qed.

  Lemma msc_step_alt : forall {state} (sys : trsys state) wl wl' inv inv',
      oneStepClosure_new sys wl wl'
      -> wl' \cap (wl \cup inv) = { }
      -> multiStepClosure sys ((inv \cup wl) \cup wl') wl' inv'
      -> multiStepClosure sys (inv \cup wl) wl inv'.
  Proof.
    Ltac uf := repeat autounfold with osc in *.
    intros.
    apply MscStep with (inv'0 := (wl \cup wl')).
    - uf; sets; firstorder.
    - replace ((inv \cup wl) \cup (wl \cup wl'))
        with (inv \cup wl \cup wl') by sets.
      replace (((wl \cup wl') \setminus (inv \cup wl)))
        with wl' by sets.
      assumption.
  Qed.

  Lemma in_empty_map_contra : (forall {t} x, Map.In (elt := t) x $0 -> False).
  Proof. propositional. invert H. invert H0. Qed.

  Lemma incl_empty_empty : (forall {t}, @incl t [] []).
  Proof. cbv; auto. Qed.

  Hint Resolve
       (* in_empty_map_contra *)
       incl_empty_empty : core.

  Ltac concrete_isteps :=
    match goal with
    | [H : indexedIdealStep _ _ _ _ |- _ ] =>
      invert H
    | [H : (indexedIdealStep _ Silent)^* ?u _ |- _] =>
      concrete iuniv u; invert H
    | [H : istepSilent^* ?u _ |- _] =>
      concrete iuniv u; invert H
    | [H : istepSilent ?u _ |- _] =>
      concrete iuniv u; invert H
    | [H : IdealWorld.lstep_universe ?u _ _ |- _] =>
      concrete iuniv u; invert H
    | [H : IdealWorld.lstep_user _ _ (_, ?p, _) _ |- _] =>
      concrete iproc p; invert H
    end.

  Ltac simplify :=
    repeat (unifyTails);
    repeat match goal with
           | [ H : True |- _ ] => clear H
           end;
    repeat progress (simpl in *; intros; try autorewrite with core in *);
                     repeat (normalize_set || doSubtract).

  Ltac infer_istep :=
    match goal with
    | [H : IdealWorld.lstep_user _ _ (_, ?u.(IdealWorld.protocol), _) _,
           L : ?m $? ?u_id = Some ?u |- _] =>
      case_lookup L
    end.

  Ltac istep := repeat ((repeat concrete_isteps); try infer_istep).

  Ltac incorp :=
    let rec preconditions acc :=
        (match goal with
         | [H : ?P |- _] =>
           match type of P with
           | Prop =>
             match eval hnf in acc with
             | context[P] => fail 1
             | _ =>
               let acc' := eval hnf in (P /\ acc)
                 in preconditions acc'
             end
           end
         | _ => acc
         end)
    in let rec existentialize p :=
           (match goal with
            | [x : ?A |- _] =>
              match type of A with
              | Prop => fail 1
              | _ =>
                match A with
                | ((RealWorld.universe _ _) * (IdealWorld.universe _) * bool)%type =>
                  fail 2
                | _  =>
                  match p with
                  | context[x] =>
                    match eval pattern x in p with
                    | ?g _ =>
                      let p' := (eval hnf in (exists y : A, g y))
                      in existentialize p'
                    end
                  end
                end
              end
            | _ => p
            end)
       in let conds := (preconditions True) in
          match goal with
          | [|- ?i ?v] =>
            is_evar i
            ; let lp := constr:(exists x , conds /\ x = v) in
              let p := fresh "p" in
              let p' := fresh "p'" in
              let x := fresh "x" in
              assert (p : lp) by (eexists; intuition eauto)
              ; destruct p as [x p']
              ; let lp' := type of p'
                in clear p'
                   ; let lp'' := existentialize lp'
                     in match eval pattern x in lp'' with
                        | ?f _ =>
                          clear x
                          ; let scomp := (eval simpl in [e | (f e)])
                            in instantiate (1 := (scomp \cup _))
                        end
          end.

  Ltac solve_returns_align1 :=
    match goal with
    | [ H : users _ $? _ = Some _ |- _ ] => progress (simpl in H)
    | [ H1 : _ $? ?u = Some ?ud, H2 : protocol ?ud = Return _ |- _ ] =>
      progress (
          repeat (  (rewrite add_eq_o in H1 by trivial)
                    || (rewrite add_neq_o in H1 by congruence)
                    || (rewrite lookup_empty_none in H1; discriminate H1)
                 )
        )
    | [ H1 : _ $+ (?u1,_) $? ?u2 = Some ?ud, H2 : protocol ?ud = Return _ |- _ ] =>
      destruct (u1 ==n u2); subst
    | [ H1 : Some _ = Some ?ud, H2 : protocol ?ud = Return _ |- _ ] =>
      injection H1; subst
    | [ H : _ = Return _ |- _ ] =>
      discriminate H
    end.

  Ltac idealUnivSilentStep uid :=
    eapply IdealWorld.LStepUser with (u_id := uid)
    ; simpl
    ; [ solve [ clean_map_lookups; trivial ]
      | solve [ idealUserSilentStep ]
      ].

  Ltac step_ideal1 uid :=
    idtac "stepping " uid
    ; eapply TrcFront
    ; [ idealUnivSilentStep uid |].
  
  Ltac multistep_ideal usrs :=
    simpl_ideal_users_context;
    match usrs with
    | ?us $+ (?uid,_) =>
      idtac "multi stepping " uid
      ; (repeat step_ideal1 uid)
      ; multistep_ideal us
    | _ => eapply TrcRefl
    end.

  Ltac run_ideal_silent_steps_to_end :=
    simpl_ideal_users_context;
    match goal with
    | [ |- istepSilent ^* {| IdealWorld.users := ?usrs |} ?U ] =>
      is_evar U
      ; multistep_ideal usrs
    end.

  Ltac solve_real_step_stuff1 :=
    equality1
    || solve_merges1
    || match goal with
      | [ |- RealWorld.keys_mine _ _ ] =>
        simpl in *; hnf
      | [ |- ?m $? next_key ?m = None ] =>
        apply Maps.next_key_not_in
        ; trivial
      | [ |- ~ Map.In (next_key ?m) ?m ] =>
        rewrite not_find_in_iff
        ; apply Maps.next_key_not_in
        ; trivial
      | [ H : _ $+ (?k1,_) $? ?kid = Some _  |- context [ ?kid ] ] =>
        is_var kid
        ; destruct (k1 ==n kid); subst; clean_map_lookups
      | [ |- context [ $0 $? _ ]] =>
        rewrite lookup_empty_none
      | [ |- _ $? _ = _ ] =>
        clean_map_lookups
      | [ |- _ -> _ ] => intros
      | [ |- _ ] => ( progress simpl ) || ( progress hnf )
      end.
  
  Ltac solve_indexedRealStep :=
    repeat (match goal with [ |- exists _ , _ ] => eexists end)
    ; econstructor; [
      solve [ simpl; clean_map_lookups; trivial ]
    | autounfold; unfold RealWorld.build_data_step; simpl;
      repeat ( match goal with
               | [ |- RealWorld.step_user _ _ _ _ ] => solve [ eapply RealWorld.StepBindProceed; eauto ]
               | [ |- RealWorld.step_user _ _ _ _ ] => eapply RealWorld.StepBindRecur; eauto
               | [ |- RealWorld.step_user _ _ (_,_,?cs,?gks,_,_,_,_,_,_,?cmd) _ ] =>
                 match cmd with
                 | RealWorld.SignEncrypt _ _ _ _ =>
                   eapply RealWorld.StepEncrypt with (c_id := next_key cs)
                 | RealWorld.Sign _ _ _ =>
                   eapply RealWorld.StepSign with (c_id := next_key cs)
                 | RealWorld.GenerateKey _ _ => 
                   eapply RealWorld.StepGenerateKey with (k_id := next_key gks)
                 | _ => econstructor
                 end
               end
             )
      ; trivial (* take a first pass to get the simple stuff *)
      ; repeat (solve_real_step_stuff1; trivial)
      ; eauto

    | reflexivity ].

  Ltac find_indexed_real_step usrs uid :=
    match usrs with
    | ?us $+ (?u,_) =>
      (unify uid u; solve [ solve_indexedRealStep ])
      || find_indexed_real_step us uid
    | $0 =>
      fail 1
    end.

  (* note the automation here creates a bunch of extra existentials while 
   * doint the search for available steps.  This creates several nats
   * that need to be resolved at the end of proofs that use it.  
   * Should look at fixing this. *)
  Ltac find_step_or_solve :=
    simpl in *;
    match goal with
    | [ H1 : forall _ _ _, indexedRealStep _ _ ?ru _ -> False
        , H2 : ?usrs $? _ = Some ?ur
        , H3 : RealWorld.protocol ?ur = RealWorld.Return _ |- _ ] =>

      ( assert (exists uid lbl ru', indexedRealStep uid lbl ru ru')
        by (eexists ?[uid]; (do 2 eexists); find_indexed_real_step usrs ?uid)
        ; split_ex; exfalso; eauto
      )
      || ( repeat solve_returns_align1
          ; ( (do 3 eexists); simpl in *; (repeat equality1) 
              ; subst
              ; repeat simple apply conj
              ; [ solve [ run_ideal_silent_steps_to_end ]
                | solve [ simpl; clean_map_lookups; trivial ]
                | reflexivity
                | reflexivity
                ]
        ))
    end.

  Ltac invert_commutes :=
    match goal with
    | [ H : commutes (RealWorld.Recv _) _ |- _ ] => invert H
    | [ H : commutes (RealWorld.Send _ _) _ |- _ ] => invert H
    | [ H : commutes _ _ |- _ ] => fail 2
    end.

  Ltac non_commuter uid :=
    exists uid; eexists; repeat simple apply conj; [
        congruence
      | solve [ autounfold; simpl; clean_map_lookups; trivial ]
      | solve [ intros; simpl; trivial] ].

  Ltac non_commuter_all uids :=
    match uids with
    | [] => fail 2
    | (?uid :: ?uids') => (non_commuter uid) || (non_commuter_all uids')
    end.

  Ltac non_commuters := non_commuter_all [0;1;2;3;4;5].

  Ltac discharge_nextStep2 :=
    repeat 
      match goal with
      | [ H : (forall _ _, ~ indexedRealStep ?uid _ ?ru _)
            \/ (exists _ _, ?uid <> _ /\ _ $? _ = Some _ /\ (forall _, ?sums $? _ = Some _ -> commutes ?proto _ -> False))
          |- _ ] => split_ex; exfalso; destruct H
      | [ H : (forall _ _, ~ indexedRealStep ?uid _ ?ru _), ARG : indexedRealStep ?uid _ ?ru _ |- _ ] =>
        eapply H in ARG; contradiction
      | [ H : summarize_univ ?ru ?sums, 
         ARG : (forall _, ?sums $? ?uid = Some _ -> commutes _ _),
         USR :  _ $? ?uid = Some _
          |- _ ] =>
        specialize (H _ _ {| sending_to := { } |} USR); split_ex
      | [ H : ?sums $? ?uid = Some _,
          COMM : (forall _, ?sums $? ?uid = Some _ -> commutes _ _)
          |- _ ] =>
        specialize (COMM _ H); simpl in COMM; contradiction
      end.

  Lemma upper_users_cant_step_rewrite :
    forall A B (U : RealWorld.universe A B) uid,
      (forall uid' ud' U', U.(RealWorld.users) $? uid' = Some ud' -> uid' > uid -> ~ indexedRealStep uid' Silent U U')
      -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent U U').
  Proof.
    intros * H * INEQ.
    unfold not; intros IRS.
    invert IRS; eauto.
    eapply H; eauto.
  Qed.

  Lemma sstep_inv_silent :
    forall A B (U U' : RealWorld.universe A B) uid U__i b st',
      indexedRealStep uid Silent U U'
      -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent U U')
      -> stepSS (U,U__i,b) st'
      -> exists U__r,
          indexedModelStep uid (U,U__i,b) (U__r,U__i,b)
          /\ indexedRealStep uid Silent U U__r
          /\ st' = (U__r,U__i,b).
  Proof.
    intros.
    invert H1; repeat equality1.
    destruct (u_id ==n uid); subst.
    - invert H2; clear_mislabeled_steps; clean_map_lookups.
      invert H5; clear_mislabeled_steps.
      eexists; eauto 8.
    - invert H2.
      + invert H5; try solve [ clear_mislabeled_steps ].
        apply not_eq in n; split_ors.
        * assert (uid > u_id) as GT by lia.
          specialize (H4 _ U' GT); contradiction.
        * assert (u_id > uid) as GT by lia.
          specialize (H0 _ ru' GT); contradiction.
      + eapply H3 in H; contradiction.
  Qed.

  Lemma sstep_inv_labeled :
    forall A B st st' ru,
      (forall uid U', ~ @indexedRealStep A B uid Silent ru U')
      -> @stepSS A B st st'
      -> labels_align st
      -> forall ru' iu iu' b b',
          st = (ru,iu,b)
          -> st' = (ru',iu',b')
          -> b = b'
            /\ (exists uid iu0 ra ia, 
                  indexedRealStep uid (Action ra) ru ru'
                  /\ (indexedIdealStep uid Silent) ^* iu iu0
                  /\ indexedIdealStep uid (Action ia) iu0 iu'
                  /\ action_matches (RealWorld.all_ciphers ru) (RealWorld.all_keys ru) (uid,ra) ia).
  Proof.
    intros; subst.
    invert H0; clear_mislabeled_steps.
    repeat equality1.

    invert H2.
    specialize (H u_id U'); simpl in *; contradiction.

    invert H5; try contradiction; eauto 12.
    clear_mislabeled_steps.
  Qed.

  Ltac rstep :=
    repeat (autounfold
            ; equality1
              || (progress ( simpl in * ))
              || discriminate
              || match goal with
                | [H : action_matches _ _ _ _ |- _] =>
                  invert H
                | [ H : forall _ _ _, _ -> _ -> _ -> _ <-> _ |- _ ] => clear H
                | [ H : forall _ _ _ _, _ -> _ -> _ -> _ -> _ <-> _ |- _ ] => clear H
                | [ H : (forall _ _ _, indexedRealStep _ _ ?ru _ -> exists _ _ _, (indexedIdealStep _ _) ^* ?iu _ /\ _) |- _ ] =>
                  clear H
                | [ H : summarize_univ _ _ |- _ ] => clear H

                | [H : indexedRealStep _ _ _ _ |- _ ] =>
                  invert H
                | [H : RealWorld.step_universe _ ?u _ _ |- _] =>
                  concrete u; churn
                | [H : RealWorld.step_user _ None _ _ |- _] =>
                  invert H
                | [H : RealWorld.step_user _ _ ?u _ |- _] =>
                  concrete u; churn
                end).

  Ltac prove_gt_pred :=
    intros
    ; simpl in *
    ; repeat 
        match goal with
        | [ H : context [ _ $+ (_,_) $- _ ] |- _ ] =>
          repeat (
              (rewrite map_add_remove_neq in H by congruence)
              || (rewrite map_add_remove_eq in H by trivial)
              || (rewrite remove_empty in H)
            )
        | [ H : _ $+ (?uid,_) $? ?uid' = Some _ |- _ ] =>
          destruct (uid ==n uid'); subst; clean_map_lookups; try lia
        | [ |- ~ indexedRealStep _ _ _ _ ] => unfold not; intros; rstep
        end.

  Ltac assert_gt_pred U uid :=
    let P := fresh "P"
    in assert (forall uid' ud' U', U.(RealWorld.users) $? uid' = Some ud'
                              -> uid' > uid
                              -> ~ indexedRealStep uid' Silent U U') as P by prove_gt_pred
       ; pose proof (upper_users_cant_step_rewrite P); clear P
  .

  Ltac assert_no_silents U :=
    let P := fresh "P"
    in assert (forall uid U', ~ indexedRealStep uid Silent U U') as P by prove_gt_pred
  .

  Ltac find_silent U us :=
    let MAX := fresh "MEQ"
    in  remember (O.max_elt us) eqn:MAX
        ; unfold O.max_elt in MAX
        ; simpl in MAX
        ; match type of MAX with
          | _ = Some (?uid,?u) =>
            ( ( assert (exists U', indexedRealStep uid Silent U U') by solve_indexedRealStep
                ; assert_gt_pred U uid)
              || find_silent U (us $- uid)
            ) || assert_no_silents U
          end
        ; subst; split_ex
  .

  Ltac inv_stepSS1 :=
    match goal with
    | [ STEP : stepSS (?U,_,_) _
      , IRS : indexedRealStep ?uid Silent ?U _
      , P : (forall _ _, _ > ?uid -> _)
        |- _ ] =>

      pose proof (sstep_inv_silent IRS P STEP)
      ; clear STEP IRS P
      ; split_ex
      ; subst

    | [ STEP : stepSS (?ru,?iu,?b) _
      , P : (forall _ _, ~ indexedRealStep _ Silent _  _)
        |- _ ] =>

      progress ( unfold not in P )

    | [ STEP : stepSS (?ru,?iu,?b) (_,_,_)
      , P : (forall _ _, indexedRealStep _ Silent _ _ -> False)
        |- _ ] =>

      concrete ru
      ; match goal with
        | [ LA : labels_align (?ru,?iu,?b) |- _ ] =>
          pose proof (sstep_inv_labeled P STEP LA eq_refl eq_refl )
          ; split_ex; subst
          ; clear STEP P LA

        | _ =>
          idtac "proving alignment 4"
          ; assert (labels_align (ru,iu,b)) by ((repeat prove_alignment1); eauto)
        end

    | [ STEP : stepSS ?st ?st'
      , P : (forall _ _, indexedRealStep _ Silent _ _ -> False)
        |- _ ] =>

      match st with
      | (_,_,_) => idtac
      | _ => destruct st as [[?ru ?iu] ?b]
      end
      ; match st' with
        | (_,_,_) => idtac
        | _ => destruct st' as [[?ru' ?iu'] ?b']
        end

    | [ H : stepSS (?U,_,_) _ |- _ ] =>
      match U with
      | {| RealWorld.users := ?usrs |} =>
        find_silent U usrs
      end
        
    | [ IMS : indexedModelStep ?uid (?U,_,_) _
      , IRS : indexedRealStep ?uid _ ?U _ 
        |- _ ] => clear IMS

    end.

  Ltac step_model1 :=
    match goal with
    | [H : Step _ _ _ |- _] =>
      simpl in H
    | [H : exists _, _ |- _] =>
      destruct H; split_ex; subst (* invert H; propositional; subst *)
    | [ H : nextAction _ _ |- _ ] =>
      progress (simpl in H)
    | [ H : nextAction ?cmd1 ?cmd2 |- _ ] =>
      is_var cmd2;
      match cmd1 with (* doubt this is general enough *)
      | (RealWorld.protocol ?ud) => concrete ud || fail 1
      | _ => concrete cmd1
      end; invert H

    | [ H : O.max_elt _ = Some _ |- _ ] => 
      unfold O.max_elt in H; simpl in H; invert H
    | [H : In _ $0 |- _] =>
      apply in_empty_map_contra in H; contradiction
      (* invert H *)
    | [H : Raw.PX.MapsTo _ _ $0 |- _] =>
      invert H
    | [H : (existT _ _ _) = (existT _ _ _) |- _] =>
      invert H

    | [ S : step ?st ?st' |- _ ] =>
      concrete st; is_var st';
      match st' with
      | (_,_,_) => fail 2
      | (?f,_) => destruct f as [?ru ?iu]
      | _ => destruct st' as [[?ru ?iu] ?b]
      end
    | [ S : step ?st _ |- _ ] =>
      concrete st;
      match goal with
      | [ LA : labels_align ?st |- _ ] =>
        eapply label_align_step_split in S; (reflexivity || eauto 2); split_ex; split_ors; split_ex; subst
      | _ =>
        idtac "proving alignment 1"; assert (labels_align st) by ((repeat prove_alignment1); eauto)
      end
    | [ S : stepC ?st _ |- _ ] =>
      concrete st; invert S

    | [ H : nextStep _ _ _ |- _ ] => invert H
    | [ S : indexedModelStep ?uid ?st _ |- _ ] =>
      concrete st;
      match goal with
      | [ LA : labels_align ?st |- _ ] =>
        eapply label_align_indexedModelStep_split in S; (reflexivity || eauto 2); split_ex; split_ors; split_ex; subst
      | _ =>
        idtac "proving alignment 2"; assert (labels_align st) by ((repeat prove_alignment1); eauto)
      end
    | [ H : (forall _ _, ~ indexedRealStep ?uid _ ?ru _)
          \/ (exists _ _, ?uid <> _ /\ _ $? _ = Some _ /\ (forall _, ?sums $? _ = Some _ -> commutes ?proto _ -> False))
      , S : summarize_univ ?ru ?sums
        |- _ ] =>
      ( (assert (exists lbl ru', indexedRealStep uid lbl ru ru') by solve_indexedRealStep )
      ; (assert (exists uid2 ud2, uid <> uid2
                           /\ ru.(RealWorld.users) $? uid2 = Some ud2
                           /\ (forall s, sums $? uid2 = Some s -> commutes proto s)) by non_commuters ))
      ; discharge_nextStep2 (* clear this goal since the preconditions weren't satisfied *)
    end.

  Ltac gen_val_typ t :=
    match t with
    | Nat    => constr:(0)
    | Bool   => constr:(true)
    | Unit   => constr:(tt)
    | Access => constr:((0,false))
    | (TPair ?t1 ?t2) =>
      let v1 := gen_val_typ t1 in
      let v2 := gen_val_typ t2
      in constr:((v1,v2))
                  
    end.

  Ltac gen_msg t :=
    match t with
    | Access => let v := gen_val_typ Access in constr:(message.Permission v)
    | Nat    => let v := gen_val_typ Nat in constr:(message.Content v)
    | (TPair ?t1 ?t2) =>
      let m1 := gen_msg t1 in
      let m2 := gen_msg t2 in
      constr:(message.MsgPair m1 m2)
    end.

  Ltac gen_crypto t :=
    let m := gen_msg t in constr:(Content m).

  Ltac gen_val_cmd_typ ct :=
    match ct with
    | Base ?t    => gen_val_typ t
    | Message ?t => gen_msg t
    | Crypto ?t  => gen_crypto t
    | UPair ?t1 ?t2 =>
      let v1 := gen_val_cmd_typ t1 in
      let v2 := gen_val_cmd_typ t2 in constr:((v1,v2))
    end.

  (* We have to be careful here when inverting the model checking terms.  If we run injection
   * on universes which only differ in their protocols, it seems that this fact gets erased.
   * I am not entirely sure why this happens.  For this reason, we carefully do the inversions
   * here manually rather than running injection.
   * 
   *)
  Ltac univ_equality_discr :=
    discriminate ||
    match goal with
    | [ H : RealWorld.Bind _ _ = RealWorld.Bind _ _ |- _ ] =>
      apply invert_bind_eq in H; split_ex
    | [ H1 : ?x = ?y1, H2 : ?x = ?y2 |- _ ] =>
      rewrite H1 in H2
      ; clear H1
    | [ H1 : ?x = ?y1, H2 : ?y2 = ?x |- _ ] =>
      rewrite H1 in H2
      ; clear H1
    | [ H : (?x1,?y1) = (?x2,?y2) |- _ ] =>
      apply tuple_eq_inv in H; split_ex; subst
    | [ H : {| users := _ |} = {| users := _ |} |- _ ] =>
      apply split_real_univ_fields in H; split_ex
    | [ H : Some _ = Some _ |- _ ] =>
      apply some_eq_inv in H; split_ex; subst
    | [ H : {| key_heap := _ |} = {| key_heap := _ |} |- _ ] =>
      apply split_real_user_data_fields in H; split_ex; subst
    | [ H : _ $+ (_,_) = _ |- _ ] =>
      apply map_eq_fields_eq in H; clean_map_lookups
    | [ H : << ?t >> -> _ = _ |- _ ] =>
      let vt := gen_val_cmd_typ t
      in specialize (H vt)
    end.

  Ltac tidy :=
    autounfold
    ; intros
    ; sets_invert
    ; propositional
    ; subst
    ; clean_map_lookups
    ; subst
    ; idtac "discriminating univ - tidy"
    ; repeat (
          univ_equality_discr
          (* equality has to run after univ equality discrimination because equality1 uses injeection
           * which isn't always safe to use on universes.  See comment on univ_equality_discr 
           *)
          || equality1   
          || inv_stepSS1
          || step_model1
        )
    ; idtac "discriminating univ - tidy done"
  .

  Ltac s := simpl in *.

  Ltac cleanup :=
    repeat (
        equality1
        || match goal with
          | [ H : True |- _ ] => clear H
          | [ H : ?X = ?X |- _ ] => clear H
          | [ H : ?x <> ?y |- _ ] =>
            match type of x with
            | nat => concrete x; concrete y; clear H
            end
          | [ H : ?x = ?y -> False |- _ ] =>
            match type of x with
            | nat => concrete x; concrete y; clear H
            end
          | [ H: RealWorld.keys_mine _ $0 |- _ ] => clear H
          | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
              (rewrite add_neq_o in H by solve_simple_ineq)
            || (rewrite add_eq_o in H by trivial)
            || (destruct (k1 ==n k2); subst)
          | [ H : context [ ChMaps.ChannelType.eq _ _ ] |- _ ] => unfold ChMaps.ChannelType.eq in H
          | [ H : _ #+ (?k1,_) #? ?k2 = None |- _ ] =>
              (rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq)
            || (rewrite ChMaps.ChMap.F.add_eq_o in H by trivial)
            || (destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst)

          | [ H : context [ _ #+ (?k,_) #? ?k ] |- _ ] =>
            is_not_evar k
            ; rewrite ChMaps.ChMap.F.add_eq_o in H by trivial
          | [ H : context [ _ #+ (?k1,_) #? ?k2 ] |- _ ] =>
            is_not_evar k1
            ; is_not_evar k2
            ; rewrite ChMaps.ChMap.F.add_neq_o in H by congruence
          | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H; simpl in H
          | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => clear H
          | [ H : ~ RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => clear H
          | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ -> False |- _ ] => clear H
          | [ H : IdealWorld.screen_msg _ _ |- _ ] => invert H
          | [ H : IdealWorld.permission_subset _ _ |- _ ] => invert H
          | [ H : IdealWorld.check_perm _ _ _ |- _ ] => unfold IdealWorld.check_perm in H
          | [ H : context [ IdealWorld.addMsg _ _ _ ] |- _ ] => unfold IdealWorld.addMsg in H; simpl in H
          | [ H : Forall _ [] |- _ ] => clear H
          | [ H : context [true || _]  |- _] => rewrite orb_true_l in H
          | [ H : context [_ || true]  |- _] => rewrite orb_true_r in H
          | [ H : context [false || _]  |- _] => rewrite orb_false_l in H
          | [ H : context [_ || false]  |- _] => rewrite orb_false_r in H
          | [ H : context [$0 $k++ _] |- _] => rewrite merge_perms_left_identity in H
          | [ H : context [_ $k++ $0] |- _] => rewrite merge_perms_right_identity in H
          | [ H : context [_ $k++ _]  |- _] =>
            erewrite reduce_merge_perms in H by (clean_map_lookups; eauto)
          | [ H : context [_ $k++ _]  |- _] =>
            unfold merge_perms, add_key_perm, fold in H; simpl in H; clean_map_lookups

          | [ H : context [ _ $+ (?k1,_) $? ?k2] |- _ ] =>
              (rewrite add_neq_o in H by solve_simple_ineq)
            || (rewrite add_eq_o in H by trivial)
          | [ H : context [ ?m $? _ ] |- _ ] =>
            progress (unfold m in H)

          | [ |- context [$0 $k++ _] ] => rewrite !merge_perms_left_identity
          | [ |- context [_ $k++ $0] ] => rewrite !merge_perms_right_identity 
          end
      ).

  Ltac close :=
    match goal with
    | [|- [_ | _] (?ru, ?iu, _)] =>
      concrete ru
      ; concrete iuniv iu
      ; tidy
      (* ; repeat( progress (subst; cleanup) ) *)
      ; repeat eexists
      ; propositional
      ; solve[ eauto
             | canonicalize users
               ; repeat univ_equality1 ]
    | [|- (?inv1 \cup ?inv2) (?ru, ?iu, _)] =>
      concrete inv1
      ; concrete ru
      ; concrete iuniv iu
      ; solve[ idtac "trying left"; left; close
             | idtac "left fails; trying right"; right; close
             | idtac "something is horribly wrong" (* prevent an infinite loop *)
             ]
    | [|- ?inv (?ru, ?iu, _)] =>
      is_evar inv
      ; concrete ru
      ; concrete iuniv iu
      ; repeat equality1
      ; solve_concrete_maps
      ; canonicalize users
      ; clean_context
      ; repeat( progress (subst; cleanup) )
      (* ; cleanup *)
      ; NatMap.clean_map_lookups
      ; ChMaps.ChMap.clean_map_lookups
      ; incorp
      ; solve[ close ]
    end.

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

  Locate intersect_empty_l.

  Ltac normalize_set_arg s :=
    match s with
    | context[@union ?A ?X ?Y] =>
      quote (@union A X Y) (@nil A)
            ltac:(fun e env =>
                    change (@union A X Y) with (interp_setexpr env e));
      rewrite <- normalize_setexpr_ok; sets_cbv
    end.

  Ltac gen1 :=
    match goal with
    | [|- multiStepClosure _ _ { } _] =>
      eapply MscDone
    | [|- multiStepClosure _ {(_,_,_)} {(_,_,_)} _] =>
      eapply MscStep
      ; [ solve[ apply oneStepClosure_grow; repeat gen1' ]
        | simplify; simpl_sets (sets; tidy)]
    | [|- multiStepClosure _ (?pr \cup ?wl) ?wl _] =>
      progress ( normalize_set_arg pr ; normalize_set_arg wl )
    | [|- multiStepClosure _ (_ \cup ?wl) ?wl _] =>
      eapply msc_step_alt
      ; [ solve[ unfold oneStepClosure_new; repeat gen1' ]
        | solve[ idtac "proving empty intersection"
                 ; simplify
                 ; sets
                 ; split_ex
                 ; propositional
                 ; idtac "preparing to discriminate universes"
                 (* equality has to run after univ equality discrimination because equality1 uses injeection
                  * which isn't always safe to use on universes.  See comment on univ_equality_discr 
                  *)
                 ; repeat (univ_equality_discr || equality1)
                 ; idtac "universes discriminated"
               | eapply intersect_empty_l]
        | rewrite ?union_empty_r ]
    end.

  (* Use this to generate the invariant *)
  Ltac gen := repeat gen1.

  Ltac discr_sets :=
    simplify
    ; sets
    ; split_ex

    (* equality has to run after univ equality discrimination because equality1 uses injeection
     * which isn't always safe to use on universes.  See comment on univ_equality_discr 
     *)
    ; repeat (univ_equality_discr || equality1).

  Ltac dedup_worklist wl k :=
    let rec dedup_wl acc wl :=
        idtac "iterating";
        match wl with
        | ?s1 \cup ?s2 =>
          ( assert ( acc \cap s1 = { } ) by discr_sets
            ; dedup_wl (acc \cup s1) s2 )
          || dedup_wl acc s2
        | ?s => 
          ( assert ( acc \cap s = { } ) by discr_sets
            ; k (acc \cup s) )
          || k acc
        end

    in idtac "wl";
       match wl with
       | { } \cup ?s  => dedup_worklist s k
       | ?s1 \cup ?s2 => dedup_wl s1 s2
       | ?s1          => k s1
       end.

End Gen.
                     
(* Helps with initial universe state proofs *)
Ltac focus_user :=
  repeat
    match goal with
    | [ H : _ $+ (?k1,_) $? ?k2 = Some ?v |- _ ] =>
      is_var v;
      match type of v with
      | RealWorld.user_data _ => idtac
      end; destruct (k1 ==n k2); subst; clean_map_lookups
    end.

