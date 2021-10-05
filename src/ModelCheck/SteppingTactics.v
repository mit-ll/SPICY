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
     Keys
     Maps
     Messages
     MessageEq
     RealWorld
     Simulation
     Tactics

     Theory.KeysTheory

     ModelCheck.ModelCheck
     ModelCheck.ProtocolFunctions
     ModelCheck.RealWorldStepLemmas
     ModelCheck.UniverseInversionLemmas
.

From SPICY Require
     IdealWorld
     RealWorld
     ChMaps
.

Import ChMaps.ChMapNotation
       ChMaps.ChNotation.

Set Implicit Arguments.

Ltac simple_clean_maps1 :=
  match goal with
  | [ H : Some _ = None |- _ ] => discriminate H
  | [ H : None = Some _ |- _ ] => discriminate H
  | [ H : Some _ = Some _ |- _ ] => apply some_eq_inv in H; subst
  | [ H : _ $+ (_,_) $? _ = _ |- _ ] =>
    progress (
      repeat ( (rewrite add_eq_o in H by trivial)           
             || (rewrite add_neq_o in H by congruence)
             || (rewrite lookup_empty_none in H) ))
  | [ H : $0 $? _ = _ |- _ ] => rewrite lookup_empty_none in H
  | [ |- _ $+ (_,_) $? _ = _ ] =>
    progress (
      repeat ( (rewrite add_eq_o by trivial)           
             || (rewrite add_neq_o by congruence)
             || (rewrite lookup_empty_none) ))
  | [ |- $0 $? _ = _ ] =>
    rewrite lookup_empty_none
  | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
  | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
    destruct (k1 ==n k2); subst
  end.

Ltac simple_clean_maps := repeat simple_clean_maps1.

Ltac equality1 :=
  invert_base_equalities1
  || simple_clean_maps1
  || match goal with
    | [ H : List.In _ _ |- _ ] => progress (simpl in H); (* intuition idtac *) split_ors

    | [ H : _ $? _ = Some _ |- _ ] => progress (simpl in H)
    | [ H : _ #? _ = Some _ |- _ ] => progress (simpl in H)

    | [ H : _ $+ (_,_) $? _ = Some ?UD |- _ ] =>
      match type of UD with
      | RealWorld.user_data _ => apply lookup_some_implies_in in H; simpl in H
      | _ => apply lookup_split in H; (* intuition idtac *) split_ors
      end
    | [ H : _ #+ (_,_) #? _ = Some ?UD |- _ ] =>
      apply ChMaps.ChMap.lookup_split in H; (* intuition idtac *) split_ors

    | [ H : _ = {| RealWorld.users := _ |} |- _ ]
      => apply split_real_univ_fields in H; split_ex; subst
    | [ |- RealWorld.protocol (RealWorld.adversary _) = RealWorld.Return _ ] => simpl
    | [ H : lameAdv _ ?adv |- RealWorld.protocol ?adv = _ ] => unfold lameAdv in H; eassumption

    | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => progress (simpl in H)

    | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => inversion H; clear H

    | [ H : Action _ = Action _ |- _ ] =>
      injection H; subst
      (* apply action_eq_inv in H; subst *)
    (* | [ H : Silent = Action _ |- _ ] => discriminate H *)
    (* | [ H : Action _ = Silent |- _ ] => discriminate H *)
    | [ H : RealWorld.Return _ = RealWorld.Return _ |- _ ] => apply invert_return in H

    | [ H: RealWorld.SignedCiphertext _ = RealWorld.SignedCiphertext _ |- _ ] =>
      injection H; subst
      (* apply ct_eq_inv in H; split_ex; subst *)
    | [ H: RealWorld.SigCipher _ _ _ _ = RealWorld.SigCipher _ _ _ _ |- _ ] =>
      injection H; subst
      (* apply sigcphr_eq_inv in H; split_ex; subst *)
    | [ H: RealWorld.SigEncCipher _ _ _ _ _ = RealWorld.SigEncCipher _ _ _ _ _ |- _ ] =>
      injection H; subst
      (* apply enccphr_eq_inv in H; split_ex; subst *)
    | [ H : _ = RealWorld.Output _ _ _ _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
    | [ H : RealWorld.Output _ _ _ _ = _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
    | [ H : _ = RealWorld.Input _ _ _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
    | [ H : RealWorld.Input _ _ _ = _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
    | [ H : MkCryptoKey _ _ _ = _ |- _ ] => apply key_eq_inv in H; split_ex; subst

    | [ H: _ = {| IdealWorld.read := _ |} |- _ ] => injection H
    | [ H: {| IdealWorld.read := _ |} = _ |- _ ] => injection H

    | [ H : keyId _ = _ |- _] => inversion H; clear H
    end.

Module SimulationAutomation.

  #[export] Hint Constructors RealWorld.msg_accepted_by_pattern : core.
  #[export] Hint Extern 1 (_ $k++ _ $? _ = Some _) => solve [ solve_perm_merges ] : core.

  Module T.
    Import RealWorld.

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
      (* | Bind _ _ => apply step_user_inv_bind in H; split_ands; split_ors; split_ands; subst; try discriminate *)
      | Bind _ _ => apply step_user_inv_bind in H; destruct H; split_ex; subst; try discriminate
      | Gen => apply step_user_inv_gen in H
      | Send _ _ => apply step_user_inv_send in H
      | Recv _ => apply step_user_inv_recv in H; split_ex; subst
                 ; try (process_message_queue; idtac "processed message quque")
      | SignEncrypt _ _ _ _ => apply step_user_inv_enc in H
      | Decrypt _ => apply step_user_inv_dec in H
      | Sign _ _ _ => apply step_user_inv_sign in H
      | Verify _ _ => apply step_user_inv_verify in H
      | GenerateKey _ _ => apply step_user_inv_genkey in H
      | realServer 0 _ _ => rewrite realserver_done in H
      | realServer _ _ _ => erewrite unroll_realserver_step in H by reflexivity
      | _ => idtac "***Missing inversion: " cmd; invert H
      end; split_ex; subst.

    Ltac step_usr_id uid :=
      match goal with
      | [ H : RealWorld.step_user _ (Some uid) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        step_usr_hyp H cmd
      end; split_ors; split_ex; subst.

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
      | [ H : _ $+ (?k1,_) $? ?k2 = Some _ |- _ ] => destruct (k1 ==n k2); subst
      | [ H : step_user (Action _) (Some ?uid) _ _ |- _ ] =>
        progress (autounfold in H; unfold RealWorld.build_data_step in H; simpl in H)
      | [ H : step_user _ (Some ?u) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u; is_not_evar u;
        step_usr_hyp H cmd
      | [ |- exists _ _ _, _ ] => simpl; (do 3 eexists); repeat simple apply conj
      end.

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
    (* clean_map_lookups1 *)
    simple_clean_maps1
    || ChMaps.ChMap.clean_map_lookups1
    || match goal with
      | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H; simpl in H

      | [ H : ?m $? _ = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m #? _ = _ |- _ ] => progress (unfold m in H)
      | [ |- context [ ?m $? _ ] ] => progress (unfold m)
      | [ |- context [ ?m #? _ ] ] => progress (unfold m)

      | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- _ ] =>
        progress ( repeat ( rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq ) )
      (* | [ |- context [ _ $+ (?kid2,_) $? ?kid1 ] ] => *)
      (*   progress ( repeat ( rewrite add_neq_o by solve_simple_ineq ) ) *)
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
    (repeat equality1); subst; split_ors; try contradiction; rw_step1.
    (* (repeat equality1); subst; rw_step1; intuition idtac; split_ex; intuition idtac; subst; try discriminate; solve_concrete_maps. *)

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

  Ltac smash_universe :=
  unfold RealWorld.buildUniverse;
  repeat (match goal with
          | [ |- {| RealWorld.users := _
                 ; RealWorld.adversary := _
                 ; RealWorld.all_ciphers := _
                 ; RealWorld.all_keys := _ |} = _
            ] => eapply real_univ_eq_fields_eq
          | [ |- {| IdealWorld.users := _;
                   IdealWorld.channel_vector := _ |} = _
            ] => eapply ideal_univ_eq_fields_eq
          | [ |- _ = _ ] => reflexivity
          end).

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

  #[export] Remove Hints TrcRefl TrcFront Trc3Refl Trc3Front : core.
  #[export] Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl : core.

  #[export] Remove Hints
         eq_sym (* includes_lookup *)
         trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat : core.

  #[export] Hint Constructors action_matches : core.
  #[export] Hint Resolve IdealWorld.LStepSend IdealWorld.LStepRecv' : core.

  Ltac solve_refl :=
    solve [
        eapply TrcRefl
      | eapply TrcRefl'; simpl; eauto ].

  Ltac simpl_real_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ RealWorld.buildUniverse ] ] => progress (unfold RealWorld.buildUniverse; simpl)
      | [ |- context [ {| RealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      end.

  Ltac simpl_ideal_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ {| IdealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      end.

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
    ; (try match goal with
           | [ |- IdealWorld.lstep_user _ (Action _) (_,idealServer 0 _ _,_) _ ] =>
             rewrite idealserver_done
           | [ |- IdealWorld.lstep_user _ (Action _) (_,idealServer _ _ _,_) _ ] =>
             erewrite unroll_idealserver_step by reflexivity
           end)
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

  #[export] Hint Extern 1 ((indexedIdealStep _ Silent) ^* _ _) =>
    repeat solve_indexed_silent_multistep; solve_refl : core.

  #[export] Hint Extern 1 (indexedIdealStep _ (Action _) _ _) => indexedIdealStep : core.

  #[export] Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_multistep : core.

  #[export] Hint Extern 1 ({| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _) => smash_universe; solve_concrete_maps : core.
  #[export] Hint Extern 1 (_ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}) => smash_universe; solve_concrete_maps : core.

  #[export] Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => step_ideal_user : core.
  
  #[export] Hint Extern 1 (List.In _ _) => progress simpl : core.
  #[export] Hint Extern 1 (~ In ?k ?m) =>
     solve_concrete_maps : core.

  #[export] Hint Extern 1 (action_adversary_safe _ _ _ = _) => unfold action_adversary_safe; simpl : core.
  #[export] Hint Extern 1 (IdealWorld.screen_msg _ _) => econstructor; progress simpl : core.

  #[export] Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl : core.

  #[export] Hint Extern 1 (_ $+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  #[export] Hint Extern 1 (_ $? _ = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  #[export] Hint Extern 1 (_ #+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress ChMaps.m_equal) || (progress ChMaps.ChMap.clean_map_lookups) : core.
  #[export] Hint Extern 1 (_ #? _ = _) =>
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

  #[export] Hint Extern 1 (action_matches _ _ _ _) =>
    repeat (solve_action_matches1)
  ; clean_map_lookups
  ; ChMaps.ChMap.clean_map_lookups : core.

  #[export] Hint Constructors RealWorld.msg_pattern_safe : core.

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
    [ solve [ eauto 3 ]
    | indexedIdealStep; simpl
    | subst; repeat solve_action_matches1; clean_map_lookups; ChMaps.ChMap.clean_map_lookups
    ]; eauto 3; simpl; eauto.

End SimulationAutomation.

Import SimulationAutomation.

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

Module Tacs.

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
  #[export] Hint Resolve
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
    | [H : IdealWorld.lstep_user _ _ (_, idealServer 0 _ _, _) _ |- _] =>
      rewrite idealserver_done in H by reflexivity
    | [H : IdealWorld.lstep_user _ _ (_, idealServer _ _ _, _) _ |- _] =>
      erewrite unroll_idealserver_step in H by reflexivity
    | [H : IdealWorld.lstep_user _ _ (_, ?p, _) _ |- _] =>
      concrete iproc p; invert H
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

  Ltac infer_istep :=
    match goal with
    | [H : IdealWorld.lstep_user _ _ (_, ?u.(IdealWorld.protocol), _) _,
           L : ?m $? ?u_id = Some ?u |- _] =>
      case_lookup L
    end.

  Ltac istep := repeat ((repeat concrete_isteps); try infer_istep).

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
    ; [ solve [ simple_clean_maps; trivial ]
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
    || (progress subst)
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
        ; destruct (k1 ==n kid); subst; simple_clean_maps
      | [ |- context [ $0 $? _ ]] =>
        rewrite lookup_empty_none
      (* | [ |- _ $? _ = _ ] => *)
      | [ |- context [ _ $? _ = _ ] ] =>
        progress (
            repeat ( (rewrite add_eq_o by trivial)           
                     || (rewrite add_neq_o by congruence)
                     || (rewrite lookup_empty_none) ))
        (* progress simple_clean_maps *)
      | [ |- _ -> _ ] => intros
      | [ |- _ ] => ( progress simpl ) || ( progress hnf )
      end.

  Ltac doRealStep :=
    repeat 
      match goal with
      | [ |- RealWorld.step_user _ _ (_,RealWorld.Bind (RealWorld.Return _) _) _ ] =>
        apply RealWorld.StepBindProceed
      | [ |- RealWorld.step_user _ _ (_,RealWorld.Bind _ _) _ ] =>
        apply RealWorld.StepBindRecur
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
      end.
  
  Ltac solve_indexedRealStep :=
    repeat (match goal with [ |- exists _ , _ ] => eexists end)
    ; econstructor; [
      solve [ simpl; simple_clean_maps; trivial ]
    | solve [ autounfold; unfold RealWorld.build_data_step; simpl
              ; doRealStep
              ; trivial (* take a first pass to get the simple stuff *)
              ; repeat (solve_real_step_stuff1; trivial)
              ; eauto ]
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

  (* Lemma sstep_inv_silent : *)
  (*   forall A B (U U' : RealWorld.universe A B) uid U__i b st', *)
  (*     indexedRealStep uid Silent U U' *)
  (*     -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent U U') *)
  (*     -> stepSS (U,U__i,b) st' *)
  (*     -> exists U__r, *)
  (*         indexedModelStep uid (U,U__i,b) (U__r,U__i,b) *)
  (*         /\ indexedRealStep uid Silent U U__r *)
  (*         /\ st' = (U__r,U__i,b). *)
  (* Proof. *)
  (*   intros. *)
  (*   invert H1; repeat equality1. *)
  (*   destruct (u_id ==n uid); subst. *)
  (*   - invert H2; clear_mislabeled_steps; clean_map_lookups. *)
  (*     invert H5; clear_mislabeled_steps. *)
  (*     eexists; eauto 8. *)
  (*   - invert H2. *)
  (*     + invert H5; try solve [ clear_mislabeled_steps ]. *)
  (*       apply not_eq in n; split_ors. *)
  (*       * assert (uid > u_id) as GT by lia. *)
  (*         specialize (H4 _ U' GT); contradiction. *)
  (*       * assert (u_id > uid) as GT by lia. *)
  (*         specialize (H0 _ ru' GT); contradiction. *)
  (*     + eapply H3 in H; contradiction. *)
  (* Qed. *)

  (* Lemma sstep_inv_labeled : *)
  (*   forall A B st st' ru, *)
  (*     (forall uid U', ~ @indexedRealStep A B uid Silent ru U') *)
  (*     -> @stepSS A B st st' *)
  (*     -> labels_align st *)
  (*     -> forall ru' iu iu' b b', *)
  (*         st = (ru,iu,b) *)
  (*         -> st' = (ru',iu',b') *)
  (*         -> b = b' *)
  (*           /\ (exists uid iu0 ra ia,  *)
  (*                 indexedRealStep uid (Action ra) ru ru' *)
  (*                 /\ (indexedIdealStep uid Silent) ^* iu iu0 *)
  (*                 /\ indexedIdealStep uid (Action ia) iu0 iu' *)
  (*                 /\ action_matches (RealWorld.all_ciphers ru) (RealWorld.all_keys ru) (uid,ra) ia). *)
  (* Proof. *)
  (*   intros; subst. *)
  (*   invert H0; clear_mislabeled_steps. *)
  (*   repeat equality1. *)

  (*   invert H2. *)
  (*   specialize (H u_id U'); simpl in *; contradiction. *)

  (*   invert H5; try contradiction; eauto 12. *)
  (*   clear_mislabeled_steps. *)
  (* Qed. *)

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

  (* Ltac inv_stepSS1 := *)
  (*   match goal with *)
  (*   | [ H : stepSS (?U,_,_) _ |- _ ] => *)
  (*     match U with *)
  (*     | {| RealWorld.users := ?usrs |} => *)
  (*       find_silent U usrs *)
  (*     end *)

  (*   | [ STEP : stepSS (?U,_,_) _ *)
  (*     , IRS : indexedRealStep ?uid Silent ?U _ *)
  (*     , P : (forall _ _, _ > ?uid -> _) *)
  (*       |- _ ] => *)

  (*     pose proof (sstep_inv_silent IRS P STEP) *)
  (*     ; clear STEP IRS P *)
  (*     ; split_ex *)
  (*     ; subst *)

  (*   | [ STEP : stepSS (?ru,?iu,?b) _ *)
  (*     , P : (forall _ _, ~ indexedRealStep _ Silent _  _) *)
  (*       |- _ ] => *)

  (*     progress ( unfold not in P ) *)

  (*   | [ STEP : stepSS (?ru,?iu,?b) (_,_,_) *)
  (*     , P : (forall _ _, indexedRealStep _ Silent _ _ -> False) *)
  (*       |- _ ] => *)

  (*     concrete ru *)
  (*     ; match goal with *)
  (*       | [ LA : labels_align (?ru,?iu,?b) |- _ ] => *)
  (*         pose proof (sstep_inv_labeled P STEP LA eq_refl eq_refl ) *)
  (*         ; split_ex; subst *)
  (*         ; clear STEP P LA *)

  (*       | _ => *)
  (*         idtac "proving alignment 4" *)
  (*         ; assert (labels_align (ru,iu,b)) by ((repeat prove_alignment1); eauto) *)
  (*       end *)

  (*   | [ STEP : stepSS ?st ?st' *)
  (*     , P : (forall _ _, indexedRealStep _ Silent _ _ -> False) *)
  (*       |- _ ] => *)

  (*     match st with *)
  (*     | (_,_,_) => idtac *)
  (*     | _ => destruct st as [[?ru ?iu] ?b] *)
  (*     end *)
  (*     ; match st' with *)
  (*       | (_,_,_) => idtac *)
  (*       | _ => destruct st' as [[?ru' ?iu'] ?b'] *)
  (*       end *)

  (*   | [ H : stepSS (?U,_,_) _ |- _ ] => *)
  (*     match U with *)
  (*     | {| RealWorld.users := ?usrs |} => *)
  (*       find_silent U usrs *)
  (*     end *)
        
  (*   | [ IMS : indexedModelStep ?uid (?U,_,_) _ *)
  (*     , IRS : indexedRealStep ?uid _ ?U _  *)
  (*       |- _ ] => clear IMS *)

  (*   end. *)

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
