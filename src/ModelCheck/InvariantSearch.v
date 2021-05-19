(*
 * © 2021 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Lia.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     Keys
     Tactics
     Simulation

     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
     ModelCheck.SilentStepElimination
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

Import Tacs Gen.

Set Implicit Arguments.

Open Scope protocol_scope.

Ltac eq1 :=
  invert_base_equalities1
  || match goal with
    | [ H : List.In _ _ |- _ ] => unfold List.In in H; intuition idtac

    | [ H : _ $+ (_,_) $? _ = Some ?UD |- _ ] =>
      match type of UD with
      | RealWorld.user_data _ =>
        apply lookup_some_implies_in in H; (* unfold List.In in H; intuition idtac *) simpl in H
      | _ => apply lookup_split in H; intuition idtac
      end
    | [ H : _ #+ (_,_) #? _ = Some ?UD |- _ ] =>
      apply ChMaps.ChMap.lookup_split in H; intuition idtac

    | [ H : _ = {| RealWorld.users := _ |} |- _ ]
      => apply split_real_univ_fields in H; split_ex; subst
    | [ |- RealWorld.protocol (RealWorld.adversary _) = RealWorld.Return _ ] =>
      unfold RealWorld.protocol, RealWorld.adversary
    | [ H : lameAdv _ ?adv |- RealWorld.protocol ?adv = _ ] => unfold lameAdv in H; eassumption

    | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => unfold RealWorld.users in H

    | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => inversion H; clear H

    | [ H : Action _ = Action _ |- _ ] =>
      injection H; subst
    | [ H : RealWorld.Return _ = RealWorld.Return _ |- _ ] => apply invert_return in H

    | [ H: RealWorld.SignedCiphertext _ = RealWorld.SignedCiphertext _ |- _ ] =>
      injection H; subst
    | [ H: RealWorld.SigCipher _ _ _ _ = RealWorld.SigCipher _ _ _ _ |- _ ] =>
      injection H; subst
    | [ H: RealWorld.SigEncCipher _ _ _ _ _ = RealWorld.SigEncCipher _ _ _ _ _ |- _ ] =>
      injection H; subst
    | [ H : _ = RealWorld.Output _ _ _ _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
    | [ H : RealWorld.Output _ _ _ _ = _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
    | [ H : _ = RealWorld.Input _ _ _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
    | [ H : RealWorld.Input _ _ _ = _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
    | [ H : MkCryptoKey _ _ _ = _ |- _ ] => apply key_eq_inv in H; split_ex; subst

    | [ H: _ = {| IdealWorld.read := _ |} |- _ ] => injection H
    | [ H: {| IdealWorld.read := _ |} = _ |- _ ] => injection H

    | [ H : keyId _ = _ |- _] => inversion H; clear H
    end.

Lemma lookup_in_merge_perm :
  forall kid (m m' : key_perms),
    m $k++ m' $? kid = match m $? kid with
                       | Some p => match m' $? kid with
                                  | Some p' => Some (greatest_permission p p')
                                  | None => Some p
                                  end
                       | None => m' $? kid
                       end.
Proof.
  intros; cases (m $? kid); cases (m' $? kid); solve_perm_merges.
Qed.

Ltac ch := (repeat equality1); subst; rw_step1.
(* Ltac ch := (repeat equality1); subst; rw_step1. *)
Ltac chu := repeat ch.

Ltac finish_honest_cmds_safe1 :=
    (* (progress solve_concrete_perm_merges) || *)
    match goal with
    (* from solve_concrete_perm_merges *)
    | [ |- context [true || _]  ] => rewrite orb_true_l
    | [ |- context [_ || true]  ] => rewrite orb_true_r
    | [ |- context [$0 $k++ _] ] => rewrite merge_perms_left_identity
    | [ |- context [_ $k++ $0] ] => rewrite merge_perms_right_identity

    | [ H : _ = {| RealWorld.users := _;
                   RealWorld.adversary := _;
                   RealWorld.all_ciphers := _;
                   RealWorld.all_keys := _ |} |- _ ] => invert H

    | [ |- honest_cmds_safe _ ] => unfold honest_cmds_safe; intros; simpl in *
    | [ |- next_cmd_safe _ _ _ _ _ _ ] => unfold next_cmd_safe; intros
    | [ H : _ $+ (?id1,_) $? ?id2 = _ |- _ ] =>
      is_var id2; destruct (id1 ==n id2); subst; clean_map_lookups
    | [ H : nextAction _ _ |- _ ] => invert H

    | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H; simpl in H
    (* | [ |- context [ RealWorld.findUserKeys ?usrs ] ] => canonicalize_map usrs *)
    | [ |- context [ RealWorld.findUserKeys _ ] ] =>
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty by eauto
    | [ H : RealWorld.findKeysMessage _ $? _ = _ |- _ ] =>
      unfold RealWorld.findKeysMessage in H; simpl in H
    | [ |- (_ -> _) ] => intros
    | [ |- context [ _ $+ (_,_) $? _ ] ] => progress clean_map_lookups
    | [ |- context [ _ $+ (_,_) $? _ ] ] =>
      progress (
          repeat (
              (rewrite add_neq_o by solve_simple_ineq)
              || (rewrite add_eq_o by trivial)
              || (rewrite lookup_empty_none)
        ))
               
    | [ H : _ $k++ _ $? ?k = Some _ |- context [ _ $? ?k ]] => (*  *)
        apply merge_perms_split in H; destruct H
    | [ |- context [ _ $k++ _ $? _ ] ] => rewrite !lookup_in_merge_perm
    | [ |- RealWorld.msg_pattern_safe _ _ ] => econstructor
    | [ |- RealWorld.honest_key _ _ ] => econstructor
    | [ |- context [ ?m $? _ ] ] => unfold m
    | [ |- Forall _ _ ] => econstructor
    | [ |- exists x y, (_ /\ _)] => (do 2 eexists); repeat simple apply conj; eauto 2
    | [ |- _ /\ _ ] => repeat simple apply conj
    | [ |- ~ List.In _ ?lst ] =>
      match lst with
      | context [OrderedTypeEx.Nat_as_OT.compare ?x ?x] =>
        let EQ := fresh "EQ" in
        let RW := fresh "RW"
        in pose proof (@OTF.elim_compare_eq x x eq_refl) as EQ; destruct EQ as [EQ RW]
           ; rewrite RW
           ; progress vm_compute
      | _ =>  progress vm_compute
      end
    | [ |- ~ (_ \/ _) ] => unfold not; intros; split_ors; subst; try contradiction
    | [ H : context [ _ \/ False ] |- False ] =>
      destruct H; try contradiction
    | [ H : (_,_) = (_,_) |- _ ] => invert H
    end.

Ltac finish_honest_cmds_safe :=
  repeat (finish_honest_cmds_safe1 || (progress simplify_terms) (* ; simpl; cbn *)).

Definition safety_inv :=
  fun t__hon t__adv st => @safety t__hon t__adv st /\ alignment st /\ @returns_align t__hon t__adv st.

#[export] Hint Opaque safety_inv.

Definition can_con_map {V} (m : Map.t V) : Map.t V.
  let m' := eval simpl in (fold (fun k v acc => acc $+ (k, v)) m $0)
    in apply m'.
Defined.

Lemma can_con_map_correct : forall {V} (m : Map.t V),
    can_con_map m = m.
Proof.
  induction m using P.map_induction_bis; intros; Equal_eq; eauto.
  unfold can_con_map.
  rewrite fold_add; eauto.
  fold (can_con_map m).
  rewrite IHm; trivial.
  Morphisms.solve_proper.
  unfold transpose_neqkey; intros.
  maps_equal.
Qed.

Ltac ccm m H :=
  replace m with (can_con_map m) in H by apply can_con_map_correct
  ; try match goal with
        | [ H : context [ can_con_map ?cm ] |- _ ] =>
          (unfold can_con_map,fold in H; simpl in H)
        end.

Ltac ccmag m :=
  replace m with (can_con_map m) by apply can_con_map_correct
  ; match goal with
    | [ |- context [ can_con_map ?cm ] ] =>
      (unfold can_con_map,fold); simpl
    end.

Ltac rwuf :=
  unfold RealWorld.buildUniverse, RealWorld.build_data_step
  , RealWorld.key_heap, RealWorld.msg_heap, RealWorld.c_heap
  , RealWorld.from_nons, RealWorld.sent_nons, RealWorld.cur_nonce
  , RealWorld.protocol, RealWorld.all_keys, RealWorld.all_ciphers
  , RealWorld.users, RealWorld.adversary
  in *.

Tactic Notation "canonicalize" "context" :=
  rwuf
  ; try
      match goal with
      | [ H : stepSS (?ru,?iu,_) _ |- _ ] =>
        match ru with
        | context [{| RealWorld.users := ?usrs |}] =>
          ccm usrs H
        end
        ; match iu with
          | context [{| IdealWorld.users := ?usrs |}] => 
            ccm usrs H
          end
      | [ H : (stepSS (t__adv:=_)) ^* (?ru,?iu,_) _ |- _ ] =>
        match ru with
        | context [{| RealWorld.users := ?usrs |}] =>
          ccm usrs H
        end
        ; match iu with
          | context [{| IdealWorld.users := ?usrs |}] => 
            ccm usrs H
          end
      end.

Tactic Notation "canonicalize" "ideal" "goal" :=
  rwuf
  ; match goal with
    | [ |- context [{| IdealWorld.users := ?usrs |}]] => ccmag usrs
    end.

Ltac idealUnivSilentStep' uid :=
  eapply IdealWorld.LStepUser with (u_id := uid)
  ; simpl
  ; [ solve [ clean_map_lookups; trivial ]
    | solve [ idealUserSilentStep ]
    ].

Ltac step_ideal1' uid :=
  idtac "stepping " uid
  ; eapply TrcFront
  ; [ idealUnivSilentStep' uid |].

(* Ltac simpl_ideal_users_context := *)
(*   simpl; *)
(*   repeat *)
(*     match goal with *)
(*     | [ |- context [ {| IdealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs *)
(*     end. *)

Ltac multistep_ideal' usrs :=
  canonicalize ideal goal;
  match usrs with
  | ?us $+ (?uid,_) =>
    idtac "multi stepping " uid
    ; (repeat step_ideal1' uid)
    ; multistep_ideal' us
  | _ => eapply TrcRefl
  end.

Ltac run_ideal_silent_steps_to_end' :=
  canonicalize ideal goal;
  match goal with
  | [ |- istepSilent ^* {| IdealWorld.users := ?usrs |} ?U ] =>
    is_evar U
    ; multistep_ideal' usrs
  end.

(* note the automation here creates a bunch of extra existentials while 
 * doint the search for available steps.  This creates several nats
 * that need to be resolved at the end of proofs that use it.  
 * Should look at fixing this. *)
Ltac find_step_or_solve' :=
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
        ; ( (do 3 eexists); simpl in *; (repeat eq1) 
            ; subst
            ; repeat simple apply conj
            ; [ solve [ run_ideal_silent_steps_to_end' ]
              | solve [ simpl; clean_map_lookups; trivial ]
              | reflexivity
              | reflexivity
              ]
      ))
  end.

Ltac finish_invariant :=
  rwuf
  ; try match goal with
    | [ |- context [{| RealWorld.users := ?users |} ]] =>
      ccmag users
    end
  ; unfold safety_inv, safety, alignment, returns_align
  ; repeat simple apply conj
  ; [ finish_honest_cmds_safe; clean_map_lookups; eauto 8
    | trivial
    | unfold labels_align; intros; rstep; subst; solve_labels_align
    | try solve [ intros; find_step_or_solve' ]
    ].

Ltac invSS1 :=
  discriminate
  || match goal with
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

    | [ H : action_matches _ _ _ _ |- _] => invert H
    | [ H : forall _ _ _, _ -> _ -> _ -> _ <-> _ |- _ ] => clear H
    | [ H : forall _ _ _ _, _ -> _ -> _ -> _ -> _ <-> _ |- _ ] => clear H
    | [ H : (forall _ _ _, indexedRealStep _ _ ?ru _ ->
                      exists _ _ _, (indexedIdealStep _ _) ^* ?iu _ /\ _) |- _ ] =>
      clear H

    | [H : indexedRealStep _ _ _ _ |- _ ] =>
      invert H
    | [H : RealWorld.step_universe _ ?u _ _ |- _] =>
      concrete u; chu
    | [H : RealWorld.step_user _ None _ _ |- _] =>
      invert H
    | [H : RealWorld.step_user _ _ ?u _ |- _] =>
      concrete u; chu

    | [ H : indexedIdealStep _ _ _ _ |- _ ] => istep (* run _after_ real steps *)
                    
    | [ H : _ ^* (?ru,?iu,_) _ |- _ ] => concrete ru; concrete iu; invert H

    | [ |- safety_inv (?ru,_,_) ] =>
      concrete ru; solve [ finish_invariant ]
    end.

Ltac cleanup1 :=
  match goal with
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
  | [ H : Map.In ?k ?m -> False |- _ ] =>
    change (Map.In k m -> False) with (~ Map.In k m) in H
    ; rewrite F.not_find_in_iff in H
  | [ H : context [ ChMaps.ChannelType.eq _ _ ] |- _ ] => unfold ChMaps.ChannelType.eq in H
  | [ H : _ #+ (?k1,_) #? ?k2 = None |- _ ] =>
    (rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq)
    || (rewrite ChMaps.ChMap.F.add_eq_o in H by trivial)
    || (destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst)

  | [ H : (Some _ = None -> False) -> ?c |- _ ] =>
    assert (c) by (apply H; intros; discriminate); clear H
  | [ H : (Some _ <> None) -> ?c |- _ ] =>
    assert (c) by (apply H; intros; discriminate); clear H
  | [ H : context [ sharePerm _ _ ] |- _ ] => unfold sharePerm in H
  | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
  | [ H : $0 $? _ = None |- _ ] => clear H
  | [ H : #0 #? _ = None |- _ ] => clear H
  | [ H : context [ add_key_perm _ _ _ ] |- _ ] => unfold add_key_perm in H

  | [ H : context [ (?uid,_) = (?x,_) \/ False] |- _ ] =>
    concrete uid; destruct H

  | [ H : MessageEq.content_eq ?m _ _ |- _ ] =>
    uf; match type of m with
        | RealWorld.message.message Nat => fail 2
        | _ => unfold MessageEq.content_eq in H
        end
  | [ H : match ?acc with _ => _ end |- _ ] =>
    match type of acc with
    | IdealWorld.IW_message.access => destruct acc
    | _ => fail 2
    end
      
  | [ H : context [ _ #+ (?k,_) #? ?k ] |- _ ] =>
    is_not_evar k
    ; rewrite ChMaps.ChMap.F.add_eq_o in H by trivial
  | [ H : context [ _ #+ (?k1,_) #? ?k2 ] |- _ ] =>
    is_not_evar k1
    ; is_not_evar k2
    ; rewrite ChMaps.ChMap.F.add_neq_o in H by congruence
  | [ H : mkKeys _ $? _ = _ |- _ ] => unfold mkKeys in H
  (* | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => clear H *)
  | [ H : ~ RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => clear H
  | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ -> False |- _ ] => clear H
  | [ H : IdealWorld.screen_msg _ _ |- _ ] => invert H
  | [ H : IdealWorld.permission_subset _ _ |- _ ] => invert H
  | [ H : IdealWorld.check_perm _ _ _ |- _ ] => unfold IdealWorld.check_perm in H
  | [ H : IdealWorld.message.Permission _ = _ |- _ ] => invert H
  | [ H : context [ IdealWorld.addMsg _ _ _ ] |- _ ] => unfold IdealWorld.addMsg in H
  | [ H : Forall _ [] |- _ ] => clear H
  | [ H : context [true || _]  |- _] => rewrite orb_true_l in H
  | [ H : context [_ || true]  |- _] => rewrite orb_true_r in H
  | [ H : context [false || _]  |- _] => rewrite orb_false_l in H
  | [ H : context [_ || false]  |- _] => rewrite orb_false_r in H
  | [ H : context [$0 $k++ _] |- _] => rewrite merge_perms_left_identity in H
  | [ H : context [_ $k++ $0] |- _] => rewrite merge_perms_right_identity in H
  | [ H : context [_ $k++ _ $? _] |- _ ] => rewrite lookup_in_merge_perm in H
  | [ H : context [_ $k++ _]  |- _] =>
    erewrite reduce_merge_perms in H by (clean_map_lookups; eauto)
  (* | [ H : context [_ $k++ _]  |- _] => *)
  (*   unfold merge_perms, add_key_perm, fold in H; clean_map_lookups *)

  | [ H : context [ _ $+ (?k1,_) $? ?k2] |- _ ] =>
    (rewrite add_neq_o in H by solve_simple_ineq)
    || (rewrite add_eq_o in H by trivial)
  | [ H : context [ ?m $? _ ] |- _ ] =>
    progress (unfold m in H)

  | [ |- context [$0 $k++ _] ] => rewrite !merge_perms_left_identity
  | [ |- context [_ $k++ $0] ] => rewrite !merge_perms_right_identity 

  | [ H : context [[] ++ _] |- _ ] => rewrite !app_nil_l in H
  | [ H : context [_ ++ []] |- _ ] => rewrite !app_nil_r in H
  end || discriminate || eq1.

(* Ltac t := (repeat eq1); try invSS1. *)
(* Ltac u := (repeat cleanup1); invSS1(* ; istep *); (repeat cleanup1). *)
Ltac do_trsys_step := invSS1; (repeat cleanup1).

Ltac transition_system_step :=
  rwuf; do_trsys_step; canonicalize context.
