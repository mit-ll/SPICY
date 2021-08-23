(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Morphisms
     Eqdep
.

From SPICY Require Import
     MyPrelude
     Maps
     Messages
     Keys
     Automation
     Tactics
     RealWorld
     AdversaryUniverse
     Simulation.

Set Implicit Arguments.

Lemma greatest_permission_refl :
  forall k,
    greatest_permission k k = k.
Proof.
  unfold greatest_permission; auto using orb_diag.
Qed.

Lemma greatest_permission_symm :
  forall kp1 kp2,
    greatest_permission kp1 kp2 = greatest_permission kp2 kp1.
Proof.
  unfold greatest_permission; auto using orb_comm.
Qed.

Lemma add_key_perm_proper :
  Proper (eq  ==>  eq  ==>  eq  ==>  eq ) add_key_perm.
Proof.
  solve_proper.
Qed.

Require Import Coq.Classes.RelationClasses.

Lemma add_key_perm_proper_Equal :
  Proper (eq  ==>  eq  ==>  Equal  ==>  Equal ) add_key_perm.
Proof.
  unfold Proper, respectful; intros; Equal_eq;
    unfold Equal; intros; trivial.
Qed.

Lemma add_key_perm_transpose :
  transpose_neqkey eq add_key_perm.
Proof.
  unfold transpose_neqkey, add_key_perm; intros.
  apply map_eq_Equal; unfold Equal; intros;
    solve_simple_maps; eauto.
Qed.

Lemma add_key_perm_transpose_Equal :
  transpose_neqkey Equal add_key_perm.
Proof.
  unfold transpose_neqkey, add_key_perm; intros.
  unfold Equal; intros;
      solve_simple_maps; eauto.
Qed.

#[export] Hint Resolve
     add_key_perm_proper       add_key_perm_transpose
     add_key_perm_proper_Equal add_key_perm_transpose_Equal
  : core.

Section KeyMergeTheorems.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Hint Resolve empty_Empty : core.

  Lemma merge_perms_notation :
    forall ks1 ks2,
      fold add_key_perm ks2 ks1 = ks1 $k++ ks2.
    unfold merge_perms; trivial.
  Qed.

  Ltac progress_fold_add1 :=
    match goal with
    | [ H : fold add_key_perm (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H
    | [ H : _ $k++ (_ $+ (_,_)) $? _ = _ |- _ ] => unfold merge_perms in H; rewrite fold_add in H
    | [ |- context[ fold add_key_perm (_ $+ (_,_)) _ ] ] => rewrite fold_add
    | [ |- context[ _ $k++ (_ $+ (_,_))] ] => unfold merge_perms; rewrite fold_add
    end.

  Ltac process_perm_merge1 :=
    match goal with
    | [ H : fold add_key_perm (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H; auto 2
    | [ H : _ $k++ (_ $+ (_,_)) $? _ = _ |- _ ] => unfold merge_perms in H
    | [ |- context[ fold add_key_perm (_ $+ (_,_)) _ ] ] => rewrite fold_add; auto 2
    | [ |- context[ _ $k++ (_ $+ (_,_))] ] => unfold merge_perms
    | [ H : context[ fold add_key_perm ?ks2 ?ks1 ] |- _] => rewrite merge_perms_notation in H
    | [ |- context[ fold add_key_perm ?ks2 ?ks1 ] ] => rewrite merge_perms_notation
    | [ H : ?ks1 $k++ ?ks2 = _ |- context [ ?ks1 $k++ ?ks2 ] ] => rewrite H
    | [ H: context [ add_key_perm ] |- _ ] => unfold add_key_perm in H
    | [ |- context [ add_key_perm ] ] => unfold add_key_perm
    end.

  Ltac process_perm_merge := repeat (process_perm_merge1).

  Lemma merge_perms_left_identity :
    forall ks,
      $0 $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; auto;
      process_perm_merge;
      solve_simple_maps;
      eauto.
  Qed.

  Lemma merge_perms_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_perms; intros; rewrite fold_Empty; eauto.
  Qed.

  Hint Rewrite merge_perms_right_identity merge_perms_left_identity : core.

  Lemma merge_perms_adds_no_new_perms :
    forall ks2 k ks1,
        ks1 $? k = None
      -> ks2 $? k = None
      -> (ks1 $k++ ks2) $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto;
      process_perm_merge;
      solve_simple_maps;
      eauto.
  Qed.

  Hint Resolve merge_perms_adds_no_new_perms : core.

  Lemma merge_perms_came_from_somewhere1 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks2 $? k = None
      -> ks1 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto;
      process_perm_merge;
      solve_simple_maps;
      eauto.
  Qed.

  Lemma merge_perms_came_from_somewhere2 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks1 $? k = None
      -> ks2 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto;
      process_perm_merge;
      solve_simple_maps;
      eauto.

    - rewrite merge_perms_right_identity in *; clean_map_lookups.
    - pose proof (merge_perms_adds_no_new_perms _ _ _ H1 H);
        clean_map_lookups.
  Qed.

  Hint Resolve merge_perms_came_from_somewhere1 merge_perms_came_from_somewhere2 : core.

  Lemma merge_perms_adds_ks1 :
    forall ks2 ks1 k v ks,
        ks1 $? k = Some v
      -> ks2 $? k = None
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof. 
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto;
      process_perm_merge;
      solve_simple_maps;
      eauto.

    - rewrite merge_perms_right_identity in *; subst; eauto.
    - unfold merge_perms;
        process_perm_merge;
        solve_simple_maps;
        eauto.
  Qed.

  Lemma merge_perms_adds_ks2 :
    forall ks2 ks1 k v ks,
        ks1 $? k = None
      -> ks2 $? k = Some v
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq;
      process_perm_merge;
      solve_simple_maps;
      eauto;
      unfold merge_perms;
      process_perm_merge;
      solve_simple_maps;
      eauto.

    pose proof (merge_perms_adds_no_new_perms _ _ _ H0 H);
        clean_map_lookups.
  Qed.

  Hint Resolve merge_perms_adds_ks1 merge_perms_adds_ks2 : core.

  Lemma merge_perms_no_disappear_perms :
    forall ks2 k ks1,
      ks1 $k++ ks2 $? k = None
    -> ks1 $? k = None
    /\ ks2 $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto;
      process_perm_merge;
      solve_simple_maps;
      eauto.
  Qed.

  Lemma merge_perms_chooses_greatest :
    forall ks2 ks1 k k' kp kp',
        ks1 $? k = Some kp
      -> ks2 $? k' = Some kp'
      -> k = k'
      -> (ks1 $k++ ks2) $? k = Some (greatest_permission kp kp').
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto;
      process_perm_merge;
      solve_simple_maps;
      eauto.

    - pose proof (merge_perms_came_from_somewhere1 _ _ _ Heq H);
        clean_map_lookups;
        rewrite greatest_permission_symm;
        eauto.

    - pose proof (merge_perms_no_disappear_perms _ _ _ Heq);
        split_ands;
        clean_map_lookups.
  Qed.

  Hint Resolve merge_perms_chooses_greatest : core.

  Lemma merge_perms_some_inv :
    forall ks1 ks2 k p,
      ks1 $k++ ks2 $? k = Some p
      -> ( ks1 $? k = Some p /\ ks2 $? k = None )
      \/ ( ks1 $? k = None /\ ks2 $? k = Some p )
      \/ ( exists p1 p2, ks1 $? k = Some p1 /\ ks2 $? k = Some p2 /\ p = greatest_permission p1 p2).
  Proof.
    intros.
    cases (ks1 $? k); cases (ks2 $? k);
      match goal with
      | [ H1 : ks1 $? k = _, H2 : ks2 $? k = _ |- _ ] =>
          (pose proof (merge_perms_chooses_greatest _ _ H1 H2 (eq_refl k)))
        || (pose proof (merge_perms_adds_ks1 _ _ _ H1 H2 (eq_refl (ks1 $k++ ks2))))
        || (pose proof (merge_perms_adds_ks2 _ _ _ H1 H2 (eq_refl (ks1 $k++ ks2))))
        || (pose proof (merge_perms_adds_no_new_perms _ _ _ H1 H2))
      end; clean_map_lookups; eauto 12.
  Qed.
          
  Lemma merge_perms_split :
    forall ks2 ks1 k kp,
      ks1 $k++ ks2 $? k = Some kp
      -> ks1 $? k = Some kp
      \/ ks2 $? k = Some kp.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto;
      process_perm_merge;
      solve_simple_maps;
      eauto.

    match goal with
    | [ H : (forall _ _ _, (_ $k++ _ $? _ = Some _) -> _)
            , ARG : _ $k++ _ $? _ = Some _
        |- context [ greatest_permission ?b1 ?b2 ] ] =>
      specialize (H _ _ _ ARG);
        split_ors;
        clean_map_lookups;
        unfold greatest_permission;
        destruct b1; destruct b2
    end; eauto.
  Qed.

End KeyMergeTheorems.

Local Ltac build_merge_term ks kid :=
  match goal with
  | [ H : ks $? kid = _ |- _ ] => fail 1
  | _ =>
    match ks with
    | (?ks1 $k++ ?ks2) =>
      try (build_merge_term ks1 kid); (* subterms need to be created before unification variables *)
      try (build_merge_term ks2 kid);
      let kp' := fresh "kp" in
      evar (kp' : option bool);
      let kp := eval unfold kp' in kp' in
          clear kp'; assert (ks1 $k++ ks2 $? kid = kp)
    | _ => cases (ks $? kid)
    end
  end.
  
Ltac merge_perms_recur1 :=
  match goal with
  (* Identities *)
  | [ H : context [ _ $k++ $0 ] |- _ ] => rewrite merge_perms_right_identity in H
  | [ |- context [ _ $k++ $0 ] ] => rewrite merge_perms_right_identity
  | [ H : context [ $0 $k++ _ ] |- _ ] => rewrite merge_perms_left_identity in H
  | [ |- context [ $0 $k++ _ ] ] => rewrite merge_perms_left_identity

  | [ H : (if ?b then _ else _) = _ |- _ ] => is_var b; destruct b; try discriminate
    
  | [ |- context [ greatest_permission ] ] => unfold greatest_permission
  | [ |- context [ _ || true ] ] => rewrite orb_true_r
  | [ |- context [ true || _ ] ] => rewrite orb_true_l
  | [ |- context [ _ || false ] ] => rewrite orb_false_r
  | [ |- context [ false || _ ] ] => rewrite orb_false_l
  | [ |- context [ ?b || ?b ] ] => rewrite orb_diag
  | [ H : context [ _ || true ] |- _  ] => rewrite orb_true_r in H
  | [ H : context [ true || _ ] |- _  ] => rewrite orb_true_l in H
  | [ H : context [ _ || false ] |- _  ] => rewrite orb_false_r in H
  | [ H : context [ false || _ ] |- _  ] => rewrite orb_false_l in H
  | [ H : context [ ?b || ?b ] |- _ ] => rewrite orb_diag in H
  | [ H : true = _ || _ |- _ ] => symmetry in H; simpl in H
  | [ H : ?b1 || ?b2 = true |- _ ] => first [
                                       is_not_var b1; is_not_var b2
                                     | rewrite orb_true_iff in H; split_ors; subst
                                     ] 

  | [ |- Some _ = _ ] => reflexivity
  | [ |- _ = Some _ ] => reflexivity
  | [ |- Some _ = Some _ ] => f_equal
  | [ |- None = _ ] => reflexivity
  | [ |- _ = None ] => reflexivity
  (* canonicalize ordering of orb so variables are in same order as lhs, and left associated *)
  | [ |- ?lhs = ?rhs ] =>
    match lhs with
    | ?x || ?y =>
      match rhs with
      | y || x => rewrite (orb_comm y x)
      end
    | _ => rewrite orb_assoc
    end

  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _ |- context [ ?ks1 $k++ ?ks2 $? ?kid ]]
    => rewrite (merge_perms_chooses_greatest _ _ H1 H2) by trivial; unfold greatest_permission; simpl
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None |- context [ ?ks1 $k++ ?ks2 $? ?kid ]]
    => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _ |- context [ ?ks1 $k++ ?ks2 $? ?kid ]]
    => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None |- context [ ?ks1 $k++ ?ks2 $? ?kid ]]
    => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) by trivial

  (* we now know ks1 or ks2 is not in the context, or we have some other sort of problem *)
  | [ |- ?ks1 $k++ ?ks2 $? ?kid = _ ] =>
    build_merge_term ks1 kid
    || build_merge_term ks2 kid
    || (unify ks1 ks2; match goal with
                      | [ H : ks1 $? kid = _ |- _ ] => generalize H; intro
                      end)
  | [ |- _ = ?ks1 $k++ ?ks2 $? ?kid ] =>
    (does_not_unify ks1 ks2; (build_merge_term ks1 kid || build_merge_term ks2 kid))
    || match goal with
      | [ H : ks1 $? kid = _ |- _ ] => generalize H; intro
      end
  end.

Lemma merge_perms_neq_add_ok :
  forall ks2 ks1 k k' kp,
    k <> k'
    -> ks1 $+ (k,kp) $k++ ks2 $? k' = ks1 $k++ ks2 $? k'.
Proof.
  intros.
  repeat (merge_perms_recur1 || solve_simple_maps1); trivial.
Qed.

Lemma merge_perms_pull1 :
  forall ks2 ks1 k kp kp' gkp,
    ks2 $? k = Some kp'
    -> gkp = greatest_permission kp kp'
    -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros kid.
  repeat (merge_perms_recur1 || solve_simple_maps1); trivial.
Qed.

Lemma merge_perms_pull2 :
  forall ks2 ks1 k kp gkp,
    ks2 $? k = None
    -> gkp = kp
    -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros kid.
  repeat (merge_perms_recur1 || solve_simple_maps1); trivial.
Qed.

Lemma merge_perms_sym :
  forall ks2 ks1,
    ks1 $k++ ks2 = ks2 $k++ ks1.
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros kid.
  repeat merge_perms_recur1; trivial.
Qed.

Lemma merge_perms_refl :
  forall ks,
    ks $k++ ks = ks.
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros kid.
  repeat merge_perms_recur1.
Qed.

Lemma merge_perms_assoc :
  forall ks3 ks1 ks2,
    ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros kid.
  repeat merge_perms_recur1; trivial.
Qed.

Lemma merge_perms_repl_add : forall ks k v,
    ks $k++ ($0 $+ (k, v)) = add_key_perm k v ks.
Proof.
  intros; unfold merge_perms, add_key_perm, fold; simpl; reflexivity.
Qed.

Lemma merge_perms_distr_add : forall ks ks' k v,
    add_key_perm k v ks $k++ ks' = add_key_perm k v (ks $k++ ks').
Proof.
  intros
  ; rewrite <- !merge_perms_repl_add, merge_perms_assoc
  ; replace ($0 $+ (k, v) $k++ ks') with (ks' $k++ ($0 $+ (k, v)))
  ; [rewrite <- merge_perms_assoc | rewrite merge_perms_sym]
  ; reflexivity.
Qed.

Lemma add_true_lookup_yields_true : forall ks k,
    add_key_perm k true ks $? k = Some true.
Proof.
  intros
  ; unfold add_key_perm
  ; destruct (ks $? k)
  ; simpl
  ; clean_map_lookups
  ; auto.
Qed.


(* Key Merge Automation 
 * 
 *  Strategy is going to be to pick apart the merge
 *  components and then leverage clean_map_lookups
 *)

Ltac split_perm_merge ks kid :=
  match ks with
  | context [ ?ks1 $k++ ?ks2 ] =>
    split_perm_merge ks1 kid;
    split_perm_merge ks2 kid
  | _ =>
    match goal with
    | [ H : ks $? kid = Some _ |- _ ] => idtac
    | [ H : ks $? kid = None |- _ ] => idtac
    | _ => cases (ks $? kid)
    end
  end.

Ltac solve_perm_merges1 :=
  merge_perms_recur1
  || match goal with
  | [ |- ?ks1 $k++ (?ks2 $k++ ?ks3) = ?ks1 $k++ ?ks2 $k++ ?ks3 ] => symmetry; apply merge_perms_assoc

  | [ H : add_key_perm _ _ _ $? _ = _ |- _ ] => unfold add_key_perm in H
  | [ H : ?ks1 $k++ ?ks2 $? ?kid = Some ?b |- _ ] =>
    (* Should we split? *)
    match goal with
    | [ |- context [ ks1 $k++ ks2 ]] =>
      match b with
      | true =>
        
        match goal with
        | [ H1 : ks1 $? kid = ?v1 |- _ ] =>
          match goal with
          | [ H2 : ks2 $? kid = ?v2 |- _ ] =>
            (* Only generalize if one or both isn't a variable *)
            first [
                match v1 with | Some ?vv1 => is_var vv1 end; match v2 with | Some ?vv2 => is_var vv2 end; fail 3 (* get out of here *)
              | match v1 with | Some ?vv1 => is_var vv1 end; fail 1 (* go to generalize branch *)
              | match v2 with | Some ?vv2 => is_var vv2 end; fail 1 (* go to generalize branch *)
              | fail 3  (* get out of here *) 
              ] 
          end
        | _ => generalize H; apply merge_perms_some_inv in H; intros; unfold greatest_permission in H; split_ors
        end
          
      | false =>

        match goal with
        | [ H1 : ks1 $? kid = ?v1 |- _ ] =>
          match goal with
          | [ H2 : ks2 $? kid = ?v2 |- _ ] =>
            (* Only generalize if one or both isn't a variable *)
            first [
                match v1 with | Some ?vv1 => is_var vv1 end; match v2 with | Some ?vv2 => is_var vv2 end; fail 3 (* get out of here *)
              | match v1 with | Some ?vv1 => is_var vv1 end; fail 1 (* go to generalize branch *)
              | match v2 with | Some ?vv2 => is_var vv2 end; fail 1 (* go to generalize branch *)
              | fail 3  (* get out of here *) 
              ] 
          end
        | _ => generalize H; apply merge_perms_some_inv in H; intros; unfold greatest_permission in H; split_ors
        end

      | _ => fail 3
      end
        
    | _ => apply merge_perms_some_inv in H; unfold greatest_permission in H; split_ors
    end
    
  | [ H : ?ks1 $k++ ?ks2 $? ?kid = None |- _ ] =>
    match goal with
    | [ |- context [ ks1 $k++ ks2 ]] =>
      match goal with
      | [ H1 : ks1 $? kid = None |- _ ] =>
        match goal with
        | [ H2 : ks2 $? kid = None |- _ ] => fail 2
        end
      | _ => generalize H; apply merge_perms_no_disappear_perms in H; intros; split_ands
      end
    | _ => apply merge_perms_no_disappear_perms in H; split_ors
    end
  end.

Ltac solve_perm_merges :=
  repeat ( maps_equal1 || solve_perm_merges1 ).

Ltac solve_greatest :=
  repeat
    match goal with
    | [ |- context [ greatest_permission ] ] => unfold greatest_permission
    | [ |- context [ _ || true ] ] => rewrite orb_true_r
    | [ |- context [ true || _ ] ] => rewrite orb_true_l
    | [ |- context [ ?b || ?b ] ] => rewrite orb_diag
    end; trivial.

#[export] Hint Extern 1 (_ = greatest_permission _ _) => solve_greatest : core.

Section FindKeysLemmas.

  Hint Constructors
       msg_pattern_safe
  : core.

  Lemma findUserKeys_foldfn_proper :
    forall {A},
      Proper (eq ==> eq ==> eq ==> eq) (fun (_ : NatMap.Map.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof. solve_proper. Qed.

  Lemma findUserKeys_foldfn_proper_Equal :
    forall {A},
      Proper (eq ==> eq ==> Equal ==> Equal) (fun (_ : NatMap.Map.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold Proper, respectful; intros; subst; Equal_eq; unfold Equal; intros; trivial.
  Qed.

  Lemma findUserKeys_foldfn_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.Map.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite !merge_perms_assoc,merge_perms_sym with (ks1:=key_heap e'); trivial.
  Qed.

  Lemma findUserKeys_foldfn_transpose_Equal :
    forall {A},
      transpose_neqkey Equal (fun (_ : NatMap.Map.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros; unfold Equal; intros.
    rewrite !merge_perms_assoc,merge_perms_sym with (ks1:=key_heap e'); trivial.
  Qed.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal
    : core.

  Lemma findUserKeys_notation :
    forall {A} (usrs : honest_users A),
      fold (fun (_ : NatMap.Map.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u) usrs $0 = findUserKeys usrs.
    unfold findUserKeys; trivial.
  Qed.

  Lemma user_keys_of_empty_is_None :
    forall {A} u_id,
      user_keys (@empty (user_data A)) u_id = None.
  Proof. unfold user_keys; intros; rewrite lookup_empty_none; trivial. Qed.

  Ltac solve_find_user_keys1 u_id usrs IHusrs :=
    match goal with
    | [ H : user_keys $0 _ = Some _ |- _ ] => rewrite user_keys_of_empty_is_None in H
    | [ |- context [ usrs $+ (_,_) $+ (u_id,_) ]] => rewrite map_ne_swap by auto 2
    | [ H : ?x <> u_id |- context [ fold _ (_ $+ (?x, _)) _]] => rewrite fold_add with (k := x); auto 2
    | [ H : usrs $? u_id = None |- context [ fold _ (_ $+ (u_id,_)) _]] => rewrite !fold_add; auto 2
    | [ |- context [ fold _ (_ $+ (u_id,_)) _]] => rewrite !findUserKeys_notation, <- IHusrs
    | [ |- context [ fold _ (_ $+ (u_id,_)) _]] => rewrite !findUserKeys_notation, IHusrs
    | [ H : context [ fold _ (_ $+ (u_id,_)) _] |- _ ] => rewrite !findUserKeys_notation, <- IHusrs in H
    | [ H : context [ fold _ (_ $+ (u_id,_)) _] |- _ ] => rewrite !findUserKeys_notation, IHusrs in H
    | [ H : context [ fold _ _ _ ] |- _ ] => rewrite !findUserKeys_notation in H
    | [ |- context [ fold _ _ _ ] ] => rewrite !findUserKeys_notation
    | [ |- _ $? _ <> _ ] => unfold not; intros
    end.

  Ltac solve_find_user_keys u_id usrs IHusrs :=
    repeat (solve_simple_maps1 || solve_perm_merges1 || maps_equal1  || solve_find_user_keys1 u_id usrs IHusrs || (progress (simpl in *))).

  Lemma findUserKeys_readd_user_same_keys_idempotent :
    forall {A} (usrs : honest_users A) u_id u_d proto msgs mycs froms sents cur_n,
      usrs $? u_id = Some u_d
      -> findUserKeys usrs = findUserKeys (usrs $+ (u_id, {| key_heap  := key_heap u_d
                                                          ; protocol  := proto
                                                          ; msg_heap  := msgs
                                                          ; c_heap    := mycs
                                                          ; from_nons := froms
                                                          ; sent_nons := sents
                                                          ; cur_nonce := cur_n
                                                         |} )).
  Proof.
    induction usrs using map_induction_bis; intros; Equal_eq;
      unfold findUserKeys;
      solve_find_user_keys u_id usrs IHusrs; eauto.
  Qed.

  Lemma findUserKeys_readd_user_same_keys_idempotent' :
    forall {A} (usrs : honest_users A) u_id ks proto msgs mycs froms sents cur_n,
      user_keys usrs u_id = Some ks
      -> findUserKeys (usrs $+ (u_id, {| key_heap  := ks
                                      ; protocol  := proto
                                      ; msg_heap  := msgs
                                      ; c_heap    := mycs
                                      ; from_nons := froms
                                      ; sent_nons := sents
                                      ; cur_nonce := cur_n |})) = findUserKeys usrs.
  Proof.
    unfold user_keys;
      induction usrs using map_induction_bis; intros; Equal_eq; auto;
        unfold findUserKeys;
        solve_find_user_keys u_id usrs IHusrs; eauto.
  Qed.

  Lemma findUserKeys_readd_user_addnl_keys :
    forall {A} (usrs : honest_users A) u_id proto msgs ks ks' mycs froms sents cur_n,
      user_keys usrs u_id = Some ks
      -> findUserKeys (usrs $+ (u_id, {| key_heap  := ks $k++ ks'
                                      ; protocol  := proto
                                      ; msg_heap  := msgs
                                      ; c_heap    := mycs
                                      ; from_nons := froms
                                      ; sent_nons := sents
                                      ; cur_nonce := cur_n |})) = findUserKeys usrs $k++ ks'.
  Proof.
    unfold user_keys;
      induction usrs using map_induction_bis; intros; Equal_eq; auto;
        unfold findUserKeys;
        solve_find_user_keys u_id usrs IHusrs;
        simpl; eauto;
          match goal with
          | [ |- ?ks1 $k++ (?ks2 $k++ ?ks3) = ?ks1 $k++ ?ks2 $k++ ?ks3 ] =>
            symmetry; apply merge_perms_assoc
          | [ |- ?kks1 $k++ ?kks2 $k++ ?kks3 = ?kks1 $k++ ?kks3 $k++ ?kks2 ] =>
            rewrite merge_perms_assoc, merge_perms_sym with (ks1 := kks2), <- merge_perms_assoc; trivial
          end.
  Qed.

  Lemma findUserKeys_readd_user_private_key :
    forall {A} (usrs : honest_users A) u_id proto msgs k_id ks mycs froms sents cur_n,
      user_keys usrs u_id = Some ks
      -> findUserKeys (usrs $+ (u_id, {| key_heap  := add_key_perm k_id true ks
                                      ; protocol  := proto
                                      ; msg_heap  := msgs
                                      ; c_heap    := mycs
                                      ; from_nons := froms
                                      ; sent_nons := sents
                                      ; cur_nonce := cur_n  |})) = findUserKeys usrs $+ (k_id,true).
  Proof.
    unfold user_keys;
      induction usrs using map_induction_bis; intros; Equal_eq; 
        clean_map_lookups; eauto.

    unfold findUserKeys;
      solve_find_user_keys u_id usrs IHusrs;
      eauto;
      try rewrite findUserKeys_notation;
      solve_perm_merges;
      eauto.
  Qed.

  Lemma findUserKeys_has_key_of_user :
    forall {A} (usrs : honest_users A) u_id u_d ks k kp,
      usrs $? u_id = Some u_d
      -> ks = key_heap u_d
      -> ks $? k = Some kp
      -> findUserKeys usrs $? k <> None.
  Proof.
    intros.
    induction usrs using map_induction_bis; intros; Equal_eq;
      subst; clean_map_lookups; eauto;
        unfold findUserKeys;
        solve_find_user_keys u_id usrs IHusrs;
        eauto.
  Qed.

  Hint Extern 1 (match _ $? _ with _ => _ end = _) => context_map_rewrites : core.
  Hint Extern 1 (match ?m $? ?k with _ => _ end = _) =>
    match goal with
    | [ H : ?m $? ?k = _ |- _ ] => rewrite H
    end : core.

  Lemma findUserKeys_has_private_key_of_user :
    forall {A} (usrs : honest_users A) u_id u_d ks k,
      usrs $? u_id = Some u_d
      -> ks = key_heap u_d
      -> ks $? k = Some true
      -> findUserKeys usrs $? k = Some true.
  Proof.
    induction usrs using map_induction_bis; intros; Equal_eq; subst;
      unfold findUserKeys;
      solve_find_user_keys u_id usrs IHusrs; eauto.

    specialize (IHusrs _ _ _ _ H0 (eq_refl (key_heap u_d)) H2); clean_map_lookups; eauto.
    specialize (IHusrs _ _ _ _ H0 (eq_refl (key_heap u_d)) H2); clean_map_lookups; eauto.
    specialize (IHusrs _ _ _ _ H0 (eq_refl (key_heap u_d)) H2); clean_map_lookups; eauto.
    specialize (IHusrs _ _ _ _ H0 (eq_refl (key_heap u_d)) H2); clean_map_lookups; eauto.
  Qed.

  Lemma findUserKeys_readd_user_same_key_heap_idempotent :
    forall {A} (usrs : honest_users A) u_id ks,
      user_keys usrs u_id = Some ks
      -> findUserKeys usrs $k++ ks = findUserKeys usrs.
  Proof.
    unfold user_keys;
      induction usrs using map_induction_bis; intros * UKS; unfold user_keys in UKS;
        Equal_eq; clean_map_lookups; eauto.

    unfold findUserKeys;
      solve_find_user_keys u_id usrs IHusrs;
      eauto.

    - rewrite merge_perms_assoc, merge_perms_refl. trivial.
    - rewrite merge_perms_assoc, merge_perms_sym with (ks1 := key_heap e), <- merge_perms_assoc;
        erewrite IHusrs; eauto.
  Qed.

  Lemma honest_key_after_new_keys :
    forall honestk msgk k_id,
        honest_key honestk k_id
      -> honest_key (honestk $k++ msgk) k_id.
  Proof.
    intros
    ; solve_perm_merges
    ; eauto.
  Qed.

  Hint Resolve honest_key_after_new_keys : core.

  Lemma honest_keyb_after_new_keys :
    forall honestk msgk k_id,
      honest_keyb honestk k_id = true
      -> honest_keyb (honestk $k++ msgk) k_id = true.
  Proof.
    intros; rewrite <- honest_key_honest_keyb in *; eauto.
  Qed.

  Hint Resolve honest_keyb_after_new_keys : core.

  Lemma message_honestly_signed_after_add_keys :
    forall {t} (msg : crypto t) cs honestk ks,
      msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed (honestk $k++ ks) cs msg = true.
  Proof.
    intros.
    destruct msg; unfold msg_honestly_signed in *; simpl in *;
      try discriminate;
      solve_simple_maps; eauto.
  Qed.

  Lemma message_honestly_signed_after_remove_pub_keys :
    forall {t} (msg : crypto t) honestk cs pubk,
      msg_honestly_signed (honestk $k++ pubk) cs msg = true
      -> (forall k kp, pubk $? k = Some kp -> kp = false)
      -> msg_honestly_signed honestk cs msg = true.
  Proof.
    intros.
    destruct msg; simpl in *; eauto;
      unfold msg_honestly_signed, honest_keyb in *;
      simpl in *;
      solve_perm_merges; eauto.

    specialize (H0 _ _ H1); destruct b; subst; auto.
    specialize (H0 _ _ H1); subst; eauto.
  Qed.

  Lemma cipher_honestly_signed_after_msg_keys :
    forall honestk msgk c,
      cipher_honestly_signed honestk c = true
      -> cipher_honestly_signed (honestk $k++ msgk) c = true.
  Proof.
    unfold cipher_honestly_signed. intros; cases c; trivial;
      rewrite <- honest_key_honest_keyb in *; eauto.
  Qed.

  Hint Resolve cipher_honestly_signed_after_msg_keys : core.

  Lemma ciphers_honestly_signed_after_msg_keys :
    forall honestk msgk cs,
      ciphers_honestly_signed honestk cs
      -> ciphers_honestly_signed (honestk $k++ msgk) cs.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Hint Extern 1 (Some _ = Some _) => f_equal : core.

End FindKeysLemmas.

Ltac solve_findUserKeys_rewrites :=
  repeat
    match goal with
    | [ |- context [RealWorld.user_keys] ] => unfold RealWorld.user_keys
    | [ |- context [ _ $? _] ] => progress clean_map_lookups
    | [ |- context [match _ $? _ with _ => _ end]] => context_map_rewrites
    end; simpl; trivial.

Hint Rewrite @findUserKeys_readd_user_same_keys_idempotent' using solve [ solve_findUserKeys_rewrites ] : find_user_keys .
Hint Rewrite @findUserKeys_readd_user_addnl_keys using solve [ solve_findUserKeys_rewrites ] : find_user_keys.
Hint Rewrite @findUserKeys_readd_user_private_key using solve [ solve_findUserKeys_rewrites ] : find_user_keys.

Section CleanKeys.

  Lemma honest_key_filter_fn_proper :
    forall honestk,
      Proper (eq  ==>  eq  ==>  eq) (honest_key_filter_fn honestk).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_key_filter_fn_filter_proper :
    forall honestk,
      Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Ltac keys_solver1 honestk :=
    match goal with
    | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b
    | [ |- context [ if ?b then _ else _ ] ] => destruct b
    | [ H : filter _ _ $? _ = Some _ |- _ ] => rewrite <- find_mapsto_iff, filter_iff in H by auto 1
    | [ |- filter _ _ $? _ = Some _ ] => rewrite <- find_mapsto_iff, filter_iff by auto 1
    | [ |- filter _ _ $? _ = None ] => rewrite <- not_find_in_iff; unfold not; intros
    | [ RW : (forall k, ?m $? k = _ $? k), H : ?m $? _ = _ |- _ ] => rewrite RW in H
    end
    || solve_simple_maps1.
  
  Ltac simplify_filter1 :=
    match goal with
    | [ H : context[fold _ (_ $+ (_, _)) _] |- _] => rewrite fold_add in H by auto 2 
    | [ H : context[if ?cond then (fold _ _ _) $+ (_, _) else (fold _ _ _)] |- _ ] => cases cond
    end.

  Ltac keys_solver honestk :=
    repeat (keys_solver1 honestk || solve_perm_merges1 || simplify_filter1).

  Lemma honest_key_filter_fn_filter_transpose :
    forall honestk,
      transpose_neqkey eq (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, honest_key_filter_fn; intros.
    keys_solver honestk; eauto.
  Qed.

  Lemma honest_key_filter_fn_filter_proper_Equal :
    forall honestk,
      Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    keys_solver honestk; eauto.
  Qed.

  Lemma honest_key_filter_fn_filter_transpose_Equal :
    forall honestk,
      transpose_neqkey Equal (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal, honest_key_filter_fn; intros.
    keys_solver honestk; eauto.
  Qed.

  Hint Resolve
       honest_key_filter_fn_proper
       honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
       honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal
    : core.

  Lemma clean_keys_inv :
    forall honestk k_id k ks,
      clean_keys honestk ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_key_filter_fn honestk k_id k = true.
  Proof.
    unfold clean_keys; intros; keys_solver honestk; eauto.
  Qed.
  
  Lemma clean_keys_inv' :
    forall honestk k_id k ks,
      clean_keys honestk ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = false.
  Proof.
    induction ks using map_induction_bis; intros; Equal_eq;
      unfold clean_keys, filter in *; keys_solver honestk; eauto.
  Qed.

  Lemma clean_keys_keeps_honest_key :
    forall honestk k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = true
      -> clean_keys honestk ks $? k_id = Some k.
  Proof.
    unfold clean_keys; intros; keys_solver honestk; eauto.
  Qed.

  Lemma clean_keys_drops_dishonest_key :
    forall honestk k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = false
      -> clean_keys honestk ks $? k_id = None.
  Proof.
    unfold clean_keys; intros;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_keys_adds_no_keys :
    forall honestk k_id ks,
        ks $? k_id = None
      -> clean_keys honestk ks $? k_id = None.
  Proof.
    induction ks using map_induction_bis; intros; Equal_eq;
      unfold clean_keys in *;
      keys_solver honestk; eauto.
  Qed.

  Hint Resolve clean_keys_adds_no_keys : core.

  Lemma clean_keys_idempotent :
    forall honestk ks,
      clean_keys honestk (clean_keys honestk ks) = clean_keys honestk ks.
  Proof.
    intros;
      apply map_eq_Equal; unfold Equal; intros.
    cases (clean_keys honestk ks $? y); eauto.
    eapply clean_keys_keeps_honest_key; auto.
    unfold clean_keys in *; keys_solver honestk; eauto.
  Qed.

  Lemma honest_perm_filter_fn_proper :
    forall honestk,
      Proper (eq  ==>  eq  ==>  eq) (honest_perm_filter_fn honestk).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper :
    forall honestk,
      Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_perm_filter_fn honestk  k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose :
    forall honestk,
      transpose_neqkey eq (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, honest_perm_filter_fn; intros;
      keys_solver honestk; eauto.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper_Equal :
    forall honestk,
      Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    keys_solver honestk; eauto.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose_Equal :
    forall honestk,
      transpose_neqkey Equal (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal, honest_perm_filter_fn; intros;
      keys_solver honestk; eauto.
  Qed.

  Hint Resolve
       honest_perm_filter_fn_proper
       honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
       honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal
    : core.

  Lemma clean_key_permissions_inv :
    forall honestk k_id k ks,
      clean_key_permissions honestk ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_perm_filter_fn honestk k_id k = true.
  Proof.
    unfold clean_key_permissions; intros;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_key_permissions_inv' :
    forall honestk k_id k ks,
      clean_key_permissions honestk ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = false.
  Proof.
    induction ks using map_induction_bis; intros; Equal_eq;
      unfold clean_key_permissions,filter in *;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_key_permissions_inv'' :
    forall honestk k_id ks,
      clean_key_permissions honestk ks $? k_id = None
      -> honestk $? k_id = Some true
      -> ks $? k_id = None.
  Proof.
    induction ks using map_induction_bis; intros; Equal_eq;
      unfold clean_key_permissions,filter in *;
      keys_solver honestk; eauto.

    unfold honest_perm_filter_fn in Heq; context_map_rewrites; discriminate.
  Qed.

  Lemma clean_key_permissions_adds_no_permissions :
    forall honestk k_id ks,
        ks $? k_id = None
      -> clean_key_permissions honestk ks $? k_id = None.
  Proof.
    induction ks using map_induction_bis; intros; Equal_eq;
      unfold clean_key_permissions in *;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_key_permissions_keeps_honest_permission :
    forall honestk k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = true
      -> clean_key_permissions honestk ks $? k_id = Some k.
  Proof.
    unfold clean_key_permissions; intros;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_key_permissions_drops_dishonest_permission :
    forall honestk k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = false
      -> clean_key_permissions honestk ks $? k_id = None.
  Proof.
    unfold clean_key_permissions; intros;
      keys_solver honestk; eauto.
  Qed.

  Hint Resolve
       clean_key_permissions_inv
       clean_key_permissions_adds_no_permissions
       clean_key_permissions_keeps_honest_permission
       clean_key_permissions_drops_dishonest_permission
  : core.

  Lemma clean_key_permissions_idempotent :
    forall honestk ks,
      clean_key_permissions honestk ks = clean_key_permissions honestk (clean_key_permissions honestk ks).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    symmetry; cases (clean_key_permissions honestk ks $? y);
      eauto;
      match goal with
      | [ H : clean_key_permissions _ _ $? _ = Some _ |- _ ] =>
        generalize (clean_key_permissions_inv _ _ _ H); intros; split_ands
      end; eauto.
  Qed.

  Ltac clean_keys_reasoner1 :=
    match goal with 
    | [ H : clean_key_permissions _ ?perms $? _ = Some _ |- _ ] => apply clean_key_permissions_inv in H
    | [ H : clean_key_permissions _ ?perms $? ?k = None |- _ ] =>
      is_var perms;
      match goal with
      | [ H1 : perms $? k = None |- _ ] => clear H
      | [ H1 : perms $? k = Some _ |- _ ] => eapply clean_key_permissions_inv' in H; eauto 2
      | _ => cases (perms $? k)
      end
    | [ H : clean_key_permissions _ (?perms1 $k++ ?perms2) $? _ = None |- _ ] =>
      match goal with
      | [ H1 : perms1 $? _ = Some _ |- _] => eapply clean_key_permissions_inv' in H; swap 1 2; [solve_perm_merges|]; eauto
      | [ H1 : perms2 $? _ = Some _ |- _] => eapply clean_key_permissions_inv' in H; swap 1 2; [solve_perm_merges|]; eauto
      end
    | [ H : honest_perm_filter_fn _ _ _ = _ |- _ ] => unfold honest_perm_filter_fn in H
    | [ H : forall k_id kp, ?pubk $? k_id = Some kp -> _, ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
    end.

  Lemma clean_key_permissions_distributes_merge_key_permissions :
    forall honestk perms1 perms2,
      clean_key_permissions honestk (perms1 $k++ perms2) =
      clean_key_permissions honestk perms1 $k++ clean_key_permissions honestk perms2.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions honestk perms1 $? y);
      cases (clean_key_permissions honestk perms2 $? y);
      cases (clean_key_permissions honestk (perms1 $k++ perms2) $? y);
      repeat (keys_solver1 honestk
              || solve_perm_merges1
              || discriminate
              || clean_keys_reasoner1); eauto.
  Qed.

  Lemma clean_honest_key_permissions_distributes :
    forall honestk perms pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> clean_key_permissions honestk (perms $k++ pubk) = clean_key_permissions honestk perms $k++ pubk.
  Proof.
    intros.
    rewrite clean_key_permissions_distributes_merge_key_permissions.
    apply map_eq_Equal; unfold Equal; intros y.
    cases (clean_key_permissions honestk perms $? y);
      cases (clean_key_permissions honestk pubk $? y);
      cases (clean_key_permissions honestk (perms $k++ pubk) $? y);
      repeat (keys_solver1 honestk
              || solve_perm_merges1
              || discriminate
              || clean_keys_reasoner1); eauto.
  Qed.

  Lemma adv_no_honest_key_honest_key :
    forall honestk pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true.
  Proof.
    intros * H * H0.
    specialize (H _ _ H0); intuition idtac.
  Qed.

  Lemma clean_keys_drops_added_dishonest_key :
    forall honestk gks k_id ku kt,
      ~ In k_id gks
      -> honestk $? k_id = None
      -> clean_keys honestk (gks $+ (k_id, {| keyId := k_id; keyUsage := ku; keyType := kt |}))
        = clean_keys honestk gks.
  Proof.
    intros; unfold clean_keys, filter; apply map_eq_Equal; unfold Equal; intros.
    rewrite fold_add; eauto.
    unfold honest_key_filter_fn; context_map_rewrites; trivial.
  Qed.

End CleanKeys.

Section MergeCleanKeysLemmas.

  Lemma merge_keys_addnl_honest :
    forall ks1 ks2,
      (forall k_id kp, ks2 $? k_id = Some kp -> ks1 $? k_id = Some true)
      -> ks1 $k++ ks2 = ks1.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (ks1 $? y); cases (ks2 $? y); subst;
      try
        match goal with
        | [ H1 : ks2 $? _ = Some ?b
                 , H2 : (forall _ _, ks2 $? _ = Some _ -> _) |- _ ]  => generalize (H2 _ _ H1); intros
        end; solve_perm_merges; intuition eauto.
  Qed.

  Lemma honestk_merge_new_msgs_keys_same :
    forall honestk cs  {t} (msg : crypto t),
      message_no_adv_private honestk cs msg
      -> (honestk $k++ findKeysCrypto cs msg) = honestk.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    solve_perm_merges; eauto;
      specialize (H _ _ Heq0); clean_map_lookups; eauto.
  Qed.

  Lemma honestk_merge_new_msgs_keys_dec_same :
    forall honestk {t} (msg : message t),
      (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> (honestk $k++ findKeysMessage msg) = honestk.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    solve_perm_merges; eauto;
      specialize (H _ _ Heq0); clean_map_lookups; eauto.
  Qed.

  Lemma add_key_perm_add_private_key :
    forall ks k_id,
      add_key_perm k_id true ks = ks $+ (k_id,true).
  Proof.
    intros; unfold add_key_perm; cases (ks $? k_id); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve
       honest_key_filter_fn_proper
       honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
       honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal
       honest_perm_filter_fn_proper
       honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
       honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal
    : core.

  Lemma message_no_adv_private_merge :
    forall honestk t (msg : crypto t) cs,
      message_no_adv_private honestk cs msg
      -> honestk $k++ findKeysCrypto cs msg = honestk.
  Proof.
    intros.
    unfold message_no_adv_private in *.
    maps_equal.
    cases (findKeysCrypto cs msg $? y); solve_perm_merges; eauto.
    specialize (H _ _ Heq); split_ands; subst; clean_map_lookups; eauto.
    specialize (H _ _ Heq); split_ands; clean_map_lookups; eauto.
  Qed.


  Lemma message_only_honest_merge :
    forall honestk t (msg : message t),
      (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> honestk $k++ findKeysMessage msg = honestk.
  Proof.
    intros.
    maps_equal.
    cases (findKeysMessage msg $? y); solve_perm_merges; eauto.
    specialize (H _ _ Heq); split_ands; subst; clean_map_lookups; eauto.
    specialize (H _ _ Heq); split_ands; clean_map_lookups; eauto.
  Qed.

  Lemma honest_keyb_true_honestk_has_key :
    forall honestk k,
      honest_keyb honestk k = true -> honestk $? k = Some true.
  Proof. intros * H; rewrite <- honest_key_honest_keyb in H; assumption. Qed.

  Lemma clean_key_permissions_new_honest_key' :
    forall honestk k_id gks,
      gks $? k_id = None
      -> clean_key_permissions (honestk $+ (k_id, true)) gks = clean_key_permissions honestk gks.
  Proof.
    intros.
    unfold clean_key_permissions, filter.
    apply P.fold_rec_bis; intros; Equal_eq; eauto.
    subst; simpl.

    rewrite fold_add; eauto.
    assert (honest_perm_filter_fn (honestk $+ (k_id,true)) k e = honest_perm_filter_fn honestk k e)
      as RW.

    unfold honest_perm_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
    apply find_mapsto_iff in H0; contra_map_lookup.
    rewrite RW; trivial.
  Qed.

  Lemma clean_key_permissions_new_honest_key :
    forall honestk k_id ks,
      ~ In k_id ks
      -> clean_key_permissions (honestk $+ (k_id, true)) (add_key_perm k_id true ks) =
        add_key_perm k_id true (clean_key_permissions honestk ks).
  Proof.
    intros; clean_map_lookups.
    unfold add_key_perm, greatest_permission.
    assert (clean_key_permissions honestk ks $? k_id = None)
      as CKP
        by (apply clean_key_permissions_adds_no_permissions; auto);
      rewrite CKP, H.
    unfold clean_key_permissions at 1; unfold filter; rewrite fold_add; eauto.
    unfold honest_perm_filter_fn; clean_map_lookups; eauto.

    apply map_eq_Equal; unfold Equal; intros.
    destruct (k_id ==n y); subst; clean_map_lookups; eauto.
    pose proof clean_key_permissions_new_honest_key';
      unfold clean_key_permissions, filter, honest_perm_filter_fn in *; eauto.
    rewrite H0; eauto.
  Qed.

  Lemma clean_key_permissions_nochange_pubk :
    forall honestk pubk perms,
      (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> clean_key_permissions (honestk $k++ pubk) perms = clean_key_permissions honestk perms.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions honestk perms $? y).
    - apply clean_key_permissions_inv in Heq; split_ands.
      apply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn in *.
      cases (honestk $? y); try destruct b0; try discriminate.
      cases (pubk $? y); solve_perm_merges; eauto.
    - cases (perms $? y).
      + eapply clean_key_permissions_inv' in Heq; eauto.
        eapply clean_key_permissions_drops_dishonest_permission; eauto.
        unfold honest_perm_filter_fn in *.
        specialize (H y).
        cases (honestk $? y); try destruct b0; try discriminate.
        cases (pubk $? y);
          match goal with
          | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
            assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
          | _ => solve_perm_merges
          end; eauto.
        cases (pubk $? y);
          match goal with
          | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
            assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
          | _ => solve_perm_merges
          end; eauto.
      + apply clean_key_permissions_adds_no_permissions; eauto.
  Qed.

  Lemma clean_keys_nochange_pubk :
    forall honestk pubk ks,
      (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> clean_keys (honestk $k++ pubk) ks = clean_keys honestk ks.
  Proof.
    intros; unfold clean_keys, filter.

    induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
    rewrite !fold_add; eauto.
    rewrite IHks; trivial.

    assert (honest_key_filter_fn (honestk $k++ pubk) x e = honest_key_filter_fn honestk x e).
    unfold honest_key_filter_fn.
    specialize (H x).
    cases (honestk $? x); cases (pubk $? x); subst;
      try match goal with
          | [ PUB : pubk $? x = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
            assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; try discriminate
          end;
      solve_perm_merges; eauto.

    rewrite H1; trivial.
  Qed.

  Lemma adv_key_not_honestk :
    forall k_id honestk advk,
      advk $? k_id = Some true
      -> adv_no_honest_keys honestk advk
      -> honest_keyb honestk k_id = false.
  Proof.
    unfold adv_no_honest_keys, honest_keyb; intros.
    specialize (H0 k_id); split_ors; split_ands;
      context_map_rewrites; auto;
        contradiction.
  Qed.

  Lemma clean_keys_new_honest_key' :
    forall honestk k_id gks,
      gks $? k_id = None
      -> clean_keys (honestk $+ (k_id, true)) gks = clean_keys honestk gks.
  Proof.
    intros.
    unfold clean_keys, filter.
    apply P.fold_rec_bis; intros; Equal_eq; eauto.
    subst; simpl.

    rewrite fold_add; eauto.
    assert (honest_key_filter_fn (honestk $+ (k_id,true)) k e = honest_key_filter_fn honestk k e)
      as RW.

    unfold honest_key_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
    apply find_mapsto_iff in H0; contra_map_lookup.
    rewrite RW; trivial.
  Qed.

  Lemma clean_keys_new_honest_key :
    forall honestk k_id k gks,
      gks $? k_id = None
      -> permission_heap_good gks honestk
      -> clean_keys (honestk $+ (k_id, true)) (gks $+ (k_id,k)) =
        clean_keys honestk gks $+ (k_id, k).
  Proof.
    intros.

    apply map_eq_Equal; unfold Equal; intros.
    destruct (k_id ==n y); subst; clean_map_lookups; eauto.
    - apply clean_keys_keeps_honest_key; clean_map_lookups; eauto.
      unfold honest_key_filter_fn; clean_map_lookups; eauto.
    - unfold clean_keys at 1.
      unfold filter.
      rewrite fold_add; eauto.
      unfold honest_key_filter_fn; clean_map_lookups; eauto.
      unfold clean_keys, filter, honest_key_filter_fn; eauto.
      pose proof (clean_keys_new_honest_key' honestk k_id gks H).
      unfold clean_keys, filter, honest_key_filter_fn in H1.
      rewrite H1; trivial.
  Qed.

End MergeCleanKeysLemmas.

