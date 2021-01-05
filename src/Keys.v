(* 
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     String
     Sumbool
     Morphisms.

From SPICY Require Import
     MyPrelude
     Common
     Maps
     Tactics.

Set Implicit Arguments.

Definition key_identifier := nat.

Inductive key_usage :=
| Encryption
| Signing.

Lemma key_usage_eq_dec :
  forall u1 u2 : key_usage, { u1 = u2 } + { u1 <> u2 }.
  decide equality.
Defined.

Inductive key_type :=
| SymKey
| AsymKey.

Lemma key_type_eq_dec :
  forall kt1 kt2 : key_type, { kt1 = kt2 } + { kt1 <> kt2 }.
  decide equality.
Defined.

Record key :=
  MkCryptoKey { keyId    : key_identifier
              ; keyUsage : key_usage
              ; keyType  : key_type
              }.

Lemma key_eq_dec :
  forall k1 k2 : key, { k1 = k2 } + { k1 <> k2 }.
  decide equality; auto using Nat.eq_dec, key_usage_eq_dec, key_type_eq_dec.
Defined.

Definition key_permission : Set := key_identifier * bool.

Lemma key_permission_eq_dec :
  forall kp1 kp2 : key_permission, { kp1 = kp2 } + { kp1 <> kp2 }.
  decide equality; auto using Nat.eq_dec, Bool.bool_dec.
Defined.

Notation "x ==kk y" := (key_eq_dec x y) (right associativity, at level 75).
Notation "x ==ku y" := (key_usage_eq_dec x y) (right associativity, at level 75).
Notation "x ==kt y" := (key_type_eq_dec x y) (right associativity, at level 75).
Notation "x ==kp y" := (key_permission_eq_dec x y) (right associativity, at level 75).

Definition keys            := NatMap.t key.
Definition key_perms       := NatMap.t bool.

Definition greatest_permission (kp1 kp2 : bool) : bool :=
  kp1 || kp2.

Definition add_key_perm (k : key_identifier)(kp : bool) (perms : key_perms) : key_perms :=
    match perms $? k with
    | None     => perms $+ (k, kp)
    | Some kp' => perms $+ (k, greatest_permission kp kp')
    end.

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

Definition merge_perms (ks ks' : key_perms) : key_perms :=
  Map.fold add_key_perm ks ks'.

Notation "m1 $k++ m2" := (merge_perms m2 m1) (at level 50, left associativity).

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

Hint Resolve
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

Hint Extern 1 (_ = greatest_permission _ _) => solve_greatest : core.
