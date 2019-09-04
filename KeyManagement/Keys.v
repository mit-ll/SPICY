From Coq Require Import String Sumbool Morphisms.

Require Import
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
  fold add_key_perm ks ks'.

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
    cases (a $? k); cases (a $? k');
      repeat (context_map_rewrites; clean_map_lookups);
      cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; trivial; contradiction.
Qed.

Lemma add_key_perm_transpose_Equal :
  transpose_neqkey Equal add_key_perm.
Proof.
  unfold transpose_neqkey, add_key_perm; intros.
  unfold Equal; intros;
    cases (a $? k); cases (a $? k');
      repeat (context_map_rewrites; clean_map_lookups);
      cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; trivial; contradiction.
Qed.

Hint Resolve
     add_key_perm_proper       add_key_perm_transpose
     add_key_perm_proper_Equal add_key_perm_transpose_Equal.

Section KeyMergeTheorems.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Hint Resolve empty_Empty.

  Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff.

  Ltac progress_fold_add1 :=
    match goal with
    | [ H : fold add_key_perm (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H
    | [ H : _ $k++ (_ $+ (_,_)) $? _ = _ |- _ ] => unfold merge_perms in H; rewrite fold_add in H
    | [ |- context[ fold add_key_perm (_ $+ (_,_)) _ ] ] => rewrite fold_add
    | [ |- context[ _ $k++ (_ $+ (_,_))] ] => unfold merge_perms; rewrite fold_add
    end.

  Lemma merge_perms_notation :
    forall ks1 ks2,
      fold add_key_perm ks2 ks1 = ks1 $k++ ks2.
    unfold merge_perms; trivial.
  Qed.

  Lemma merge_perms_left_identity :
    forall ks,
      $0 $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; auto.

    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm; auto.
    rewrite IHks; auto.
    case_eq (ks $? x); intros; subst; clean_map_lookups; trivial.
  Qed.

  Lemma merge_perms_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_perms; intros; rewrite fold_Empty; eauto.
  Qed.

  Hint Rewrite merge_perms_right_identity merge_perms_left_identity.

  Lemma merge_perms_adds_no_new_perms :
    forall ks2 k ks1,
        ks1 $? k = None
      -> ks2 $? k = None
      -> (ks1 $k++ ks2) $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    case (x ==n k); intros; subst; clean_map_lookups.
    cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Hint Resolve merge_perms_adds_no_new_perms.

  Lemma merge_perms_came_from_somewhere1 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks2 $? k = None
      -> ks1 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    case (x ==n k); intros; subst; clean_map_lookups.
    progress_fold_add1; auto.
    rewrite merge_perms_notation in *.
    unfold add_key_perm in *.
    cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_came_from_somewhere2 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks1 $? k = None
      -> ks2 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - rewrite merge_perms_right_identity in H; clean_map_lookups.
    - case (k ==n x); intros; subst; clean_map_lookups;
        progress_fold_add1; auto;
          rewrite merge_perms_notation in *;
          unfold add_key_perm in *.
      + assert (ks1 $k++ ks2 $? x = None) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
      + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_came_from_somewhere1 merge_perms_came_from_somewhere2.

  Lemma merge_perms_adds_ks1 :
    forall ks2 ks1 k v ks,
        ks1 $? k = Some v
      -> ks2 $? k = None
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - subst; rewrite fold_Empty; eauto.
    - case (x ==n k); intros; subst; clean_map_lookups; eauto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm.
      cases ( ks1 $k++ ks2 $? x ); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_adds_ks2 :
    forall ks2 ks1 k v ks,
        ks1 $? k = None
      -> ks2 $? k = Some v
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    subst; progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    cases (k ==n x); subst; clean_map_lookups.
    + assert (ks1 $k++ ks2 $? x = None) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
    + cases ( ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_adds_ks1 merge_perms_adds_ks2.

  Lemma merge_perms_chooses_greatest :
    forall ks2 ks1 k k' kp kp',
        ks1 $? k = Some kp
      -> ks2 $? k' = Some kp'
      -> k = k'
      -> (ks1 $k++ ks2) $? k = Some (greatest_permission kp kp').
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    subst.
    cases (x ==n k'); subst; clean_map_lookups.
    + assert (ks1 $k++ ks2 $? k' = Some kp) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
      rewrite greatest_permission_symm; trivial.
    + cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_chooses_greatest.

  Lemma merge_perms_split :
    forall ks2 ks1 k kp,
      ks1 $k++ ks2 $? k = Some kp
      -> ks1 $? k = Some kp
      \/ ks2 $? k = Some kp.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    cases (x ==n k); subst; clean_map_lookups; auto;
      progress_fold_add1; auto;
        rewrite merge_perms_notation in *;
        unfold add_key_perm in *.

    + subst. clean_map_lookups.
      cases (ks1 $k++ ks2 $? k); clean_map_lookups; auto.
      apply merge_perms_came_from_somewhere1 in Heq; auto.
      unfold greatest_permission; cases e; cases b; simpl; auto.

    + cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_no_disappear_perms :
    forall ks2 k ks1,
      ks1 $k++ ks2 $? k = None
    -> ks1 $? k = None
    /\ ks2 $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation in *; clean_map_lookups.
    unfold add_key_perm in *.
    cases (ks1 $k++ ks2 $? x);
      cases (x ==n k); subst; clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_neq_add_ok :
    forall ks2 ks1 k k' kp,
      k <> k'
      -> ks1 $+ (k,kp) $k++ ks2 $? k' = ks1 $k++ ks2 $? k'.
  Proof.
    intros.
    cases (ks1 $? k'); cases (ks2 $? k').
    - erewrite !merge_perms_chooses_greatest; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_ks1; auto; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_ks2; auto; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_no_new_perms; clean_map_lookups; auto.
  Qed.

  Hint Resolve merge_perms_neq_add_ok.

  Lemma merge_perms_pull1 :
    forall ks2 ks1 k kp kp' gkp,
        ks2 $? k = Some kp'
      -> gkp = greatest_permission kp kp'
      -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    apply map_eq_Equal; unfold Equal; intros.
    cases (k ==n x); cases (k ==n y); cases (x ==n y); subst; clean_map_lookups; try contradiction.
    - eapply merge_perms_chooses_greatest; auto; clean_map_lookups; trivial.
    - unfold merge_perms at 1; rewrite fold_add; auto; rewrite merge_perms_notation; unfold add_key_perm.
      assert (ks1 $+ (x, kp) $k++ ks2 $? x = Some kp) by (eapply merge_perms_adds_ks1; eauto; clean_map_lookups; trivial).
      context_map_rewrites; clean_map_lookups.
      unfold merge_perms at 2; rewrite fold_add; auto; rewrite merge_perms_notation with (ks1:=ks1); unfold add_key_perm.
      cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups; eauto.
    - progress_fold_add1; auto.
      rewrite merge_perms_notation; unfold add_key_perm.
      cases (ks1 $+ (y, kp) $k++ ks2 $? x); clean_map_lookups; auto;
        erewrite merge_perms_chooses_greatest; auto; clean_map_lookups; eauto.
    - unfold merge_perms; rewrite !fold_add; auto.
      rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
      unfold add_key_perm.
      cases (ks1 $k++ ks2 $? y); eauto.
      + assert (ks1 $? y = Some b) by eauto.
        assert (ks1 $+ (k, kp) $k++ ks2 $? y = Some b). eapply merge_perms_adds_ks1; auto. clean_map_lookups; auto. auto.
        context_map_rewrites; clean_map_lookups; trivial.
      + eapply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        assert (ks1 $+ (k, kp) $k++ ks2 $? y = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
        context_map_rewrites; clean_map_lookups; auto.
    - unfold merge_perms; rewrite !fold_add; auto.
      rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
      unfold add_key_perm.
      cases (ks1 $k++ ks2 $? x); clean_map_lookups.
      + apply merge_perms_came_from_somewhere1 in Heq; eauto.
        assert (ks1 $+ (k, kp) $k++ ks2 $? x = Some b). eapply merge_perms_adds_ks1; auto. clean_map_lookups; auto. auto.
        context_map_rewrites; clean_map_lookups; auto.
      + eapply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        assert (ks1 $+ (k, kp) $k++ ks2 $? x = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
        context_map_rewrites; clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_pull2 :
    forall ks2 ks1 k kp gkp,
        ks2 $? k = None
      -> gkp = kp
      -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; autorewrite with core; subst; auto.
    cases (x ==n k); subst; clean_map_lookups.
    unfold merge_perms; rewrite !fold_add; auto.
    rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
    unfold add_key_perm.
    cases (ks1 $k++ ks2 $? x).
    - apply merge_perms_came_from_somewhere1 in Heq; auto.
      assert (ks1 $+ (k, kp) $k++ ks2 $? x = Some b) by (eapply merge_perms_adds_ks1; trivial; clean_map_lookups; auto).
      context_map_rewrites; clean_map_lookups; auto.
      erewrite IHks2; auto.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n x); cases (y ==n k); subst; clean_map_lookups; auto; contradiction.
    - apply merge_perms_no_disappear_perms in Heq; auto; split_ands.
      assert (ks1 $+ (k, kp) $k++ ks2 $? x = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
      context_map_rewrites.
      apply map_eq_Equal; unfold Equal; intros.
      erewrite IHks2; auto.
      cases (y ==n x); cases (y ==n k); subst; clean_map_lookups; auto; contradiction.
  Qed.

  Lemma merge_perms_sym :
    forall ks2 ks1,
      ks1 $k++ ks2 = ks2 $k++ ks1.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - rewrite merge_perms_right_identity, merge_perms_left_identity; trivial.
    - unfold merge_perms at 1; rewrite fold_add; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm; simpl.

      cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups.
      + apply merge_perms_came_from_somewhere1 in Heq; auto.
        erewrite merge_perms_pull1; eauto; rewrite IHks2; auto.
      + apply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        erewrite merge_perms_pull2; eauto; rewrite IHks2; auto.
  Qed.

  Lemma merge_perms_refl :
    forall ks,
      ks $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    erewrite merge_perms_pull2; clean_map_lookups; auto.
    rewrite map_add_eq, IHks; rewrite greatest_permission_refl; trivial.
  Qed.

  Lemma merge_perms_assoc :
    forall ks3 ks1 ks2,
      ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Proof.
    induction ks3 using P.map_induction_bis; intros; Equal_eq; auto.
    unfold merge_perms at 1.
    unfold merge_perms at 3.
    rewrite !fold_add; auto.
    rewrite merge_perms_notation.
    rewrite merge_perms_notation with (ks1:=ks2).
    unfold add_key_perm.

    cases (ks2 $k++ ks3 $? x).
    - cases (ks1 $k++ ks2 $k++ ks3 $? x);
        subst; rewrite IHks3 in Heq0; clean_map_lookups; eauto.
      + cases (ks1 $? x).
        * assert (ks1 $k++ (ks2 $k++ ks3) $? x = Some (greatest_permission b1 b)) by eauto.
          clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n x); subst; clean_map_lookups.
          ** assert (ks1 $k++ (ks2 $k++ ks3 $+ (x, greatest_permission e b)) $? x = Some (greatest_permission b1 (greatest_permission e b)))
              by (eapply merge_perms_chooses_greatest; auto; clean_map_lookups; auto).
             context_map_rewrites; unfold greatest_permission.
             rewrite !orb_assoc, orb_comm with (b1:=e); trivial.
          ** symmetry; rewrite merge_perms_sym.
             rewrite merge_perms_neq_add_ok, merge_perms_sym, <- IHks3; auto; trivial.
        * assert (ks1 $k++ (ks2 $k++ ks3) $? x = Some b) by eauto; clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n x); subst; clean_map_lookups.
          ** assert (ks1 $k++ (ks2 $k++ ks3 $+ (x, greatest_permission e b)) $? x = Some (greatest_permission e b))
              by (eapply merge_perms_adds_ks2; auto; clean_map_lookups; auto).
             context_map_rewrites; eauto.
          ** symmetry; rewrite merge_perms_sym.
             rewrite merge_perms_neq_add_ok, merge_perms_sym, <- IHks3; auto; trivial.

      + apply merge_perms_no_disappear_perms in Heq0; auto; split_ands; contra_map_lookup.

    - unfold merge_perms at 7.
      rewrite fold_add; auto.
      unfold add_key_perm at 1. rewrite merge_perms_notation with (ks2:=ks2 $k++ ks3).
      rewrite IHks3; trivial.
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

End KeyMergeTheorems.

Section KeyPermFind.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.

  Class KeyPermFind (k : nat) (m : option bool) (ks : key_perms) :=
    { kp_find : ks $? k = m }.

  Program Instance find_empty k : KeyPermFind k None $0.
  (* Program Instance found_already_known ks k v (known : ks $? k = Some v) : KeyPermFind k (Some v) ks. *)
  (* Program Instance not_found_already_known ks k (known : ks $? k = None) : KeyPermFind k None ks. *)
  Lemma found_already_known' :
    forall ks k v,
      ks $? k = Some v
      -> KeyPermFind k (Some v) ks.
  Proof.
    intros; econstructor; trivial.
  Qed.
  Lemma not_found_already_known' :
    forall ks k,
      ks $? k = None
      -> KeyPermFind k None ks.
  Proof.
    intros; econstructor; trivial.
  Qed.

  Program Instance find_found k v ks : KeyPermFind k (Some v) (ks $+ (k, v)).
  Next Obligation. apply add_eq_o; auto. Qed.

  (* Program Instance find_not_found k k' v ks *)
  (*         (neq : k <> k') (f : KeyPermFind k None ks) *)
  (*   : KeyPermFind k None (ks $+ (k', v)). *)
  (* Next Obligation. destruct f; rewrite add_neq_o; eauto. Qed. *)

  Lemma find_preserve :
    forall k k' v ks sv,
      k <> k'
      -> KeyPermFind k sv ks
      -> KeyPermFind k sv (ks $+ (k', v)).
  Proof.
    intros.
    destruct H0; econstructor; clean_map_lookups; trivial.
  Qed.

  Program Instance find_merge_left k v ks1 ks2
          (f1 : KeyPermFind k (Some v) ks1) (f2 : KeyPermFind k None ks2)
    : KeyPermFind k (Some v) (ks1 $k++ ks2).
  Next Obligation. destruct f1, f2; eapply merge_perms_adds_ks1; eauto. Qed.

  Program Instance find_merge_right k v ks1 ks2
          (f1 : KeyPermFind k None ks1) (f2 : KeyPermFind k (Some v) ks2)
    : KeyPermFind k (Some v) (ks1 $k++ ks2).
  Next Obligation. destruct f1, f2; eapply merge_perms_adds_ks2; eauto. Qed.

  Program Instance find_merge_greatest k v1 v2 ks1 ks2
          (f1 : KeyPermFind k (Some v1) ks1) (f2 : KeyPermFind k (Some v2) ks2)
    : KeyPermFind k (Some (greatest_permission v1 v2)) (ks1 $k++ ks2).
  Next Obligation. destruct f1, f2; eapply merge_perms_chooses_greatest; eauto. Qed.

  Lemma find_merge_greatest' :
    forall k v1 v2 ks1 ks2 gp,
        KeyPermFind k (Some v1) ks1
      -> KeyPermFind k (Some v2) ks2
      -> gp = greatest_permission v1 v2
      -> KeyPermFind k (Some gp) (ks1 $k++ ks2).
  Proof.
    intros.
    destruct H; destruct H0; econstructor; subst; eapply merge_perms_chooses_greatest; eauto.
  Qed.

  Program Instance find_merge_neither k ks1 ks2
          (f1 : KeyPermFind k None ks1) (f2 : KeyPermFind k None ks2)
    : KeyPermFind k None (ks1 $k++ ks2).
  Next Obligation. destruct f1, f2; eapply merge_perms_adds_no_new_perms; eauto. Qed.


  Lemma key_perm_find_map_lookup_iff :
    forall ks k sv,
      KeyPermFind k sv ks <-> ks $? k = sv.
  Proof.
    intros.
    unfold iff; split; intros.
    - invert H; trivial.
    - constructor; trivial.
  Qed.

  Lemma key_perm_lookups_equal1 :
    forall ks1 ks2 k sv,
        KeyPermFind k sv ks1
      -> KeyPermFind k sv ks2
      -> ks1 $? k = ks2 $? k.
  Proof.
    intros.
    invert H; invert H0; auto.
  Qed.

  Lemma key_perm_lookups_equal2 :
    forall ks1 ks2 k,
      ks1 $? k = ks2 $? k
      -> exists sv, KeyPermFind k sv ks1
            /\ KeyPermFind k sv ks2.
  Proof.
    intros.
    cases (ks1 $? k); cases (ks2 $? k);
      repeat
        match goal with
        | [ H : Some _ = _ |- _ ] => invert H
        | [ H : None = _ |- _ ] => invert H
        | [ H : _ $? _ = _ |- _ ] => rewrite <- key_perm_find_map_lookup_iff in H
        end; eexists; intuition eauto.
  Qed.


End KeyPermFind.

Ltac simplify_key_merges1 :=
  match goal with
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_chooses_greatest _ _ H1 H2) by trivial; unfold greatest_permission; simpl
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
    => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_chooses_greatest _ _ H1 H2) in H3 by trivial; unfold greatest_permission in H3; simpl in *
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
    => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _ |- _ ] =>
    match goal with
    | [ H : ?P |- _ ] =>
      match P with
      | context [ks1 $k++ ks2 $? kid]
        => rewrite (merge_perms_chooses_greatest _ _ H1 H2) in H by trivial; unfold greatest_permission; simpl
      end
    end
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None |- _ ] =>
    match goal with
    | [ H : ?P |- _ ] =>
      match P with
      | context [ks1 $k++ ks2 $? kid]
        => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) in H by trivial
      end
    end
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _ |- _ ] =>
    match goal with
    | [ H : ?P |- _ ] =>
      match P with
      | context [ks1 $k++ ks2 $? kid]
        => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) in H by trivial
      end
    end
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None |- _ ] =>
    match goal with
    | [ H : ?P |- _ ] =>
      match P with
      | context [ks1 $k++ ks2 $? kid]
        => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) in H by trivial
      end
    end
  end.

(* Hint Constructors KeyPermFind. *)
Hint Resolve
     find_preserve
     find_merge_greatest'
     found_already_known'
     not_found_already_known'
     find_empty
     find_found
     find_merge_left
     find_merge_right
     find_merge_greatest
     find_merge_neither
.

Ltac solve_greatest :=
  repeat
    match goal with
    | [ |- context [ greatest_permission ] ] => unfold greatest_permission
    | [ |- context [ _ || true ] ] => rewrite orb_true_r
    | [ |- context [ true || _ ] ] => rewrite orb_true_l
    | [ |- context [ ?b || ?b ] ] => rewrite orb_diag
    end; trivial.

Hint Extern 1 (_ = greatest_permission _ _) => solve_greatest.

Ltac simplify_key_merges :=
  repeat
    match goal with
    | [ |- context [ _ $k++ $0 ] ] => rewrite merge_perms_right_identity
    | [ |- context [ $0 $k++ _ ] ] => rewrite merge_perms_left_identity
    | [ |- _ $? ?y = _ $? ?y ] => eapply key_perm_lookups_equal1
    | [ |- context [ _ $? _ = _ ] ] => rewrite <- key_perm_find_map_lookup_iff
    end.

Ltac case_perm_merge ks kid :=
  match ks with
  | context [ ?ks1 $k++ ?ks2 ] => idtac ks1 ks2; case_perm_merge ks1 kid; case_perm_merge ks2 kid
  | _ =>
    match goal with
    | [ H : ks $? kid = Some _ |- _ ] => idtac
    | [ H : ks $? kid = None |- _ ] => idtac
    | _ => cases (ks $? kid)
    end
  end.

Ltac simplify_perm_merges :=
  match goal with
  | [ |- context [ ?ks1 $k++ ?ks2 $? ?kid ] ] =>
    case_perm_merge ks1 kid;
    case_perm_merge ks2 kid
  end.
