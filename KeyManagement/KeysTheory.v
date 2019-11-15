From Coq Require Import
     List
     Morphisms
     Eqdep
.

Require Import
        MyPrelude
        Maps
        Messages
        Common
        MapLtac
        Keys
        Automation
        Tactics
        RealWorld
        AdversaryUniverse.

Set Implicit Arguments.

Section CleanKeys.
  Import RealWorld.

  Variable honestk : key_perms.

  Lemma honest_key_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) (honest_key_filter_fn honestk).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_key_filter_fn_filter_proper :
    Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_key_filter_fn_filter_transpose :
    transpose_neqkey eq (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey; intros.
    unfold honest_key_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Lemma honest_key_filter_fn_filter_proper_Equal :
    Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    destruct (honest_key_filter_fn honestk y y0); eauto.
    destruct (y ==n y2); subst; clean_map_lookups; auto.
  Qed.

  Lemma honest_key_filter_fn_filter_transpose_Equal :
    transpose_neqkey Equal (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal; intros.
    unfold honest_key_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Hint Resolve
       honest_key_filter_fn_proper
       honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
       honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal.

  Lemma clean_keys_inv :
    forall k_id k ks,
      clean_keys honestk ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_key_filter_fn honestk k_id k = true.
  Proof.
    unfold clean_keys; intros until ks.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_keys_inv' :
    forall k_id k ks,
      clean_keys honestk ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = false.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; clean_map_lookups; eauto.

    destruct (x ==n k_id); subst; clean_map_lookups; eauto.
    - unfold clean_keys,filter in H0; rewrite fold_add in H0; eauto.
      cases (honest_key_filter_fn honestk k_id k); clean_map_lookups; try discriminate; trivial.
    - eapply IHks; eauto.
      unfold clean_keys, filter in H0.
      rewrite fold_add in H0; eauto.
      cases (honest_key_filter_fn honestk x e); eauto.
      clean_map_lookups; eauto.
  Qed.

  Lemma clean_keys_keeps_honest_key :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = true
      -> clean_keys honestk ks $? k_id = Some k.
  Proof.
    unfold clean_keys; intros.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
    rewrite find_mapsto_iff; eauto.
  Qed.

  Lemma clean_keys_drops_dishonest_key :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn honestk k_id k = false
      -> clean_keys honestk ks $? k_id = None.
  Proof.
    unfold clean_keys; intros.
    rewrite <- not_find_in_iff.
    unfold not; intros.
    rewrite in_find_iff in H1.
    cases (filter (honest_key_filter_fn honestk) ks $? k_id); try contradiction.
    rewrite <- find_mapsto_iff in Heq.
    rewrite filter_iff in Heq; eauto.
    split_ands.
    rewrite find_mapsto_iff in H2.
    clean_map_lookups.
    rewrite H0 in H3; discriminate.
  Qed.

  Lemma clean_keys_adds_no_keys :
    forall k_id ks,
        ks $? k_id = None
      -> clean_keys honestk ks $? k_id = None.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
    unfold clean_keys, filter; rewrite fold_add; eauto.
    destruct (x ==n k_id); subst; clean_map_lookups.
    destruct (honest_key_filter_fn honestk x e); eauto.
    clean_map_lookups; eauto.
  Qed.

  Lemma clean_keys_idempotent :
    forall ks,
      clean_keys honestk (clean_keys honestk ks) = clean_keys honestk ks.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (clean_keys honestk ks $? y); eauto using clean_keys_adds_no_keys.
    eapply clean_keys_keeps_honest_key; auto.
    apply clean_keys_inv in Heq; split_ands; auto.
  Qed.

  Lemma honest_perm_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) (honest_perm_filter_fn honestk).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper :
    Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_perm_filter_fn honestk  k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose :
    transpose_neqkey eq (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey; intros.
    unfold honest_perm_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper_Equal :
    Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    destruct (honest_perm_filter_fn honestk y y0); eauto.
    destruct (y ==n y2); subst; clean_map_lookups; auto.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose_Equal :
    transpose_neqkey Equal (fun k v m => if honest_perm_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal; intros.
    unfold honest_perm_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Hint Resolve
       honest_perm_filter_fn_proper
       honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
       honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal.

  Lemma clean_key_permissions_inv :
    forall k_id k ks,
      clean_key_permissions honestk ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_perm_filter_fn honestk k_id k = true.
  Proof.
    unfold clean_key_permissions; intros until ks.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_key_permissions_inv' :
    forall k_id k ks,
      clean_key_permissions honestk ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = false.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; clean_map_lookups; eauto.

    destruct (x ==n k_id); subst; clean_map_lookups; eauto.
    - unfold clean_key_permissions,filter in H0; rewrite fold_add in H0; eauto.
      cases (honest_perm_filter_fn honestk k_id k); clean_map_lookups; try discriminate; trivial.
    - eapply IHks; eauto.
      unfold clean_key_permissions, filter in H0.
      rewrite fold_add in H0; eauto.
      cases (honest_perm_filter_fn honestk x e); eauto.
      clean_map_lookups; eauto.
  Qed.

  Lemma clean_key_permissions_adds_no_permissions :
    forall k_id ks,
        ks $? k_id = None
      -> clean_key_permissions honestk ks $? k_id = None.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
    unfold clean_key_permissions, filter; rewrite fold_add; eauto.
    destruct (x ==n k_id); subst; clean_map_lookups.
    destruct (honest_perm_filter_fn honestk x e); eauto.
    clean_map_lookups; eauto.
  Qed.

  Lemma clean_key_permissions_keeps_honest_permission :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = true
      -> clean_key_permissions honestk ks $? k_id = Some k.
  Proof.
    unfold clean_key_permissions; intros.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
    rewrite find_mapsto_iff; eauto.
  Qed.

  Lemma clean_key_permissions_drops_dishonest_permission :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn honestk k_id k = false
      -> clean_key_permissions honestk ks $? k_id = None.
  Proof.
    unfold clean_key_permissions; intros.
    rewrite <- not_find_in_iff.
    unfold not; intros.
    rewrite in_find_iff in H1.
    cases (filter (honest_perm_filter_fn honestk) ks $? k_id); try contradiction.
    rewrite <- find_mapsto_iff in Heq.
    rewrite filter_iff in Heq; eauto.
    split_ands.
    rewrite find_mapsto_iff in H2.
    clean_map_lookups.
    rewrite H0 in H3; discriminate.
  Qed.

  Lemma clean_key_permissions_idempotent :
    forall ks,
      clean_key_permissions honestk ks = clean_key_permissions honestk (clean_key_permissions honestk ks).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    symmetry; cases (clean_key_permissions honestk ks $? y).
    - generalize (clean_key_permissions_inv _ _ Heq); intros;
        split_ands; apply clean_key_permissions_keeps_honest_permission; eauto.
    - eapply clean_key_permissions_adds_no_permissions; eauto.
  Qed.

  Lemma clean_key_permissions_distributes_merge_key_permissions :
    forall perms1 perms2,
      clean_key_permissions honestk (perms1 $k++ perms2) = clean_key_permissions honestk perms1 $k++ clean_key_permissions honestk perms2.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions honestk perms1 $? y);
      cases (clean_key_permissions honestk perms2 $? y);
      cases (clean_key_permissions honestk (perms1 $k++ perms2) $? y); simplify_key_merges1; eauto;
        repeat (
            match goal with
            | [ H1 : honest_perm_filter_fn _ ?y _ = true, H2 : honest_perm_filter_fn _ ?y _ = false |- _ ] =>
              unfold honest_perm_filter_fn in *; cases (honestk $? y); try discriminate
            | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b; try discriminate
            | [ H : clean_key_permissions _ _ $? _ = Some _ |- _ ] => apply clean_key_permissions_inv in H
            | [ H0 : ?perms $? ?y = Some _ , H : clean_key_permissions _ ?perms $? ?y = None |- _ ] =>
              apply (clean_key_permissions_inv' _ _ H) in H0; clear H
            | [ H1 : _ $? ?y = Some _, H2 : perms1 $k++ perms2 $? ?y = None |- _ ] =>
              apply merge_perms_no_disappear_perms in H2; split_ands; contra_map_lookup
            | [ H0 : ?perms $? ?y = None , H : clean_key_permissions _ ?perms $? ?y = None |- _ ] =>
              simplify_key_merges1; eauto 2
            | [ H : clean_key_permissions _ ?perms $? ?y = None |- _ ] =>
              match goal with
                | [ H : perms $? y = _ |- _ ] => fail 1
                | _ => cases (perms $? y)
              end
            | [ H1 : perms1 $? ?y = _, H2 : perms2 $? ?y = _ |- _ ] => simplify_key_merges1
            end; split_ands; auto 2).
  Qed.

  Lemma clean_honest_key_permissions_distributes :
    forall perms pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> clean_key_permissions honestk (perms $k++ pubk) = clean_key_permissions honestk perms $k++ pubk.
  Proof.
    intros.

    rewrite clean_key_permissions_distributes_merge_key_permissions.
    apply map_eq_Equal; unfold Equal; intros.
    cases (pubk $? y).
    - specialize (H _ _ Heq); split_ands; subst.
      assert (clean_key_permissions honestk pubk $? y = Some false)
        by (eapply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial).
      cases (clean_key_permissions honestk perms $? y);
        simplify_key_merges; eauto.
    - assert (clean_key_permissions honestk pubk $? y = None) 
        by (apply clean_key_permissions_adds_no_permissions; eauto).
      cases (clean_key_permissions honestk perms $? y);
        simplify_key_merges; eauto.
  Qed.

  Lemma adv_no_honest_key_honest_key :
    forall pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true.
  Proof.
    intros.
    specialize (H _ _ H0); intuition idtac.
  Qed.

End CleanKeys.
