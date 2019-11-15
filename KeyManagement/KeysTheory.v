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
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : context [ match honestk $? ?k with _ => _ end ] |- _] => progress context_map_rewrites || cases (honestk $? k)
    | [ |- context [ honestk $? ?k ]] => progress context_map_rewrites || cases (honestk $? k)
    | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b
    | [ |- context [ if ?b then _ else _ ] ] => destruct b
    | [ |- context [ _ $+ (?k1,_) $? ?k2 ] ] => progress clean_map_lookups || (destruct (k1 ==n k2); subst)
    | [ H : context [ _ $+ (?k1,_) $? ?k2 ] |- _ ] => progress clean_map_lookups || (destruct (k1 ==n k2); subst)
    | [ H : ?m $? ?k <> None |- _ ] => cases (m $? k); try contradiction; clear H
    | [ H : filter _ _ $? _ = Some _ |- _ ] => rewrite <- find_mapsto_iff, filter_iff in H by auto 1
    | [ |- filter _ _ $? _ = Some _ ] => rewrite <- find_mapsto_iff, filter_iff by auto 1
    | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
    | [ |- context [ MapsTo _ _ _ ] ] => rewrite find_mapsto_iff
    | [ H1 : _ = true , H2 : _ = false |- _ ] => rewrite H1 in H2; invert H2
    | [ |- filter _ _ $? _ = None ] => rewrite <- not_find_in_iff; unfold not; intros
    | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
    end.
  
  Ltac simplify_filter1 :=
    match goal with
    | [ H : context[fold _ (_ $+ (_, _)) _] |- _] => rewrite fold_add in H by auto 2 
    | [ H : context[if ?cond then (fold _ _ _) $+ (_, _) else (fold _ _ _)] |- _ ] => cases cond
    end.

  Ltac keys_solver honestk :=
    repeat (keys_solver1 honestk || clean_map_lookups1 || simplify_filter1).

  Lemma honest_key_filter_fn_filter_transpose :
    forall honestk,
      transpose_neqkey eq (fun k v m => if honest_key_filter_fn honestk k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, honest_key_filter_fn; intros.
    keys_solver honestk; eauto.
    (* issue-072 *)
    rewrite map_ne_swap; auto.
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
       honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal.

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
    induction ks using P.map_induction_bis; intros; Equal_eq;
      unfold clean_keys,filter in *; keys_solver honestk; eauto.
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
    induction ks using P.map_induction_bis; intros; Equal_eq;
      unfold clean_keys in *;
      keys_solver honestk; eauto.
  Qed.

  Hint Resolve clean_keys_adds_no_keys.

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
    rewrite map_ne_swap; auto.
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
       honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal.

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
    induction ks using P.map_induction_bis; intros; Equal_eq;
      unfold clean_key_permissions,filter in *;
      keys_solver honestk; eauto.
  Qed.

  Lemma clean_key_permissions_adds_no_permissions :
    forall honestk k_id ks,
        ks $? k_id = None
      -> clean_key_permissions honestk ks $? k_id = None.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq;
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
       clean_key_permissions_drops_dishonest_permission.

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
      | [ H1 : perms1 $? _ = Some _ |- _] => eapply clean_key_permissions_inv' in H; swap 1 2; [simplify_key_merges1|]; eauto
      | [ H1 : perms2 $? _ = Some _ |- _] => eapply clean_key_permissions_inv' in H; swap 1 2; [simplify_key_merges1|]; eauto
      end
    | [ H : honest_perm_filter_fn _ _ _ = _ |- _ ] => unfold honest_perm_filter_fn in H
    | [ H : forall k_id kp, ?pubk $? k_id = Some kp -> _, ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
    end.

  Lemma clean_key_permissions_distributes_merge_key_permissions :
    forall honestk perms1 perms2,
      clean_key_permissions honestk (perms1 $k++ perms2) = clean_key_permissions honestk perms1 $k++ clean_key_permissions honestk perms2.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions honestk perms1 $? y);
      cases (clean_key_permissions honestk perms2 $? y);
      cases (clean_key_permissions honestk (perms1 $k++ perms2) $? y);
      repeat (keys_solver1 honestk
              || clean_map_lookups1
              || simplify_key_merges1
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
    apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions honestk perms $? y);
      cases (clean_key_permissions honestk pubk $? y);
      cases (pubk $? y);
      repeat (keys_solver1 honestk
              || clean_map_lookups1
              || simplify_key_merges1
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

End CleanKeys.


Hint Resolve
     honest_key_filter_fn_proper
     honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
     honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal
     honest_perm_filter_fn_proper
     honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
     honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal.
