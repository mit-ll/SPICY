From Coq Require Import
  FSets.FMapList
  FSets.FMapFacts
  Structures.OrderedTypeEx.

Module Import NatMap := FMapList.Make(Nat_as_OT).
Module P := WProperties_fun Nat_as_OT NatMap.
Module F := P.F.

Export NatMap P F.

From Coq Require List.

Set Implicit Arguments.

Notation "$0" := (empty _).
Notation "m $+ ( k , v )" := (add k v m) (at level 50, left associativity).
Notation "m $- k" := (remove k m) (at level 50, left associativity).
Notation "m $? k" := (find k m) (at level 50, left associativity).

Definition user_id              := nat.
Definition user_list (A : Type) := NatMap.t A.

Definition updateUserList {V : Type} (usrs : user_list V) (u : user_id) (u_d : V) : user_list V :=
  usrs $+ (u,u_d).

(* Infix "$<=" := includes (at level 90). *)

Definition merge_maps {V : Type} (m1 m2 : NatMap.t V) : NatMap.t V :=
  fold (fun k v m => m $+ (k,v) ) m1 m2.

Notation "m1 $++ m2" := (merge_maps m2 m1) (at level 50, left associativity).

Lemma lookup_split : forall V (m : NatMap.t V) k v k' v',
    (m $+ (k, v)) $? k' = Some v'
    -> (k' <> k /\ m $? k' = Some v') \/ (k' = k /\ v' = v).
Proof.
  intros.
  case (eq_dec k k').
  - intros.
    subst.
    right; intuition.
    rewrite add_eq_o in H by auto.
    congruence.
  - intros. left.
    intuition.
    rewrite add_neq_o in H by auto.
    exact H.
Qed.

Lemma lookup_split' : forall V (m : NatMap.t V) k v,
    m $? k = Some v
    -> fold (fun k' v' p => p \/ (k = k' /\ v = v')) m False.
Proof.
  intros.
  (* rewrite <- find_mapsto_iff in H. *)
  revert dependent H.
  apply P.fold_rec; intros.

  - rewrite <- find_mapsto_iff in H0.
    specialize (H k v). contradiction.

  - case (eq_dec k k0).
    + intros. subst.
      right; intuition.
      unfold Add in H1.
      specialize (H1 k0). rewrite H3 in H1.
      symmetry in H1; rewrite <- find_mapsto_iff in H1.
      rewrite add_mapsto_iff in H1.
      destruct H1; intuition.
    + intros. left. apply H2; auto.
      (* rewrite <- find_mapsto_iff in H3. unfold Add in *. *)
      specialize (H1 k). rewrite H3 in H1. symmetry in H1.
      rewrite <- find_mapsto_iff in H1.
      rewrite add_mapsto_iff in H1.
      destruct H1; intuition.
      symmetry in H4; contradiction.
      apply find_mapsto_iff; auto.
Qed.

Lemma lookup_some_implies_in : forall V (m : NatMap.t V) k v,
    m $? k = Some v
    -> List.In (k,v) (to_list m).
Proof.
  intros.

  rewrite <- find_mapsto_iff in H.
  rewrite elements_mapsto_iff in H.
  rewrite InA_alt in H.
  destruct H. destruct H.
  unfold to_list.

  unfold eq_key_elt, Raw.PX.eqke in H; simpl in H.
  destruct H.
  subst.
  rewrite (surjective_pairing x) in H0.
  assumption.
Qed.
