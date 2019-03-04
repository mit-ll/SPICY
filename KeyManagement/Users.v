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
(* Definition user_list (A : Type) := list (nat * A). *)
Definition user_list (A : Type) := NatMap.t A.

(* Definition updF {V : Type} (u : user_id) (v : V) : nat * V -> nat * V := *)
(*   fun p => let '(u',v') := p in (u', if u ==n u' then v else v'). *)

Definition updateUserList {V : Type} (usrs : user_list V) (u : user_id) (u_d : V) : user_list V :=
  (* map (updF u u_d) usrs. *)
  (* NatMap.add u u_d usrs. *)
  (* mapi (fun k v => if eq_dec k u then u_d else v) usrs. *)
  usrs $+ (u,u_d).

(* Infix "$-" := remove (at level 50, left associativity). *)
(* Infix "$++" := join (at level 50, left associativity). *)
(* Infix "$?" := lookup (at level 50, no associativity). *)
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


(* Lemma update_inserted : *)
(*   forall {V} u_id v v' (usrs : user_list V), *)
(*         In (u_id,v)  usrs *)
(*       -> In (u_id,v') (updateUserList usrs u_id v'). *)
(* Proof. *)
(*   intros. *)
(*   assert (FX: (updF u_id v') (u_id,v) = (u_id,v')) *)
(*     by (simpl; cases (u_id ==n u_id); [reflexivity | contradiction]). *)
(*   rewrite <- FX. *)
(*   unfold updateUserList. *)
(*   eapply in_map; eauto. *)
(* Qed. *)

(* Definition keys_uniq {V} (usrs : user_list V) : Prop := *)
(*   forall k v, *)
(*     In (k,v) usrs *)
(*     -> forall v', In (k,v') usrs *)
(*             -> v = v'. *)

(* Lemma keys_uniq_in : *)
(*   forall {V} k v (usrs : user_list V), *)
(*     In (k,v) usrs *)
(*     -> keys_uniq usrs *)
(*     -> exists l1 l2, *)
(*         usrs = l1 ++ (k,v) :: l2 *)
(*         /\ (forall v', In (k,v') l1 -> v = v') *)
(*         /\ (forall v', In (k,v') l2 -> v = v'). *)
(* Proof. *)
(*   intros. *)

(*   pose proof (in_split (k,v) usrs H) as IN. *)
(*   destruct IN as [l1 IN]. destruct IN as [l2 IN]. *)
(*   exists l1. exists l2. *)
(*   unfold keys_uniq in H0. *)
(*   propositional; eauto. *)

(*   eapply H0; eauto. rewrite IN. eapply in_or_app; eauto. *)
(*   eapply H0; eauto. rewrite IN. eapply in_or_app. right. eapply in_cons; eauto. *)
(* Qed. *)

(* Lemma in_then_same : *)
(*   forall {V} k v (l : user_list V), *)
(*     (forall v', In (k, v') l -> v = v') *)
(*     -> map (updF k v) l = l. *)
(* Proof. *)
(*   intros. *)
(*   induct l; auto; simpl. *)

(*   destruct a as [k' v']. *)

(*   unfold updF at 1. cases (k ==n k'). *)
(*   rewrite e in H. *)
(*   pose proof (H v') as CONTRA. simpl in CONTRA. destruct CONTRA; eauto. *)
(*   rewrite IHl; eauto. rewrite e. *)
(*   intros. *)
(*   eapply H; simpl; eauto. *)

(*   simpl in H. *)
(*   rewrite IHl; eauto. *)
(* Qed. *)

(* Lemma update_identity_idem : *)
(*   forall {V} u_id v (usrs : user_list V), *)
(*       keys_uniq usrs *)
(*     -> In (u_id,v) usrs *)
(*     -> usrs = updateUserList usrs u_id v. *)
(* Proof. *)
(*   intros. *)
(*   unfold updateUserList. *)

(*   pose proof (keys_uniq_in u_id v H0 H). *)
(*   destruct H1 as [l1]. *)
(*   destruct H1 as [l2]. *)
(*   destruct H1. *)
(*   destruct H2. *)
(*   rewrite H1. *)
(*   rewrite map_app; simpl. *)
(*   cases (u_id ==n u_id); swap 1 2. contradiction. *)
(*   rewrite (in_then_same); eauto. *)
(*   rewrite (in_then_same); eauto. *)
(* Qed. *)
