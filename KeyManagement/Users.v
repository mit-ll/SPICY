From Coq Require Import
  FSets.FMapList
  FSets.FMapFacts
  Structures.OrderedTypeEx.

Module Import NatMap := FMapList.Make(Nat_as_OT).
Module P := WProperties_fun Nat_as_OT NatMap.
Module F := P.F.

Export NatMap P F.

Set Implicit Arguments.

Definition user_id              := nat.
(* Definition user_list (A : Type) := list (nat * A). *)
Definition user_list (A : Type) := NatMap.t A.

(* Definition updF {V : Type} (u : user_id) (v : V) : nat * V -> nat * V := *)
(*   fun p => let '(u',v') := p in (u', if u ==n u' then v else v'). *)

Definition updateUserList {V : Type} (usrs : user_list V) (u : user_id) (u_d : V) : user_list V :=
  (* map (updF u u_d) usrs. *)
  NatMap.add u u_d usrs.

Notation "$0" := (empty _).
Notation "m $+ ( k , v )" := (add k v m) (at level 50, left associativity).
Notation "m $- k" := (remove k m) (at level 50, left associativity).
Notation "m $? k" := (find k m) (at level 50, left associativity).
(* Infix "$-" := remove (at level 50, left associativity). *)
(* Infix "$++" := join (at level 50, left associativity). *)
(* Infix "$?" := lookup (at level 50, no associativity). *)
(* Infix "$<=" := includes (at level 90). *)

Definition merge_maps {V : Type} (m1 m2 : NatMap.t V) : NatMap.t V :=
  fold (fun k v m => m $+ (k,v) ) m1 m2.

Notation "m1 $++ m2" := (merge_maps m2 m1) (at level 50, left associativity).

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
