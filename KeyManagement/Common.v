Require Import Frap.
Set Implicit Arguments.


Definition user_id              := nat.
Definition user_list (A : Type) := list (user_id * A).

Definition updF {V : Type} (u : user_id) (v : V) : nat * V -> nat * V :=
  fun p => let '(u',v') := p in (u', if u ==n u' then v else v').

Definition updateUserList {V : Type} (usrs : user_list V) (u : user_id) (u_d : V) : user_list V :=
  map (updF u u_d) usrs.

Lemma update_inserted :
  forall {V} u_id v v' (usrs : user_list V),
        In (u_id,v)  usrs
      -> In (u_id,v') (updateUserList usrs u_id v').
Proof.
  intros.
  assert (FX: (updF u_id v') (u_id,v) = (u_id,v'))
    by (simpl; cases (u_id ==n u_id); [reflexivity | contradiction]).
  rewrite <- FX.
  unfold updateUserList.
  eapply in_map; eauto.
Qed.

Definition keys_uniq {V} (usrs : user_list V) : Prop :=
  forall k v,
    In (k,v) usrs
    -> forall v', In (k,v') usrs
            -> v = v'.

Lemma keys_uniq_in :
  forall {V} k v (usrs : user_list V),
    In (k,v) usrs
    -> keys_uniq usrs
    -> exists l1 l2,
        usrs = l1 ++ (k,v) :: l2
        /\ (forall v', In (k,v') l1 -> v = v')
        /\ (forall v', In (k,v') l2 -> v = v').
Proof.
  intros.

  pose proof (in_split (k,v) usrs H) as IN.
  destruct IN as [l1 IN]. destruct IN as [l2 IN].
  exists l1. exists l2.
  unfold keys_uniq in H0.
  propositional; eauto.

  eapply H0; eauto. rewrite IN. eapply in_or_app; eauto.
  eapply H0; eauto. rewrite IN. eapply in_or_app. right. eapply in_cons; eauto.
Qed.

Lemma in_then_same :
  forall {V} k v (l : user_list V),
    (forall v', In (k, v') l -> v = v')
    -> map (updF k v) l = l.
Proof.
  intros.
  induct l; auto; simpl.

  destruct a as [k' v'].

  unfold updF at 1. cases (k ==n k').
  rewrite e in H.
  pose proof (H v') as CONTRA. simpl in CONTRA. destruct CONTRA; eauto.
  rewrite IHl; eauto. rewrite e.
  intros.
  eapply H; simpl; eauto.

  simpl in H.
  rewrite IHl; eauto.
Qed.

Lemma update_identity_idem :
  forall {V} u_id v (usrs : user_list V),
      keys_uniq usrs
    -> In (u_id,v) usrs
    -> usrs = updateUserList usrs u_id v.
Proof.
  intros.
  unfold updateUserList.

  pose proof (keys_uniq_in u_id v H0 H).
  destruct H1 as [l1].
  destruct H1 as [l2].
  destruct H1.
  destruct H2.
  rewrite H1.
  rewrite map_app; simpl.
  cases (u_id ==n u_id); swap 1 2. contradiction.
  rewrite (in_then_same); eauto.
  rewrite (in_then_same); eauto.
Qed.

(* Syntactic type of types for messages *)
Inductive type :=
| Nat : type
| Unit : type
(* We will definitely need Text, but do we also need special
 * types for, say, keys.  If so, then we most definitely need
 * type to be implemented separately for both Real and Ideal worlds.
 *
 * | Text : type
 *)
| Prod (t1 t2 : type) : type
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat  => nat
  | Unit => unit
  | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end.



(* Exisistential wrapper for stuff, so we can put it in collections *)
Inductive exmsg : Type :=
| Exm {A : Type} (wrapped : A) : exmsg.

(* Labels for the labeled transition system *)
Inductive label  {A} : Type :=
  Silent : label
| Action :  A -> label
.

Lemma pair_uneq_if_fst_uneq:
  forall {A: Type} (p1 p2 : (user_id * A)) ineq,
    ((fst p1) ==n (fst p2)) = right ineq
    -> p1 <> p2.
Proof.
  intros. simpl. destruct p1 as [u1 a1]. destruct p2 as [u2 a2].
  simpl in *. unfold not; intros. inversion H0. auto.
Qed.

Hint Resolve pair_uneq_if_fst_uneq.

(* Theorem update_adds_no_duplicate_keys: *)
(*   forall {V} (users users' : user_list V) u_id v, *)
(*     (forall u_id1 u_id2 v1 v2, *)
(*         In (u_id1,v1) users -> In (u_id2,v2) users -> u_id1 <> u_id2 \/ (u_id1 = u_id2 /\ v1 = v2)) *)
(*     -> updateUserList users u_id v = users' *)
(*     -> forall u_id1 u_id2 v1 v2, *)
(*         In (u_id1,v1) users' -> In (u_id2,v2) users' -> u_id1 <> u_id2 \/ (u_id1 = u_id2 /\ v1 = v2). *)
(* Proof. *)
(*   induct users; intros; simpl in *; rewrite <- H0 in H1; rewrite <- H0 in H2. *)
(*   - right. apply in_inv in H1; apply in_inv in H2. propositional; inversion H3; inversion H1; subst; auto. *)
(*   - cases (u_id1 ==n u_id2). *)
(*     + subst. destruct a. apply H; cases (u_id2 ==n u); right; subst; propositional. *)
