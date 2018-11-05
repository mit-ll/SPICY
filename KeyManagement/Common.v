Require Import Frap.
Set Implicit Arguments.


Definition user_id              := nat.
Definition user_list (A : Type) := list (user_id * A).

Fixpoint updateUserList {V : Type} (usrs : user_list V) (u : user_id) (u_d : V) :=
  match usrs with
  | (k,v) :: usrs' => if k ==n u
                     then (u,u_d) :: usrs' (* Case we are interested in *)
                     else (k,v)   :: updateUserList usrs' u u_d
  | []             => [(u,u_d)]
  end.

Theorem update_inserted:
  forall V (users users' : user_list V) u_id v,
    updateUserList users u_id v = users'
    -> In (u_id,v) users'.
Proof.
  induct users; intros.
  - unfold updateUserList in H. invert H. apply in_eq.
  - destruct a. simpl in *. cases (u_id ==n u). simpl.
    + rewrite e in *. rewrite <- H. cases (u ==n u); auto using in_eq. destruct n. trivial.
    + cases (u ==n u_id).
      * rewrite e in n. destruct n. trivial.
      * destruct users'.
        invert H.
        apply in_cons. apply IHusers. inversion H. trivial.
Qed.


Print eq_nat_dec.

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
