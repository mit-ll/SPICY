(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     String
     Sumbool
     Eqdep.

From SPICY Require Import
     MyPrelude.

Set Implicit Arguments.

Ltac split_ands :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac split_ex :=
  repeat match goal with
         | [ H : exists _, _ |- _ ] => destruct H
         | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac split_ors :=
  repeat
    match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    end; split_ex.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Ltac is_not_var V :=
  first [ is_var V; fail 1
        | idtac ].

Ltac is_not_evar V :=
  first [ is_evar V; fail 1
        | idtac ].

Ltac does_not_unify term1 term2 :=
  first [ unify term1 term2; fail 1
        | idtac ].

Ltac prop_not_exists P :=
  match goal with
  | [ H : P |- _ ] => fail 1
  | _ => idtac
  end.

Ltac prop_not_unifies P :=
  match goal with
  (* | [ H : P |- _ ] => fail 1 *)
  | [ H : ?Q |- _ ] => unify P Q; fail 1
  | _ => idtac
  end.

Ltac assert_if_new P tac :=
  match goal with
  | [ H : P |- _ ] => fail 1
  | _ => assert P by tac
  end.

Global Set Structural Injection.

Section OtherInvLemmas.

  Lemma nil_not_app_cons :
    forall A (l1 l2 : list A) e,
      [] = l1 ++ e :: l2
      -> False.
  Proof.
    intros.
    destruct l1.
    rewrite app_nil_l in H; invert H.
    rewrite <- app_comm_cons in H; invert H.
  Qed.

  Lemma some_eq_inv :
    forall A (a a' : A), Some a = Some a' -> a = a'.
  Proof. intros * H; injection H; trivial. Qed.
    
  Lemma tuple_eq_inv :
    forall A B (a a' : A) (b b' : B), (a,b) = (a',b') -> a = a' /\ b = b'.
  Proof. intros * H; invert H; eauto. Qed.

  Lemma list_eq_inv :
    forall A (x x' : A) xs xs', x :: xs = x' :: xs' -> x = x' /\ xs = xs'.
  Proof. intros * H; invert H; eauto. Qed.

End OtherInvLemmas.


Ltac invert_base_equalities1 :=
  discriminate
  || contradiction
  || (progress split_ex)
  || match goal with
    | [ H : ?x = ?x |- _ ] => clear H
    | [ H : ?x <> ?x |- _ ] => contradict H; trivial
    (* | [ H : exists _, _ |- _ ] => destruct H *)
    (* | [ H : _ /\ _ |- _ ] => destruct H *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
    | [ H : Some _ = Some _ |- _ ] => injection H; subst (* apply some_eq_inv in H; subst *)
    | [ H : (_ :: _) = (_ :: _) |- _ ] => injection H; subst (* apply list_eq_inv in H; split_ex; subst *)
    | [ H : (_ :: _) = ?x |- _ ] => is_var x; invert H
    | [ H : ?x = (_ :: _) |- _ ] => is_var x; invert H
    | [ H : (_,_) = (_,_) |- _ ] => injection H; subst (* apply tuple_eq_inv in H; split_ex; subst *)
    | [ H : [] = _ ++ _ :: _ |- _ ] => apply nil_not_app_cons in H; contradiction
    (* | [ H : Some _ = Some _ |- _ ] => injection H; subst *)
    | [ H1 : ?lhs = true , H2 : ?lhs = false |- _ ] => rewrite H1 in H2; discriminate H2
    | [ H : Some ?x1 <> Some ?x2 |- _ ] =>
      let I := fresh "I" in
      assert (x1 <> x2) by (unfold not; intro I; apply (f_equal Some) in I; contradiction); clear H
    | [ H : Some ?x1 = Some ?x2 -> False |- _ ] =>
      let I := fresh "I" in
      assert (x1 <> x2) by (unfold not; intro I; apply (f_equal Some) in I; contradiction); clear H
    end.

Lemma Forall_app_sym :
  forall {A} (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P (l2 ++ l1).
Proof.
  split; intros;
    rewrite Forall_forall in *; intros;
      repeat 
        match goal with
        | [ H : forall x, _ -> ?P x |- ?P ?x ] => apply H
        | [ |- In _ (_ ++ _) ] => rewrite in_app_iff
        | [ H : In _ (_ ++ _) |- _ ] => rewrite in_app_iff in H
        end; intuition eauto.
Qed.

Lemma Forall_app :
  forall {A} (P : A -> Prop) (l : list A) a,
    Forall P (l ++ [a]) <-> Forall P (a :: l).
Proof.
  intros.
  rewrite Forall_app_sym; simpl; split; trivial.
Qed.

Lemma Forall_dup :
  forall {A} (P : A -> Prop) (l : list A) a,
    Forall P (a :: a :: l) <-> Forall P (a :: l).
Proof.
  split; intros;
    rewrite Forall_forall in *; intros;
      repeat
        match goal with
        | [ H : forall x, _ -> ?P x |- ?P ?x ] => apply H
        | [ H : In _ (_ :: _) |- _ ] => apply in_inv in H
        end; split_ors; subst; simpl; eauto.
Qed.

