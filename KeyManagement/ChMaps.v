From Coq Require Import
     Structures.OrderedType
     Structures.OrderedTypeEx
.

Require Import MyPrelude Tactics Maps.

Inductive channel_id := 
| Single (n : nat)
| Intersection (ch1 ch2 : nat)
.

Module ChannelType <: UsualOrderedType.
  Definition t := channel_id.

  Definition eq := @eq t.
    
  Definition lt ch1 ch2 : Prop :=
    match (ch1, ch2) with
    | (Single n, Single n') => n < n'
    | (Intersection _ _, Single _) => True
    | (Intersection n1 n2, Intersection n1' n2') => (n1 = n1' /\ n2 < n2') \/ n1 < n1'
    | (Single _, Intersection _ _) => False
    end.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros; destruct x, y, z; try Nat.order; try propositional;
      [> left; split | right | right | right ]; Nat.order.
  Qed.

  Lemma lt_not_eq :
    forall x y, lt x y -> ~ eq x y.
  Proof.
    intros * H; destruct x, y; unfold lt in H; unfold not, eq;
      intro EQ; invert EQ; split_ors; subst; try Nat.order.
  Qed.

  Lemma compare :
    forall( x y : t), Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    case_eq (Nat.compare n n0); intro.
    apply EQ; unfold eq; f_equal; now apply nat_compare_eq.
    apply LT; unfold lt; now apply nat_compare_lt.
    apply GT; unfold lt; now apply nat_compare_gt.
    apply GT; unfold lt; eauto.
    apply LT; unfold lt; eauto.
    case_eq (Nat.compare ch1 ch0).
    case_eq (Nat.compare ch2 ch3); intros.
    apply EQ. unfold eq; f_equal; now apply nat_compare_eq.
    apply LT; unfold lt; f_equal; left.
    split; [ now apply nat_compare_eq
           | now apply nat_compare_lt].
    apply GT; unfold lt; left. split. apply Nat.eq_sym. now apply nat_compare_eq. now apply nat_compare_gt.

    intros; apply LT. unfold lt. right. now apply nat_compare_lt.
    intros; apply GT. unfold lt. right. now apply nat_compare_gt.
  Defined.

  Lemma eq_dec :
    forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq; destruct x, y.
    - destruct (eq_dec n n0); subst; eauto.
      right; intros H; invert H; contradiction.
    - right; unfold not; intros; discriminate.
    - right; unfold not; intros; discriminate.

    - cases (ch1 ==n ch0); cases (ch2 ==n ch3); cases (ch1 ==n ch3); cases (ch2 ==n ch0); subst;
        eauto; right; unfold not; intros H; invert H; contradiction.
  Qed.

End ChannelType.

Definition combine (ch1 ch2 : channel_id) :=
  match (ch1, ch2) with
  | (Single n, Single n') => if n <? n'
                            then Some (Intersection n' n)
                            else Some (Intersection n n')
  | _ => None
  end.

Module Import ChMap := MyOrderedMap( ChannelType ).

Module ChMapNotation.
  Notation "#0" := (empty _).
  Notation "m #+ ( k , v )" := (add k v m) (at level 50, left associativity).
  Notation "m #- k" := (remove k m) (at level 50, left associativity).
  Notation "m #? k" := (find k m) (at level 50, left associativity).
End ChMapNotation.

Export ChMapNotation.
  
