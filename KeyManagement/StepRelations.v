Set Implicit Arguments.

Section trc.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive trc : A -> A -> Prop :=
  | TrcRefl : forall x, trc x x
  | TrcFront : forall x y z,
    R x y
    -> trc y z
    -> trc x z.

  Hint Constructors trc.

  Theorem trc_one : forall x y, R x y
    -> trc x y.
  Proof.
    eauto.
  Qed.

  Hint Resolve trc_one.

  Theorem trc_trans : forall x y, trc x y
    -> forall z, trc y z
      -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trans.

End trc.

Section trc_tri.
  Variable A B : Type.
  Variable R : A -> B -> A -> Prop.
  (* Variable P : B -> Prop. *)

  Inductive trc3 (P : B -> Prop) : A -> A -> Prop :=
  | Trc3Refl : forall x, trc3 P x x
  | Trc3Front : forall x y z b,
      P b
      -> R x b y
      -> trc3 P y z
      -> trc3 P x z.

  Hint Constructors trc3.

  Theorem trc3_one : forall x y b (P : B -> Prop), P b -> R x b y
    -> trc3 P x y.
  Proof.
    eauto.
  Qed.

  Hint Resolve trc3_one.

  Theorem trc3_trans : forall x y (P : B -> Prop), trc3 P x y
    -> forall z, trc3 P y z
      -> trc3 P x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc3_trans.

End trc_tri.

Notation "R ^*" := (trc R) (at level 0).
Notation "R / P ^*" := (trc3 R P) (at level 0).

Hint Constructors trc trc3.
