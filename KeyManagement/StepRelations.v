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

  Inductive trcEnd : A -> A -> Prop :=
  | TrcEndRefl : forall x, trcEnd x x
  | TrcBack : forall x y z,
      trcEnd x y
      -> R y z
      -> trcEnd x z.

  Hint Constructors trcEnd.
  
  Lemma TrcFront' : forall x y z,
      R x y
      -> trcEnd y z
      -> trcEnd x z.
  Proof.
    induction 2; eauto.
  Qed.
  
  Hint Resolve TrcFront'.
  
  Theorem trc_trcEnd : forall x y,
      trc x y
      -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcEnd.

  Lemma TrcBack' : forall x y z,
    trc x y
    -> R y z
    -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve TrcBack'.

  Theorem trcEnd_trans : forall x y, trcEnd x y
    -> forall z, trcEnd y z
      -> trcEnd x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trans.
  
  Theorem trcEnd_trc : forall x y, trcEnd x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trc.

  Inductive trcLiteral : A -> A -> Prop :=
  | TrcLiteralRefl : forall x, trcLiteral x x
  | TrcTrans : forall x y z, trcLiteral x y
    -> trcLiteral y z
    -> trcLiteral x z
  | TrcInclude : forall x y, R x y
    -> trcLiteral x y.

  Hint Constructors trcLiteral.

  Theorem trc_trcLiteral : forall x y, trc x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trc : forall x y, trcLiteral x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcLiteral trcLiteral_trc.

  Theorem trcEnd_trcLiteral : forall x y, trcEnd x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trcEnd : forall x y, trcLiteral x y
    -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trcLiteral trcLiteral_trcEnd.

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
(* Notation "< R | P >*" := (trc3 R P) (at level 0). *)

Hint Constructors trc trc3.
