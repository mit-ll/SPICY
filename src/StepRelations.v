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

From Frap Require Export Relations.

Set Implicit Arguments.

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

Hint Constructors trc3 : core.
