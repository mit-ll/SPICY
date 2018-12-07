From Coq Require Import List Classical ClassicalEpsilon.
Require Import Frap Eqdep.

Require Import Common. 
Require IdealWorld.
Require RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Definition idealWorldIsReallyFinalState {A} (U : IdealWorld.universe A) : Prop :=
  Forall (fun '(_,u_data) => exists a, u_data.(IdealWorld.protocol) = IdealWorld.Return a) U.(IdealWorld.users).

Definition realWorldIsReallyFinalState {A} (U : RealWorld.universe A) : Prop :=
  Forall (fun '(_,u_data) => exists a, u_data.(RealWorld.protocol) = RealWorld.Return a) U.(RealWorld.users).

Definition idealWorldReturnOf {A} (c : IdealWorld.user A) : option A :=
  match c.(IdealWorld.protocol) with
  | IdealWorld.Return a => Some a
  | _                   => None
  end.

Definition realWorldReturnOf {A} (c : RealWorld.user_data A) : option A :=
  match c.(RealWorld.protocol) with 
  | RealWorld.Return a => Some a
  | _                  => None
  end.

Fixpoint returnsOfHelper {B : Type} {A : Type -> Type} (users : user_list (A B)) (f : A B -> option B) : list B :=
  match users with
  | []          => []
  | (_,a) :: xs =>
    match f a with
    | Some b => b :: returnsOfHelper xs f
    | None   => returnsOfHelper xs f
    end
  end.

Definition idealWorldReturnsOf {A : Type} (U : IdealWorld.universe A) : list A :=
  returnsOfHelper U.(IdealWorld.users) idealWorldReturnOf.

Definition realWorldReturnsOf {A : Type} (U : RealWorld.universe A) : list A :=
  returnsOfHelper U.(RealWorld.users) realWorldReturnOf.

Definition finalAnswerInclusion {A} (U1 : RealWorld.universe A) (U2 : IdealWorld.universe A) :=

  forall finalStateOfU1, RealWorld.step_universe^* U1 finalStateOfU1
                    -> realWorldIsReallyFinalState finalStateOfU1
                    -> exists finalStateOfU2, IdealWorld.step_universe^* U2 finalStateOfU2
                                        /\ idealWorldIsReallyFinalState finalStateOfU2
                                        /\ realWorldReturnsOf finalStateOfU1 = idealWorldReturnsOf finalStateOfU2.

Definition simulates {A : Type} (R : RealWorld.universe A -> IdealWorld.universe A -> Prop)
           (U1 : RealWorld.universe A) (U2 : IdealWorld.universe A) :=
  (forall U1 U2,
      R U1 U2
      -> forall U1',
        RealWorld.step_universe U1 U1'
        -> exists U2',
          IdealWorld.step_universe^* U2 U2'
          /\ R U1' U2')

  /\ (forall U1 U2,
        R U1 U2
        -> realWorldIsReallyFinalState U1
        -> idealWorldIsReallyFinalState U2
          /\ realWorldReturnsOf U1 = idealWorldReturnsOf U2)

  /\ R U1 U2.

Definition refines {A : Type} (U1 : RealWorld.universe A)(U2 : IdealWorld.universe A) :=
  exists R, simulates R U1 U2.

Infix "<|" := refines (no associativity, at level 70).

Hint Constructors IdealWorld.step_user IdealWorld.step_universe trc.
Hint Resolve in_eq in_cons.

Ltac invert H :=
  (FrapWithoutSets.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.
  
Lemma addKeyTwice :
  forall K V (k : K) (v v' : V) m,
    m $+ (k, v) $+ (k, v') = m $+ (k, v').
Proof.
  intros. maps_equal.
Qed.

(* Question for Adam.  Is there a better way to do this??? *)
Section decide.
  Variable P : Prop.

  Lemma decided : inhabited (sum P (~P)).
  Proof.
    destruct (classic P).
    constructor; exact (inl _ H).
    constructor; exact (inr _ H).
  Qed.

  Definition decide : sum P (~P) :=
    epsilon decided (fun _ => True).
End decide.

Lemma addRemoveKey : 
  forall K V (k : K) (v : V) m,
    m $? k = None
    -> m $+ (k,v) $- k = m.
Proof.
  intros.
  eapply fmap_ext.
  intros.

  destruct (decide (k0 = k)).
  * subst. simplify. eauto.
  * symmetry.
    rewrite <- lookup_add_ne with (k := k) (v := v); auto.
    rewrite lookup_remove_ne; auto.
Qed.

Theorem lookup_empty_not_Some :
  forall K V (k : K) (v : V),
    empty K V $? k = Some v -> False.
Proof.
  intros.
  apply lookup_Some_dom in H.
  rewrite dom_empty in H. invert H.
Qed.

Hint Rewrite addKeyTwice addRemoveKey.
Hint Resolve lookup_add_eq lookup_empty lookup_empty_not_Some.
Hint Resolve IdealWorld.StepUser' IdealWorld.StepSend' IdealWorld.StepRecv'.

Ltac fixcontext :=
  match goal with
  | [ H : $0 $? _ = Some _ |- _ ] => apply lookup_empty_not_Some in H; contradiction
  | [ H : (_ $+ (_, _)) $? _ = Some _ |- _ ] => apply lookup_split in H; propositional; subst
  | [ H : (_, _) = (_,_) |- _ ] => invert H
  | [ H : In _ _ |- _ ] => inversion H; clear H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ H : (_ :: _) = _ |- _ ] => invert H
  end.

Ltac rw_step :=
  match goal with
  | [ H : RealWorld.step_universe _ _ |- _ ] => invert H
  | [ H : RealWorld.step_user _ _ _ |- _ ] => invert H
  end.

Ltac doit :=
  repeat (rw_step; repeat fixcontext).

Hint Constructors Forall.
Hint Unfold simulates.

Ltac process1 :=
  match goal with
  | [ H : simulates _ _ _ |- _ ] => invert H
  | [ H : exists _, _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  end.

Ltac process := repeat process1.

  (* Lemma shouldStepOrDone : *)
  (*   forall {A} {U1 U1' : IdealWorld.universe A} *)
  (*     {U2 : RealWorld.universe A} *)
  (*     {R : IdealWorld.universe A -> RealWorld.universe A -> Prop}, *)
  (*     simulates R U1 U2 *)
  (*     -> IdealWorld.step_universe^* U1 U1' *)
  (*     -> idealWorldIsReallyFinalState U1' *)
  (*     -> idealWorldIsReallyFinalState U1 (* already there! *) *)
  (*       \/ (exists U1'' U2', IdealWorld.step_universe U1 U1'' *)
  (*                      /\ IdealWorld.step_universe^* U1'' U1' *)
  (*                      /\ RealWorld.step_universe^* U2 U2' *)
  (*                      /\ simulates R U1'' U2'). *)
  (* Proof. *)
  (*   intros. *)

  (*   invert H0; process; eauto. *)

  (*   right. *)
  (*   eapply H0 in H4; eauto; process. eexists. eexists. propositional; eauto. *)
  (* Qed. *)

Lemma realWorldManyStepsIdealWorldToo :
  forall {A} {U1 U1': RealWorld.universe A} {R},
    RealWorld.step_universe^* U1 U1'
    -> forall U2, simulates R U1 U2
            -> exists U2', IdealWorld.step_universe^* U2 U2'
                     /\ simulates R U1' U2'.
Proof.
  induct 1; intros; eauto.

  process;
    (* Step forward *)
    (match goal with
     | [ H : (forall _ _, R _ _ -> forall _, _ -> exists _, _) , H1 : R _ _ |- _ ] => eapply H in H1; eauto
     end); process;
    (* Apply induction hypothesis *)
    match goal with
    | [ H : R ?x ?y , IH : forall _, _ -> _ |- _ ]
      => assert (S : simulates R x y) by (unfold simulates; propositional); apply IH in S
    end; process;
    (* Pick correct final state *)
    match goal with
    | [ H : R z ?x |- _ ] => exists x
    end; propositional; eauto using trc_trans.
Qed.

Lemma refines_implies_inclusion :
  forall A (U1 : RealWorld.universe A) (U2 : IdealWorld.universe A),
    U1 <| U2
    -> finalAnswerInclusion U1 U2.
Proof.
  unfold finalAnswerInclusion, refines in *. intros.
  process;
    match goal with
    | [ H : RealWorld.step_universe ^* _ _ |- _ ] => eapply realWorldManyStepsIdealWorldToo in H
    end; process; eauto.
Qed.
