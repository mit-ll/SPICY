(* From Coq Require Import Basics. *)
Require Import Frap.

Require Import Common.
Require IdealWorld.
Require RealWorld.

Set Implicit Arguments.



Definition idealWorldIsReallyFinalState {A} (U : IdealWorld.universe A) : Prop :=
  Forall (fun '(_,prog) => exists a, prog = IdealWorld.Return a) U.(IdealWorld.users).

Definition realWorldIsReallyFinalState {A} (U : RealWorld.universe A) : Prop :=
  Forall (fun '(_,u_data) => exists a, u_data.(RealWorld.protocol) = RealWorld.Return a) U.(RealWorld.users).

Definition idealWorldReturnOf {A} (c : IdealWorld.cmd A) : option A :=
  match c with
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

(* Fixpoint idealWorldReturnsOf' {A} (users : user_list (IdealWorld.cmd A)) : list A := *)
(*   match users with *)
(*   | []      => [] *)
(*   | (_,c) :: xs => *)
(*     match idealWorldReturnOf c with *)
(*     | Some a => a :: idealWorldReturnsOf' xs *)
(*     | None   => idealWorldReturnsOf' xs *)
(*     end *)
(*     (* match c in (IdealWorld.cmd A') return (list A' -> list A') with *) *)
(*     (* | IdealWorld.Return a => fun xs => a :: xs *) *)
(*     (* | _                   => fun xs => xs *) *)
(*     (* end (idealWorldReturnsOf' xs) *) *)
(*   end. *)

Definition idealWorldReturnsOf {A : Type} (U : IdealWorld.universe A) : list A :=
  returnsOfHelper U.(IdealWorld.users) idealWorldReturnOf.

Definition realWorldReturnsOf {A : Type} (U : RealWorld.universe A) : list A :=
  returnsOfHelper U.(RealWorld.users) realWorldReturnOf.



Definition finalAnswerInclusion {A} (U1 : IdealWorld.universe A) (U2 : RealWorld.universe A) :=

  forall finalStateOfU1, IdealWorld.step_universe^* U1 finalStateOfU1
                    -> idealWorldIsReallyFinalState finalStateOfU1
                    -> exists finalStateOfU2, RealWorld.step_universe^* U2 finalStateOfU2
                                        /\ realWorldIsReallyFinalState finalStateOfU2
                                        /\ idealWorldReturnsOf finalStateOfU1 = realWorldReturnsOf finalStateOfU2.







(* multi step relation for some users in U1 *)




Definition stepSilent (U1 U2 : u)   := step_universe U1 Silent U2.
Definition kstepSilent (U1 U2 : ku) := Keys.step_universe U1 Keys.Silent U2.

Inductive actionCorrespondance : observable -> Keys.Observable -> Prop :=
| EqSendPlain : forall {A : Set} o ko usr1 usr2 (msg1 : A) (msg2 : Keys.message A),
    o = Output usr1 msg1
    -> ko = Keys.Output usr2 msg2
    (* Something here about equality of messages and users.
     * Will eventually need to handle the notion of encryption! *)
    -> msg2 = Keys.Plaintext msg1 (* sending the same body!! *)
    -> actionCorrespondance o ko.
 
Definition simulates (R : u -> ku -> Prop) (U : u) (KU : ku) :=
  (forall U KU, R U KU
           -> forall U', stepSilent U U'
                   -> exists KU', kstepSilent^* KU KU'
                            /\ R U' KU')

  /\ (forall U KU, R U KU
             -> forall a1 a2 U', step_universe U (Visible a1) U'
                       -> exists KU' KU'', kstepSilent^* KU KU'
                                     /\ Keys.step_universe KU' (Keys.Visible a2) KU''
                                     (* We may eventually need here to handle multiple
                                      * real world steps in order to collect the things
                                      * needed to ensure the same cryptographic properties
                                      * hold between the two universes *)
                                     /\ actionCorrespondance a1 a2
                                     /\ R U' KU'')
  

  /\ R U KU.

Definition refines (U1 : u) (U2 : ku) :=
  exists R, simulates R U1 U2.

