Require Import Common.
Require RealWorld.
Require IdealWorld.

Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.

Inductive message_eq : forall A,  (RealWorld.message A) -> (IdealWorld.message A) -> Prop :=
| PlaintextMessage : forall content,
    message_eq (RealWorld.Plaintext content) (IdealWorld.Content content).