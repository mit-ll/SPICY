(* module that takes access type, either KeyId or Permission *)

(* Labels for the labeled transition system, a wrapper for messages *)
Inductive label  {A} : Type :=
  Silent : label
| Action :  A -> label
.

Inductive type : Set :=
| Access
| Bool
| Nat
| Unit
| TPair (t1 t2 : type)
.

Module Type GRANT_ACCESS.
  Parameter access : Set.
End GRANT_ACCESS.

Module Messages (GA : GRANT_ACCESS).

  Inductive message : type -> Type :=
  | Permission (acc : GA.access) : message Access
  | Content (n : nat) : message Nat
  | MsgPair {t1 t2} (m1 : message t1) (m2 : message t2) : message (TPair t1 t2)
  .

  Fixpoint typeDenote (t : type) :=
    match t with
    | Access => GA.access
    | Bool => bool
    | Nat => nat
    | Unit => unit
    | TPair t1 t2 => (typeDenote t1 * typeDenote t2)%type
    end
  .

End Messages.
