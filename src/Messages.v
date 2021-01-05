(* 
 * © 2019-2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
Inductive label {A} : Type :=
  Silent : label
| Action : A -> label
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

  Definition extractContent (msg : message Nat) : nat :=
    match msg with
    | Content t => t
    end.

  Definition extractPermission (msg : message Access) : GA.access :=
    match msg with
    | Permission a => a
    end.

  Definition msgFst {t1 t2} (msg : message (TPair t1 t2)) : (message t1) :=
    match msg with
    | MsgPair m1 _ => m1
    end.

  Definition msgSnd {t1 t2} (msg : message (TPair t1 t2)) : (message t2) :=
    match msg with
    | MsgPair _ m2 => m2
    end.

End Messages.
