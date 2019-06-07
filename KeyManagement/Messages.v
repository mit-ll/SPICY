(* module that takes access type, either KeyId or Permission *)
(* sigma type *)
(* content equality *)

(* Labels for the labeled transition system *)
Inductive label  {A} : Type :=
  Silent : label
| Action :  A -> label
.

(* Type grant_access. *)
(* Inductive type : Set := *)
(* | Nat *)
(* (* | Text *) *)
(* | Access *)
(* | Pair (t1 t2 : type) *)
(* . *)

(* Fixpoint typeDenote (t : type) : Set := *)
(*   match t with *)
(*   | Nat => nat *)
(*   | Access => key_permission *)
(*   | CipherId => grant_access *)
(*   | Pair t1 t2 => typeDenote t1 * typeDenote t2 *)
(*   end. *)

(* Inductive message : type -> Type := *)
(* | Access (id : channel_id) (p : permission) : message (Pair ChanId Perm) *)
(* | Content (n : nat) : message Nat *)
(* | MsgPair {t1 t2} (m1 : message t1) (m2 : message t2) : message (Pair t1 t2) *)
