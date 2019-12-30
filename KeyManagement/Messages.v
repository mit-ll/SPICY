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

(* module that takes access type, either KeyId or Permission *)
(* Labels for the labeled transition system, a wrapper for messages *)
Inductive label {A} : Type :=
  Silent : label
| Action : A -> label
.

Inductive type : Set :=
| Nat
(* | Text *)
| Access
| Pair (t1 t2 : type)
.

Module Type GRANT_ACCESS.
  Parameter access : Set.
End GRANT_ACCESS.

Module Messages (GA : GRANT_ACCESS).

  Inductive message : type -> Type :=
  | Permission (acc : GA.access) : message Access
  | Content (n : nat) : message Nat
  | MsgPair {t1 t2} (m1 : message t1) (m2 : message t2) : message (Pair t1 t2)
  .

End Messages.
