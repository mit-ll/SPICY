(* 
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From SPICY Require Import
     MyPrelude
     Maps.

Definition user_id              := nat.
Definition user_list (A : Type) := NatMap.t A.
