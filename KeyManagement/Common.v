Require Import
        MyPrelude
        Maps.

Definition user_id              := nat.
Definition user_list (A : Type) := NatMap.t A.
