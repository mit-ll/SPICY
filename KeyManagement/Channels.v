Inductive channel_id := 
| Single (n : nat)
| Intersection (ch1 ch2 : nat)
.

Definition combine (ch1 ch2 : channel_id) :=
  match (ch1, ch2) with
  | (Single n, Single n') => Some (Intersection n n')
  | _ => None
  end.

Fixpoint eq (ch1 ch2 : channel_id) :=
  match (ch1, ch2) with
  | (Single n, Single n') => n = n'
  | (Intersection n1 n2, Intersection n1' n2') =>
    (n1 = n1' /\ n2 = n2') \/ (n1 = n2' /\ n2 = n1')
  | _ => False
  end.

