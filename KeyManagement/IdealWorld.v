From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := var.

Definition channel_id := nat.

Record permission := construct_permission
  { read : bool ;
    write : bool }.

Definition permissions := fmap channel_id permission.

Definition creator_permission := construct_permission true true.

Inductive message : Type -> Type :=
| Permission (id : channel_id) (p : permission) : message (channel_id * permission)
| Content {A : Type} (m : A) : message A
| MsgPair {A B : Type} (m1 : message A) (m2 : message B) : message (A * B).

(* Exisistential wrapper for message, so we can put it in collections *)
Inductive exmsg : Type :=
| Exm {A : Type} (msg : message A) : exmsg.

Definition channels := fmap channel_id (set exmsg).

Inductive cmd : Type -> Type :=
| Return {result : Type} (r : result) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Send {msg_ty : Type} (m : message msg_ty) (ch_id : channel_id) : cmd unit
| Recv {msg_ty : Type} (ch_id : channel_id) : cmd (message msg_ty)
| CreateChannel : cmd channel_id.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

Record user :=
  { protocol : cmd unit ;
    perms : permissions }.

Record universe := construct_universe
                     { channel_vector : fmap channel_id channels ;
                       users : fmap user_id user}.

(* write as inductive relation *)
Fixpoint chs_search {A} (m : message A) : list (channel_id * permission) :=
  match m with
  | Permission id p => [(id, p)]
  | Content _ => []
  | MsgPair m1 m2 => chs_search m1 ++ chs_search m2        
  end.

Definition permission_subset p1 p2 : Prop :=
  p1 = construct_permission true true \/
  (p1 = construct_permission true false /\ p2.(write) = false) \/
  (p1 = construct_permission false true /\ p2.(read) = false) \/
  (p1 = construct_permission false false /\
   p2 = construct_permission false false).

Fixpoint msg_permissions_valid {A} (m : message A) ps : Prop :=
  List.Forall
    (fun '(id, ps_sent) =>
      match ps $? id with
      | Some p => permission_subset ps_sent p
      | None => False
      end)
    (chs_search m).
    

Fixpoint add_chs_to_set (ks : list (channel_id * permission)) (ps : permissions) :=
  match ks with
  | [] => ps
  | (id, perm) :: ks' => (add (add_chs_to_set ks' ps) id perm)
  end.

Inductive step_user : forall A, channels * cmd A * permissions -> channels * cmd A * permissions -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) cv cv' ps ps',
    step_user (cv, c1, ps) (cv', c1', ps') ->
    step_user (cv, (Bind c1 c2), ps) (cv', (Bind c1' c2), ps')
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) cv ps,
    step_user (cv, (Bind (Return v) c2), ps) (cv, c2 v, ps)
| StepCreateChannel : forall ch_id cv ps,
    ~(ch_id \in dom cv) ->
    step_user (cv, CreateChannel, ps)
              (cv $+ (ch_id, {}), Return ch_id, ps $+ (ch_id, creator_permission))
| StepSend : forall A cv (m : message A) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv $? ch_id = Some ch_d ->
    msg_permissions_valid m ps ->
    step_user (cv, Send m ch_id, ps) (cv $+ (ch_id, {Exm m} \cup ch_d) , Return tt, ps)
| StepRecv : forall A (cv cv' : channels) ch_d ps (m : message A) ch_id (ms ms' : list (user_id * exmsg)) b,
    cv $? ch_id = Some ch_d ->
    ps $? ch_id = Some {| read := true ; write := b |} ->
    (Exm m) \in ch_d ->
    step_user (cv, Recv ch_id, ps)
              (cv, Return m, add_chs_to_set (chs_search m) ps).
