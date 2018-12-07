From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.

Require Import Common.
Set Implicit Arguments.

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

(* shouldn't this be just Permissions ? *)
Definition channels := fmap channel_id (set exmsg).

Inductive cmd : Type -> Type :=
| Return {result : Type} (r : result) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Send {msg_ty : Type} (m : message msg_ty) (ch_id : channel_id) : cmd unit
| Recv {msg_ty : Type} (ch_id : channel_id) : cmd (message msg_ty)
| CreateChannel : cmd channel_id.

Module IdealNotations.
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75) : idealworld_scope.
  Delimit Scope idealworld_scope with idealworld.
End IdealNotations.

Import IdealNotations.
Open Scope idealworld_scope.

Record user A :=
  { protocol : cmd A ;
    perms : permissions }.

Record universe A :=
  construct_universe {
      channel_vector : channels (* fmap channel_id channels *)
    ; users : user_list (user A)
    }.

(* Record universe := construct_universe *)
(*                      { channel_vector : channels ; *)
(*                        users : fmap user_id user}. *)

(* write as inductive relation *)
Fixpoint chs_search {A} (m : message A) : list (channel_id * permission) :=
  match m with
  | Permission id p => [(id, p)]
  | Content _ => []
  | MsgPair m1 m2 => chs_search m1 ++ chs_search m2        
  end.

Inductive permission_subset : permission -> permission -> Prop :=
| ReadWriteCase : forall p2,
    permission_subset (construct_permission true true) p2
| WriteCase : forall b,
    permission_subset (construct_permission false true) (construct_permission false b)
| ReadCase : forall b,
    permission_subset (construct_permission true false) (construct_permission b false).

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
| StepBindProceed : forall (result result' : Type) (v : result') (c2 : result' -> cmd result) cv ps,
    step_user (cv, (Bind (Return v) c2), ps) (cv, c2 v, ps)
| StepCreateChannel : forall ch_id cv ps,
    ~(ch_id \in dom cv) ->
    step_user (cv, CreateChannel, ps)
              (cv $+ (ch_id, {}), Return ch_id, ps $+ (ch_id, creator_permission))
| StepSend : forall A cv (m : message A) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv $? ch_id = Some ch_d ->
    msg_permissions_valid m ps ->
    step_user (cv, Send m ch_id, ps) (cv $+ (ch_id, {Exm m} \cup ch_d), Return tt, ps)
| StepRecv : forall A (cv : channels) ch_d ps (m : message A) ch_id b,
    cv $? ch_id = Some ch_d ->
    ps $? ch_id = Some {| read := true ; write := b |} ->
    (Exm m) \in ch_d ->
    step_user (cv, Recv ch_id, ps)
              (cv, Return m, add_chs_to_set (chs_search m) ps).


Lemma StepSend' : forall A cv cv' (m : message A) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |}
    -> cv $? ch_id = Some ch_d
    -> msg_permissions_valid m ps
    -> cv' = cv $+ (ch_id, {Exm m} \cup ch_d)
    -> step_user (cv, Send m ch_id, ps) (cv', Return tt, ps).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Lemma StepRecv' : forall A (cv : channels) ch_d ps ps' (m : message A) ch_id b,
    cv $? ch_id = Some ch_d
    -> ps $? ch_id = Some {| read := true ; write := b |}
    -> (Exm m) \in ch_d
    -> ps' = add_chs_to_set (chs_search m) ps
    -> step_user (cv, Recv ch_id, ps)
                (cv, Return m, ps').
Proof.
  intros; subst; econstructor; eauto.
Qed.

Inductive step_universe : forall {A : Type}, universe A -> universe A -> Prop :=
| StepUser : forall A (U : universe A) u_id u proto chans perms',
    In (u_id,u) U.(users)
    -> step_user (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> step_universe U (construct_universe
                         chans
                         (updateUserList U.(users) u_id {| protocol := proto ; perms := perms' |})).


Lemma StepUser' : forall A (U U': universe A) u_id u proto chans perms',
    In (u_id,u) U.(users)
    -> step_user (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> U' = (construct_universe
              chans
              (updateUserList U.(users) u_id {| protocol := proto ; perms := perms' |}))
    -> step_universe U U'.
Proof.
  intros. subst. econstructor; eauto.
Qed.


Definition extractContent {A} (msg : message A) : option A :=
  match msg with
  | Content t => Some t
  | _         => None
  end.
