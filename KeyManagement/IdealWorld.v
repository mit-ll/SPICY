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

Inductive type :=
| Nat
| ChanId
| Perm
(* | Text *)
| Pair (t1 t2 : type)
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | ChanId => channel_id
  | Perm => permission
  | Pair t1 t2 => typeDenote t1 * typeDenote t2
  end.

Inductive message : type -> Type :=
| Permission (id : channel_id) (p : permission) : message (Pair ChanId Perm)
| Content (n : nat) : message Nat
| MsgPair {t1 t2} (m1 : message t1) (m2 : message t2) : message (Pair t1 t2)
.

(* shouldn't this be just Permissions ? *)
Definition channels := fmap channel_id (set exmsg).

Inductive cmd : Type -> Type :=
| Return {result : Type} (r : result) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Gen : cmd nat
| Send {t} (m : message t) (ch_id : channel_id) : cmd unit
| Recv {t} (ch_id : channel_id) : cmd (message t)
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
| StepSend : forall t cv (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv $? ch_id = Some ch_d ->
    msg_permissions_valid m ps ->
    step_user (cv, Send m ch_id, ps) (cv $+ (ch_id, {Exm m} \cup ch_d), Return tt, ps)
| StepRecv : forall t (cv : channels) ch_d ps (m : message t) ch_id b,
    cv $? ch_id = Some ch_d ->
    ps $? ch_id = Some {| read := true ; write := b |} ->
    (Exm m) \in ch_d ->
    step_user (cv, Recv ch_id, ps)
              (cv, Return m, add_chs_to_set (chs_search m) ps)
.

Lemma StepSend' : forall t cv cv' (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |}
    -> cv $? ch_id = Some ch_d
    -> msg_permissions_valid m ps
    -> cv' = cv $+ (ch_id, {Exm m} \cup ch_d)
    -> step_user (cv, Send m ch_id, ps) (cv', Return tt, ps).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Lemma StepRecv' : forall t (cv : channels) ch_d ps ps' (m : message t) ch_id b,
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

Definition extractContent {t} (msg : message t) : option nat :=
  match msg with
  | Content t => Some t
  | _         => None
  end.


(* Labeled transition system *)

Inductive action : Type :=
| Input  t (msg : message t) (ch_id : channel_id) (cs : channels) (ps : permissions)
| Output t (msg : message t) (ch_id : channel_id) (cs : channels) (ps : permissions)
.

Definition ilabel := @label action.

Inductive lstep_user : forall A, ilabel -> channels * cmd A * permissions -> channels * cmd A * permissions -> Prop :=
| LStepBindRecur : forall result result' lbl (c1 c1' : cmd result') (c2 : result' -> cmd result) cv cv' ps ps',
    lstep_user lbl (cv, c1, ps) (cv', c1', ps') ->
    lstep_user lbl (cv, (Bind c1 c2), ps) (cv', (Bind c1' c2), ps')
| LStepBindProceed : forall (result result' : Type) (v : result') (c2 : result' -> cmd result) cv ps,
    lstep_user Silent (cv, (Bind (Return v) c2), ps) (cv, c2 v, ps)
| LStepGen : forall cv ps n,
    lstep_user Silent (cv, Gen, ps) (cv, Return n, ps)
| LStepCreateChannel : forall ch_id cv ps,
    ~(ch_id \in dom cv) ->
    lstep_user Silent
               (cv, CreateChannel, ps)
               (cv $+ (ch_id, {}), Return ch_id, ps $+ (ch_id, creator_permission))
| LStepSend : forall t cv (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv $? ch_id = Some ch_d ->
    msg_permissions_valid m ps ->
    lstep_user
      (Action (Output m ch_id cv ps))
      (cv, Send m ch_id, ps)
      (cv $+ (ch_id, {Exm m} \cup ch_d), Return tt, ps)
| LStepRecv : forall t (cv : channels) ch_d ps (m : message t) ch_id b,
    cv $? ch_id = Some ch_d ->
    ps $? ch_id = Some {| read := true ; write := b |} ->
    (Exm m) \in ch_d ->
    lstep_user
      (Action (Input m ch_id cv ps))
      (cv, Recv ch_id, ps)
      (cv, Return m, add_chs_to_set (chs_search m) ps)
.

Lemma LStepSend' : forall t cv cv' (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |}
    -> cv $? ch_id = Some ch_d
    -> msg_permissions_valid m ps
    -> cv' = cv $+ (ch_id, {Exm m} \cup ch_d)
    -> lstep_user (Action (Output m ch_id cv ps)) (cv, Send m ch_id, ps) (cv', Return tt, ps).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Lemma LStepRecv' : forall t (cv : channels) ch_d ps ps' (m : message t) ch_id b,
    cv $? ch_id = Some ch_d
    -> ps $? ch_id = Some {| read := true ; write := b |}
    -> (Exm m) \in ch_d
    -> ps' = add_chs_to_set (chs_search m) ps
    -> lstep_user
        (Action (Input m ch_id cv ps))
        (cv, Recv ch_id, ps)
        (cv, Return m, ps').
Proof.
  intros; subst; econstructor; eauto.
Qed.

Inductive lstep_universe : forall {A : Type}, universe A -> ilabel -> universe A -> Prop :=
| LStepUser : forall A (U : universe A) u_id u proto chans perms' lbl,
    In (u_id,u) U.(users)
    -> lstep_user lbl (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> lstep_universe U lbl (construct_universe
                             chans
                             (updateUserList U.(users) u_id {| protocol := proto ; perms := perms' |})).


Lemma LStepUser' : forall A (U U': universe A) u_id u proto chans perms' lbl,
    In (u_id,u) U.(users)
    -> lstep_user lbl (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> U' = (construct_universe
              chans
              (updateUserList U.(users) u_id {| protocol := proto ; perms := perms' |}))
    -> lstep_universe U lbl U'.
Proof.
  intros. subst. econstructor; eauto.
Qed.
