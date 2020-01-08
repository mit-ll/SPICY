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
From Coq Require Import String Bool.Sumbool Logic.

Require Import MyPrelude.

(* Module Foo <: EMPTY. End Foo. *)
(* Module Import SN := SetNotations(Foo). *)

Require Import Common Maps Messages.
Require Messages.
Set Implicit Arguments.

Definition channel_id := nat.

Record permission := construct_permission
  { read : bool ;
    write : bool }.

Definition permissions := NatMap.t permission.

Definition creator_permission := construct_permission true true.

Record access := construct_access
                   { ch_perm : permission ;
                     ch_id : channel_id }.

Module IW_message <: GRANT_ACCESS.
  Definition access := access.
End IW_message.

Module message := Messages(IW_message).
Import message.
Export message.

(* shouldn't this be just Permissions ? *)
Definition channels := NatMap.t (list (sigT message)).

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
  | Permission (construct_access p id) => [(id, p)]
  | Content _ => []
  | MsgPair m1 m2 => chs_search m1 ++ chs_search m2        
  end.

Inductive permission_subset : permission -> permission -> Prop :=
| ReadWriteCase : forall p2,
    permission_subset p2 (construct_permission true true)
| WriteCase : forall b,
    permission_subset (construct_permission false b) (construct_permission false true)
| ReadCase : forall b,
    permission_subset (construct_permission b false) (construct_permission true false).

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
  | (id, perm) :: ks' => (add_chs_to_set ks' ps) $+ (id, perm)
  end.


Definition extractContent {t} (msg : message t) : option nat :=
  match msg with
  | Content t => Some t
  | _         => None
  end.

Definition extractPermission {t} (msg : message t) : option access :=
  match msg with
  | Permission a => Some a
  | _            => None
  end.

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
    ~(In ch_id cv) ->
    lstep_user Silent
               (cv, CreateChannel, ps)
               (cv $+ (ch_id, []), Return ch_id, ps $+ (ch_id, creator_permission))
| LStepSend : forall t cv (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv $? ch_id = Some ch_d ->
    msg_permissions_valid m ps ->
    lstep_user
      (Action (Output m ch_id cv ps))
      (cv, Send m ch_id, ps)
      (cv $+ (ch_id, ch_d ++ [existT _ _ m]), Return tt, ps)
| LStepRecv : forall t (cv cv' : channels) ch_d ch_d' ps (m : message t) ch_id b,
    cv $? ch_id = Some ch_d ->
    ps $? ch_id = Some {| read := true ; write := b |} ->
    ch_d = (existT _ _ m) :: ch_d' ->
    cv' = cv $+ (ch_id, ch_d') ->
    lstep_user
      (Action (Input m ch_id cv ps))
      (cv, Recv ch_id, ps)
      (cv', Return m, add_chs_to_set (chs_search m) ps)
.

Lemma LStepSend' : forall t cv cv' (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |}
    -> cv $? ch_id = Some ch_d
    -> msg_permissions_valid m ps
    -> cv' = cv $+ (ch_id, ch_d ++ [existT _ _ m])
    -> lstep_user (Action (Output m ch_id cv ps)) (cv, Send m ch_id, ps) (cv', Return tt, ps).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Lemma LStepRecv' : forall t (cv cv' : channels) ch_d ch_d' ps ps' (m : message t) ch_id b,
    cv $? ch_id = Some ch_d
    -> ps $? ch_id = Some {| read := true ; write := b |}
    -> ch_d = (existT _ _ m) :: ch_d'
    -> ps' = add_chs_to_set (chs_search m) ps
    -> cv' = cv $+ (ch_id, ch_d')
    -> lstep_user
        (Action (Input m ch_id cv ps))
        (cv, Recv ch_id, ps)
        (cv', Return m, ps').
Proof.
  intros; subst; econstructor; eauto.
Qed.

Inductive lstep_universe : forall {A : Type}, universe A -> ilabel -> universe A -> Prop :=
| LStepUser : forall A (U : universe A) u_id u proto chans perms' lbl,
    U.(users) $? u_id = Some u
    -> lstep_user lbl (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> lstep_universe U lbl (construct_universe
                             chans
                             (U.(users) $+ (u_id, {| protocol := proto ; perms := perms' |}))).


Lemma LStepUser' : forall A (U U': universe A) u_id u proto chans perms' lbl,
    U.(users) $? u_id = Some u
    -> lstep_user lbl (U.(channel_vector), u.(protocol), u.(perms)) (chans, proto, perms')
    -> U' = (construct_universe
              chans
              (U.(users) $+ (u_id, {| protocol := proto ; perms := perms' |})))
    -> lstep_universe U lbl U'.
Proof.
  intros. subst. econstructor; eauto.
Qed.
