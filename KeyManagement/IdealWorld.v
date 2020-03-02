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

Require Import Common ChMaps Maps Messages.

Require Messages.
Set Implicit Arguments.

Definition channel_id := ChMaps.channel_id.

Record permission := construct_permission
  { read : bool ;
    write : bool }.

(* The user's list of allowed channels, the nat corresponds to the nat in Single n *)
Definition permissions := NatMap.t permission.
Definition perm_id := nat.

Definition creator_permission := construct_permission true true.

(* this is what you send to a different user to grant access, later restricted to 
   Single channel ids *)
Record access := construct_access
                   { ch_perm : permission ;
                     ch_id : perm_id }.

Module IW_message <: GRANT_ACCESS.
  Definition access := access.
End IW_message.

Module message := Messages(IW_message).
Import message.
Export message.

(* now it's an inductive channel ID map *)
(* channels are created when:
   1) the universe is initialized with a non-empty map
   2) a user generates a new channel
   3) a user sends or receives on a channel intersection for the first time *)
Definition channels := ChMap.t (list (sigT message)).

Definition perm_intersection (perm1 perm2 : permission) :=
  match (perm1, perm2) with
  | (construct_permission rb1 wb1, construct_permission rb2 wb2) =>
    construct_permission (andb rb1 rb2) (andb wb1 wb2)
  end.

Definition check_perm (ch : channel_id) (ps : permissions) (target : permission) : Prop :=
  match ch with
  | Single n =>
    match (ps $? n) with
    | Some p' => p' = target
    | None => False
    end
  | Intersection n1 n2 =>
    match (ps $? n1, ps $? n2) with
    | (Some p1, Some p2) => (perm_intersection p1 p2) = target
    | _ => False
    end
  end.


Inductive cmd_type :=
| ChannelId
| Base (t : type)
| Message (t : type)
.

Definition denote (t : cmd_type) :=
  match t with
  | ChannelId => perm_id
  | Base t' => typeDenote t'
  | Message t' => message t'
  end
.
Notation "<< t >>" := (denote t) (at level 75) : idealworld_scope.
Delimit Scope idealworld_scope with idealworld.
Open Scope idealworld_scope.

Inductive cmd : cmd_type -> Type :=
| Return {result : cmd_type} (r : <<result>>) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : <<result'>> -> cmd result) : cmd result
| Gen : cmd (Base Nat)
| Send {t} (m : message t) (ch_id : channel_id) : cmd (Base Unit)
| Recv {t} (ch_id : channel_id) : cmd (Message t)
| CreateChannel : cmd ChannelId
.

Module IdealNotations.
  Ltac denoteInvert T :=
    match T with
      | channel_id => exact ChannelId
      | bool => exact (Base Bool)
      | nat => exact (Base Nat)
      | unit => exact (Base Unit)
      | (?T1 * ?T2)%type =>
        exact (TPair ltac:(denoteInvert T1) ltac:(denoteInvert T2))
      end
  .
  Ltac typeOf x :=
    match type of x with
    | ?T => denoteInvert T
    end
  .
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75) : idealworld_scope.
  Notation "'ret' x" := (@Return ltac:(typeOf x) x) (at level 75, only parsing) : idealworld_scope.
  Delimit Scope idealworld_scope with idealworld.
End IdealNotations.
Import IdealNotations.

Record user A :=
  { protocol : cmd (Base A) ;
    perms : permissions }.

Record universe A :=
  construct_universe {
      channel_vector : channels (* fmap channel_id channels *)
      ; users : user_list (user A)
    }.

Inductive permission_subset : permission -> permission -> Prop :=
| ReadWriteCase : forall p2,
    permission_subset p2 (construct_permission true true)
| WriteCase : forall b,
    permission_subset (construct_permission false b) (construct_permission false true)
| ReadCase : forall b, 
    permission_subset (construct_permission b false) (construct_permission true false).

Inductive screen_msg : forall A, permissions -> message A -> Prop :=
| ContentCase : forall c ps,
    screen_msg ps (Content c)
| PairCase : forall {A B} (m1 : message A) (m2 : message B) ps,
    screen_msg ps m1
    -> screen_msg ps m2
    -> screen_msg ps (MsgPair m1 m2)
| PermCase : forall p ps p_data,
    ps $? p.(ch_id) = Some p_data
    -> permission_subset p.(ch_perm) p_data
    -> screen_msg ps (Permission p).

(* Definition perm_intersection p1 p2 := *)
(*   match (p1, p2) with *)

Fixpoint add_ps_to_set {A} (m : message A) (ps : permissions) : permissions :=
  match m with
  | Content _ => ps
  | Permission p => ps $+ (p.(ch_id), p.(ch_perm))
  | MsgPair m1 m2 => add_ps_to_set m1 (add_ps_to_set m2 ps)
  end.

Inductive action : Type :=
| Input  t (msg : message t) (ch_id : channel_id) (cs : channels) (ps : permissions)
| Output t (msg : message t) (ch_id : channel_id) (cs : channels) (ps : permissions)
.

Definition ilabel := @label action.

Inductive lstep_user : forall A, ilabel -> channels * cmd A * permissions -> channels * cmd A * permissions -> Prop :=
| LStepBindRecur : forall {result result'} lbl (c1 c1' : cmd result') (c2 : <<result'>> -> cmd result) cv cv' ps ps',
    lstep_user lbl (cv, c1, ps) (cv', c1', ps') ->
    lstep_user lbl (cv, (Bind c1 c2), ps) (cv', (Bind c1' c2), ps')
| LStepBindProceed : forall {result result'} (v : <<result'>>) (c2 : <<result'>> -> cmd result) cv ps,
    lstep_user Silent (cv, (Bind (Return v) c2), ps) (cv, c2 v, ps)
| LStepGen : forall cv ps n,
    lstep_user Silent (cv, Gen, ps) (cv, Return n, ps)
| LStepCreateChannel : forall ch_id cv ps,
    cv #? (Single ch_id) = None ->
    lstep_user Silent
               (cv, CreateChannel, ps)
               (cv #+ ((Single ch_id), []), @Return ChannelId ch_id, ps $+ (ch_id, creator_permission))
| LStepSend : forall t (cv : channels) (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |} ->
    cv #? (Single ch_id) = Some ch_d ->
    screen_msg ps m ->
    lstep_user
      (Action (Output m (Single ch_id) cv ps))
      (cv, Send m (Single ch_id), ps) (cv #+ (Single ch_id, (ch_d ++ [existT _ _ m])), @Return (Base Unit) tt, ps)
| LStepDualSend : forall t cv (m : message t) ch_id1 ch_id2 ps ch_d b ms,
    check_perm (Intersection ch_id1 ch_id2) ps {| read := b ; write := true |}
    -> screen_msg ps m
    (* replace the following with non-option map lookup? *)
    -> (cv #? (Intersection ch_id1 ch_id2) = Some ch_d -> ms = ch_d)
      \/ (cv #? (Intersection ch_id1 ch_id2) = None -> ms = [])
    -> lstep_user
      (Action (Output m (Intersection ch_id1 ch_id2) cv ps))
      (cv, Send m (Intersection ch_id1 ch_id2), ps)
      (cv #+ (Intersection ch_id1 ch_id2, (ms ++ [existT _ _ m])), @Return (Base Unit) tt, ps)
| LStepRecv : forall t (cv cv' : channels) ch_d ch_d' ps (m : message t) ch_id b,
    cv #? ch_id = Some ch_d
    -> check_perm ch_id ps {| read := true ; write := b |}
    -> ch_d = (existT _ _ m) :: ch_d'
    -> cv' = cv #+ (ch_id, ch_d')
    -> lstep_user
        (Action (Input m ch_id cv ps))
        (cv, Recv ch_id, ps)
        (cv', @Return (Message t) m, add_ps_to_set m ps).

(* do the following two lemmas need to be extended for dual sends or do I need a total of 4 lemmas? *)
Lemma LStepSend' : forall t cv cv' (m : message t) ch_id ps ch_d b,
    ps $? ch_id = Some {| read := b ; write := true |}
    -> cv #? (Single ch_id) = Some ch_d
    -> screen_msg ps m
    -> cv' = cv #+ (Single ch_id, (ch_d ++ [existT _ _ m]))
    -> lstep_user (Action (Output m (Single ch_id) cv ps)) (cv, Send m (Single ch_id), ps) (cv', @Return (Base Unit) tt, ps).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Hint Extern 1 (check_perm _ _ _) => unfold check_perm; clean_map_lookups : core.

Lemma LStepRecv' : forall t (cv cv' : channels) ch_d ch_d' ps ps' (m : message t) ch_id b,
    cv #? (Single ch_id) = Some ch_d
    -> ps $? ch_id = Some {| read := true ; write := b |}
    -> ch_d = (existT _ _ m) :: ch_d'
    -> ps' = add_ps_to_set m ps
    -> cv' = cv #+ (Single ch_id, ch_d')
    -> lstep_user
        (Action (Input m (Single ch_id) cv ps))
        (cv, Recv (Single ch_id), ps)
        (cv', @Return (Message t) m, ps').
Proof.
  intros; subst; econstructor; eauto. 
Qed.

Inductive lstep_universe : forall {A}, universe A -> ilabel -> universe A -> Prop :=
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
