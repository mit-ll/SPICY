From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := var.

Definition channel_id := nat.

Definition msg_index := nat.

(* A message sent over a channel can either be:
    A string being sent as part of a protocol between users
    A channel id granting the recipient access to a channel
*)
Inductive message :=
| ChannelId : channel_id -> message
| ProtocolMsg : string -> message.

Record security_properties :=
  { confidentiality : bool ;
    authenticity : bool ;
    integrity : bool }.

(* Default channels are 1-1 simplex
     When a user is created, default channels to all other users are created
   Broadcast channels are 1-many simplex; only the owner can send
   Symmetric channels are duplex; anyone with the channel_id can send/recv
*)
Inductive channel_type :=
| Default : user_id -> user_id -> channel_type
| Broadcast : user_id -> channel_type
| Symmetric : channel_type.

Record channel_data := construct_channel
  { properties : security_properties ;
    type : channel_type ;
    messages_sent : list (user_id * message) ;
    user_pointers : fmap user_id nat }.

Definition channels := fmap channel_id channel_data.

Definition send_message m ch_d :=
  {| properties := ch_d.(properties) ;
     type := ch_d.(type) ;
     messages_sent := app ch_d.(messages_sent) [m] ;
     user_pointers := ch_d.(user_pointers) |}.

Fixpoint recv_message' ms (u : user_id) i : option message :=
  match ms with
  | [] => None
  | (u', m) :: ms' => match i with
                     | O => if u ==v u' then recv_message' ms' u O else Some m
                     | S n => recv_message' ms' u n
                     end
  end.

Definition recv_message (ch_d : channel_data) (u : user_id) :=
  match ch_d.(user_pointers) $? u with
  | Some n => recv_message' ch_d.(messages_sent) u n
  | None => recv_message' ch_d.(messages_sent) u O
  end.


Definition inc_pointer ch_d u :=
  match ch_d.(user_pointers) $? u with
  | Some n => {| properties := ch_d.(properties) ;
                 type := ch_d.(type) ;
                 messages_sent := ch_d.(messages_sent) ;
                 user_pointers := (ch_d.(user_pointers) $+ (u, S n)) |}
  | None => {| properties := ch_d.(properties) ;
               type := ch_d.(type) ;
               messages_sent := ch_d.(messages_sent) ;
               user_pointers := (ch_d.(user_pointers) $+ (u, 1)) |}
  end.

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Send {msg_ty : Set} (m : msg_ty) (ch_id : channel_id) : cmd unit
| Recv {msg_ty : Set} (ch_id : channel_id) : cmd msg_ty
| CreateChannel (p : security_properties) : cmd channel_id.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

Record universe := construct_universe
(* The universe consists of:
    Channels (represented as a map from channel_id to channel_data)
    Users (a map of user_id to user_data)
    A trace of all messages sent on all channels
*)
  { channel_vector : fmap channel_id channel_data ;
    users : fmap user_id (cmd unit)}.

Inductive step_user : forall A, channels * cmd A -> channels * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) cv cv',
    step_user (cv, c1) (cv', c1') ->
    step_user (cv, (Bind c1 c2)) (cv', (Bind c1' c2))
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) cv,
    step_user (cv, (Bind (Return v) c2)) (cv, c2 v)
| StepCreateChannel : forall ch_id p cv,
    ~(ch_id \in dom cv) ->
    step_user (cv, (CreateChannel p))
              ((cv $+ (ch_id, construct_channel p Symmetric [] $0)), (Return ch_id))
| StepSendBroadcast : forall cv (ch_id : channel_id) (ch_d : channel_data) {m_ty : Set} (m : m_ty),
    cv $? ch_id = Some ch_d ->
    step_user (cv, (Send m ch_id)) (cv, (Return tt))
| StepSendSymmetric : forall cv cv' (ch_id : channel_id) {m_ty : Set} (m : m_ty) ch_d,
    cv $? ch_id = Some ch_d ->
    ch_d.(type) = Symmetric ->
    step_user (cv, (Send m ch_id)) (cv', (Return tt))
| StepSendDefault : forall cv ch_d (ch_id : channel_id) {m_ty : Set} (m : m_ty),
    cv $? ch_id = Some ch_d ->
    step_user (cv, (Send m ch_id)) (cv, (Return tt))
| StepRecvBroadcast : forall cv (ch_id : channel_id) {msg_ty : Set} (m : msg_ty) ,
    step_user (cv, (Recv ch_id)) (cv, (Return m))
| StepRecvSymmetric : forall cv ch_id {m_ty : Set} (m : m_ty),
    step_user (cv, (Recv ch_id)) (cv, (Return m))
| StepRecvDefault : forall cv ch_id {m_ty : Set} (m : m_ty),
    step_user (cv, (Recv ch_id)) (cv, (Return m)).

Inductive step_universe : universe -> universe -> Prop :=
| StepUser : forall U u u_d cs' u_d',
    U.(users) $? u = Some u_d ->
    step_user (U.(channel_vector), u_d) (cs', u_d') ->
    step_universe U (construct_universe cs' (U.(users) $+ (u, u_d'))).

Example ping :=
  $0 $+ ("0", x <- (Send (ProtocolMsg "Hello") 0) ; (Recv 0))
     $+ ("1", x <- (Recv 0) ; if x ==v "Hello" then (Send x 0) else (Send "Huh?" 0)).

Example ping_universe :=
{| channel_vector := $0 $+ (1, {| properties := {| confidentiality := true ;
                                                   integrity := true ;
                                                   authenticity := true |} ;
                                  type := Default "1" "2" ;
                                  messages_sent := [] ;
                                  user_pointers := $0 |}) ;
   users := ping |}.
   
Check ping_universe.