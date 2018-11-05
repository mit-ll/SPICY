From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Require Import Common.
Set Implicit Arguments.

Definition channel_id := nat.

(*
 *
 * Description of channels which allow users to send messages with certain security properties.
 *
 *)
(* High level definition of security can be defined as a subset of CIA. *)
Record security_properties := construct_properties
  { confidentiality : bool ;
    authenticity : bool ;
    integrity : bool ; }.

(* Two kinds of channels follow from the mere presence of a user in universe since users are defined as a 
   named entity (real world analog: the owner of a public key). Consider each case from A's perspective:
   - Default channels
     - two owners with equal privileges 
     - always CIA
     - users may send 
     - real world analog is using B's public key to encrypt a message signed by A's private key
   - Broadcast Channels
     - have single owner
     - either confidential to owner or authentic (integrity follows) to owner
     - "real world" analog is signing with A's public key or encrypting with B's public key

   Users themselves can create symmetric channels with a given set of properties
   - some restrictions since an authentic symmetric channel is impossible with more than 2 users
   - "real world" analog is using symmetric HMAC and/or symmetric encryption with shared key
*)
Inductive channel_type :=
| Default : user_id -> user_id -> channel_type
| Broadcast : user_id -> channel_type
| Symmetric : channel_type.


(* Exisistential wrapper for message, so we can put it in collections *)
Inductive exmsg : Type :=
| Exm {A : Type} (msg : A) : exmsg.

Record channel_data := construct_channel
  { properties : security_properties ;
    type : channel_type ;
    messages_sent : list (user_id * exmsg) ;
    user_pointers : fmap user_id nat }.

Definition channels := fmap channel_id channel_data.

(* 
 *
 * The following are helper functions for permuting the universe when messages are published
 * or received.
 *
 *)
Definition send_message u m ch_d :=
  {| properties := ch_d.(properties) ;
     type := ch_d.(type) ;
     messages_sent := app ch_d.(messages_sent) [(u, m)] ;
     user_pointers := ch_d.(user_pointers) |}.

(* Helper function, finds first message sent by another user after last message seen if channel has 
   been accessed before or from beginning if this is the user's first access. *)
(* am I dealing with polymorphism right? does this pass in the "expected type" from the user cmd? *)
Fixpoint recv_message' {A} ms (u : user_id) i : option A :=
  match ms with
  | [] => None
  | (u', m) :: ms'
    => match i with
       | O => if u ==n u' then recv_message' ms' u O else Some m
       | S n => recv_message' ms' u n                
       end     
  end.

(* Get message from channel or else learn no valid message has been sent. *)
Definition recv_message (ch_d : channel_data) (u : user_id) :=
  match ch_d.(user_pointers) $? u with
  | Some n => recv_message' ch_d.(messages_sent) u n
  | None => recv_message' ch_d.(messages_sent) u O
  end.

(* Recorded in universe'; the next access by the user will not reconsume a previously seen
   message. *)
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

(*
 *
 * Properties of channels that allow reading or writing only under some circumstances.
 *
 *)
Definition is_default_channel_owner user1 ch_ty :=
  forall user2, ch_ty = Default user1 user2 \/ ch_ty = Default user2 user1.

(* Deserving of its own definition because in broadcasts integrity <-> authenticity since we decided that 
   giving a user "too much security" is better than making the sets of properties and channel types 
   invalid. A "CIA Broadcast" channel is invalid. *)
Definition I_A_IA_properties ps := ps = construct_properties false true true \/
                                   ps = construct_properties false false true \/
                                   ps = construct_properties false true false.

Definition is_valid_IA_broadcast user ch_d :=
  ch_d.(type) = Broadcast user /\ I_A_IA_properties ch_d.(properties).

Definition is_C_broadcast ch_d :=
  forall user, ch_d.(type) = Broadcast user /\ ch_d.(properties) = construct_properties true false false.

Definition is_valid_C_broadcast user1 ch_d :=
  forall user2, (ch_d.(type) = Default user1 user2 \/ ch_d.(type) = Default user2 user1) /\
                ch_d.(properties) = construct_properties true false false.

Definition is_IA_broadcast ch_d :=
  forall user, ch_d.(type) = Broadcast user /\ I_A_IA_properties ch_d.(properties).

Inductive cmd : Type -> Type :=
| Return {result : Type} (r : result) : cmd result
| Bind {result' result} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Send {msg_ty : Type} (m : msg_ty) (ch_id : channel_id) : cmd unit
| Recv {msg_ty : Type} (ch_id : channel_id) : cmd msg_ty
| CreateChannel (p : security_properties) : cmd channel_id.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

Record universe (A : Type) : Type
  := construct_universe
       { channel_vector : fmap channel_id channel_data ;
         users : user_list (cmd A)
       }.

Inductive step_user : forall A, user_id * channels * cmd A -> user_id * channels * cmd A -> Prop :=
| StepBindRecur : forall u result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) cv cv',
    step_user (u, cv, c1) (u, cv', c1') ->
    step_user (u, cv, (Bind c1 c2)) (u, cv', (Bind c1' c2))
| StepBindProceed : forall u (result result' : Type) (v : result') (c2 : result' -> cmd result) cv,
    step_user (u, cv, (Bind (Return v) c2)) (u, cv, c2 v)
| StepCreateChannel : forall u ch_id p cv,
    ~(ch_id \in dom cv) ->
    (* Unclear how to handle this for authenticity; it can work but only if there are two parties and 
       there is no way of telling at this stage. *)
    step_user (u, cv, (CreateChannel p))
              (u, (cv $+ (ch_id, construct_channel p Symmetric [] $0)), (Return ch_id))
| StepSendBroadcast : forall u cv (ch_id : channel_id) (ch_d : channel_data) {m_ty : Type} (m : m_ty),
    cv $? ch_id = Some ch_d ->
    (is_valid_IA_broadcast u ch_d \/ is_C_broadcast ch_d) ->
    step_user (u, cv, (Send m ch_id))
              (u, cv $+ (ch_id, send_message u (Exm m) ch_d), (Return tt))
| StepSendSymmetric : forall u cv (ch_id : channel_id) {m_ty : Type} (m : m_ty) ch_d,
    cv $? ch_id = Some ch_d ->
    ch_d.(type) = Symmetric ->
    (* check user set of allowed channels for ch_id, check if CIA is valid *)
    step_user (u, cv, Send m ch_id)
              (u, cv $+ (ch_id, send_message u (Exm m) ch_d), Return tt)
| StepSendDefault : forall u cv ch_d (ch_id : channel_id) {m_ty : Type} (m : m_ty),
    cv $? ch_id = Some ch_d ->
    is_default_channel_owner u ch_d.(type) ->
    step_user (u, cv, Send m ch_id)
              (u, cv $+ (ch_id, send_message u (Exm m) ch_d), Return tt)
| StepRecvBroadcast : forall u cv ch_d (ch_id : channel_id) {msg_ty : Type} (m : msg_ty) ,
    (* check if m is a symmetric channel id; add to set of allowed channels *)
    cv $? ch_id = Some ch_d ->
    (is_valid_C_broadcast u ch_d \/ is_IA_broadcast ch_d) ->
    recv_message ch_d u = Some (Exm m) ->
    step_user (u, cv, (Recv ch_id))
              (u, cv $+ (ch_id, inc_pointer ch_d u), (Return m))
| StepRecvSymmetric : forall u cv ch_d ch_id {m_ty : Type} (m : m_ty),
    (* check set of allowed channels for ch_id *)
    cv $? ch_id = Some ch_d ->
    recv_message ch_d u = Some (Exm m) ->
    (* check if m is a symmetric channel id; add to set of allowed channels *)
    step_user (u, cv, (Recv ch_id))
              (u, cv $+ (ch_id, inc_pointer ch_d u), (Return m))
| StepRecvDefault : forall u cv ch_id ch_d {m_ty : Type} (m : m_ty),
    cv $? ch_id = Some ch_d ->
    is_default_channel_owner u ch_d.(type) ->
    recv_message ch_d u = Some (Exm m) ->
    (* check if m is a symmetric channel id; add to set of allowed channels *)
    step_user (u, cv, Recv ch_id)
              (u, cv $+ (ch_id, (inc_pointer ch_d u)), Return m).

Inductive step_universe : forall {A : Type}, universe A -> universe A -> Prop :=
| StepUser : forall A (U : universe A) u u_d cs' u_d',
    In (u,u_d) U.(users) ->
    (* U.(users) $? u = Some u_d -> *)
    step_user (u, U.(channel_vector), u_d) (u, cs', u_d') ->
    step_universe U (construct_universe cs' (updateUserList U.(users) u u_d')).

Example ping : user_list (cmd nat) :=
    (0, _ <- (Send 1 1) ; (Recv 1))
 :: (1, r <- (Recv 0) ; _ <- (Send 0 0) ; Return r)
 :: [].

Example ping_universe :=
{| channel_vector := $0 $+ (1, {| properties := {| confidentiality := true ;
                                                   integrity := true ;
                                                   authenticity := true |} ;
                                  type := Default 1 2 ;
                                  messages_sent := [] ;
                                  user_pointers := $0 |}) ;
   users := ping |}.

Check ping_universe.
