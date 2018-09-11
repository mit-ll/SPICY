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
     messages_sent := m :: ch_d.(messages_sent) ;
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

Inductive cmd :=
| Return (r : message)
| Bind (c1 : cmd) (c2 : message -> cmd)
| Send (m ch_id : message) (* Message must be a channel id container. *)
| Recv (ch_id : message) (* Message must be a channel id container. *)
| CreateChannel (p : security_properties).

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

Record universe := construct_universe
(* The universe consists of:
    Channels (represented as a map from channel_id to channel_data)
    Users (a map of user_id to user_data)
    A trace of all messages sent on all channels
*)
  { channel_vector : fmap channel_id channel_data ;
    users : fmap user_id cmd}.

Inductive step_user : user_id * channels * cmd -> user_id * channels * cmd -> Prop :=
| StepBindRecur : forall u (c1 c1' : cmd) (c2 : message -> cmd) cv cv',
    step_user (u, cv, c1) (u, cv', c1') ->
    step_user (u, cv, (Bind c1 c2)) (u, cv', (Bind c1' c2))
| StepBindProceed : forall u v (c2 : message -> cmd ) cv,
    step_user (u, cv, (Bind (Return v) c2)) (u, cv, c2 v)
| StepCreateChannel : forall ch_id p cv u,
    ~(ch_id \in dom cv) ->
    step_user (u, cv, (CreateChannel p))
              (u, (cv $+ (ch_id, construct_channel p Symmetric [] $0)), (Return (ChannelId ch_id)))
| StepSend : forall ch_id m cv ch_d u,
    cv $? ch_id = Some ch_d ->
    step_user (u, cv, Send (ProtocolMsg m) (ChannelId ch_id))
              (u, cv $+ (ch_id, send_message (u, ProtocolMsg m) ch_d), Return (ProtocolMsg ""))
| StepRecv : forall ch_id m cv ch_d u,
    cv $? ch_id = Some ch_d ->
    recv_message ch_d u = Some m -> 
    step_user (u, cv, Recv (ChannelId ch_id)) (u, (cv $+ (ch_id, (inc_pointer ch_d u))), Return m).

Inductive step_universe : universe -> universe -> Prop :=
| StepUser : forall U u u_d cs' u_d',
    U.(users) $? u = Some u_d ->
    step_user (u, U.(channel_vector), u_d) (u, cs', u_d') ->
    step_universe U (construct_universe cs' (U.(users) $+ (u, u_d'))).

Example ping :=
  $0 $+ ("0", x <- (Send (ProtocolMsg "Hello") (ChannelId 0)) ; (Recv (ChannelId 0)))
     $+ ("1", x <- (Recv (ChannelId 0)) ; (Send x (ChannelId 0))).

Example ping_universe :=
{| channel_vector := $0 $+ (1, {| properties := {| confidentiality := true ;
                                                   integrity := true ;
                                                   authenticity := true |} ;
                                  type := Default "1" "2" ;
                                  messages_sent := [] ;
                                  user_pointers := $0 |}) ;
   users := ping |}.
Check ping_universe.


(* Universe Generator Stuff *)

(* This assumes the user_data.(protocol) is empty at the beginning. If this
 * assumption is false, need to re-add list user_data as an input. Currently
 * just adds a skip to the user protocol (not sure what it should be if it
 * has not yet been populated).
 *)
Fixpoint add_users (user_id_list : list user_id) : fmap user_id cmd :=
match user_id_list with
| [] => $0
| id::tail =>  (add_users tail) $+ (id, Return (ProtocolMsg "Placeholder")) (* Change later to be the protocols
                                                                             *  passed in by the user
                                                                             *)
end.

(* Helper Function for generate_universe *)
Fixpoint generate_all_pairs (user_id_list : list user_id) : list (user_id * user_id) :=
let generate_pairs := (fix gp (user_a : user_id)
                              (pair_user_list : list user_id) : (list (user_id * user_id)) :=
                       match pair_user_list with
                       | uId::tail => (pair user_a uId) :: (gp user_a tail)
                       | [] => []
                       end) in
match user_id_list with
| uId::tail => (generate_all_pairs tail) ++ (generate_pairs uId tail)
| [] => []
end.

(* Helper Function for generate_universe 
 * Only adds 1-1 CIA channels for now.
 * Assumes users do not get to choose the channelId, only the var that maps to it in their
 *  memory.
 *)
Fixpoint add_CIA_channels (plist : list (user_id * user_id))
                          (ch_id : channel_id)
                          (umap : fmap user_id cmd) : universe :=
let empty_universe := {| channel_vector := $0 ; users := umap |} in
let empty_cmd := Return (ProtocolMsg "Placeholder") in
match plist with
| [] => empty_universe
| pair'::t => match pair' with
              | (pair id1 id2) => let next_iter := (add_CIA_channels t (ch_id + 1) umap) in
                                  let id1_data := match (umap $? id1) with
                                                  | None => empty_cmd  (* This case should never happen *)
                                                  | Some rec => rec
                                                  end in
                                  let id2_data := match (umap $? id2) with
                                                  | None => empty_cmd (* This case should never happen *)
                                                  | Some rec => rec
                                                  end in
                                    {| channel_vector := (next_iter.(channel_vector) $+ (ch_id, {| properties := {| confidentiality := true;
                                                                                                                    authenticity := true;
                                                                                                                    integrity := true |};
                                                                                                   type := Default id1 id2;
                                                                                                   messages_sent := [];
                                                                                                   user_pointers := $0 |})) ;
                                       users := (next_iter.(users) $+ (id1, id1_data)
                                                                   $+ (id2, id2_data)) |}
              end
end.

Fixpoint add_Broadcast_channels (user_id_list : list user_id)
                                (ch_id : channel_id)
                                (U : universe) : universe :=
match user_id_list with 
| [] => U
| uid::tail => let U' := {| channel_vector := U.(channel_vector) $+ (ch_id, {| properties := {| confidentiality := false ;
                                                                                                authenticity := true ;
                                                                                                integrity := true |} ;
                                                                               type := Broadcast uid ;
                                                                               messages_sent := [] ;
                                                                               user_pointers := $0|}) ; 
                            users := U.(users) |}
               in
               add_Broadcast_channels tail
                                      (ch_id + 1)
                                      U'
end.

(* Generates a universe with 1-1 CIA channels between each user. These channels are currently added
 *  to the environment of each user. The channelIds have the corresponding userId as their keys.
 *
 * Change so that it takes protocols as well so that those can be loaded into memory when the users 
 *  are created and added to the universe.
 *)
Fixpoint generate_universe (cmds_list : list cmd) (user_id_list : list user_id) : universe :=
let pairs_list := (generate_all_pairs user_id_list) in
  let umap := (add_users user_id_list) in
   let ch_id' := (length user_id_list) * ((length user_id_list) - 1) / 2 in
    add_Broadcast_channels user_id_list
                           ch_id'
                           (add_CIA_channels pairs_list 0 umap).