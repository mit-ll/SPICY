From Coq Require Import String.
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
    users : fmap user_id cmd ;
    trace : list (channel_id * (user_id * message)) }.

Inductive step : universe -> universe -> Prop :=
| StepCreateChannel : forall U ch_id channel_vector' p u users',
    ~(ch_id \in dom U.(channel_vector)) ->
    channel_vector' = U.(channel_vector) $+ (ch_id, construct_channel p Symmetric [] $0) ->
    U.(users) $? u = Some (CreateChannel p) ->
    users' = U.(users) $+ (u, Return (ChannelId ch_id)) ->
    step U (construct_universe channel_vector' users' U.(trace))
| StepSend : forall U u ch_id m users' channel_vector' ch_d,
    U.(users) $? u = Some (Send (ChannelId ch_id) m) ->
    users' = U.(users) $+ (u, Return (ProtocolMsg "")) ->
    U.(channel_vector) $? ch_id = Some (ch_d) ->
    channel_vector' = U.(channel_vector) $+ (ch_id, send_message (u, m) ch_d) ->
    step U (construct_universe channel_vector' users' ((ch_id, (u, m))::U.(trace)))
| StepRecv : forall U u ch_id users' m channel_vector' ch_d,
    U.(users) $? u = Some (Recv (ChannelId ch_id)) ->
    users' = U.(users) $+ (u, Return m) ->
    U.(channel_vector) $? ch_id = Some ch_d ->
    Some m = recv_message ch_d u ->
    channel_vector' = U.(channel_vector) $+ (ch_id, inc_pointer ch_d u) ->
    step U (construct_universe  channel_vector' users' U.(trace))
| StepBindRecur : forall U u c1 c2,
    U.(users) $? u = Some (Bind c1 c2) ->
    (* TODO not sure how to do this: 
       only change u to protocol c1?
       put (u, c1) in a universe with no other users? 
       should I parallelize all users at the start? *)
    step U (construct_universe U.(channel_vector) U.(users) U.(trace))
| StepBindProceed : forall U u r c2 users',
    U.(users) $? u = Some (Bind (Return r) c2) ->
    users' = U.(users) $+ (u, (c2 r)) ->
    step U (construct_universe U.(channel_vector) users' U.(trace)).


(* Not fully implemented.
 * The users from universe
 * Questions:
 * 1. How does a user reference a channel_id when sending a message? Send takes a channel_id and a message, 
       but the channel_id is stored in memory as fmap var message. So, need to do some look-up within the 
       cmd? i.e., accessing memory from protocol.
 *)
Example ping :=
  $0 $+ ("0", {| protocol := (Send (Var "B") (ProtocolMsg  "Good Morning")) ;;
                                                  ("wait" <- (Recv (Var "1")));
               mem := $0 $+ ("1", ChannelId (0)) |})
   $+ ("1", {| protocol := ("wait" <- (Recv (Var "1"))) ;; (Send (Var "A") (ProtocolMsg "Good Morning")) ;
               mem := $0 $+ ("0", ChannelId (0)) |}).

Example ping_universe :=
{| channel_vector := $0 $+ (1, {| properties := {| confidentiality := true ;
                                                   integrity := true ;
                                                   authenticity := true |} ;
                                  type := Default "1" "2" ;
                                  messages_sent := [] ;
                                  user_pointers := $0 |}) ;
   users := ping ;
   trace := [] |}.
Check ping_universe.

(* Universe Generator Stuff *)

(* This assumes the user_data.(protocol) is empty at the beginning. If this
 * assumption is false, need to re-add list user_data as an input. Currently
 * just adds a skip to the user protocol (not sure what it should be if it
 * has not yet been populated).
 *)
Fixpoint add_users (user_id_list : list user_id) : fmap user_id user_data :=
match user_id_list with
| [] => $0
| id::tail =>  (add_users tail) $+ (id, {| protocol := Skip ;
                                           mem := $0 |})
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
                          (umap : fmap user_id user_data) : universe :=
let empty_universe := {| channel_vector := $0 ; users := umap ; trace := [] |} in
let empty_user_data := {| protocol := Skip ; mem := $0 |} in
match plist with
| [] => empty_universe
| pair'::t => match pair' with
              | (pair id1 id2) => let next_iter := (add_CIA_channels t (ch_id + 1) umap) in
                                  let id1_data := match (umap $? id1) with
                                                  | None => empty_user_data  (* This case should never happen *)
                                                  | Some rec => rec
                                                  end in
                                  let id2_data := match (umap $? id2) with
                                                  | None => empty_user_data (* This case should never happen *)
                                                  | Some rec => rec
                                                  end in
                                    {| channel_vector := (next_iter.(channel_vector) $+ (ch_id, {| properties := {| confidentiality := true;
                                                                                                                    authenticity := true;
                                                                                                                    integrity := true |};
                                                                                                   type := Default id1 id2;
                                                                                                   messages_sent := [];
                                                                                                   user_pointers := $0 |})) ;
                                       users := (next_iter.(users) $+ (id1, {| protocol := id1_data.(protocol);
                                                                               mem := id1_data.(mem) $+ (id2, ChannelId (ch_id)) |})
                                                                   $+ (id2, {| protocol := id2_data.(protocol);
                                                                               mem := id2_data.(mem) $+ (id1, ChannelId (ch_id)) |})) ;
                                       trace := [] |}
              end
end.

(* Generates a universe with 1-1 CIA channels between each user. These channels are currently added
 *  to the environment of each user. The channelIds have the corresponding userId as their keys.
 *
 * Takes a list of user_data as input.
 *  The protocol and environment can be empty. This is just so we know how many users exist.
 *  The code can be changed easily (probably?) to match any other type of input.
 *)
Fixpoint generate_universe (user_id_list : list user_id) : universe :=
let pairs_list := (generate_all_pairs user_id_list) in
  let umap := (add_users user_id_list) in
    add_CIA_channels pairs_list 0 umap.
