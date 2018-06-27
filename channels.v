From Coq Require Import String.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := var.

Definition channel_id := nat.

Definition next_message := nat.

Definition msg_index := nat.

(* A message sent over a channel can either be:
    A string being sent as part of a protocol between users
    A channel id granting the recipient access to a channel
*)
Inductive message :=
| ChannelId : (channel_id * next_message) -> message
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

Record channel_data :=
  { properties : security_properties ;
    type : channel_type ;
    messages_sent : list (user_id * message) }.

(* Each user has a heap of protocol memory, represented as a 
   map from variable names to messages.
   The map key should be var, not user_id, but we had some issues
   with the universe generator. See question for Adam below.
*)

Definition memory := fmap var message. 

(* The protocol language has two types of instructions: commands with return values
   and commands without return values. *)
Inductive returns :=
| Recv (ch : returns)
| CreateChannel (sp : security_properties)
| Var (x : var).

Inductive cmd :=
| Skip
| Assign (x : var) (e : returns)
| Sequence (c1 c2 : cmd)
| Send (ch_id : channel_id) (m : message).
(* if? *)

Notation "x <- e" := (Assign x e) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)

Record user_data :=
  { protocol : cmd ;
    mem : memory }.

Record universe := construct_universe
(* The universe consists of:
    Channels (represented as a map from channel_id to channel_data)
    Users (a map of user_id to user_data)
    A trace of all messages sent on all channels
*)
  { channel_vector : fmap channel_id channel_data ;
    users : fmap user_id user_data ;
    trace : list (channel_id * (user_id * message)) }.



(* Not fully implemented.
 * The users from universe
 * Questions:
 * 1. How does a user reference a channel_id when sending a message? Send takes a channel_id and a message, 
       but the channel_id is stored in memory as fmap var message. So, need to do some look-up within the 
       cmd? i.e., accessing memory from protocol.
 *)
Example ping :=
$0 $+ ("0", {| protocol := (Send 0 (ProtocolMsg (append "Good" "Morning"))) ;; ("wait" <- (Recv (Var "1")));
               mem := $0 $+ ("1", ChannelId (0, 0)) |})
   $+ ("1", {| protocol := ("wait" <- (Recv (Var "1"))) ;; (Send 0 (ProtocolMsg "Good Morning")) ;
               mem := $0 $+ ("0", ChannelId (0, 0)) |}).

Example ping_universe :=
{| channel_vector := $0 $+ (1, {| properties := {| confidentiality := true ;
                                                   integrity := true ;
                                                   authenticity := true |} ;
                                  type := Default "1" "2" ;
                                  messages_sent := [] |}) ;
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
                                                                                                   messages_sent := [] |})) ;
                                       users := (next_iter.(users) $+ (id1, {| protocol := id1_data.(protocol);
                                                                               mem := id1_data.(mem) $+ (id2, ChannelId (ch_id, 0)) |})
                                                                   $+ (id2, {| protocol := id2_data.(protocol);
                                                                               mem := id2_data.(mem) $+ (id1, ChannelId (ch_id, 0)) |})) ;
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











(*
Fixpoint interp
         (r : returns)
         (chs : fmap channel_id channel_data)
         (u : user_id)
         (new_id : channel_id)
         (i : msg_index)
         (v : memory)
  : option message :=
  let not_sent_by_me := (fix nsbm index msgs :=
                           match msgs with
                           | [] => None
                           | (u', m) :: msgs' => match index with
                                          | S i => nsbm i msgs'
                                          | O => if u' ==v u then nsbm index msgs' else Some m
                                          end
                           end) in
  match r with
  | CreateChannel props => Some(ChannelId(new_id, 0))
  | Recv ret => match interp ret chs u new_id i v with
                  | Some m 
      chs $? (* interp  with
                  | None => None
                  | Some ch_d => not_sent_by_me i ch_d.(messages_sent)
                  end
  | Var x => v $? x
                    (* const *)
  end.

Inductive step : universe -> universe -> Prop :=
  (* step send *)
| StepSeq2 : forall (U : universe) (v : memory) (c2 : cmd) (stepped_users : fmap user_id user_data),
    (exists (u : user_id),
      (users U) $? u = Some {| protocol := (Sequence Skip c2) ; mem := v |} ->
      stepped_users = U.(users) $+ (u, {| protocol := c2; mem := v |})) ->
      step U (construct_universe U.(channel_vector) stepped_users U.(trace))
| StepAssignVar : forall  (U : universe) (v : memory) (c2 : cmd) (stepped_users : fmap user_id user_data) x x' val,
    (exists (u : user_id),
    (users U) $? u = Some {| protocol := (Assign x (Var x')) ; mem := v |} ->
    interp (Var x') U.(channel_vector) u (0 : channel_id) (0 : msg_index) v  = Some val ->
      stepped_users = U.(users) $+ (u, {| protocol := Skip; mem := v $+ (x, val) |})) ->
      step U (construct_universe U.(channel_vector) stepped_users U.(trace))
| StepAssignRecv : forall  (U : universe) (v : memory) (c2 : cmd) (stepped_users : fmap user_id user_data) (u : user_id) x id val,
    (users U) $? u = Some {| protocol := (Assign x (Recv id)) ; mem := v |} ->
    interp (Recv id) U.(channel_vector) u (0 : channel_id) (0 : msg_index) v  = Some val ->
      stepped_users = U.(users) $+ (u, {| protocol := Skip; mem := v $+ (x, val) |}) ->
      step U (construct_universe U.(channel_vector) stepped_users U.(trace))
| StepAssignChannel : forall  (U : universe) (v : memory) (c2 : cmd) (stepped_users : fmap user_id user_data) (u : user_id) x prop val,
    (users U) $? u = Some {| protocol := (Assign x (CreateChannel prop)) ; mem := v |} ->
    interp (CreateChannel prop) U.(channel_vector) u (0 : channel_id) (0 : msg_index) v  = Some val ->
      stepped_users = U.(users) $+ (u, {| protocol := Skip; mem := v $+ (x, val) |}) ->
      step U (construct_universe U.(channel_vector) stepped_users U.(trace)).
*)*)

