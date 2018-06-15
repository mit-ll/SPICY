From Coq Require Import String.
Require Import Frap.

(* Defines ideal functionality for creating secure channels between users and sending messages over those channels. *)

(* A plaintext message *)
Definition message := string.

(* A unique identifier for a user *) 
Definition user_id := nat.

(* A property of the channel that indicates whether it is for broadcast or group messaging *)
Inductive roles :=
| Owner : user_id -> roles
| Members : list user_id -> roles.

(* The security properties provided by the channel *)
Record channel_permissions :=
  { confidentiality : bool ;
    authenticity : bool ;
    integrity : bool }.

(* A communication channel between a set of users *)
Record channel :=
  { properties : channel_permissions ;
    parties : roles }.

(* A unique identifier for a channel *)
Definition channel_id := nat.

(* Owned by users; represents access points to channels.
   Contains a list of all messages others have sent on the channel that have not yet been read by the owner of this port. 
   *)
Record port_data :=
  { ch : channel_id ;
   unread : list message ; }.

(* A unique identifier for a port *)
Definition port_id := nat.

(* The ports the user has access to and the program they'll run *)
Record user_data :=
  { ports : list port_data (*fmap port_id port_data*)
    (*program : nat*) }.

(* The master type that stores everything *)
Record universe :=
  { users : fmap user_id user_data ;
    channels : fmap channel_id channel ;
    trace : list message }.

(* Helper function for creating a channel
   Produces a new user map in which specified users have ports to a newly created channel *)
Fixpoint add_ports (port_receivers : list user_id) (users :  fmap user_id user_data) (ch_id : channel_id) : (fmap user_id user_data) :=
  let new_port := {|ch := ch_id ; unread := [] |} in
  match port_receivers with
  | [] => users
  | pr :: port_receivers' => let rec := users $? pr in
                             match rec with
                             | None => $0
                             | Some valid_rec => (add_ports port_receivers' users ch_id) $+ (pr, {| ports := new_port ::(valid_rec.(ports))|})
                             end
  end.
  
(* Helper function for creating a channel       (List.Forall)
   Check that specified users exist *)
Fixpoint all_existing_users (members : list user_id)  users : Prop :=
  match members with
  | [] => True
  | m :: ms => m \in users /\ all_existing_users ms users
  end.

(* Valid properties for a broadcast channel. 
   Authenticity/integrity to the creator of the channel are guarenteed to all other users while confidentiality is guarenteed 
   to the creator not other users. If a channel is allowed to have confidentiality and other attributes it is no longer true
   that all messages on the channel have the security attributes listed. *)
Definition valid_properties attributes : Prop :=
  if attributes.(confidentiality)
  then attributes.(authenticity) = false /\ attributes.(integrity) = false
  else True.

(* Split channel creation into two cases: creating a channel where everyone has equal privileges to send messages
   with the requested security properties and creating a channel where one owner is able to authenticate messages xor receive 
   confidential messages. *)
Inductive create_channel  : universe -> universe -> Prop :=
| GroupChannel : forall (requester : user_id)
                        (other_members : list user_id)
                        (attributes : channel_permissions)
                        (ch_id : channel_id)
                        (U : universe),
    requester \in (dom U.(users)) ->
                  ~(ch_id \in (dom U.(channels))) ->
                  member requester other_members = false ->
                  (*cast list to set, check if subset*)
                  all_existing_users other_members (dom U.(users)) ->
                  create_channel U {| users := add_ports (requester :: other_members) U.(users) ch_id;
                                      channels := (U.(channels) $+ (ch_id, {| properties := attributes ;
                                                                              parties := (Members (requester :: other_members)) |})) ;
                                      trace := "new channel" :: U.(trace) |}.
(*
| BroadcastChannel : forall (requester : user_id)
                            (attributes : channel_permissions)
                            (ch_id : channel_id)
                            (U : universe),
    requester \in (dom U.(users)) ->
                  valid_properties attributes ->
                  create_channel U {| users := add_ports ( (minus (dom U.(users)) {user_id})) U.(users) ch_id ;
                                      channels := U.(channels) $+ (ch_id, {| properties := attributes ;
                                                                              parties := (Owner user_id) |}) ;
                                      trace := "new channel" :: U.(trace) |}.
*)

(* Helper function for WriteToPort:
   Write the specified message to the ports on the given channel for every specified receiver *)
Fixpoint send_msg (msg : message) (msg_recievers : list user_id) (users : fmap user_id user_data) (ch_id : channel_id) : (fmap user_id user_data) :=
  let write_to_port_list := (fix wtp p_list := match p_list with
      | [] => p_list
      | pr::pr' => {| ch := pr.(ch) ; unread := pr.(unread) ++ [msg] |} :: (wtp pr')
      end)
  in
  match msg_recievers with
  | [] => users
  | reciever::other_recievers' => let rec := users $? reciever in
                     match rec with
                     | None => $0
                     | Some valid_rec => let ports_list := valid_rec.(ports) in
                                         (send_msg msg other_recievers' users ch_id)
                                         $+ (reciever, {| ports := (write_to_port_list ports_list) |})
                     end
  end.

(* Helper function for WriteToPort
   Given a channel id and a list of ports, if the list of ports contains a port with the corresponding channel id, 
   return true, else return false. *)
Fixpoint in_list (ch_id : channel_id) (p_list : list port_data) : Prop :=
  match p_list with
  | [] => False
  | p :: p' => if p.(ch) =? ch_id then True else in_list ch_id p'
  end.

(* Helper function for WriteToPort:
   Given the user_id of the requester, a channel id, and the set of users, if
   check if the requester has the correct port for the channel he is requesting (currently to write to) *)
Fixpoint has_port (requester : user_id) (ch_id : channel_id) users : Prop :=
  let rec := users $? requester in
  match rec with
  | None => False
  | Some valid_rec => let ports_list := valid_rec.(ports) in
                      in_list ch_id ports_list
  end.

(* Helper function for WriteToPort (not implemented yet):
   Returns the list of all users that aren't the writer in the channel *)
Fixpoint get_receivers (writer : user_id) (ch_id : channel_id) (channels : fmap channel_id channel) : (list user_id) :=
[].

(* Implementation not yet finished.
   Check that the writer has the correct port, then write the message to all receiver ports and to the trace *) 
Inductive WriteToPort :  message -> universe -> universe -> Prop :=
| WriteToGroup : forall (writer : user_id)
                        (msg : message)
                        (ch_id : channel_id)
                        (U : universe),
   ch_id \in (dom U.(channels)) -> (* Change this. Writer should exhibit the port, not channel id *)
     has_port writer ch_id U.(users) ->
       WriteToPort msg U {| users := U.(users)(* send_msg msg (get_receivers writer ch_id U.channels) U.(users) ch_id *) ;
                        channels := U.(channels) ;
                        trace := U.(trace) |}. (* Is something added to the trace after message is sent? *)
   
(* Implementation not yet finished.
   Updates user data for a reader after they read from a channel. Drops read message from message list. 
   Will eventually pattern match so reader can wait for specific messages. *)
Fixpoint check_port (port_reader : user_id) (users : fmap user_id user_data) (ch_id : channel_id) : ((user_id * user_data)) :=
  let rec := users $? port_reader in
  match rec with 
  | None => (0, {| ports := [] |}) (* reader is not a user *)
  | Some valid_rec => let ports_list := valid_rec.(ports) in
                      match ports_list with
                      | [] => (port_reader, valid_rec) (* no ports to read from *)
                      | pr::other_ports => match pr.(ch) with
                                           | ch_id => match pr.(unread) with
                                                      | [] => (port_reader, valid_rec) (* no messages to read *)
                                                      | h::t => (port_reader, {| ports := {| ch := ch_id ;
                                                                                             unread := t |} 
                                                                                          :: other_ports |}) 
                                                      end
                                           end
                      end
  end.
  
(* Should I just return the whole users set of universe? 
   How to remove old set element from the set of users *)

(*
   | ReadFromPort
   | WriteToPort *)
(* create new channel with group and security properties *)

(* send message with given port *)
(* receive message from given port (from given channel?) *)

