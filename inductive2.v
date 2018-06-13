From Coq Require Import String.
Require Import Frap.

Definition message := string.

Definition user_id := nat.

Inductive roles :=
| Owner : user_id -> roles
| Members : list user_id -> roles.

Record channel_permissions :=
  { confidentiality : bool ;
    authenticity : bool ;
    integrity : bool }.

Record channel :=
  { properties : channel_permissions ;
    parties : roles }.

Definition channel_id := nat.

Record port :=
  { ch : channel_id ;
   unread : list message ; }.

Definition port_id := nat.

Record user_data :=
  { ports : list port
    (*program : nat*) }.

Record universe :=
  { users : fmap user_id user_data ;
    channels : fmap channel_id channel ;
    trace : list message }.


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

Fixpoint all_existing_users (members : list user_id)  users : Prop :=
  match members with
  | [] => True
  | m :: ms => m \in users /\ all_existing_users ms users
  end.

(* groups of 2 can't have one but not the other when it comes to IA. should requesting one without the other be invalid? or should we automatically give the other one? *)
Definition valid_properties group_size attributes : Prop :=
  if group_size =? 1 then
    True else attributes = {| confidentiality := false ; authenticity := false ; integrity := true |}.

Inductive create_channel  : universe -> universe -> Prop :=
| GroupChannel : forall (requester : user_id)
                        (other_members : list user_id)
                        (attributes : channel_permissions)
                        (ch_id : channel_id)
                        (U : universe),
    requester \in (dom U.(users)) ->
                  member requester other_members = false ->
                  all_existing_users other_members (dom U.(users)) ->
                  create_channel U {| users := add_ports (requester :: other_members) U.(users) ch_id;
                                      channels := (U.(channels) $+ (ch_id, {| properties := attributes ;
                                                                              parties := (Members (requester :: other_members)) |})) ;
                                      trace := "new channel" :: U.(trace) |}.
(* | BroadcastChannel 
                  valid_properties (length other_members) attributes -> 
   | ReadFromPort
   | WriteToPort *)
(* create new channel with group and security properties *)

(* send message with given port *)
(* receive message from given port (from given channel?) *)

(* real world only *)
(* sign *)
(* verify *)
(* encrypt *)
(* decrypt *)