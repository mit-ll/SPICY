From Coq Require Import String.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := nat.

Definition channel_id := nat.

Definition next_message := nat.

Definition msg_index := nat.

(* Messages *)
Inductive message :=
| ChannelId : (channel_id * next_message) -> message
| MessageBody : string -> message.

Record security_properties :=
  { confidentiality : bool ;
    authenticity : bool ;
    integrity : bool }.

Inductive channel_type :=
| Broadcast : user_id -> channel_type
| Default : user_id -> user_id -> channel_type
| Symmetric : channel_type.

Record channel_data :=
  { properties : security_properties ;
    type : channel_type ;
    messages_sent : list (user_id * message) }.

(* Definition valuation := fmap var message. *)
Definition valuation := fmap user_id message. (* Changed to make universe generator work 
                                               * Ask Adam questions from below. *)

Inductive returns :=
| Recv (ch_id : channel_id)
| CreateChannel (sp : security_properties).

Inductive cmd :=
| Skip
| Assign (x : var) (e : returns)
| Sequence (c1 c2 : cmd)
| Send (ch_id : channel_id) (m : message).

Record user_data :=
  { protocol : cmd ;
    env : valuation }.

Record universe  :=
  { channel_vector : fmap channel_id channel_data ;
    users : fmap user_id user_data ;
    trace : list (channel_id * (user_id * message)) }.

Fixpoint interp
         (r : returns)
         (chs : fmap channel_id channel_data)
         (u : user_id)
         (new_id : channel_id)
         (i : msg_index)
  : option message :=
  let not_sent_by_me := (fix nsbm index msgs :=
                           match msgs with
                           | [] => None
                           | (u', m) :: msgs' => match index with
                                          | S i => nsbm i msgs'
                                          | O => if u' =? u then nsbm index msgs' else Some m
                                          end
                           end) in
  match r with
  | CreateChannel props => Some(ChannelId(new_id, 0))
  | Recv ch_id => match chs $? ch_id with
                  | None => None
                  | Some ch_d => not_sent_by_me i ch_d.(messages_sent)
                  end

  end.

(*
Inductive eval : universe -> universe -> Prop.
Admitted.
*)




(* Universe Generator Stuff *)

(* Helper Function for generate_universe *)
Fixpoint add_users (new_u_id : user_id) (user_data_list : list user_data) (umap : fmap user_id user_data) : (fmap user_id user_data) :=
match user_data_list with
| [] => umap
| udata::t => let user_map' := umap $+ (new_u_id, udata) in
                (add_users (new_u_id + 1) t user_map')
end.

(* Helper Function for generate_universe *)
Fixpoint generate_all_pairs (uList : list user_id) : list (user_id * user_id) :=
let generate_pairs := (fix gp (u_id_from : user_id)
                              (u_id_to : user_id)
                              (uList : list user_id) : (list (user_id * user_id)) :=
                          match uList with
                          | [] => []
                          | uId::uIds' => (pair u_id_from u_id_to) :: (gp u_id_from (u_id_to + 1) uIds')
                          end) in
match uList with
| [] => []
| uId::[] => []
| uId::uIds' => (generate_all_pairs uIds') ++ (generate_pairs uId (uId + 1) uIds')
end.

(* Helper Function for generate_universe *)
Fixpoint add_channels' (plist : list (user_id * user_id))
                       (ch_id : channel_id)
                       (umap : fmap user_id user_data) : universe :=
let empty_universe := {| channel_vector := $0 ; users := umap ; trace := [] |} in
let empty_user_data := {| protocol := Skip ; env := $0 |} in
match plist with
| [] => empty_universe
| pair'::t => match pair' with
              | (pair id1 id2) => let next_iter := (add_channels' t (ch_id + 1) umap) in
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
                                                                               env := id1_data.(env) $+ (id2, ChannelId (ch_id, 0)) |})
                                                                   $+ (id2, {| protocol := id2_data.(protocol);
                                                                               env := id2_data.(env) $+ (id1, ChannelId (ch_id, 0)) |})) ;
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
Fixpoint generate_universe (user_data_list : list user_data) : universe :=
let generate_ulist := (fix g_ulist (uid : user_id)
                                   (user_data_list : list user_data) : (list user_id) :=
                        match user_data_list with
                        | [] => []
                        | data::t => (uid : user_id) :: (g_ulist (uid + 1) t)
                        end) in
 let ulist := generate_ulist 0 user_data_list in
  let umap' := (add_users 0 user_data_list $0) in
    add_channels' (generate_all_pairs ulist) (0 : channel_id) umap'.

