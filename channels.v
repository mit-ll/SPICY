From Coq Require Import String.
Require Import Frap.

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

Definition valuation := fmap var message.

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

Record universe :=
  { channel_vector := fmap channel_id channel_data ;
    users := fmap user_id user_data ;
    trace := list (channel_id * (user_id * message)) }.

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

Inductive eval : universe -> universe -> Prop.