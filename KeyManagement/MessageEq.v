Require Import Maps Messages.
Require RealWorld IdealWorld Common Keys MyPrelude.
From Coq Require Import List.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).


Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.
(* assumes that there is a shadow copy of the built message in every store in the cipherheap *)
(* potential major refactor for usage/id/sym interraction?*)

Fixpoint content_eq  {t__rw t__iw} (m__rw : RealWorld.message.message t__rw) (m__iw : IdealWorld.message.message t__iw) : Prop :=
  match (m__rw, m__iw) with
  | (RealWorld.message.Content c__rw, IdealWorld.message.Content c__iw) => c__rw = c__iw
  | (RealWorld.message.Permission _, IdealWorld.message.Permission _) => True
  | (RealWorld.message.MsgPair m__rw1 m__rw2, IdealWorld.message.MsgPair m__iw1 m__iw2) =>
    content_eq m__rw1 m__iw1 /\ content_eq m__rw2 m__iw2
  | _ => False
  end.

Inductive  message_eq : forall {A B} {t : type}, (* just one t : type? *)
  RealWorld.crypto t -> RealWorld.universe A B ->
  IdealWorld.message.message t -> IdealWorld.universe A -> IdealWorld.channel_id -> Prop :=
| ContentCase : forall {A B t}  (U__rw : RealWorld.universe A B) U__iw (m__rw : RealWorld.message.message t) m__iw ch_id user_data,
    content_eq m__rw m__iw
    ->( forall u, U__iw.(IdealWorld.users) $? u = Some user_data
            -> user_data.(IdealWorld.perms) $? ch_id = Some (IdealWorld.construct_permission true true))
    -> message_eq (RealWorld.Content m__rw) U__rw m__iw U__iw ch_id
| CryptoSigCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign
                    (m__rw : RealWorld.message.message t) data__rw data__iw b__rw b__iw,
    U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigCipher k__sign m__rw)
    -> content_eq m__rw m__iw
    -> (forall u, U__rw.(RealWorld.users) $? u = Some data__rw
            -> U__iw.(IdealWorld.users) $? u = Some data__iw
            -> (data__rw.(RealWorld.key_heap) $? k__sign = Some b__rw
               <-> data__iw.(IdealWorld.perms) $? ch_id = Some (IdealWorld.construct_permission true b__iw)))
    -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id
| CryptoSigEncCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign k__enc
                       (m__rw : RealWorld.message.message t) data__rw data__iw b__rwsig,
    U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc m__rw)
    -> content_eq m__rw m__iw
    -> (forall u, U__rw.(RealWorld.users) $? u = Some data__rw
            -> U__iw.(IdealWorld.users) $? u = Some data__iw
            -> ((data__rw.(RealWorld.key_heap) $? k__sign = Some b__rwsig
                /\ data__rw.(RealWorld.key_heap) $? k__enc = Some true)
               <-> data__iw.(IdealWorld.perms) $? ch_id = Some (IdealWorld.construct_permission true true)))
    -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id.
