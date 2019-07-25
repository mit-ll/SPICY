Require Import Maps.
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

Inductive message_eq : forall {A B} {t__rw : RealWorld.message.type} {t__iw : IdealWorld.message.type},
    RealWorld.crypto t__rw -> IdealWorld.message.message t__iw ->
    RealWorld.universe A B -> IdealWorld.universe A ->
    set Keys.key_identifier -> set Keys.key_identifier -> Prop :=
| ContentCase : forall {A B t__rw t__iw}
                       (c : RealWorld.message.message t__rw)
                       (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A)
                       (readers writers : set Keys.key_identifier) (m : IdealWorld.message.message t__iw)
                       (ms : list (sigT (IdealWorld.message.message)))
                       (u : Common.user_id)
                       (data__rw : RealWorld.user_data A)
                       (data__iw : IdealWorld.user A)
                       (k__enc k__sig : Keys.key_identifier)
                       (ch_id : IdealWorld.channel_id)
                       (b : bool),
      U__iw.(IdealWorld.channel_vector) $? ch_id = Some ((existT _ _ m) :: ms) ->
      U__rw.(RealWorld.users) $? u = Some data__rw ->
      U__iw.(IdealWorld.users) $? u = Some data__iw ->
      k__enc \in writers ->
      (data__rw.(RealWorld.key_heap) $? k__enc = Some true
       <-> data__iw.(IdealWorld.perms) $? ch_id = Some (IdealWorld.construct_permission b true)) ->
      k__enc \in readers ->
      (data__rw.(RealWorld.key_heap) $? k__enc = Some true
       <-> data__iw.(IdealWorld.perms) $? ch_id = Some (IdealWorld.construct_permission true b)) ->
      message_eq (RealWorld.Content c) m U__rw U__iw readers writers
| SignEncCase : forall {A B t__rw t__iw}
                       (c__id : RealWorld.cipher_id)
                       (c : RealWorld.crypto t__rw) (m : IdealWorld.message.message t__iw)
                       (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A)
                       (readers writers : set Keys.key_identifier)
                       (k__enc k__sig : Keys.key_identifier),
    U__rw.(RealWorld.all_ciphers) $? c__id = Some (RealWorld.SigEncCipher k__sig k__enc c) ->
    message_eq c m U__rw U__iw ({k__enc} \cup readers) ({k__sig} \cup writers) ->
    @message_eq A B t__rw t__iw (RealWorld.SignedCiphertext k__enc k__sig c__id) m U__rw U__iw readers writers
| SignatureCase : forall {A B t__rw t__iw}
                         (c__id : RealWorld.cipher_id)
                         (m : RealWorld.crypto t__rw) (m__iw : IdealWorld.message.message t__iw)
                         (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A)
                         (readers writers : set Keys.key_identifier)
                         (k__sig : Keys.key_identifier),
    U__rw.(RealWorld.all_ciphers) $? c__id = Some (RealWorld.SigCipher k__sig m) ->
    message_eq m m__iw U__rw U__iw readers ({k__sig} \cup writers) ->
    message_eq (RealWorld.Signature m k__sig c__id) m__iw U__rw U__iw readers writers.


(* Definition garbage : option (list RealWorld.key_identifier) * exmsg := *)
(*   (None, Exm (RealWorld.Plaintext 0)). *)

(* Fixpoint key_sets {t : RealWorld.type} (msg : RealWorld.message t) (cipher_heap : RealWorld.ciphers) (form : RealWorld.message_form) := *)
(*   match form with *)
(*   | RealWorld.PtKeyForm => match msg with *)
(*                 | RealWorld.Plaintext c => (Some nil, Exm c) :: nil *)
(*                 | RealWorld.KeyMessage k => (Some nil, Exm (RealWorld.Plaintext 0)) :: nil *)
(*                 | _ => garbage :: nil *)
(*                 end *)
(*   | RealWorld.CryptoForm f => match msg with *)
(*                | RealWorld.SignedCiphertext _ _ id => *)
(*                  match cipher_heap $? id with *)
(*                  | Some (RealWorld.SigEncCipher k__sig k__enc m _) => *)
(*                    map (fun x => (match fst x with *)
(*                                   | Some ls => Some (k__sig :: k__enc :: ls) *)
(*                                   | None => None         *)
(*                                end, snd x)) (key_sets m cipher_heap f) *)
(*                  | Some _ *)
                        
(*                  | None => garbage :: nil *)
(*                  endjk *)
(*                | RealWorld.Signature _ id _ => *)
(*                  match cipher_heap $? id with *)
(*                  | Some (RealWorld.SigCipher k_id m _) => *)
(*                    map (fun x => (match fst x with *)
(*                                   | Some ls => Some (k_id :: ls) *)
(*                                   | None => None *)
(*                                end, snd x)) (key_sets m cipher_heap f) *)
(*                        | Some _  *)
(*                  | None => garbage :: nil *)
(*                  end                         *)
(*                | _ => garbage :: nil *)
(*                end *)
(*   | RealWorld.PairForm _ => garbage :: nil *)
(*   end. *)


(* Definition get_keys_from_ids (ks : list (RealWorld.key_identifier)) (heap : RealWorld.keys) := *)
(*   map (fun k => heap $? k) ks. *)

(* (* This list represents all the keys that must be owned by the readers of the channel this message is  *)
(*    sent on. *) *)
(* Fixpoint asym_enc (ks : list (option RealWorld.key)) : list RealWorld.key_identifier := *)
(*   match ks with *)
(*   | nil => nil *)
(*   | k :: ks' => match k with *)
(*                | Some k' => match k'.(RealWorld.keyUsage) with *)
(*                            | (RealWorld.Encryption) => k'.(RealWorld.keyId) :: (asym_enc ks') *)
(*                            | _ => asym_enc ks' *)
(*                            end *)
(*                | _ => asym_enc ks' (* handle differently? this key doesn't exist so it should be handled when attempting to send *) *)
(*                end *)
(*   end. *)

(* (* If this returns Some key then that is the last key to sign the message. That means that the last place  *)
(*    this message should have been written is on channel on which only the owner of this key can write. That  *)
(*    channel may have limited readability; use "encrypting keys" to find the set of keys owned by readers *) *)
(* Fixpoint asym_sign (ks : list (option RealWorld.key)) : option RealWorld.key_identifier := *)
(*   match ks with *)
(*   | nil => None *)
(*   | k :: ks' => match k with *)
(*                | Some k' => match (k'.(RealWorld.keyUsage), k'.(RealWorld.keyType)) with *)
(*                            | (RealWorld.Signing, RealWorld.AsymKey) => Some k'.(RealWorld.keyId) *)
(*                            | _ => asym_sign ks' *)
(*                            end *)
(*                | None => asym_sign ks' *)
(*                end *)
(*   end. *)
(* (* The owners of the set of all these keys should be able to read and  write to the channel this message  *)
(*    is sent on. *) *)
(* Fixpoint sym_keys (ks : list (option RealWorld.key)) : list RealWorld.key_identifier := *)
(*   match ks with *)
(*   | nil => nil *)
(*   | k :: ks' => match k with *)
(*                | Some k' => match k'.(RealWorld.keyType) with *)
(*                            | RealWorld.SymKey => k'.(RealWorld.keyId) :: sym_keys ks' *)
(*                            | _ => sym_keys ks'                                    *)
(*                            end *)
(*                | None => sym_keys ks' (* handle differently? *) *)
(*                end *)
(*   end. *)

(* Fixpoint content_eq {t__rw t__iw} (m__rw : RealWorld.message t__rw) (m__iw : IdealWorld.message t__iw) := *)
(*   match (m__rw, m__iw) with *)
(*   | (RealWorld.Plaintext n__rw, IdealWorld.Content n__id) => n__rw = n__id *)
(*   | (RealWorld.KeyMessage _, IdealWorld.Permission _ _) => True *)
                                                          
(*   | _ => False *)
(*   end. *)

(* (* have this take an exmsg *) *)
(* Definition key_sets_helper {A B t__rw} (msg : RealWorld.message t__rw) (U__rw : RealWorld.universe A B) := *)
(*   match msg with *)
(*   | RealWorld.Plaintext _ *)
(*   | RealWorld.KeyMessage _ *)
(*   | RealWorld.MsgPair _ _ => nil *)
(*   | RealWorld.SignedCiphertext _ _ c__id => *)
(*     match U__rw.(RealWorld.all_ciphers) $? c__id with *)
(*     | Some (RealWorld.SigEncCipher _ _ _ mf) => key_sets msg U__rw.(RealWorld.all_ciphers) mf *)
(*     | _ => nil *)
(*     end *)
(*   | RealWorld.Signature _ _ c__id => *)
(*     match U__rw.(RealWorld.all_ciphers) $? c__id with *)
(*     | Some (RealWorld.SigCipher _ _ mf) => key_sets msg U__rw.(RealWorld.all_ciphers) mf *)
(*     | _ => nil *)
(*     end *)
(*   end. *)

(* Inductive message_matches {A B t__rw t__iw} : RealWorld.message t__rw * RealWorld.universe A B -> IdealWorld.message t__iw * IdealWorld.universe A -> Prop := *)
(* | CheckMessage : forall U__rw U__iw msg__rw msg__iw keys content ksets keys__sym key__sign keys__enc, *)
(*     (Some keys, content) :: ksets = key_sets_helper msg__rw U__rw *)
(*     -> keys__sym = sym_keys (get_keys_from_ids keys U__rw.(RealWorld.all_keys)) *)
(*     -> key__sign = asym_sign (get_keys_from_ids keys U__rw.(RealWorld.all_keys)) *)
(*     -> keys__enc = asym_enc (get_keys_from_ids keys U__rw.(RealWorld.all_keys)) *)
(*     -> (exists ch__iw, *)
(*           (forall user k ks' ks'' udata__rw udata__iw, *)
(*               keys__sym = ks' :: k :: ks'' *)
(*               -> U__rw.(RealWorld.users) $? user = Some udata__rw                                *)
(*               -> udata__rw.(RealWorld.key_heap) $? k = Some true *)
(*               -> U__iw.(IdealWorld.users) $? user = Some udata__iw *)
                                                      
(*                                      -> udata__iw.(IdealWorld.perms) $? ch__iw = Some (IdealWorld.construct_permission true true)) *)
(*           /\ (forall user k udata__rw udata__iw b, key__sign = Some k *)
(*                                        -> U__rw.(RealWorld.users) $? user = Some udata__rw *)
(*                                        -> udata__rw.(RealWorld.key_heap) $? k = Some true *)
(*                                        -> U__iw.(IdealWorld.users) $? user = Some udata__iw *)
(*                                        -> udata__iw.(IdealWorld.perms) $? ch__iw = Some (IdealWorld.construct_permission b true)) *)
(*           /\ (forall user k ks' ks'' udata__rw udata__iw b, *)
(*                 keys__enc = ks' :: k :: ks'' *)
(*                 -> U__rw.(RealWorld.users) $? user = Some udata__rw *)
(*                 -> udata__rw.(RealWorld.key_heap) $? k = Some true *)
(*                 -> U__iw.(IdealWorld.users) $? user = Some udata__iw *)
(*                 -> udata__iw.(IdealWorld.perms) $? ch__iw = Some (IdealWorld.construct_permission true b)) *)
(*           /\ (forall ch__set, *)
(*                 U__iw.(IdealWorld.channel_vector) $? ch__iw = Some ch__set *)
(*                 -> (Exm msg__rw) \in ch__set)) *)
(*     (*-> content_eq content msg__iw exists T message queue type in RW *) *)
(*     -> message_matches (msg__rw, U__rw) (msg__iw, U__iw). *)
