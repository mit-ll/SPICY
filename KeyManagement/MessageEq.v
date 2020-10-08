(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import List.

Require Import
        MyPrelude
        AdversaryUniverse
        ChMaps
        Messages
        Maps
        Common
        Keys
        Tactics
        IdealWorld
        RealWorld
.

(* Require RealWorld IdealWorld. *)
Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.
(* assumes that there is a shadow copy of the built message in every store in the cipherheap *)
(* potential major refactor for usage/id/sym interraction?*)

(* Inductive content_eq (gks : keys) : *)
(*   forall {t__rw t__iw}, RealWorld.message.message t__rw -> IdealWorld.message.message t__iw -> Prop := *)

(* | ContentEq : forall c__rw c__iw, *)
(*     c__rw = c__iw *)
(*     ->  content_eq gks (RealWorld.message.Content c__rw) (IdealWorld.message.Content c__iw) *)
(* | PermissionSymEq : forall kid kt tf ch_id a, *)
(*     gks $? kid = Some (MkCryptoKey kid kt SymKey) *)
(*     -> a = IdealWorld.construct_permission true true *)
(*     -> content_eq gks *)
(*                  (RealWorld.message.Permission (kid,tf)) *)
(*                  (IdealWorld.message.Permission (IdealWorld.construct_access a ch_id)) *)
(* | PermissionAsymSignEq : forall kid tf ch_id a anyB, *)
(*     gks $? kid = Some (MkCryptoKey kid Signing AsymKey) *)
(*     -> a = IdealWorld.construct_permission true anyB *)
(*     -> content_eq gks *)
(*                  (RealWorld.message.Permission (kid,tf)) *)
(*                  (IdealWorld.message.Permission (IdealWorld.construct_access a ch_id)) *)
(* | PermissionAsymEncEq : forall kid tf ch_id a anyB, *)
(*     gks $? kid = Some (MkCryptoKey kid Encryption AsymKey) *)
(*     -> a = IdealWorld.construct_permission anyB true *)
(*     -> content_eq gks *)
(*                  (RealWorld.message.Permission (kid,tf)) *)
(*                  (IdealWorld.message.Permission (IdealWorld.construct_access a ch_id)) *)

(* . *)

Fixpoint content_eq {t__rw t__iw}
         (m__rw : RealWorld.message.message t__rw)
         (m__iw : IdealWorld.message.message t__iw) gks : Prop :=
  match (m__rw, m__iw) with
  | (RealWorld.message.Content c__rw, IdealWorld.message.Content c__iw) => c__rw = c__iw
  | (RealWorld.message.Permission (id, pk) , IdealWorld.message.Permission (IdealWorld.construct_access a _)) =>
    match (gks $? id) with
    | Some (Keys.MkCryptoKey id _ Keys.SymKey) => a = (IdealWorld.construct_permission true true)
    | Some (Keys.MkCryptoKey id Keys.Signing Keys.AsymKey) => a = (IdealWorld.construct_permission true pk)
    | Some (Keys.MkCryptoKey id Keys.Encryption Keys.AsymKey) => a = (IdealWorld.construct_permission pk true)
    | _ => False
    end
  | (RealWorld.message.MsgPair m__rw1 m__rw2, IdealWorld.message.MsgPair m__iw1 m__iw2) =>
    content_eq m__rw1 m__iw1 gks /\ content_eq m__rw2 m__iw2 gks
  | _ => False
  end.

Definition resolve_perm (ps : IdealWorld.permissions) id :=
  match id with
  | ChMaps.Single ch => ps $? ch
  | ChMaps.Intersection ch1 ch2 =>
    match (ps $? ch1, ps $? ch2) with
    | (Some p1, Some p2) => Some (IdealWorld.perm_intersection p1 p2)
    | _ => None
    end
  end.

Definition not_replayed (cs : RealWorld.ciphers) (honestk : key_perms)
           (uid : user_id) (froms : RealWorld.recv_nonces) {t} (msg : RealWorld.crypto t) :=
  RealWorld.msg_honestly_signed honestk cs msg
  && RealWorld.msg_to_this_user cs (Some uid) msg
  && match msg_nonce_ok cs froms msg with
     | Some f => true
     | None   => false
     end.

Definition key_perms_from_known_ciphers (cs : RealWorld.ciphers) (mycs : RealWorld.my_ciphers) (ks0 : key_perms) :=
  fold_left (fun kys cid => match cs $? cid with
                         | Some (RealWorld.SigCipher _ _ _ m) => kys $k++ RealWorld.findKeysMessage m
                         | Some (RealWorld.SigEncCipher _ _ _ _ m) => kys $k++ RealWorld.findKeysMessage m
                         | None => kys
                         end) mycs ks0.

Definition key_perms_from_message_queue (cs : RealWorld.ciphers) (honestk: key_perms)
           (msgs : RealWorld.queued_messages) (uid : user_id) (froms : RealWorld.recv_nonces) (ks0 : key_perms) :=
  let cmsgs := clean_messages honestk cs (Some uid) froms msgs
  in  fold_left (fun kys '(existT _ _ m) => kys $k++ RealWorld.findKeysCrypto cs m) cmsgs ks0.

Inductive compat_perm : option bool -> bool -> Prop :=
| CompatEq :
    compat_perm (Some false) false
| CompatNone :
    compat_perm None false
| CompatTrue : forall sp,
    compat_perm sp true.

(* Inductive user_perms_channel_match {A} (uid : user_id) (usr__rw : RealWorld.user_data A) (usr__iw : IdealWorld.user A) *)
(*           (honestk : key_perms) (cs : RealWorld.ciphers) (c_id : RealWorld.cipher_id) (ch_id : channel_id) : Prop := *)

(* | SigChannel : forall mks cks ks b__read b__write k__sign u_id msg_seq t (m__rw : RealWorld.message.message t), *)
(*     RealWorld.honest_key honestk k__sign *)
(*     -> cs $? c_id = Some (RealWorld.SigCipher k__sign u_id msg_seq m__rw) *)
(*     -> cks = key_perms_from_known_ciphers cs usr__rw.(RealWorld.c_heap) $0 *)
(*     (* -> mks = key_perms_from_message_queue cs honestk usr__rw.(RealWorld.msg_heap) uid usr__rw.(RealWorld.from_nons) $0 *) *)
(*     -> mks = $0 *)
(*     -> ks = usr__rw.(RealWorld.key_heap) $k++ cks $k++ mks *)
(*     -> resolve_perm usr__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write) *)
(*     -> compat_perm (ks $? k__sign) b__write *)
(*     -> b__read = true *)
(*     -> user_perms_channel_match uid usr__rw usr__iw honestk cs c_id ch_id *)
(* | SigEncChannel : forall mks cks ks b__read b__write k__sign k__enc u_id msg_seq t (m__rw : RealWorld.message.message t), *)
(*     RealWorld.honest_key honestk k__sign *)
(*     -> cs $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc u_id msg_seq m__rw) *)
(*     -> cks = key_perms_from_known_ciphers cs usr__rw.(RealWorld.c_heap) $0 *)
(*     (* -> mks = key_perms_from_message_queue cs honestk usr__rw.(RealWorld.msg_heap) uid usr__rw.(RealWorld.from_nons) $0 *) *)
(*     -> mks = $0 *)
(*     -> ks = usr__rw.(RealWorld.key_heap) $k++ cks $k++ mks *)
(*     -> resolve_perm usr__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write) *)
(*     -> compat_perm (ks $? k__sign) b__write *)
(*     -> compat_perm (ks $? k__enc) b__read *)
(*     -> user_perms_channel_match uid usr__rw usr__iw honestk cs c_id ch_id *)
(* . *)

(* Inductive  message_eq : forall {A B t}, *)
(*     RealWorld.crypto t -> RealWorld.universe A B -> *)
(*     IdealWorld.message.message t -> IdealWorld.universe A -> IdealWorld.channel_id -> Prop := *)
(* | CryptoSigCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign *)
(*                     (m__rw : RealWorld.message.message t) honestk u_id msg_seq, *)
(*     U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigCipher k__sign u_id msg_seq m__rw) *)
(*     -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys) *)
(*     -> honestk = RealWorld.findUserKeys (U__rw.(RealWorld.users)) *)
(*     -> (forall u data__rw data__iw, *)
(*           U__rw.(RealWorld.users) $? u = Some data__rw *)
(*           -> U__iw.(IdealWorld.users) $? u = Some data__iw *)
(*           -> RealWorld.honest_key honestk k__sign *)
(*           -> user_perms_channel_match u data__rw data__iw honestk U__rw.(RealWorld.all_ciphers) c_id ch_id *)
(*       ) *)
(*     -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id *)

(* | CryptoSigEncCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign k__enc *)
(*                        (m__rw : RealWorld.message.message t) honestk u_id msg_seq, *)
(*     U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc u_id msg_seq m__rw) *)
(*     -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys) *)
(*     -> honestk = RealWorld.findUserKeys U__rw.(RealWorld.users) *)
(*     -> (forall u data__rw data__iw, *)
(*           U__rw.(RealWorld.users) $? u = Some data__rw *)
(*           -> U__iw.(IdealWorld.users) $? u = Some data__iw *)
(*           -> RealWorld.honest_key honestk k__sign *)
(*           -> RealWorld.honest_key honestk k__enc *)
(*           -> user_perms_channel_match u data__rw data__iw honestk U__rw.(RealWorld.all_ciphers) c_id ch_id *)
(*       ) *)
(*     -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id. *)
