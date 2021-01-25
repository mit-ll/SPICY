(* 
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List.

From SPICY Require Import
     MyPrelude
     AdversaryUniverse
     ChMaps
     Messages
     Maps
     Keys
     Tactics
     IdealWorld
     RealWorld
.

Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.

Fixpoint content_eq {t__rw t__iw}
         (m__rw : RealWorld.message.message t__rw)
         (m__iw : IdealWorld.message.message t__iw) gks : Prop :=
  match (m__rw, m__iw) with
  | (RealWorld.message.Content c__rw, IdealWorld.message.Content c__iw) => c__rw = c__iw
  | (RealWorld.message.Permission (id, pk) , IdealWorld.message.Permission (IdealWorld.construct_access a _)) =>
    match (gks $? id) with
    | Some (Keys.MkCryptoKey _ _ Keys.SymKey) => a = (IdealWorld.construct_permission true true)
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
