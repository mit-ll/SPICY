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
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
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
.

Require Import MessagesTheory.

Require RealWorld IdealWorld.
Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.
(* assumes that there is a shadow copy of the built message in every store in the cipherheap *)
(* potential major refactor for usage/id/sym interraction?*)

Fixpoint content_eq  {t__rw t__iw}
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
  in  fold_left (fun kys '(existT _ _ m) => kys $k++ RealWorld.findKeysCrypto cs m) cmsgs.


(* Definition key_perms_from_message_queue (cs : RealWorld.ciphers) (honestk: key_perms) *)
(*            (msgs : RealWorld.queued_messages) (uid : user_id) (froms : RealWorld.recv_nonces) (ks0 : key_perms) := *)
(*   match msgs with *)
(*   | (existT _ _ m :: ms) => if not_replayed cs honestk uid froms m *)
(*                           then ks0 $k++ RealWorld.findKeysCrypto cs m *)
(*                           else ks0 *)
(*   | _                   => ks0 *)
(*   end. *)

Lemma key_perms_from_known_ciphers_notation :
  forall cs mycs ks,
  fold_left (fun kys cid => match cs $? cid with
                         | Some (RealWorld.SigCipher _ _ _ m) => kys $k++ RealWorld.findKeysMessage m
                         | Some (RealWorld.SigEncCipher _ _ _ _ m) => kys $k++ RealWorld.findKeysMessage m
                         | None => kys
                         end) mycs ks
  = key_perms_from_known_ciphers cs mycs ks.
  unfold key_perms_from_known_ciphers; trivial.
Qed.

Lemma key_perms_from_message_queue_notation :
  forall cs honestk msgs ks uid froms,
    (let cmsgs := clean_messages honestk cs (Some uid) froms msgs
     in  fold_left (fun kys '(existT _ _ m) => kys $k++ RealWorld.findKeysCrypto cs m) cmsgs)
    = key_perms_from_message_queue cs honestk msgs uid froms ks.
  unfold key_perms_from_message_queue; trivial.
Qed.

Lemma clean_messages_cons_split :
  forall cs honestk uid froms msgs cmsgs t (msg : RealWorld.crypto t),
    cmsgs = clean_messages honestk cs (Some uid) froms ((existT _ _ msg) :: msgs)
    -> (cmsgs = clean_messages honestk cs (Some uid) froms msgs /\ not_replayed cs honestk uid froms msg = false)
      \/ exists n, 
        cmsgs = (existT _ _ msg) :: clean_messages honestk cs (Some uid) (n :: froms) msgs
        /\ not_replayed cs honestk uid froms msg = true.
Proof.
  unfold clean_messages, clean_messages'; simpl; intros.
  cases (not_replayed cs honestk uid froms msg); subst; simpl;
    unfold not_replayed in * |- ; unfold RealWorld.msg_signed_addressed.

  - right.
    rewrite !andb_true_iff in *; split_ex.
    rewrite H, H1; simpl.
    unfold msg_nonce_ok in *; destruct msg; try discriminate.
    cases (cs $? c_id); try discriminate.
    cases (count_occ RealWorld.msg_seq_eq froms (RealWorld.cipher_nonce c)); try discriminate.
    eexists; split; eauto.
    rewrite !fold_clean_messages2', clean_messages'_fst_pull, !fold_clean_messages; simpl; trivial.

  - left.
    cases (RealWorld.msg_honestly_signed honestk cs msg); eauto.
    cases (RealWorld.msg_to_this_user cs (Some uid) msg); eauto.
    simpl.
    cases (msg_nonce_ok cs froms msg); try discriminate; eauto.
Qed.

Lemma key_perms_from_known_ciphers_pull_merge :
  forall cs mycs ks newk,
    key_perms_from_known_ciphers cs mycs (ks $k++ newk)
    = key_perms_from_known_ciphers cs mycs ks $k++ newk.
Proof.
  unfold key_perms_from_known_ciphers.
  induction mycs; intros; eauto.
  simpl.
  cases (cs $? a); eauto.
  destruct c; eauto.
  - rewrite merge_perms_assoc, merge_perms_sym with (ks1 := newk), <- merge_perms_assoc.
    specialize (IHmycs (ks $k++ RealWorld.findKeysMessage msg) newk); eauto.
  - rewrite merge_perms_assoc, merge_perms_sym with (ks1 := newk), <- merge_perms_assoc.
    specialize (IHmycs (ks $k++ RealWorld.findKeysMessage msg) newk); eauto.
Qed.

Lemma key_perms_from_message_queue_pull_merge :
  forall cs msgs ks honestk uid froms newk,
    key_perms_from_message_queue' cs honestk msgs uid froms (ks $k++ newk)
    = key_perms_from_message_queue' cs honestk msgs uid froms ks $k++ newk.
Proof.
  unfold key_perms_from_message_queue'.
  induction msgs; intros; eauto.
  simpl; destruct a.
  cases (not_replayed cs honestk uid froms c); eauto.

  rewrite merge_perms_assoc, merge_perms_sym with (ks1 := newk), <- merge_perms_assoc; trivial.
Qed.

Lemma key_perms_from_known_ciphers_idempotent_add_known_cipher :
  forall cs mycs ks c_id c newk,
    cs $? c_id = Some c
    -> List.In c_id mycs
    -> newk = match c with
             | (RealWorld.SigCipher _ _ _ m) => RealWorld.findKeysMessage m
             | (RealWorld.SigEncCipher _ _ _ _ m) => RealWorld.findKeysMessage m
             end
    -> key_perms_from_known_ciphers cs mycs ks
      = key_perms_from_known_ciphers cs mycs (ks $k++ newk).
Proof.
  induction mycs; intros; eauto.
  invert H0.

  invert H0.
  - simpl; context_map_rewrites.
    destruct c; eauto.
    symmetry; rewrite merge_perms_assoc, merge_perms_refl; trivial.
    symmetry; rewrite merge_perms_assoc, merge_perms_refl; trivial.
    
  - eapply IHmycs with (ks := ks) in H2; eauto.
    simpl.
    cases (cs $? a); eauto.
    destruct c, c0; eauto.

    all :
      symmetry; rewrite key_perms_from_known_ciphers_pull_merge;
      symmetry; rewrite key_perms_from_known_ciphers_pull_merge, <- H2; trivial.
Qed.

Lemma key_perms_from_message_queue_idempotent_add_known_message :
  forall t (msg : RealWorld.crypto t) msgs cs honestk ks uid froms newk,
    List.In (existT _ _ msg) msgs
    -> newk = (if not_replayed cs honestk uid froms msg
              then RealWorld.findKeysCrypto cs msg
              else $0)
    -> key_perms_from_message_queue' cs honestk msgs uid froms ks
      = key_perms_from_message_queue' cs honestk msgs uid froms (ks $k++ newk).
Proof.
  induction msgs; intros; eauto.
  invert H.

  invert H; simpl.
  - cases ( not_replayed cs honestk uid froms msg ); eauto.
    symmetry; rewrite merge_perms_assoc, merge_perms_refl; trivial.
    
  - eapply IHmsgs with (ks := ks) (cs := cs) (honestk := honestk) in H1; eauto.
    destruct a; simpl in *.
    cases ( not_replayed cs honestk uid froms c ); eauto.
    cases ( not_replayed cs honestk uid froms msg ); eauto.

    rewrite key_perms_from_message_queue_pull_merge.
    symmetry; rewrite key_perms_from_message_queue_pull_merge.
    rewrite <- H1; trivial.
Qed.

Inductive user_perms_channel_match {A} (uid : user_id) (usr__rw : RealWorld.user_data A) (usr__iw : IdealWorld.user A)
          (honestk : key_perms) (cs : RealWorld.ciphers) (c_id : RealWorld.cipher_id) (ch_id : channel_id) : Prop :=

| SigChannel : forall mks cks ks b__read b__write k__sign u_id msg_seq t (m__rw : RealWorld.message.message t),
    RealWorld.honest_key honestk k__sign
    -> cs $? c_id = Some (RealWorld.SigCipher k__sign u_id msg_seq m__rw)
    -> cks = key_perms_from_known_ciphers cs usr__rw.(RealWorld.c_heap) $0
    -> mks = key_perms_from_message_queue cs honestk usr__rw.(RealWorld.msg_heap) uid usr__rw.(RealWorld.from_nons) $0
    -> ks = usr__rw.(RealWorld.key_heap) $k++ cks $k++ mks
    -> resolve_perm usr__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write)
    (* -> ks $? k__sign = None *)
    -> ks $? k__sign = Some b__write
    -> b__read = true
    -> user_perms_channel_match uid usr__rw usr__iw honestk cs c_id ch_id
| SigEncChannel : forall mks cks ks b__read b__write k__sign k__enc u_id msg_seq t (m__rw : RealWorld.message.message t),
    RealWorld.honest_key honestk k__sign
    -> cs $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc u_id msg_seq m__rw)
    -> cks = key_perms_from_known_ciphers cs usr__rw.(RealWorld.c_heap) $0
    -> mks = key_perms_from_message_queue cs honestk usr__rw.(RealWorld.msg_heap) uid usr__rw.(RealWorld.from_nons) $0
    -> ks = usr__rw.(RealWorld.key_heap) $k++ cks $k++ mks
    -> resolve_perm usr__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write)
    (* -> ( ks $? k__sign = None \/ ks $? k__enc = None ) *)
    -> ks $? k__sign = Some b__write
    -> ks $? k__enc  = Some b__read
    -> user_perms_channel_match uid usr__rw usr__iw honestk cs c_id ch_id
.

Lemma ch_keys_from_cipher :
  forall A (usr usr' : RealWorld.user_data A) usr__iw honestk uid cs c_id c_id' c ch_id newk,
    cs $? c_id' = Some c
    (* -> c_id <> c_id' *)
    -> List.In c_id' usr.(RealWorld.c_heap)
    -> newk = match c with
             | (RealWorld.SigCipher _ _ _ m) => RealWorld.findKeysMessage m
             | (RealWorld.SigEncCipher _ _ _ _ m) => RealWorld.findKeysMessage m
             end
    -> usr' = RealWorld.addUserKeys newk usr
    -> user_perms_channel_match uid usr usr__iw honestk cs c_id ch_id
    -> user_perms_channel_match uid usr' usr__iw honestk cs c_id ch_id.
Proof.
  intros.
  invert H3; [ econstructor 1 | econstructor 2]; simpl; eauto.

  all : 
    rewrite merge_perms_assoc with (ks3 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0);
    rewrite merge_perms_sym with (ks2 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0);
    rewrite <- key_perms_from_known_ciphers_pull_merge;
    erewrite <- key_perms_from_known_ciphers_idempotent_add_known_cipher with (c_id := c_id'); eauto.
Qed.

Lemma ch_keys_from_cipher_inv :
  forall A (usr usr' : RealWorld.user_data A) usr__iw honestk cs uid c_id c_id' c ch_id newk,
    cs $? c_id' = Some c
    (* -> c_id <> c_id' *)
    -> List.In c_id' usr.(RealWorld.c_heap)
    -> newk = match c with
             | (RealWorld.SigCipher _ _ _ m) => RealWorld.findKeysMessage m
             | (RealWorld.SigEncCipher _ _ _ _ m) => RealWorld.findKeysMessage m
             end
    -> usr' = RealWorld.addUserKeys newk usr
    -> user_perms_channel_match uid usr' usr__iw honestk cs c_id ch_id
    -> user_perms_channel_match uid usr usr__iw honestk cs c_id ch_id.
Proof.
  intros.
  invert H3; [ econstructor 1 | econstructor 2]; simpl in *; eauto; simpl in *.

  all : 
    rewrite merge_perms_assoc with (ks3 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0) in H10;
    rewrite merge_perms_sym with (ks2 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0) in H10;
    rewrite <- key_perms_from_known_ciphers_pull_merge in H10;
    erewrite <- key_perms_from_known_ciphers_idempotent_add_known_cipher with (c_id := c_id') in H10; eauto.

  rewrite merge_perms_assoc with (ks3 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0) in H11;
    rewrite merge_perms_sym with (ks2 := key_perms_from_known_ciphers cs (RealWorld.c_heap usr) $0) in H11;
    rewrite <- key_perms_from_known_ciphers_pull_merge in H11;
    erewrite <- key_perms_from_known_ciphers_idempotent_add_known_cipher with (c_id := c_id') in H11; eauto.
Qed.

(* Lemma ch_keys_from_msg : *)
(*   forall A (usr usr' : RealWorld.user_data A) t (msg : RealWorld.crypto t) usr__iw cs honestk newk uid c_id ch_id, *)
(*     List.In (existT _ _ msg) usr.(RealWorld.msg_heap) *)
(*     -> newk = (if RealWorld.msg_honestly_signed honestk cs msg *)
(*               then RealWorld.findKeysCrypto cs msg *)
(*               else $0) *)
(*     -> usr' = {| RealWorld.key_heap  := usr.(RealWorld.key_heap) *)
(*                 ; RealWorld.protocol  := usr.(RealWorld.protocol) *)
(*                 ; RealWorld.msg_heap  := (existT _ _ msg) :: usr.(RealWorld.msg_heap) *)
(*                 ; RealWorld.c_heap    := usr.(RealWorld.c_heap) *)
(*                 ; RealWorld.from_nons := usr.(RealWorld.from_nons) *)
(*                 ; RealWorld.sent_nons := usr.(RealWorld.sent_nons) *)
(*                 ; RealWorld.cur_nonce := usr.(RealWorld.cur_nonce) *)
(*              |} *)
(*     -> user_perms_channel_match uid usr usr__iw honestk cs c_id ch_id *)
(*     -> user_perms_channel_match uid usr' usr__iw honestk cs c_id ch_id. *)
(* Proof. *)
(*   intros. *)
(*   invert H2; [ econstructor 1 | econstructor 2]; simpl; eauto; *)
(*     cases (not_replayed cs honestk uid usr.(RealWorld.from_nons) msg); eauto. *)

(*   all :  *)
(*     erewrite <- key_perms_from_message_queue_idempotent_add_known_message; eauto; rewrite Heq; eauto. *)
(* Qed. *)

(* Lemma ch_keys_from_msg_inv : *)
(*   forall A (usr usr' : RealWorld.user_data A) t (msg : RealWorld.crypto t) usr__iw cs honestk newk uid c_id ch_id, *)
(*     List.In (existT _ _ msg) usr.(RealWorld.msg_heap) *)
(*     -> newk = (if RealWorld.msg_honestly_signed honestk cs msg *)
(*               then RealWorld.findKeysCrypto cs msg *)
(*               else $0) *)
(*     -> usr' = {| RealWorld.key_heap  := usr.(RealWorld.key_heap) *)
(*                 ; RealWorld.protocol  := usr.(RealWorld.protocol) *)
(*                 ; RealWorld.msg_heap  := (existT _ _ msg) :: usr.(RealWorld.msg_heap) *)
(*                 ; RealWorld.c_heap    := usr.(RealWorld.c_heap) *)
(*                 ; RealWorld.from_nons := usr.(RealWorld.from_nons) *)
(*                 ; RealWorld.sent_nons := usr.(RealWorld.sent_nons) *)
(*                 ; RealWorld.cur_nonce := usr.(RealWorld.cur_nonce) *)
(*              |} *)
(*     -> user_perms_channel_match uid usr' usr__iw honestk cs c_id ch_id *)
(*     -> user_perms_channel_match uid usr usr__iw honestk cs c_id ch_id. *)
(* Proof. *)
(*   intros. *)
(*   invert H2; [ econstructor 1 | econstructor 2]; simpl; eauto; simpl in *; *)
(*     cases (not_replayed cs honestk uid usr.(RealWorld.from_nons) msg); eauto. *)

(*   erewrite <- key_perms_from_message_queue_idempotent_add_known_message in H9; eauto; rewrite Heq; trivial. *)
(*   erewrite <- key_perms_from_message_queue_idempotent_add_known_message in H9; eauto; rewrite Heq; trivial. *)
(*   erewrite <- key_perms_from_message_queue_idempotent_add_known_message in H10; eauto; rewrite Heq; trivial. *)
(* Qed. *)

Inductive  message_eq : forall {A B t},
    RealWorld.crypto t -> RealWorld.universe A B ->
    IdealWorld.message.message t -> IdealWorld.universe A -> IdealWorld.channel_id -> Prop :=
| CryptoSigCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign
                    (m__rw : RealWorld.message.message t) honestk u_id msg_seq,
    U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigCipher k__sign u_id msg_seq m__rw)
    -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys)
    -> honestk = RealWorld.findUserKeys (U__rw.(RealWorld.users))
    -> (forall u data__rw data__iw,
	  U__rw.(RealWorld.users) $? u = Some data__rw
          -> U__iw.(IdealWorld.users) $? u = Some data__iw
          -> RealWorld.honest_key honestk k__sign
          -> user_perms_channel_match u data__rw data__iw honestk U__rw.(RealWorld.all_ciphers) c_id ch_id)
    (* -> (forall u data__rw data__iw b__read b__write, *)
    (*       U__rw.(RealWorld.users) $? u = Some data__rw *)
    (*       -> U__iw.(IdealWorld.users) $? u = Some data__iw *)
    (*       -> RealWorld.honest_key honestk k__sign *)
    (*       -> resolve_perm data__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write) *)
    (*       -> data__rw.(RealWorld.key_heap) $? k__sign = None *)
    (*       \/ (data__rw.(RealWorld.key_heap) $? k__sign = Some b__write /\ b__read = true) *)
    (*   ) *)
    -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id

| CryptoSigEncCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign k__enc
                       (m__rw : RealWorld.message.message t) honestk u_id msg_seq,
    U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc u_id msg_seq m__rw)
    -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys)
    -> honestk = RealWorld.findUserKeys U__rw.(RealWorld.users)
    -> (forall u data__rw data__iw,
	  U__rw.(RealWorld.users) $? u = Some data__rw
          -> U__iw.(IdealWorld.users) $? u = Some data__iw
          -> RealWorld.honest_key honestk k__sign
          -> RealWorld.honest_key honestk k__enc
          -> user_perms_channel_match u data__rw data__iw honestk U__rw.(RealWorld.all_ciphers) c_id ch_id
          (* -> resolve_perm data__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__read b__write) *)
          (* -> ( data__rw.(RealWorld.key_heap) $? k__sign = None \/ data__rw.(RealWorld.key_heap) $? k__enc = None ) *)
          (* \/ ( data__rw.(RealWorld.key_heap) $? k__sign = Some b__write *)
          (*   /\ data__rw.(RealWorld.key_heap) $? k__enc  = Some b__read) *)
      )
    -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id.


(* Inductive  message_eq : forall {A B t}, *)
(*     RealWorld.crypto t -> RealWorld.universe A B -> *)
(*     IdealWorld.message.message t -> IdealWorld.universe A -> IdealWorld.channel_id -> Prop := *)
(* | ContentCase : *)
(*     forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__rw : RealWorld.message.message t) m__iw ch_id user_data, *)
(*       content_eq m__rw m__iw U__rw.(RealWorld.all_keys) *)
(*     -> (forall u, U__iw.(IdealWorld.users) $? u  = Some user_data *)
(*             -> resolve_perm user_data.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission true true)) *)
(*     -> message_eq (RealWorld.Content m__rw) U__rw m__iw U__iw ch_id *)
(* | CryptoSigCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign *)
(*                     (m__rw : RealWorld.message.message t) b__iw honestk u_id msg_seq, *)
(*     U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigCipher k__sign u_id msg_seq m__rw) *)
(*     -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys) *)
(*     -> honestk = RealWorld.findUserKeys (U__rw.(RealWorld.users)) *)
(*     -> (forall u data__rw data__iw, *)
(* 	  U__rw.(RealWorld.users) $? u = Some data__rw *)
(*           -> U__iw.(IdealWorld.users) $? u = Some data__iw *)
(*           ->  RealWorld.honest_key honestk k__sign *)
(*           (*sign key is honest.  honest key : find user keys on all users*) *)
(*           -> (data__rw.(RealWorld.key_heap) $? k__sign = Some true *)
(*              -> resolve_perm data__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission true b__iw))) *)
(*     -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id *)
(* | CryptoSigEncCase : forall {A B t} (U__rw : RealWorld.universe A B) U__iw (m__iw : IdealWorld.message.message t) c_id ch_id k__sign k__enc *)
(*                        (m__rw : RealWorld.message.message t) honestk u_id msg_seq, *)
(*     U__rw.(RealWorld.all_ciphers) $? c_id = Some (RealWorld.SigEncCipher k__sign k__enc u_id msg_seq m__rw) *)
(*     -> content_eq m__rw m__iw U__rw.(RealWorld.all_keys) *)
(*     -> honestk = RealWorld.findUserKeys (U__rw.(RealWorld.users)) *)
(*     -> (forall u data__rw data__iw b__rwenc, *)
(* 	  U__rw.(RealWorld.users) $? u = Some data__rw *)
(*           -> U__iw.(IdealWorld.users) $? u = Some data__iw *)
(*           -> RealWorld.honest_key honestk k__sign *)
(*           -> RealWorld.honest_key honestk k__enc *)
(*           -> ((data__rw.(RealWorld.key_heap) $? k__sign = Some true *)
(*               /\ data__rw.(RealWorld.key_heap) $? k__enc = Some b__rwenc) *)
(*              -> resolve_perm data__iw.(IdealWorld.perms) ch_id = Some (IdealWorld.construct_permission b__rwenc true))) *)
(*     -> message_eq (RealWorld.SignedCiphertext c_id) U__rw m__iw U__iw ch_id. *)
