(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Program.Equality.

From SPICY Require Import
     MyPrelude
     Tactics
     AdversaryUniverse
     ChMaps
     Messages
     MessageEq
     Maps
     Keys
     Simulation

     Theory.CipherTheory
     Theory.KeysTheory
     Theory.MessagesTheory
     Theory.NonceTracking
     Theory.UsersTheory
.

From SPICY Require
     RealWorld
     IdealWorld.

Import RealWorld.RealWorldNotations
       IdealWorld.IdealNotations.

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
     in  fold_left (fun kys '(existT _ _ m) => kys $k++ RealWorld.findKeysCrypto cs m) cmsgs ks)
    = key_perms_from_message_queue cs honestk msgs uid froms ks.
  unfold key_perms_from_message_queue; trivial.
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
    key_perms_from_message_queue cs honestk msgs uid froms (ks $k++ newk)
    = key_perms_from_message_queue cs honestk msgs uid froms ks $k++ newk.
Proof.
  unfold key_perms_from_message_queue.
  induction msgs; intros; eauto. simpl.
  simpl; destruct a.
  pose proof (clean_messages_cons_split cs honestk uid froms msgs c eq_refl).
  split_ors.
  - rewrite !H; eauto.
  - rewrite !H; simpl.
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

Lemma content_eq_strip_keys :
  forall t (m__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t) honestk gks,
    content_eq m__rw m__iw (clean_keys honestk gks)
    -> content_eq m__rw m__iw gks.
Proof.
  induction m__rw; intros; eauto.
  - dependent destruction m__iw.
    unfold content_eq in *; simpl in *.
    destruct acc; destruct acc0.

    cases (clean_keys honestk gks $? k); try contradiction.
    apply clean_keys_inv in Heq; split_ands; context_map_rewrites; eauto.
    
  - dependent destruction m__iw.
    invert H.
    econstructor; eauto.
Qed.

Lemma key_perms_from_known_ciphers_clean_ciphers :
  forall cs mycs ks honestk,
    user_cipher_queue_ok cs honestk mycs
    -> key_perms_from_known_ciphers (clean_ciphers honestk cs) mycs ks
      = key_perms_from_known_ciphers cs mycs ks.
Proof.
  unfold key_perms_from_known_ciphers.
  induction mycs; intros; eauto.
  invert H; split_ex; simpl.
  erewrite clean_ciphers_keeps_honest_cipher; eauto; context_map_rewrites.
  destruct x;
    eapply IHmycs with (ks := ks $k++ RealWorld.findKeysMessage msg) in H3; eauto.
Qed.

Hint Resolve honest_cipher_filter_fn_true_honest_signing_key : core.

Lemma findKeysCrypto_same_after_cipher_cleaning :
  forall t (msg : RealWorld.crypto t) cs honestk,
    RealWorld.msg_honestly_signed honestk cs msg = true
    -> RealWorld.findKeysCrypto (clean_ciphers honestk cs) msg = RealWorld.findKeysCrypto cs msg.
Proof.
  destruct msg; intros; eauto.
  unfold RealWorld.findKeysCrypto.
  unfold RealWorld.msg_honestly_signed in H.
  cases (RealWorld.msg_signing_key cs (@RealWorld.SignedCiphertext t0 c_id)); try discriminate.
  unfold RealWorld.msg_signing_key in Heq; cases (cs $? c_id); try discriminate.
  invert Heq.
  erewrite clean_ciphers_keeps_honest_cipher; eauto.
  eapply honest_cipher_filter_fn_true_honest_signing_key; eauto.
  unfold RealWorld.honest_keyb in H; eauto.
  cases( honestk $? RealWorld.cipher_signing_key c )
  ; try discriminate
  ; destruct b
  ; try discriminate
  ; eauto.
Qed.

Lemma key_perms_from_message_queue_clean_ciphers :
  forall cs msgs ks honestk uid froms A (usrs : RealWorld.honest_users A) kid kp,
    honestk = RealWorld.findUserKeys usrs
    -> RealWorld.honest_key honestk kid
    -> key_perms_from_message_queue
        (clean_ciphers honestk cs)
        (RealWorld.findUserKeys (clean_users honestk cs usrs))
        (clean_messages honestk cs (Some uid) froms msgs)
        uid froms ks $? kid = Some kp
    -> key_perms_from_message_queue cs honestk msgs uid froms ks $? kid = Some kp.
Proof.
  unfold key_perms_from_message_queue.
  induction msgs; intros; eauto.
  destruct a; simpl in *.
  pose proof (clean_messages_cons_split cs honestk uid froms msgs c eq_refl);
    split_ors.

  - rewrite H2 in *.
    apply IHmsgs in H1; eauto.
  - erewrite <- clean_messages_idempotent in H1; eauto.
    rewrite H2 in *; simpl in *.
    eapply IHmsgs; eauto.
    erewrite <- clean_messages_idempotent; eauto.
    rewrite findKeysCrypto_same_after_cipher_cleaning in H1; eauto.
    unfold not_replayed in H3; rewrite !andb_true_iff in H3; split_ex; eauto.

    all: 
      intros KEY HONK; subst;
      pose proof (findUserKeys_clean_users_correct usrs cs KEY) as CORRECT;
      rewrite HONK in CORRECT; eauto.
Qed.

Lemma key_perms_from_message_queue_clean_ciphers' :
  forall cs msgs ks honestk uid froms A (usrs : RealWorld.honest_users A) kid kp,
    honestk = RealWorld.findUserKeys usrs
    -> RealWorld.honest_key honestk kid
    -> key_perms_from_message_queue
        (clean_ciphers honestk cs)
        (RealWorld.findUserKeys (clean_users honestk cs usrs))
        (clean_messages honestk cs (Some uid) froms msgs)
        uid froms ks $? kid = kp
    -> key_perms_from_message_queue cs honestk msgs uid froms ks $? kid = kp.
Proof.
  unfold key_perms_from_message_queue.
  induction msgs; intros; eauto.
  destruct a; simpl in *.
  pose proof (clean_messages_cons_split cs honestk uid froms msgs c eq_refl);
    split_ors.

  - rewrite H2 in *.
    apply IHmsgs in H1; eauto.
  - erewrite <- clean_messages_idempotent in H1; eauto.
    rewrite H2 in *; simpl in *.
    eapply IHmsgs; eauto.
    erewrite <- clean_messages_idempotent; eauto.
    rewrite findKeysCrypto_same_after_cipher_cleaning in H1; eauto.
    unfold not_replayed in H3; rewrite !andb_true_iff in H3; split_ex; eauto.

    all: 
      intros KEY HONK; subst;
      pose proof (findUserKeys_clean_users_correct usrs cs KEY) as CORRECT;
      rewrite HONK in CORRECT; eauto.
Qed.

