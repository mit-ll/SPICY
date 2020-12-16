(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2020 Massachusetts Institute of Technology.
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

From SPICY Require Import
     MyPrelude
     Common
     Tactics
     AdversaryUniverse
     ChMaps
     Messages
     MessageEq
     Maps
     Keys

     Theory.MessagesTheory
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

Lemma clean_messages_cons_split :
  forall cs honestk uid froms msgs cmsgs t (msg : RealWorld.crypto t),
    cmsgs = clean_messages honestk cs (Some uid) froms ((existT _ _ msg) :: msgs)
    -> (cmsgs = clean_messages honestk cs (Some uid) froms msgs /\ not_replayed cs honestk uid froms msg = false)
      \/ exists n cid c, 
        cmsgs = (existT _ _ msg) :: clean_messages honestk cs (Some uid) (n :: froms) msgs
        /\ not_replayed cs honestk uid froms msg = true
        /\ msg = RealWorld.SignedCiphertext cid
        /\ cs $? cid = Some c
        /\ n = RealWorld.cipher_nonce c.
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
    (do 3 eexists); repeat simple apply conj; eauto.
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
    key_perms_from_message_queue cs honestk msgs uid froms (ks $k++ newk)
    = key_perms_from_message_queue cs honestk msgs uid froms ks $k++ newk.
Proof.
  unfold key_perms_from_message_queue.
  induction msgs; intros; eauto. simpl.
  simpl; destruct a.
  pose proof (clean_messages_cons_split cs honestk uid froms msgs _ _ c eq_refl); intros.
  split_ors; split_ex.
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
