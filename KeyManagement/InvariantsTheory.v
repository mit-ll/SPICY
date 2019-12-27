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
From Coq Require Import
     List
     Morphisms
     Eqdep
.

Require Import
        MyPrelude
        Maps
        Messages
        Common
        Keys
        Tactics
        AdversaryUniverse
        Simulation
        RealWorld
        Automation
        CipherTheory.

Set Implicit Arguments.


Section RealWorldLemmas.

  Hint Unfold message_no_adv_private.

  Lemma adv_no_honest_keys_empty :
    forall honestk,
    adv_no_honest_keys honestk $0.
    unfold adv_no_honest_keys; intros; simpl.
    cases (honestk $? k_id); subst; intuition idtac.
    cases b; subst; intuition idtac.
    right; right; intuition idtac.
    invert H.
  Qed.

  Lemma msg_honestly_signed_addnl_cipher :
    forall {t} (msg : crypto t) honestk cs c_id c,
      ~ In c_id cs
      -> msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed honestk (cs $+ (c_id,c)) msg = true.
  Proof.
    destruct msg; intros; eauto;
      unfold msg_honestly_signed, msg_signing_key in *;
      repeat
        match goal with
        | [ |- context [ ?cs $+ (?cid1,_) $? ?cid2 ] ] => destruct (cid1 ==n cid2); subst; clean_map_lookups
        | [ H1 : ?cs $? ?cid = _ |- _ ] =>
          match goal with
          | [ H2 : ?P |- _] =>
            match P with
            | context [ match cs $? cid with _ => _ end ] => rewrite H1 in H2
            end
          end
        end; clean_map_lookups; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_addnl_cipher.

  Lemma msg_honestly_signed_addnl_honest_key :
    forall {t} (msg : crypto t) honestk cs k_id,
      ~ In k_id honestk
      -> msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed (honestk $+ (k_id,true)) cs msg = true.
  Proof.
    destruct msg; intros; eauto;
      unfold msg_honestly_signed, msg_signing_key in *;
      repeat
        match goal with
        | [ |- context [ ?cs $? ?cid ] ] => cases (cs $? cid)
        | [ |- context [ match ?c with _ => _ end ]] => is_var c; destruct c
        | [ |- context [ honest_keyb _ _ = _ ] ] => unfold honest_keyb in *
        | [ H : ?honk $+ (?kid1,_) $? ?kid2 = _ |- _ ] => destruct (kid1 ==n kid2); subst; clean_map_lookups
        | [ H : ?honk $? ?kid = _, M : match ?honk $? ?kid with _ => _ end = _ |- _ ] => rewrite H in M
        end; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_addnl_honest_key.

  Lemma msgCiphersSignedOk_addnl_cipher' :
    forall cs (msgs : queued_messages) honestk c_id c,
      ~ In c_id cs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk (cs $+ (c_id,c)) m = true end) msgs.
  Proof.
    induction msgs; intros; eauto.
    invert H0;
      econstructor; eauto.
    destruct a; intuition eauto.
  Qed.

  Lemma msgCiphersSignedOk_addnl_cipher :
    forall {t} (msg : crypto t) honestk cs c_id c,
      ~ In c_id cs
      -> msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk honestk (cs $+ (c_id,c)) msg.
  Proof. unfold msgCiphersSignedOk; intros; eapply msgCiphersSignedOk_addnl_cipher'; eauto. Qed.

  Hint Resolve
       msgCiphersSignedOk_addnl_cipher.
  
  Lemma msgCiphersSignedOk_new_honest_key' :
    forall (msgCphrs : queued_messages) honestk cs k,
      honestk $? keyId k = None
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgCphrs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed (honestk $+ (keyId k,true)) cs m = true end) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H0; eauto; clean_map_lookups.
    destruct a; intuition eauto.
  Qed.

  Lemma msgCiphersSignedOk_new_honest_key :
    forall {t} (msg : crypto t) honestk cs k,
      msgCiphersSignedOk honestk cs msg
      -> honestk $? keyId k = None
      -> msgCiphersSignedOk (honestk $+ (keyId k, true)) cs msg.
  Proof.
    intros; eapply msgCiphersSignedOk_new_honest_key'; eauto.
  Qed.

  Hint Resolve msgCiphersSignedOk_new_honest_key.

  Lemma msg_signing_key_in_ciphers :
    forall {t} (c : crypto t) cs k,
      msg_signing_key cs c = Some k
      -> exists cid cphr,
        msg_cipher_id c = Some cid
        /\ cs  $? cid = Some cphr
        /\ cipher_signing_key cphr = k.
  Proof.
    intros.
    unfold msg_signing_key in *; destruct c; try discriminate;
      unfold msg_cipher_id, cipher_signing_key;
      cases (cs $? c_id); try discriminate; destruct c; try discriminate;
        invert H; eauto.
  Qed.

  Lemma msgCiphersSignedOk_cleaned_honestk' :
    forall (msgCphrs : queued_messages) honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgCphrs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk' (clean_ciphers honestk cs) m = true end) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H0; eauto; clean_map_lookups.
    destruct a; intuition eauto;
      unfold msg_honestly_signed in *;
      cases (msg_signing_key cs c); try discriminate.

    assert (msg_signing_key (clean_ciphers honestk cs) c = Some k).
    unfold msg_signing_key; unfold msg_signing_key in Heq;
      destruct c; try discriminate.
    cases (cs $? c_id); try discriminate; destruct c; try discriminate; invert Heq;
      erewrite clean_ciphers_keeps_honest_cipher; eauto; simpl; eauto.

    rewrite H0; unfold honest_keyb in *.
    cases (honestk $? k); try discriminate; destruct b; try discriminate.
    assert (honestk' $? k = Some true) as RW by eauto; rewrite RW; eauto.
  Qed.

  Lemma msgCiphersSigned_cleaned_honestk :
    forall {t} (msg : crypto t) honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk honestk' (clean_ciphers honestk cs) msg.
  Proof. unfold msgCiphersSignedOk; intros; eapply msgCiphersSignedOk_cleaned_honestk'; auto. Qed.

  Hint Resolve msgCiphersSigned_cleaned_honestk.

  Hint Constructors encrypted_cipher_ok.
  
  Lemma encrypted_cipher_ok_addnl_cipher :
    forall honestk cs ks c_id c1 c2,
      encrypted_cipher_ok honestk cs ks c1
      -> ~ In c_id cs
      -> encrypted_cipher_ok honestk (cs $+ (c_id,c2)) ks c1.
  Proof.
    inversion 1; intros; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_cipher :
    forall honestk cs ks c_id c,
      Forall_natmap (encrypted_cipher_ok honestk cs ks) cs
      -> ~ In c_id cs
      -> Forall_natmap (encrypted_cipher_ok honestk (cs $+ (c_id, c)) ks) cs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in *.
    intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_cipher.
  Qed.

  Lemma encrypted_cipher_ok_addnl_key :
    forall honestk cs ks k c,
      encrypted_cipher_ok honestk cs ks c
      -> ~ In (keyId k) ks
      -> encrypted_cipher_ok honestk cs (ks $+ (keyId k, k)) c.
  Proof.
    inversion 1; intros; subst; invert H;
      try solve [
            try contradiction; econstructor; try assumption;
            try
              match goal with
              | [ |- _ $+ (?kid1,_) $? ?kid2 = _] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              end; eauto
          ].

    - clean_map_lookups.
      eapply SigEncCipherAdvSignedOk; eauto.
      cases (keyId k ==n k__s); subst; clean_map_lookups; eauto.
      cases (keyId k ==n k__e); subst; clean_map_lookups; eauto.
      intros.
      cases (keyId k ==n k0); subst; clean_map_lookups; eauto.
      eexists; intuition eauto; subst.
      specialize (H14 _ _ H); split_ex; split_ands; auto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_key :
    forall honestk cs ks k_id k,
      encrypted_ciphers_ok honestk cs ks
      -> ~ In (keyId k) ks
      -> k_id = keyId k
      -> encrypted_ciphers_ok honestk cs (ks $+ (k_id, k)).
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *.
    intros; subst.
    specialize (H _ _ H2); eauto using encrypted_cipher_ok_addnl_key.
  Qed.

  Lemma keys_mine_addnl_honest_key :
    forall honestk k_id ks,
      keys_mine honestk ks
      -> keys_mine (honestk $+ (k_id,true)) ks.
  Proof.
    intros; unfold keys_mine; intros.
    destruct (k_id ==n k_id0); subst; clean_map_lookups;
      destruct kp; eauto.
  Qed.

  Hint Resolve keys_mine_addnl_honest_key.

  Lemma encrypted_cipher_ok_addnl_honest_key :
    forall honestk cs ks k c,
      encrypted_cipher_ok honestk cs ks c
      -> ~ In (keyId k) honestk
      -> ~ In (keyId k) ks
      -> encrypted_cipher_ok (honestk $+ (keyId k, true)) cs (ks $+ (keyId k, k)) c.
  Proof.
    inversion 1; intros; subst; invert H; clean_map_lookups;
      try solve [
            econstructor; try assumption;
            repeat
              match goal with
              | [ H : (forall k kp, findKeysMessage _ $? k = Some kp -> _) |- (forall k kp, findKeysMessage _ $? k = Some kp -> _ ) ] => intros
              | [ H : (forall k, findKeysMessage _ $? k = _ -> _) |- (forall k, findKeysMessage  _ $? k = _ -> _ ) ] => intros
              | [ H : (forall k, findKeysMessage ?msg $? k = ?opt -> _), FK : findKeysMessage ?msg $? _ = ?opt |- _ ] =>
                specialize (H _ FK); split_ex; split_ands
              | [ H : ?m $? _ = Some _, H1 : (forall k_id kp, ?m $? k_id = Some kp -> _) |- _ /\ _ ] => specialize (H1 _ _ H)
              | [ |- context [_ $+ (?kid1,_) $? ?kid2 = _] ] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              | [ |- context [_ $+ (?kid1,_) $? ?kid2 <> _] ] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              end; intuition eauto
          ].

    eapply SigEncCipherAdvSignedOk; eauto.
    - destruct (keyId k ==n k__s); subst; clean_map_lookups; eauto.
    - destruct (keyId k ==n k__s); subst; clean_map_lookups; eauto.
    - destruct (keyId k ==n k__e); subst; clean_map_lookups; eauto.
    - intros.
      specialize (H15 _ _ H); split_ex; split_ands.
      eexists; destruct (keyId k ==n k0); subst; clean_map_lookups; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_honest_key :
    forall honestk cs ks k_id k,
      encrypted_ciphers_ok honestk cs ks
      -> ~ In (keyId k) ks
      -> ~ In (keyId k) honestk
      -> k_id = keyId k
      -> encrypted_ciphers_ok (honestk $+ (k_id,true)) cs (ks $+ (k_id, k)).
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *.
    intros; subst; eauto using encrypted_cipher_ok_addnl_honest_key.
  Qed.

  Hint Resolve
       encrypted_ciphers_ok_addnl_cipher
       encrypted_ciphers_ok_addnl_key.

  Lemma adv_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs ks
        -> adv_cipher_queue_ok cs usrs mycs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 1; inversion 7; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; auto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H23 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros.
        specialize (H4 _ _ H5).
        specialize (ADV k); unfold not; split_ors; split_ands; contra_map_lookup; try contradiction;
          unfold keys_and_permissions_good, permission_heap_good in *; split_ands;
            try specialize (H11 _ _ H4); try specialize (H12 _ _ H4);  split_ex; eexists;
              intuition (intros; eauto); contra_map_lookup;
                contradiction.
    - econstructor; eauto.
      specialize (H20 k_id); eauto.
      eapply SigCipherNotHonestOk; unfold not; intros; split_ors; split_ands; contra_map_lookup; try contradiction; eauto.
  Qed.

  Lemma universe_ok_adv_step :
    forall {A B} (U__r : universe A B) lbl usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
      universe_ok U__r
      -> adv_universe_ok U__r
      -> step_user lbl None
                  (users U__r, adversary U__r, all_ciphers U__r, all_keys U__r,
                   key_heap (adversary U__r), msg_heap (adversary U__r),
                   c_heap (adversary U__r), from_nons (adversary U__r),
                   sent_nons (adversary U__r), cur_nonce (adversary U__r),
                   protocol (adversary U__r)) (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> universe_ok
          (buildUniverseAdv
             usrs cs gks
             {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                ; from_nons := froms; sent_nons := sents; cur_nonce := cur_n |}).
  Proof.
    unfold universe_ok, adv_universe_ok; destruct U__r; simpl; intros; split_ands; eauto using adv_step_encrypted_ciphers_ok.
  Qed.

End RealWorldLemmas.