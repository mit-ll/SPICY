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
        KeysTheory
        Tactics
        AdversaryUniverse
        Simulation
        RealWorld
        Automation
        CipherTheory
        SafetyAutomation.

Set Implicit Arguments.

Import SafetyAutomation.

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

  Lemma encrypted_ciphers_ok_new_honest_key_adv_univ :
    forall honestk honestk' cs k_id k gks gks',
      ~ In k_id gks
      -> permission_heap_good gks honestk
      -> k_id = keyId k
      -> gks' = gks $+ (k_id, k)
      -> honestk' = honestk $+ (k_id, true)
      -> encrypted_ciphers_ok honestk cs gks
      -> encrypted_ciphers_ok honestk' cs gks'.
  Proof.
    intros; subst; eapply encrypted_ciphers_ok_addnl_honest_key; eauto.
    cases (honestk $? keyId k); clean_map_lookups; eauto.
    specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
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
      specialize (H21 k_id); eauto.
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

Lemma honest_users_only_honest_keys_nochange_keys :
  forall {A} u_id (usrs : honest_users A) (cmd cmd' : user_cmd (Base A))
    ks qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

    honest_users_only_honest_keys usrs
    -> usrs $? u_id = Some {| key_heap := ks;
                             protocol := cmd;
                             msg_heap := qmsgs;
                             c_heap := mycs;
                             from_nons := froms;
                             sent_nons := sents;
                             cur_nonce := cur_n |}
    -> honest_users_only_honest_keys
        (usrs $+ (u_id, {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs';
                           c_heap := mycs';
                           from_nons := froms';
                           sent_nons := sents';
                           cur_nonce := cur_n' |})).
Proof.
  intros.
  unfold honest_users_only_honest_keys in *;
    autorewrite with find_user_keys;
    intros;
    eauto.
  
  destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto 2.
Qed.

Lemma honest_users_only_honest_keys_gen_key :
  forall {A} u_id (usrs : honest_users A) (cmd cmd' : user_cmd (Base A)) k_id
    ks qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

    honest_users_only_honest_keys usrs
    -> usrs $? u_id = Some {| key_heap := ks;
                             protocol := cmd;
                             msg_heap := qmsgs;
                             c_heap := mycs;
                             from_nons := froms;
                             sent_nons := sents;
                             cur_nonce := cur_n |}
    -> honest_users_only_honest_keys
        (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                           protocol := cmd';
                           msg_heap := qmsgs';
                           c_heap := mycs';
                           from_nons := froms';
                           sent_nons := sents';
                           cur_nonce := cur_n' |})).
Proof.
  intros.
  unfold honest_users_only_honest_keys in *; intros.
  assert (add_key_perm k_id true ks = ks $+ (k_id,true))
    as RW1 by (unfold add_key_perm; cases (ks $? k_id); eauto).
  assert (ks $+ (k_id,true) = ks $k++ ($0 $+ (k_id,true))) as RW2 by eauto.
  rewrite RW1, RW2; clear RW1 RW2.
  rewrite findUserKeys_readd_user_addnl_keys; eauto.

  unfold add_key_perm in *.
  destruct (u_id ==n u_id0); subst; simpl in *; clean_map_lookups.

  - specialize (H _ _ H0); simpl in *.
    destruct (ks $? k_id); destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
    + cases (findUserKeys usrs $? k_id0).
      eapply merge_perms_chooses_greatest with (ks2 := $0 $+ (k_id0, true)) in Heq;
        eauto; clean_map_lookups; eauto; solve_greatest.
      
      eapply merge_perms_adds_ks2; eauto.
      clean_map_lookups; eauto.
        
    + eapply merge_perms_adds_ks1; eauto.
      clean_map_lookups; eauto.
    + cases (findUserKeys usrs $? k_id0).
      eapply merge_perms_chooses_greatest with (ks2 := $0 $+ (k_id0, true)) in Heq;
        eauto; clean_map_lookups; eauto; solve_greatest.
      
      eapply merge_perms_adds_ks2; eauto.
      clean_map_lookups; eauto.

    + eapply merge_perms_adds_ks1; eauto.
      clean_map_lookups; eauto.

  - specialize (H _ _ H1 _ _ H2).
    destruct (k_id ==n k_id0); subst.
    eapply merge_perms_chooses_greatest with (ks2 := $0 $+ (k_id0, true)) in H; eauto.
    clean_map_lookups; reflexivity.

    eapply merge_perms_adds_ks1; eauto.
    clean_map_lookups; eauto.
Qed.

  Lemma encrypted_cipher_ok_addnl_pubk :
    forall honestk pubk gks c cs,
      encrypted_cipher_ok honestk cs gks c
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> encrypted_cipher_ok (honestk $k++ pubk) cs gks c.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
      solve_perm_merges; eauto. 
      intros;
        cases (pubk $? k_id);
        repeat
          match goal with
          | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          | [ H : (forall k, ?fkm $? k = Some ?tf -> _), ARG : ?fkm $? _ = Some ?tf |- _ ] =>
            specialize (H _ ARG)
          end; solve_perm_merges; eauto.

    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); solve_perm_merges;
        match goal with
        | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG); split_ands; subst
        end; clean_map_lookups.
    - eapply SigEncCipherAdvSignedOk; eauto.
      + unfold not; intros.
        solve_perm_merges; clean_context; eauto.

      + intros. specialize (H2 _ _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros; subst.
        specialize (H5 (eq_refl true)).
        solve_perm_merges; clean_context; eauto.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto;
        solve_perm_merges; eauto.
      unfold keys_mine in *; intros.
      specialize (H3 _ _ H5).
      solve_perm_merges.
  Qed.

  Lemma encrypted_cipher_ok_addnl_pubk' :
    forall honestk pubk gks c cs,
      encrypted_cipher_ok honestk cs gks c
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true)
      -> encrypted_cipher_ok (honestk $k++ pubk) cs gks c.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
      solve_perm_merges; eauto. 
      intros;
        cases (pubk $? k_id);
        repeat
          match goal with
          | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          | [ H : (forall k, ?fkm $? k = Some ?tf -> _), ARG : ?fkm $? _ = Some ?tf |- _ ] =>
            specialize (H _ ARG)
          end; solve_perm_merges; eauto.

    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); solve_perm_merges;
        match goal with
        | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG); split_ands; subst
        end; clean_map_lookups.
    - eapply SigEncCipherAdvSignedOk; eauto.
      + unfold not; intros.
        solve_perm_merges; clean_context; eauto.

      + intros. specialize (H2 _ _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros; subst.
        specialize (H5 (eq_refl true)).
        solve_perm_merges; clean_context; eauto.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto;
        solve_perm_merges; eauto.
      unfold keys_mine in *; intros.
      specialize (H3 _ _ H5).
      solve_perm_merges.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_pubk :
    forall honestk pubk cs gks,
      encrypted_ciphers_ok honestk cs gks
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> encrypted_ciphers_ok (honestk $k++ pubk) cs gks.
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *; intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_pubk.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_pubk' :
    forall honestk pubk cs gks,
      encrypted_ciphers_ok honestk cs gks
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true)
      -> encrypted_ciphers_ok (honestk $k++ pubk) cs gks.
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *; intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_pubk'.
  Qed.
  Lemma user_cipher_queues_ok_readd_user :
    forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs froms froms' sents sents' cur_n cur_n',
      usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok cs
          (findUserKeys usrs)
          (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok;
      rewrite Forall_natmap_forall; intros.

    unfold user_cipher_queues_ok in H0;
      rewrite Forall_natmap_forall in H0.
    cases (k ==n u_id); subst; clean_map_lookups; simpl; eauto.
    eapply H0 in H; eauto.
  Qed.

  Lemma user_cipher_queue_ok_addnl_global_cipher :
    forall honestk cs c_id c mycs,
      Forall (fun cid => exists c, cs $? cid = Some c /\ cipher_honestly_signed honestk c = true) mycs
      -> ~ In (elt:=cipher) c_id cs
      -> Forall (fun cid => exists c0, cs $+ (c_id,c) $? cid = Some c0 /\ cipher_honestly_signed honestk c0 = true) mycs.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    specialize (H _ H1); invert H.
    eexists; cases (c_id ==n x); subst; split_ands; clean_map_lookups; eauto.
  Qed.

  Hint Resolve user_cipher_queue_ok_addnl_global_cipher.

  Lemma user_cipher_queues_ok_addnl_global_cipher :
    forall {A} (usrs : honest_users A) honestk cs c_id c,
      user_cipher_queues_ok cs honestk usrs
      -> ~ In (elt:=cipher) c_id cs
      -> user_cipher_queues_ok (cs $+ (c_id,c)) honestk usrs.
  Proof.
    unfold user_cipher_queues_ok; intros.
    rewrite Forall_natmap_forall in *; intros; eauto.
    eapply user_cipher_queue_ok_addnl_global_cipher; eauto.
    eapply H; eauto.
  Qed.

  Lemma user_cipher_queue_ok_addnl_pubk :
    forall honestk pubk cs mycs,
      user_cipher_queue_ok cs honestk mycs
      -> user_cipher_queue_ok cs (honestk $k++ pubk) mycs.
  Proof.
    induction 1; intros; econstructor; eauto;
      split_ex; eexists; intuition eauto using cipher_honestly_signed_after_msg_keys.
  Qed.

  Lemma user_cipher_queues_ok_addnl_pubk :
    forall {A} (usrs : honest_users A) honestk pubk cs,
      user_cipher_queues_ok cs honestk usrs
      -> user_cipher_queues_ok cs (honestk $k++ pubk) usrs.
  Proof.
    induction 1; intros; econstructor; eauto using user_cipher_queue_ok_addnl_pubk.
  Qed.

  Lemma user_cipher_queue_ok_addnl_generated_key :
    forall honestk cs mycs k_id,
      user_cipher_queue_ok cs honestk mycs
      -> user_cipher_queue_ok cs (add_key_perm k_id true honestk) mycs.
  Proof.
    induction 1; intros; econstructor; eauto;
      split_ex; eexists; intuition eauto.

    destruct x0; unfold cipher_honestly_signed in *; simpl; 
      rewrite <- honest_key_honest_keyb in *;
      unfold add_key_perm;
      match goal with
      | [ H : honest_key _ ?kid |- _ ] => invert H; econstructor; destruct (k_id ==n kid); subst
      end; context_map_rewrites; clean_map_lookups; simpl; eauto;
        cases (honestk $? k_id); clean_map_lookups; auto.
  Qed.

  Lemma user_cipher_queues_ok_addnl_global_generated_key :
    forall {A} (usrs : honest_users A) ks cs k_id,
      ks = findUserKeys usrs
      -> Forall_natmap (fun u => user_cipher_queue_ok cs ks u.(c_heap)) usrs
      -> Forall_natmap (fun u => user_cipher_queue_ok cs (add_key_perm k_id true ks) u.(c_heap)) usrs.
  Proof.
    intros; rewrite Forall_natmap_forall in *;
      intros; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms sents cur_n,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (add_key_perm k_id true (findUserKeys usrs))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok; rewrite Forall_natmap_forall; intros.
    user_cipher_queue_lkup UCQ.

    split_ex; destruct (k ==n u_id); subst; clean_map_lookups; simpl.
    user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
    clear H2; user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key' :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms sents cur_n,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (findUserKeys usrs $+ (k_id,true))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |})).
  Proof.
    intros.
    pose proof (user_cipher_queues_ok_addnl_generated_key ks k_id _ cmd qmsgs froms sents cur_n H H0).
    unfold add_key_perm in H1 at 1; unfold greatest_permission in H1;
      cases (findUserKeys usrs $? k_id); simpl in *; eapply H1.
  Qed.

  Hint Resolve user_cipher_queues_ok_addnl_generated_key user_cipher_queues_ok_addnl_generated_key'.

  Lemma msgCiphersSignedOk_user_cipher_queue_ok_findCiphers :
    forall {t} (msg : crypto t) honestk cs,
      msgCiphersSignedOk honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeysCrypto cs msg) (findCiphers msg).
  Proof.
    induction msg;
      intros;
      unfold user_cipher_queue_ok in *;
      repeat
        match goal with
        | [ H : msg_honestly_signed _ _ (SignedCiphertext ?cid) = true |- _ ] =>
          unfold msg_honestly_signed, msg_signing_key in H;
            cases (cs $? cid); try discriminate;
              destruct c; try discriminate; simpl in H
        | [ H : msgCiphersSignedOk _ _ _ |- _ ] => invert H; simpl in *; split_ands; split_ex
        | [ H : honest_keyb _ _ = true |- _ ] => apply honest_keyb_true_honestk_has_key in H2
        | [ |- Forall _ _ ] => econstructor
        | [ |- exists _, _ /\ _ ] => eexists; split
        | [ |- cipher_honestly_signed _ _ = _ ] => simpl; unfold honest_keyb; solve_perm_merges
        | [ |- ?cs $? _ = _ ] => eassumption
        end; eauto.
  Qed.

  Hint Resolve
       cipher_honestly_signed_after_msg_keys
       msgCiphersSignedOk_user_cipher_queue_ok_findCiphers.

  Lemma user_cipher_queue_ok_add_user :
    forall {t} (msg : crypto t) cs honestk mycs,
      user_cipher_queue_ok cs honestk mycs
      -> msgCiphersSignedOk honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeysCrypto cs msg) (findCiphers msg ++ mycs).
  Proof.
    induction 1; unfold msgCiphersSignedOk; intros.
    - rewrite app_nil_r; eauto.
    - unfold user_cipher_queue_ok. rewrite Forall_app_sym, <- app_comm_cons.
      econstructor; split_ex; split_ands.
      + intuition eauto.
      + rewrite Forall_app_sym;
          eapply IHForall; auto.
  Qed.

  Hint Resolve
       user_cipher_queue_ok_add_user
       user_cipher_queue_ok_addnl_pubk.

  Lemma user_cipher_queues_ok_add_user :
    forall {A t} (usrs usrs' : honest_users A) (msg : crypto t) honestk u_id ks cmd cmd' qmsgs qmsgs' mycs froms froms' sents sents' cur_n cur_n' cs,
      user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> msgCiphersSignedOk (findUserKeys usrs) cs msg
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ findKeysCrypto cs msg; protocol := cmd'; msg_heap := qmsgs'
                                  ; c_heap := findCiphers msg ++ mycs ; from_nons := froms'; sent_nons := sents' ; cur_nonce := cur_n' |})
      -> honestk = findUserKeys usrs'
      -> user_cipher_queues_ok cs honestk usrs'.
  Proof.
    intros;
      unfold user_cipher_queues_ok.
    rewrite Forall_natmap_forall; intros; subst.
    autorewrite with find_user_keys.
    cases (u_id ==n k); subst; clean_map_lookups; user_cipher_queues_prop; eauto.
  Qed.
  Lemma keys_and_permissions_good_user_new_pubk :
    forall {A t} (usrs : honest_users A) gks (msg : message t) u_id u_d ks cmd qmsgs mycs froms sents cur_n adv_heap,
      keys_and_permissions_good gks usrs adv_heap
      -> (forall (k : NatMap.Map.key) (kp : bool), findKeysMessage msg $? k = Some kp -> gks $? k <> None)
      -> u_d = {| key_heap := ks $k++ findKeysMessage msg
               ; msg_heap := qmsgs
               ; protocol := cmd
               ; c_heap   := mycs
               ; from_nons := froms
               ; sent_nons := sents
               ; cur_nonce := cur_n |}
      -> user_keys usrs u_id = Some ks
      -> keys_and_permissions_good gks (usrs $+ (u_id,u_d)) adv_heap.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition idtac.
    econstructor; eauto; subst; simpl.

    permission_heaps_prop.
    unfold permission_heap_good; intros.
    cases (ks $? k_id); cases (findKeysMessage msg $? k_id); solve_perm_merges; eauto.
    cases (gks $? k_id); eauto.
    exfalso; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_user_new_pubk.

  Ltac process_permission_heaps :=
    repeat
      match goal with
      | [ H : keys_and_permissions_good _ _ _ |- keys_and_permissions_good _ _ _ ] =>
        unfold keys_and_permissions_good in *; split_ands; intuition idtac
      | [ |- permission_heap_good _ (RealWorld.key_heap ?u) ] => progress simpl || destruct u; simpl in *
      | [ |- Forall_natmap (fun _ => permission_heap_good _ _) ?usrs ] => rewrite Forall_natmap_forall; intros
      | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => destruct (k1 ==n k2); subst; clean_map_lookups
      | [ OK : Forall_natmap (fun _ => permission_heap_good _ _) ?usrs
        , USR : ?usrs $? _ = Some {| key_heap := ?ks ; protocol := _ ; msg_heap := _ ; c_heap := _ |}
          |- permission_heap_good _ ?ks ] => generalize (Forall_natmap_in_prop _ OK USR); intros; clear USR
      | [ OK : Forall_natmap (fun _ => permission_heap_good _ _) ?usrs
        , USR : ?usrs $? _ = Some {| key_heap := ?ks ; protocol := _ ; msg_heap := _ ; c_heap := _ |}
        , KS : ?ks $? _ = Some _
          |- permission_heap_good _ ?ks ] => generalize (Forall_natmap_in_prop _ OK USR); intros; clear USR
      | [ H : permission_heap_good _ _ |- _ ] => unfold permission_heap_good in H
      | [ |- permission_heap_good _ _ ] => unfold permission_heap_good; intros; simpl in *
      | [ H : ?m1 $k++ ?m2 $? ?kid = _ |- _ ] => cases (m1 $? kid); cases (m2 $? kid); solve_perm_merges; clean_context
      | [ H : keys_mine _ ?othr_kys, KS : ?othr_kys $? _ = Some _ |- _ ] => specialize (H _ _ KS); split_ors; split_ands
      | [ H : (forall k kp, findKeysMessage ?msg $? k = Some kp -> _ ), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
        specialize (H _ _ ARG); split_ands; subst
      | [ H : (forall k_id kp, ?perms $? k_id = Some kp -> _), ARG : ?perms $? ?k = Some _ |- _ $? ?k <> None ] =>
        specialize (H _ _ ARG); split_ex
      end.

  Lemma honest_labeled_step_keys_and_permissions_good :
    forall {A B C} suid u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> message_queues_ok cs usrs gks
            -> forall usrs'' cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs'
                                            ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}) 
                -> keys_and_permissions_good gks' usrs'' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto 2;
      clean_context;
      msg_queue_prop;
      eauto;
      process_permission_heaps;
      permission_heaps_prop;
      specialize_msg_ok;
      eauto;
      clean_map_lookups.

    cases (gks' $? k_id); try contradiction; eauto.
  Qed.

  Lemma permission_heap_good_addnl_key :
    forall gks ks k_id k,
      permission_heap_good gks ks
      -> ~ In k_id gks
      -> keyId k = k_id
      -> permission_heap_good (gks $+ (k_id,k)) ks.
  Proof.
    unfold permission_heap_good; intros; subst.
    destruct (keyId k ==n k_id0); subst; clean_map_lookups; eauto.
  Qed.

  Lemma permission_heap_good_new_key_perm :
    forall gks ks k_id k,
      permission_heap_good gks ks
      -> ~ In k_id gks
      -> keyId k = k_id
      -> permission_heap_good (gks $+ (k_id,k)) (add_key_perm k_id true ks).
  Proof.
    unfold permission_heap_good; intros; subst.
    unfold add_key_perm in *.
    destruct (keyId k ==n k_id0); subst; clean_map_lookups; eauto.
    cases (ks $? keyId k); clean_map_lookups; eauto.
  Qed.

  Hint Resolve permission_heap_good_addnl_key permission_heap_good_new_key_perm.

  Lemma permission_heaps_good_addnl_key :
    forall {A} (usrs : honest_users A) gks k,
      ~ In (keyId k) gks
      -> Forall_natmap (fun u => permission_heap_good gks (key_heap u)) usrs
      -> Forall_natmap (fun u => permission_heap_good (gks $+ (keyId k, k)) (key_heap u)) usrs.
  Proof.
    intros; rewrite Forall_natmap_forall in *; intros; eauto.
  Qed.

  Hint Resolve permission_heaps_good_addnl_key.
  
  Lemma keys_and_permissions_good_addnl_key :
    forall {A} gks (usrs : honest_users A) adv_heap k_id k,
      keys_and_permissions_good gks usrs adv_heap
      -> ~ In k_id gks
      -> keyId k = k_id
      -> keys_and_permissions_good (gks $+ (k_id,k)) usrs adv_heap.
  Proof.
    intros. unfold keys_and_permissions_good in *; split_ands; subst; intuition eauto.
    destruct (keyId k ==n k_id); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_addnl_key.

  Lemma keys_and_permissions_good_readd_user_same_perms :
    forall {A} (usrs : honest_users A) adv_heap gks ks cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' u_id,
      keys_and_permissions_good gks usrs adv_heap
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> keys_and_permissions_good gks (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs'
                                                         ; from_nons := froms'; sent_nons := sents' ; cur_nonce := cur_n' |})) adv_heap.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition eauto.
    econstructor; eauto.
    simpl.
    eapply Forall_natmap_in_prop in H; eauto.
    simpl in *; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_readd_user_same_perms.

  Lemma keys_and_permissions_good_new_honest_key :
    forall {A} (usrs : honest_users A) gks k_id k ks u_id cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' adv_heap,
      gks $? k_id = None
      -> keys_and_permissions_good gks usrs adv_heap
      -> k_id = keyId k
      -> usrs $? u_id = Some {| key_heap := ks ; protocol := cmd ; msg_heap := qmsgs ; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> keys_and_permissions_good (gks $+ (k_id,k))
                                  (usrs $+ (u_id,
                                            {| key_heap := add_key_perm k_id true ks
                                             ; protocol := cmd'
                                             ; msg_heap := qmsgs'
                                             ; c_heap   := mycs'
                                             ; from_nons := froms'
                                             ; sent_nons := sents'
                                             ; cur_nonce := cur_n' |}))
                                  adv_heap.
  Proof.
    intros.
    keys_and_permissions_prop.
    unfold keys_and_permissions_good; intuition eauto.
    - destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
    - econstructor; eauto; simpl.
      + unfold permission_heap_good; intros; simpl in *.
        destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
        unfold add_key_perm in *.
        cases (ks $? keyId k); clean_map_lookups; try discriminate; process_permission_heaps.
        specialize (H7 _ _ H8); auto.
        specialize (H7 _ _ H8); auto.
      + eapply keys_and_permissions_good_addnl_key; eauto; unfold keys_and_permissions_good; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_new_honest_key.

  Lemma honest_silent_step_keys_good :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> keys_and_permissions_good gks'
                                              (usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}))
                                              adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst;
      try discriminate; eauto 2; clean_context.

    user_cipher_queues_prop;
      encrypted_ciphers_prop.

    eapply keys_and_permissions_good_user_new_pubk; eauto;
      keys_and_permissions_prop;
      process_permission_heaps;
      intuition contra_map_lookup.
  Qed.


    Lemma honest_labeled_step_user_cipher_queues_ok :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a suid,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate; eauto;
      autorewrite with find_user_keys; clean_context.

    - msg_queue_prop; eauto.
      specialize_msg_ok.
      eapply user_cipher_queues_ok_add_user; autorewrite with find_user_keys; eauto.

    - remember ((usrs $+ (rec_u_id,
                          {| key_heap := key_heap rec_u;
                             protocol := protocol rec_u;
                             msg_heap := msg_heap rec_u ++ [existT crypto t0 msg];
                             c_heap := c_heap rec_u |}))) as usrs'.

      assert (findUserKeys usrs = findUserKeys usrs') as RW
          by (subst; autorewrite with find_user_keys; eauto).

      rewrite RW; clear RW.
      destruct rec_u; simpl in *.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
      autorewrite with find_user_keys.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
  Qed.

    Hint Resolve
       user_cipher_queues_ok_addnl_global_cipher
       user_cipher_queues_ok_add_user
       user_cipher_queues_ok_readd_user
       user_cipher_queues_ok_addnl_pubk
       findUserKeys_has_key_of_user
       findUserKeys_has_private_key_of_user
  .


  Lemma honest_silent_step_user_cipher_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        user_cipher_queues_prop;
        clean_context; eauto.

    - econstructor; simpl.
      +  econstructor; eauto.
         eexists; clean_map_lookups; intuition eauto.
         assert (findUserKeys usrs' $? k__signid = Some true) by eauto.
         simpl; unfold honest_keyb; context_map_rewrites; eauto.
      +  eapply user_cipher_queues_ok_addnl_global_cipher; eauto.

    - econstructor; simpl; eauto.
      + econstructor; clean_map_lookups; eauto.
        eexists; intuition eauto.
        assert (findUserKeys usrs' $? k_id = Some true) by eauto.
        simpl; unfold honest_keyb; context_map_rewrites; eauto.
        
      + eapply user_cipher_queues_ok_addnl_global_cipher; eauto.
  Qed.

  Lemma adv_step_user_cipher_queues_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> user_cipher_queues_ok cs' honestk' usrs'.
  Proof.
    induction 1; inversion 1; inversion 4; intros; subst; eauto.

    destruct rec_u; simpl in *;
      autorewrite with find_user_keys; eauto.
  Qed.


    Lemma message_no_adv_private_new_keys :
    forall {t} (msg : crypto t) honestk cs pubk,
      message_no_adv_private honestk cs msg
      -> message_no_adv_private (honestk $k++ pubk) cs msg.
  Proof.
    unfold message_no_adv_private; intros.
    specialize (H _ _ H0).
    cases (pubk $? k); solve_perm_merges; intuition eauto.
  Qed.

  Lemma message_no_adv_private_new_honestk :
    forall {t} (msg : crypto t) honestk cs k_id,
      message_no_adv_private honestk cs msg
      -> message_no_adv_private (honestk $+ (k_id,true)) cs msg.
  Proof.
    unfold message_no_adv_private; intros.
    specialize (H _ _ H0).
    destruct (k_id ==n k); subst; clean_map_lookups; intuition auto.
  Qed.

  Hint Resolve message_no_adv_private_new_keys message_no_adv_private_new_honestk.
  Lemma msgCiphersSigned_after_msg_keys :
    forall {t} (msg : crypto t) cs honestk msgk,
      msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk (honestk $k++ msgk) cs msg.
  Proof.
    unfold msgCiphersSignedOk.
    induction 1; eauto.
    econstructor; intuition eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto using message_honestly_signed_after_add_keys.
  Qed.

  Lemma msgCiphersSigned_new_private_key :
    forall {t} (msg : crypto t) cs honestk k_id,
      msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk (honestk $+ (k_id,true)) cs msg.
  Proof.
    unfold msgCiphersSignedOk.
    induction 1; eauto.
    econstructor; eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto; repeat process_keys_messages; eauto.
  Qed.

  Hint Resolve msgCiphersSigned_after_msg_keys msgCiphersSigned_new_private_key.

  Lemma message_queue_ok_adding_public_keys :
    forall msgs cs honestk pubk ks,
      message_queue_ok honestk cs msgs ks
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true)
      -> message_queue_ok (honestk $k++ pubk) cs msgs ks.
  Proof.
    unfold message_queue_ok; induction 1; eauto; intros;
      econstructor; eauto.

    destruct x; simpl in *; intuition eauto;
      specialize_msg_ok; eauto;
        repeat
          match goal with
          | [ H : honest_key (_ $k++ _) _ |- _ ] => invert H
          | [ H : _ $k++ _ $? _ = Some true |- _ ] => apply merge_perms_split in H; split_ors
          end;
        specialize_msg_ok; eauto.
  Qed.

  Lemma message_queue_ok_adding_public_keys' :
    forall msgs cs honestk pubk ks,
      message_queue_ok honestk cs msgs ks
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> message_queue_ok (honestk $k++ pubk) cs msgs ks.
  Proof.
    intros; eapply message_queue_ok_adding_public_keys; eauto.
  Qed.

  Hint Resolve message_queue_ok_adding_public_keys message_queue_ok_adding_public_keys'.

  Lemma message_queues_ok_user_adding_public_keys :
    forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs mycs mycs' froms froms' sents sents' cur_n cur_n',
      message_queues_ok cs usrs gks
      -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := msg::msgs
                             ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ pubk; protocol := cmd'; msg_heap := msgs
                                ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
      -> message_queues_ok cs usrs' gks.
  Proof.
    intros; subst.
    unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros.
    destruct (u_id ==n k); subst; clean_map_lookups; autorewrite with find_user_keys; eauto; simpl.
    eapply message_queue_ok_adding_public_keys; eauto.
    specialize (H _ _ H1); invert H; eauto.
  Qed.

  Lemma message_queues_ok_user_adding_public_keys' :
    forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs mycs mycs' froms froms' sents sents' cur_n cur_n',
      message_queues_ok cs usrs gks
      -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true /\ p = false)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := msg::msgs
                             ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ pubk; protocol := cmd'; msg_heap := msgs
                                ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
      -> message_queues_ok cs usrs' gks.
  Proof.
    intros; subst.
    eapply message_queues_ok_user_adding_public_keys; eauto.
  Qed.

  Hint Resolve message_queues_ok_user_adding_public_keys message_queues_ok_user_adding_public_keys'.

  Lemma message_queues_ok_readd_user_same_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' sents sents' cur_n cur_n' gks,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                             ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; autorewrite with find_user_keys; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_same_queue.

  Lemma message_queues_ok_readd_user_popped_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' sents sents' cur_n cur_n' gks qmsg,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsg :: qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; autorewrite with find_user_keys; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve
       message_queues_ok_readd_user_popped_queue
       msgCiphersSignedOk_addnl_cipher
       msgCiphersSignedOk_new_honest_key'.

  Lemma message_queue_ok_addnl_cipher :
    forall msgs cs honestk c_id c gks,
      message_queue_ok honestk cs msgs gks
      -> ~ In c_id cs
      -> message_queue_ok honestk (cs $+ (c_id, c)) msgs gks.
  Proof.
    unfold message_queue_ok; induction 1; eauto; intros;
      econstructor; eauto.

    destruct x; simpl in *; split_ands.
    repeat (apply conj); intros.
    - unfold findKeysCrypto in *; destruct c0; eauto.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; simpl in *;
        assert ( cs $? c_id0 <> None ) by eauto; try contradiction.

      cases (cs $? c_id0); try contradiction; context_map_rewrites.
      assert ( Some (cipher_signing_key c0) = Some (cipher_signing_key c0) ) as CS by eauto.
      specialize (H3 _ CS); split_ands; eauto.

    - unfold msg_cipher_id in *; destruct (c_id ==n cid); subst; clean_map_lookups.
      destruct c0; eauto.
    - unfold msg_signing_key in *; destruct c0; try discriminate;
        destruct (c_id ==n c_id0); subst; clean_map_lookups; simpl in *; context_map_rewrites;
          assert (cs $? c_id0 <> None) by eauto; try contradiction.
      cases (cs $? c_id0); try discriminate; clean_context.
      assert (Some (cipher_signing_key c0) = Some (cipher_signing_key c0)) as SC by trivial.
      specialize (H3 _ SC); intuition eauto.
      unfold message_no_adv_private,findKeysCrypto in *; intros; clean_map_lookups; context_map_rewrites; eauto.
  Qed.

  Hint Resolve message_queue_ok_addnl_cipher.

  Lemma message_queues_ok_addnl_cipher :
    forall {A} (usrs : honest_users A) cs c_id c gks,
      message_queues_ok cs usrs gks
      -> ~ In c_id cs
      -> message_queues_ok (cs $+ (c_id,c)) usrs gks.
  Proof.
    unfold message_queues_ok in *; intros; rewrite Forall_natmap_forall in *; intros; eauto.
  Qed.

  Hint Resolve message_queues_ok_addnl_cipher.

  Lemma new_global_key_not_in_heaps :
    forall perms ks k_id,
      ~ In k_id ks
      -> permission_heap_good ks perms
      -> perms $? k_id = None.
  Proof.
    intros.
    cases (perms $? k_id); clean_map_lookups; trivial.
    match goal with
    | [ H : permission_heap_good _ ?perms, H1 : ?perms $? _ = _ |- _ ] =>
      specialize (H _ _ H1); split_ex; contra_map_lookup
    end.
  Qed.

  Hint Resolve new_global_key_not_in_heaps.

  Lemma msg_signing_key_cipher_id_in_ciphers :
    forall {t} (c : crypto t) cs k_id c_id,
      msg_signing_key cs c = Some k_id
      -> msg_cipher_id c = Some c_id
      -> exists c, cs $? c_id = Some c
             /\ (exists {t} (m : message t) msg_to nonce,
                   c = SigCipher k_id msg_to nonce m
                 \/ exists k__enc, c = SigEncCipher k_id k__enc msg_to nonce m).
  Proof.
    intros.
    unfold msg_signing_key, msg_cipher_id in *.
    destruct c; try discriminate; invert H0;
      cases (cs $? c_id); try discriminate.

    destruct c; try discriminate; clean_context;
      eexists; split; eauto 8.
  Qed.

  Lemma message_queue_ok_addnl_honest_key :
    forall msgs cs honestk k_id gks usage kt,
      message_queue_ok honestk cs msgs gks
      -> gks $? k_id = None
      -> honestk $? k_id = None
      -> encrypted_ciphers_ok honestk cs gks
      -> message_queue_ok (honestk $+ (k_id,true)) cs msgs (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |} )).
  Proof.
    induction 1; intros; econstructor; unfold message_queue_ok in *; eauto.

    destruct x; simpl in *; intros.
    assert (honestk $? k_id = None) by eauto.
    split_ands; repeat (apply conj); intros; eauto.
    - unfold not; intro; destruct (k_id ==n k); subst; split_ands; clean_map_lookups; specialize_msg_ok; eauto.
    - specialize_msg_ok; destruct (k_id ==n k); subst; clean_map_lookups; split_ands; try contradiction; eauto.
      split; intros; repeat invert_base_equalities1; eauto.
      invert H4; clean_map_lookups; specialize_msg_ok; eauto.
  Qed.

  Lemma message_queue_ok_addnl_adv_key :
    forall msgs cs honestk k_id gks usage kt,
      message_queue_ok honestk cs msgs gks
      -> ~ In k_id gks
      -> permission_heap_good gks honestk
      -> message_queue_ok honestk cs msgs (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |} )).
  Proof.
    induction 1; intros; econstructor; eauto.
    - destruct x; simpl in *; intros.
      assert (honestk $? k_id = None) by eauto.
      intuition eauto; specialize_msg_ok; eauto.
      + destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      + destruct (k_id ==n k); subst; clean_map_lookups; specialize_msg_ok; eauto.
    - eapply IHForall; eauto.
  Qed.

  Lemma message_queues_ok_addnl_honest_key :
    forall {A} (usrs : honest_users A) cs u_id k_id gks ks cmd cmd' qmsgs mycs froms sents cur_n usage kt,
      message_queues_ok cs usrs gks
      -> ~ In k_id gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs
                          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}))
                          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold message_queues_ok; rewrite Forall_natmap_forall; intros.
    destruct (k ==n u_id); subst; clean_map_lookups; simpl;
      msg_queue_prop;
      autorewrite with find_user_keys;
      eapply message_queue_ok_addnl_honest_key; eauto.
  Qed.

  Lemma message_queues_ok_addnl_adv_key :
    forall {A} (usrs : honest_users A) cs k_id gks usage kt,
      message_queues_ok cs usrs gks
      -> ~ In k_id gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> message_queues_ok cs
                          usrs
                          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold message_queues_ok; rewrite Forall_natmap_forall; intros.
    destruct v; simpl.
    msg_queue_prop; eapply message_queue_ok_addnl_adv_key; eauto.
  Qed.

  Hint Resolve message_queues_ok_addnl_honest_key message_queues_ok_addnl_adv_key.

  Lemma msg_cipher_id_in_mycs :
    forall {t} (msg : crypto t) mycs c_id,
      incl (findCiphers msg) mycs
      -> msg_cipher_id msg = Some c_id
      -> List.In c_id mycs.
  Proof.
    intros; destruct msg; simpl in *; try discriminate;
      clean_context; eauto.
  Qed.

  Hint Resolve msg_cipher_id_in_mycs.
    
  Lemma honestly_signed_message_in_key_heap :
    forall {t} (msg : crypto t) honestk cs gks k_id,
      msg_honestly_signed honestk cs msg = true
      -> permission_heap_good gks honestk
      -> msg_signing_key cs msg = Some k_id
      -> gks $? k_id <> None.
  Proof.
    intros.
    unfold msg_honestly_signed in *;
      rewrite H1 in H;
      process_keys_messages.
    specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
  Qed.

  Hint Resolve honestly_signed_message_in_key_heap.

  Lemma honest_labeled_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                            ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context; msg_queue_prop; specialize_msg_ok; eauto.

    eapply message_queues_ok_readd_user_same_queue;
      clean_map_lookups; eauto.

    unfold keys_and_permissions_good in *; split_ands; permission_heaps_prop.
    msg_queue_prop.
    econstructor; autorewrite with find_user_keys; eauto.
    simpl.
    eapply Forall_app; simpl; econstructor; eauto.
    split; intros.
    - specialize (H0 _ _ H16);
        split_ors; split_ands;
        match goal with
        | [ H : permission_heap_good _ ?ks , H1 : ?ks $? _ = _ |- _ ] =>
          specialize (H _ _ H1); split_ex; contra_map_lookup
        end.

    - split; intros.
      + assert (List.In cid mycs') by eauto.
        user_cipher_queues_prop.
      + unfold msg_signing_key in *.

        destruct msg; try discriminate;
          cases (cs' $? c_id); try discriminate;
            clean_context;
            encrypted_ciphers_prop;
            intuition eauto;
            simpl in *;
            contra_map_lookup;
            unfold message_no_adv_private;
            intros;
            simpl in *;
            clean_context;
            context_map_rewrites;
            clean_map_lookups.

        * destruct p; specialize_msg_ok; eauto.
        * unfold msg_honestly_signed in *; simpl in *; context_map_rewrites; simpl in *.
            unfold honest_keyb in *;
            cases (findUserKeys usrs $? k); try discriminate;
              destruct b; try discriminate; contradiction.
  Qed.

  Lemma honest_silent_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> permission_heap_good gks honestk
        -> message_queues_ok cs usrs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    msg_queue_prop.
    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    econstructor; autorewrite with find_user_keys; simpl; eauto.
    rewrite Forall_natmap_forall; intros; eauto.
    msg_queue_prop; eauto.
  Qed.
