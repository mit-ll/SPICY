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

From SPICY Require Import
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
     SafetyAutomation

     Theory.CipherTheory
     Theory.KeysTheory
     Theory.MessagesTheory
     Theory.UsersTheory

.

Set Implicit Arguments.

Import SafetyAutomation.

Section RealWorldLemmas.

  Hint Unfold message_no_adv_private : core.

  Lemma adv_no_honest_keys_empty :
    forall honestk,
      adv_no_honest_keys honestk $0.
    unfold adv_no_honest_keys; intros; simpl.
    cases (honestk $? k_id); subst; intuition idtac.
    cases b; subst; intuition idtac.
    right; right; intuition idtac.
    invert H.
  Qed.

  Hint Resolve
       msg_honestly_signed_addnl_cipher
       msg_honestly_signed_addnl_honest_key : core.

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

  Hint Constructors encrypted_cipher_ok : core.
  
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

  Hint Resolve keys_mine_addnl_honest_key : core.

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
       encrypted_ciphers_ok_addnl_key
    : core.

  (* Definition adv_preds {B} (adv : user_data B) (honestk : key_perms) := *)
  (*   (forall kid, adv.(key_heap) $? kid = Some true -> honestk $? kid = Some true -> False). *)

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
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; auto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H24 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros.
        specialize (H4 _ _ H5).
        specialize (ADV k); unfold not; split_ors; split_ex; contra_map_lookup; try contradiction;
          unfold keys_and_permissions_good, permission_heap_good in *; split_ex
          ; match goal with
            | [ H : (forall _ _, key_heap ?u $? _ = Some _ -> _), ARG : key_heap ?u $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG); split_ex; eexists;
                intuition (intros; eauto); contra_map_lookup
            end.

    - econstructor; eauto.
      specialize (H22 k_id); eauto.
      eapply SigCipherNotHonestOk; unfold not; intros; split_ors; split_ands; contra_map_lookup; try contradiction; eauto.
  Qed.

End RealWorldLemmas.

(* honest users only honest keys *)

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
    eapply merge_perms_adds_ks1; eauto.
    clean_map_lookups; eauto.
Qed.

Hint Resolve honest_users_only_honest_keys_gen_key honest_users_only_honest_keys_nochange_keys : core.

Lemma honest_users_only_honest_keys_adv_steps :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' suid,
    step_user lbl suid bd bd'
    -> forall (cmd : user_cmd C) honestk,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> suid = None
      -> honestk = findUserKeys usrs
      -> honest_users_only_honest_keys usrs
      -> forall cmd',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> honest_users_only_honest_keys usrs'.
Proof.
  induction 1; inversion 1; inversion 4;
    intros; subst;
      eauto.

  clean_context.
  destruct rec_u; eauto.
Qed.

    Lemma honest_users_only_honest_keys_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        honest_users_only_honest_keys usrs
        -> honestk = findUserKeys usrs
        -> honest_users_only_honest_keys (clean_users honestk cs usrs).
    Proof.
      intros.
      unfold honest_users_only_honest_keys in *; intros.
      apply clean_users_cleans_user_inv in H1; split_ex.
      simpl in *.
      specialize (H _ _ H1); simpl in *.
      rewrite H3 in H2.
      apply clean_key_permissions_inv in H2; split_ands.
      specialize (H _ _ H2).
      pose proof (findUserKeys_clean_users_correct usrs cs k_id);
        context_map_rewrites; subst; eauto.
    Qed.



(* encrypted cipher ok *)


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

Hint Resolve
     clean_keys_keeps_honest_key
  : core.

Lemma clean_ciphers_encrypted_ciphers_ok :
  forall honestk cs gks,
    encrypted_ciphers_ok honestk cs gks
    -> encrypted_ciphers_ok honestk (clean_ciphers honestk cs) (clean_keys honestk gks).
Proof.
  unfold encrypted_ciphers_ok; intros; rewrite Forall_natmap_forall in *.
  intros.

  assert (clean_ciphers honestk cs $? k = Some v) as CSOK by assumption.
  rewrite <- find_mapsto_iff in CSOK.
  rewrite clean_ciphers_mapsto_iff in CSOK; split_ands.
  rewrite find_mapsto_iff in H1.
  specialize (H _ _ H1).
  unfold honest_cipher_filter_fn, cipher_honestly_signed in H2.

  destruct v.
  - eapply honest_keyb_true_honestk_has_key in H2.
    invert H; try contradiction.
    econstructor; eauto.
  - eapply honest_keyb_true_honestk_has_key in H2.
    invert H; try contradiction.
    eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
Qed.


Lemma clean_ciphers_encrypted_ciphers_ok' :
  forall honestk honestk' cs gks,
    encrypted_ciphers_ok honestk cs gks
    -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
    -> encrypted_ciphers_ok honestk' (clean_ciphers honestk cs) (clean_keys honestk gks).
Proof.
  unfold encrypted_ciphers_ok; intros; rewrite Forall_natmap_forall in *.
  intros.

  assert (clean_ciphers honestk cs $? k = Some v) as CSOK by assumption.
  rewrite <- find_mapsto_iff in CSOK.
  rewrite clean_ciphers_mapsto_iff in CSOK; split_ands.
  rewrite find_mapsto_iff in H2.
  specialize (H _ _ H2).
  unfold honest_cipher_filter_fn, cipher_honestly_signed in H3.

  destruct v;
    repeat
      match goal with
      | [ H : honest_keyb _ _ = true |- _ ] => eapply honest_keyb_true_honestk_has_key in H
      | [ H : encrypted_cipher_ok _ _ _ _ |- _ ] => invert H; try contradiction
      end.

  - econstructor; eauto.
    intros * ARG; specialize (H11 _ _ ARG); split_ex; eauto.

  - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
Qed.


(* user cipher queues ok *)

Lemma user_cipher_queue_cleaned_users_nochange :
  forall {A} (usrs : honest_users A) honestk cs u_id,
    user_cipher_queue (clean_users honestk cs usrs) u_id
    = user_cipher_queue usrs u_id.
Proof.
  unfold user_cipher_queue, clean_users; simpl; intros.
  rewrite mapi_o; intros; subst; auto; unfold option_map; simpl.
  cases (usrs $? u_id); auto.
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

Hint Resolve user_cipher_queue_ok_addnl_global_cipher : core.

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

Hint Resolve
     user_cipher_queues_ok_addnl_generated_key
     user_cipher_queues_ok_addnl_generated_key'
     clean_ciphers_keeps_honest_cipher
  : core.

Lemma user_cipher_queue_ok_after_cleaning :
  forall cs honestk honestk' mycs,
    user_cipher_queue_ok cs honestk mycs
    -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
    -> user_cipher_queue_ok (clean_ciphers honestk cs) honestk' mycs.
Proof.
  unfold user_cipher_queue_ok; intros; rewrite Forall_forall in *;
    intros.
  specialize (H _ H1); split_ex.
  eexists; intuition eauto.
  unfold cipher_honestly_signed in *.
  destruct x0; unfold honest_keyb in *;
    match goal with
    | [ |- context [ honestk' $? ?kid ]] =>
      cases (honestk $? kid); try discriminate;
        destruct b; try discriminate;
          assert (honestk' $? kid = Some true) as RW by auto 2;
          rewrite RW; trivial
    end.
Qed.

Lemma user_cipher_queues_ok_after_cleaning :
  forall {A} (usrs : honest_users A) honestk honestk' cs,
    user_cipher_queues_ok cs honestk usrs
    -> honestk = findUserKeys usrs
    -> honestk' = findUserKeys (clean_users honestk cs usrs)
    -> user_cipher_queues_ok (clean_ciphers honestk cs) honestk' (clean_users honestk cs usrs).
Proof.
  unfold user_cipher_queues_ok; intros.
  pose proof (clean_users_no_change_honestk usrs).
  rewrite Forall_natmap_forall in *; intros.
  rewrite <- find_mapsto_iff in H3; unfold clean_users in H3;
    rewrite mapi_mapsto_iff in H3; intros; subst; trivial.
  split_ex; split_ands; subst; simpl in *.
  rewrite find_mapsto_iff in H1; specialize (H _ _ H1).
  eapply user_cipher_queue_ok_after_cleaning; auto.
Qed.

(* keys and permissions good *)

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

Hint Resolve keys_and_permissions_good_user_new_pubk : core.

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
    clean_map_lookups;
    eauto.
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

Hint Resolve permission_heap_good_addnl_key permission_heap_good_new_key_perm : core.

Lemma permission_heaps_good_addnl_key :
  forall {A} (usrs : honest_users A) gks k,
    ~ In (keyId k) gks
    -> Forall_natmap (fun u => permission_heap_good gks (key_heap u)) usrs
    -> Forall_natmap (fun u => permission_heap_good (gks $+ (keyId k, k)) (key_heap u)) usrs.
Proof.
  intros; rewrite Forall_natmap_forall in *; intros; eauto.
Qed.

Hint Resolve permission_heaps_good_addnl_key : core.

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

Hint Resolve keys_and_permissions_good_addnl_key : core.

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

Hint Resolve keys_and_permissions_good_readd_user_same_perms : core.

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

Hint Resolve keys_and_permissions_good_new_honest_key : core.

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

Ltac invert_adv_msg_queue_ok :=
  match goal with
  | [ H : adv_message_queue_ok _ _ _ (_ ++ _ :: _) |- _ ] =>
    hnf in H; eapply break_msg_queue_prop in H
  end; split_ex.

Lemma adv_step_keys_good :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl None bd bd'
    -> forall (cmd : user_cmd C),
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> ks = adv.(key_heap)
      -> adv_message_queue_ok usrs cs gks qmsgs
      -> adv_cipher_queue_ok cs usrs mycs
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> keys_and_permissions_good gks usrs ks
      -> forall cmd',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> keys_and_permissions_good gks' usrs' ks'.
Proof.
  induction 1; inversion 1; inversion 6; intros; subst; try discriminate;
    eauto; clean_context.

  - unfold keys_and_permissions_good in *; intuition eauto.
    unfold permission_heap_good in *; intros.
    cases (key_heap adv' $? k_id); eauto.
    invert_adv_msg_queue_ok.
    cases (findKeysCrypto cs' msg $? k_id); solve_perm_merges.
    specialize (H5 _ _ H10); split_ands; subst.
    cases (gks' $? k_id); try contradiction; eauto.
  - destruct rec_u; simpl in *.
    eapply keys_and_permissions_good_readd_user_same_perms; eauto.
  - unfold keys_and_permissions_good in *; intuition eauto.
    unfold permission_heap_good in *; intros.
    eapply merge_perms_split in H5; split_ors; eauto.
    encrypted_ciphers_prop; clean_map_lookups; eauto.
    + specialize_msg_ok; split_ex; intuition eauto.
    + assert (permission_heap_good gks' (findUserKeys usrs')) by eauto.
      specialize_msg_ok; subst.
      specialize (H9 _ _ H20); eauto.

  - unfold keys_and_permissions_good in *; intuition eauto.
    destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
    rewrite Forall_natmap_forall in *; intros.
    eapply permission_heap_good_addnl_key; eauto.
Qed.
  
Lemma permission_heap_good_clean_keys :
  forall honestk gks uks,
    permission_heap_good gks uks
    -> permission_heap_good (clean_keys honestk gks) (clean_key_permissions honestk uks).
Proof.
  unfold permission_heap_good; intros.
  apply clean_key_permissions_inv in H0; split_ands.
  specialize (H _ _ H0); split_ex.
  eexists; eapply clean_keys_keeps_honest_key; eauto.
Qed.

Hint Resolve permission_heap_good_clean_keys : core.

Lemma keys_and_permissions_good_clean_keys :
  forall {A} (usrs : honest_users A) adv_heap cs gks,
    keys_and_permissions_good gks usrs adv_heap
    -> keys_and_permissions_good
        (clean_keys (findUserKeys usrs) gks)
        (clean_users (findUserKeys usrs) cs usrs)
        (clean_key_permissions (findUserKeys usrs) adv_heap).
Proof.
  unfold keys_and_permissions_good; intros; split_ands.
  intuition (simpl; eauto).

  Ltac inv_cleans :=
    repeat
      match goal with
      | [ H : clean_keys _ _ $? _ = Some _ |- _ ] => eapply clean_keys_inv in H; split_ands
      | [ H : clean_keys _ _ $? _ = None |- _ ] => eapply clean_keys_inv' in H; split_ands
      | [ H : clean_users _ _ _ $? _ = Some _ |- _ ] => eapply clean_users_cleans_user_inv in H; split_ex; split_ands
      end.
  
  - inv_cleans; eauto.
  - apply Forall_natmap_forall; intros; inv_cleans.
    rewrite H3.
    permission_heaps_prop; eauto.
Qed.

Lemma users_permission_heaps_good_merged_permission_heaps_good :
  forall {A} (usrs : honest_users A) gks,
    Forall_natmap (fun u : user_data A => permission_heap_good gks (key_heap u)) usrs
    -> permission_heap_good gks (findUserKeys usrs).
Proof.
  induction usrs using P.map_induction_bis; intros; Equal_eq; eauto.
Qed.

    Lemma clean_keys_new_honest_key' :
      forall honestk k_id gks,
        gks $? k_id = None
        -> clean_keys (honestk $+ (k_id, true)) gks = clean_keys honestk gks.
    Proof.
      intros.
      unfold clean_keys, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      subst; simpl.

      rewrite fold_add; eauto.
      assert (honest_key_filter_fn (honestk $+ (k_id,true)) k e = honest_key_filter_fn honestk k e)
        as RW.

      unfold honest_key_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      apply find_mapsto_iff in H0; contra_map_lookup.
      rewrite RW; trivial.
    Qed.

    Lemma clean_keys_new_honest_key :
      forall honestk k_id k gks,
        gks $? k_id = None
        -> permission_heap_good gks honestk
        -> clean_keys (honestk $+ (k_id, true)) (gks $+ (k_id,k)) =
          clean_keys honestk gks $+ (k_id, k).
    Proof.
      intros.

      apply map_eq_Equal; unfold Equal; intros.
      destruct (k_id ==n y); subst; clean_map_lookups; eauto.
      - apply clean_keys_keeps_honest_key; eauto.
        unfold honest_key_filter_fn; clean_map_lookups; eauto.
      - unfold clean_keys at 1.
        unfold filter.
        rewrite fold_add; eauto.
        unfold honest_key_filter_fn; clean_map_lookups; eauto.
        unfold clean_keys, filter, honest_key_filter_fn; eauto.
        pose proof (clean_keys_new_honest_key' honestk k_id gks H).
        unfold clean_keys, filter, honest_key_filter_fn in H1.
        rewrite H1; trivial.
    Qed.

(* user cipher queues ok *)

Lemma user_cipher_queues_ok_add_user :
  forall {A t} (usrs usrs' : honest_users A) (msg : crypto t) honestk u_id ks
    cmd cmd' qmsgs qmsgs' mycs froms froms' sents sents' cur_n cur_n' cs,
    user_cipher_queues_ok cs (findUserKeys usrs) usrs
    -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
    -> message_no_adv_private (findUserKeys usrs) cs msg
    -> msg_honestly_signed (findUserKeys usrs) cs msg = true
    -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ findKeysCrypto cs msg; protocol := cmd'; msg_heap := qmsgs'
                                 ; c_heap := findCiphers msg ++ mycs ; from_nons := froms'; sent_nons := sents' ; cur_nonce := cur_n' |})
    -> honestk = findUserKeys usrs'
    -> user_cipher_queues_ok cs honestk usrs'.
Proof.
  intros;
    unfold user_cipher_queues_ok.
  rewrite Forall_natmap_forall; intros; subst.
  autorewrite with find_user_keys.
  cases (u_id ==n k); subst; clean_map_lookups; user_cipher_queues_prop
  ; rewrite message_no_adv_private_merge
  ; eauto.

  unfold user_cipher_queue_ok in *.
  rewrite List.Forall_app; split; eauto.
  rewrite Forall_forall; intros.
  unfold message_no_adv_private in H1.
  
  unfold findCiphers in H3
  ; unfold msg_honestly_signed, msg_signing_key in H2
  ; unfold findKeysCrypto in H1
  ; destruct msg
  ; try discriminate.

  cases (cs $? c_id)
  ; try discriminate.

  invert H4.
  
  eexists; split; eauto.
  unfold cipher_honestly_signed.
  unfold honest_keyb, cipher_signing_key in H2
  ; destruct c
  ; eauto.

  invert H5.
  
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
  : core.


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




(* Here *)



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

Hint Resolve message_no_adv_private_new_keys message_no_adv_private_new_honestk : core.

(* message queue ok *)

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

Hint Resolve message_queue_ok_adding_public_keys
     message_queue_ok_adding_public_keys'
     break_msg_queue_prop : core.

Lemma message_queues_ok_user_adding_public_keys :
  forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs1 msgs2
    mycs mycs' froms froms' sents sents' cur_n cur_n',
    message_queues_ok cs usrs gks
    -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true)
    -> usrs $? u_id = Some (mkUserData ks cmd (msgs1 ++ msg :: msgs2) mycs froms sents cur_n)
    -> usrs' = usrs $+ (u_id, (mkUserData (ks $k++ pubk) cmd' (msgs1 ++ msgs2) mycs' froms' sents' cur_n'))
    -> message_queues_ok cs usrs' gks.
Proof.
  intros; subst.
  unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros.
  destruct (u_id ==n k); subst; clean_map_lookups; autorewrite with find_user_keys; eauto; simpl.
  eapply message_queue_ok_adding_public_keys; eauto.
  specialize (H _ _ H1); simpl in H; eauto.
  eapply break_msg_queue_prop; eauto.
Qed.

Lemma message_queues_ok_user_adding_public_keys' :
  forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs1 msgs2
    mycs mycs' froms froms' sents sents' cur_n cur_n',
    message_queues_ok cs usrs gks
    -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true /\ p = false)
    -> usrs $? u_id = Some (mkUserData ks cmd (msgs1 ++ msg :: msgs2) mycs froms sents cur_n)
    -> usrs' = usrs $+ (u_id, (mkUserData (ks $k++ pubk) cmd' (msgs1 ++ msgs2) mycs' froms' sents' cur_n'))
    -> message_queues_ok cs usrs' gks.
Proof.
  intros; subst.
  eapply message_queues_ok_user_adding_public_keys; eauto.
Qed.

Hint Resolve message_queues_ok_user_adding_public_keys message_queues_ok_user_adding_public_keys' : core.

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

Hint Resolve message_queues_ok_readd_user_same_queue : core.

Lemma message_queues_ok_readd_user_popped_queue :
  forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs1 qmsgs2 mycs mycs'
    froms froms' sents sents' cur_n cur_n' gks qmsg,
    message_queues_ok cs usrs gks
    -> usrs $? u_id = Some (mkUserData ks cmd (qmsgs1 ++ qmsg :: qmsgs2) mycs froms sents cur_n)
    -> message_queues_ok cs (usrs $+ (u_id, mkUserData ks cmd' (qmsgs1 ++ qmsgs2) mycs' froms' sents' cur_n')) gks.
Proof.
  intros; unfold message_queues_ok; intros.
  econstructor; autorewrite with find_user_keys; eauto; simpl.
  msg_queue_prop; eauto.
Qed.

Hint Resolve
     message_queues_ok_readd_user_popped_queue
  : core.

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

Hint Resolve message_queue_ok_addnl_cipher : core.

Lemma message_queues_ok_addnl_cipher :
  forall {A} (usrs : honest_users A) cs c_id c gks,
    message_queues_ok cs usrs gks
    -> ~ In c_id cs
    -> message_queues_ok (cs $+ (c_id,c)) usrs gks.
Proof.
  unfold message_queues_ok in *; intros; rewrite Forall_natmap_forall in *; intros; eauto.
Qed.

Hint Resolve message_queues_ok_addnl_cipher : core.

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

Hint Resolve new_global_key_not_in_heaps : core.

Lemma msg_signing_key_cipher_id_in_ciphers :
  forall {t} (c : crypto t) cs k_id c_id,
    msg_signing_key cs c = Some k_id
    -> msg_cipher_id c = Some c_id
    -> exists c, cs $? c_id = Some c
                 /\ (exists t (m : message t) msg_to nonce,
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
    repeat
      match goal with
      | [ H : honest_key _ _ |- _ ] => invert H
      end; clean_map_lookups; specialize_msg_ok; eauto.
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

Hint Resolve message_queues_ok_addnl_honest_key message_queues_ok_addnl_adv_key : core.

Lemma msg_cipher_id_in_mycs :
  forall {t} (msg : crypto t) mycs c_id,
    incl (findCiphers msg) mycs
    -> msg_cipher_id msg = Some c_id
    -> List.In c_id mycs.
Proof.
  intros; destruct msg; simpl in *; try discriminate;
    clean_context; eauto.
Qed.

Hint Resolve msg_cipher_id_in_mycs : core.

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

Hint Resolve honestly_signed_message_in_key_heap : core.

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
  - specialize (H0 _ _ H15);
      split_ors;
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

Lemma adv_step_message_queues_ok :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl None bd bd'
    -> forall (cmd : user_cmd C) honestk,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> honestk = findUserKeys usrs
      -> ks = adv.(key_heap)
      -> qmsgs = adv.(msg_heap)
      -> mycs = adv.(c_heap)
      -> encrypted_ciphers_ok honestk cs gks
      -> message_queues_ok cs usrs gks
      -> permission_heap_good gks honestk
      -> permission_heap_good gks ks
      -> adv_cipher_queue_ok cs usrs mycs
      -> forall cmd' honestk',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> honestk' = findUserKeys usrs'
          -> message_queues_ok cs' usrs' gks'.
Proof.
  induction 1; inversion 1; inversion 10; intros; subst;
    eauto 2; try discriminate; eauto;
      clean_context.
  
  unfold message_queues_ok in *;
    rewrite Forall_natmap_forall in *;
    intros.

  destruct (rec_u_id ==n k); subst; clean_map_lookups;
    eauto;
    autorewrite with find_user_keys;
    simpl; eauto.

  unfold message_queue_ok; eapply Forall_app.
  unfold message_queue_ok in *; econstructor; eauto.

  repeat (apply conj); intros; eauto.
  - specialize (H0 _ _ H); split_ors; split_ands; subst; eauto.
    specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
    specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
  - unfold not; intros.
    unfold keys_mine in *.
    destruct msg; simpl in *; try discriminate; clean_context.
    unfold adv_cipher_queue_ok in H27; rewrite Forall_forall in H27.
    assert (List.In cid (c_heap adv)) by eauto.
    specialize (H27 _ H); split_ex; split_ands; contra_map_lookup.
  - unfold msg_signing_key in *; destruct msg; try discriminate;
      cases (cs' $? c_id); try discriminate;
        clean_context.
    simpl in *; context_map_rewrites.

    encrypted_ciphers_prop; simpl in *; eauto;
      clean_context; intuition clean_map_lookups; eauto;
        unfold message_no_adv_private; intros; simpl in *; context_map_rewrites;
          repeat
            match goal with
            | [ ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] => is_var b; destruct b
            | [ H : (forall k, findKeysMessage ?msg $? k = Some ?b -> _), ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] =>
              specialize (H _ ARG)
            | [ H : honest_key ?honk ?k, H2 : ?honk $? ?k = Some true -> False |- _ ] => invert H; contradiction
            end; try contradiction; clean_map_lookups; eauto.
Qed.

    Hint Resolve honest_cipher_filter_fn_true_honest_signing_key : core.
    Hint Extern 1 (honest_key _ _) => process_keys_messages : core.

    Lemma message_queue_ok_after_cleaning :
      forall msgs honestk honestk' cs gks suid mycs,
        message_queue_ok honestk cs msgs gks
        -> encrypted_ciphers_ok honestk cs gks
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> message_queue_ok honestk' (clean_ciphers honestk cs)
                           (clean_messages honestk cs suid mycs msgs) (clean_keys honestk gks).
    Proof.
      intros; unfold message_queue_ok in *; rewrite Forall_forall in *; intros.
      eapply clean_messages_list_in_safe in H2; split_ands; destruct x.
      specialize (H _ H2); simpl in *; split_ands.

      repeat (apply conj); intros; specialize_msg_ok; eauto;
        unfold msg_signed_addressed in H3; eapply andb_prop in H3; split_ands;
          unfold msg_honestly_signed, msg_signing_key in *;
          destruct c; try discriminate.
      
      - unfold not; intros.

        unfold findKeysCrypto in *;
          cases (cs $? c_id); try discriminate;
            simpl in *.

        assert (clean_ciphers honestk cs $? c_id = Some c) by eauto;
          context_map_rewrites;
          destruct c; clean_map_lookups.
        specialize (H _ _ H6).

        assert (Some k__sign = Some k__sign) as KSEQ by trivial.
        specialize (H5 _ KSEQ); split_ands.
        simpl in H3; rewrite <- honest_key_honest_keyb in H3; specialize (H10 H3); split_ands.
        unfold message_no_adv_private in H10.
        simpl in *; context_map_rewrites.
        specialize (H10 _ _ H6); split_ands; subst.
        cases (gks $? k); try contradiction.
        eapply clean_keys_inv' in H8; eauto.
        unfold honest_key_filter_fn in H8; context_map_rewrites; discriminate.

      - simpl in *; clean_context;
          cases (cs $? cid); try discriminate.

        unfold not; intros;
          eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto;
            contra_map_lookup.

      - cases (clean_ciphers honestk cs $? c_id); try discriminate;
          clean_context.

        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq;
          split_ands; context_map_rewrites.
        assert (Some (cipher_signing_key c) = Some (cipher_signing_key c)) as CSK by trivial.
        specialize (H5 _ CSK); split_ands.
        rewrite <- honest_key_honest_keyb in H3.
        specialize (H9 H3); split_ands.
        cases (gks $? cipher_signing_key c); try contradiction.

        intuition eauto.

        + eapply clean_keys_inv' in H10; eauto.
          unfold honest_key_filter_fn in *; invert H3; context_map_rewrites; discriminate.

        + unfold message_no_adv_private in *; intros; clean_context; simpl in *.
          context_map_rewrites; eapply clean_ciphers_keeps_honest_cipher in H6;
            eauto; context_map_rewrites.

          destruct c; clean_map_lookups.
          specialize (H9 _ _ H11); intuition eauto.
    Qed.

    Hint Immediate
         clean_users_no_change_honestk
         clean_users_no_change_honestk' : core.

    Lemma message_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs gks,
        message_queues_ok cs usrs gks
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs) (clean_keys honestk gks).
    Proof.
      unfold message_queues_ok; intros.
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H2;
        unfold clean_users in H2; rewrite mapi_mapsto_iff in H2; intros; subst; trivial.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H2; specialize (H _ _ H2).
      eapply message_queue_ok_after_cleaning; auto.
    Qed.






(* BREAK *)




















Lemma adv_cipher_queue_ok_read_msg :
  forall {A} (usrs : honest_users A) cs {t} (msg : crypto t) gks qmsgs1 qmsgs2 advcs,
    adv_message_queue_ok usrs cs gks (qmsgs1 ++ (existT _ _ msg) :: qmsgs2)
    -> adv_cipher_queue_ok cs usrs advcs
    -> adv_cipher_queue_ok cs usrs (findCiphers msg ++ advcs).
Proof.
  unfold adv_cipher_queue_ok; intros;
    rewrite Forall_forall in *; intros.

  destruct msg; simpl in *; eauto.
  split_ors; subst; eauto.
  clear H0.
  unfold adv_message_queue_ok in H;
    apply break_msg_queue_prop in H; split_ex; simpl in *.
  assert (cs $? x <> None) by eauto; cases (cs $? x); try contradiction.
  assert (x = x \/ False) as ARG by (left; trivial).
  specialize (H3 _ ARG); split_ex; split_ands; clear ARG; clean_map_lookups.
  eexists; split; eauto.
Qed.

Lemma adv_cipher_queue_ok_readd_user_same_mycs_froms_msgs :
  forall {A} (usrs : honest_users A) cs u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n cur_n',
    adv_cipher_queue_ok cs usrs adv_mycs
    -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                              ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
    -> adv_cipher_queue_ok cs
                           (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs
                                              ; c_heap := mycs; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n' |})) adv_mycs.
Proof.
  unfold adv_cipher_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H _ H1); split_ex; split_ands.
  eexists; split; eauto.
  autorewrite with find_user_keys; split_ors; eauto.

  right.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0); subst; clean_map_lookups; simpl in *; eauto 10.
Qed.

Lemma msg_to_this_user_addnl_cipher :
  forall {t} (msg : crypto t) cs suid c_id c,
    ~ In c_id cs
    -> msg_to_this_user cs suid msg = true
    -> msg_to_this_user (cs $+ (c_id,c)) suid msg = true.
Proof.
  unfold msg_to_this_user, msg_destination_user; intros.
  destruct msg; try discriminate.
  solve_simple_maps; eauto.
Qed.

Hint Resolve
     msg_honestly_signed_addnl_cipher
     msg_to_this_user_addnl_cipher
  : core.

Lemma adv_cipher_queue_ok_msg_send :
  forall {A t} (usrs : honest_users A) (msg : crypto t) cs u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n cur_n',
    adv_cipher_queue_ok cs usrs adv_mycs
    -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                              ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
    -> adv_cipher_queue_ok cs
                           (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs ++ [existT _ _ msg]
                                              ; c_heap := mycs; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n' |})) adv_mycs.
Proof.
  unfold adv_cipher_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H _ H1); split_ex; split_ands.
  eexists; autorewrite with find_user_keys; split; eauto.
  split_ors; split_ex; split_ands; eauto.
  right.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0); subst; try contradiction;
      clean_map_lookups; simpl in *; eauto 10.

  split; [trivial|]; (do 3 eexists); split; eauto.
  split; clean_map_lookups; eauto.
  split; eauto.
  split; eauto.
  split.
  reflexivity.
  simpl; split_ors; eauto.
  right.
  rewrite Exists_exists in *; split_ex; split_ands; destruct x3.
  eexists.
  rewrite in_app_iff; split.
  left; eauto.
  simpl; eauto.
Qed.

Lemma adv_cipher_queue_ok_new_cipher :
  forall {A} (usrs : honest_users A) cs c_id c u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n gks,
    ~ In c_id cs
    -> adv_cipher_queue_ok cs usrs adv_mycs
    -> message_queues_ok cs usrs gks
    -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                              ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
    -> adv_cipher_queue_ok (cs $+ (c_id, c))
                           (usrs $+ (u_id,
                                     {| key_heap := ks;
                                        protocol := cmd';
                                        msg_heap := qmsgs;
                                        c_heap := c_id :: mycs;
                                        from_nons := froms;
                                        sent_nons := sents;
                                        cur_nonce := 1 + cur_n |})) adv_mycs.
Proof.
  unfold adv_cipher_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H0 _ H3); split_ex; split_ands.
  destruct (c_id ==n x); subst; clean_map_lookups; eauto.
  eexists; split; eauto.
  autorewrite with find_user_keys; split_ors; split_ex; split_ands; eauto 9.
  right.
  destruct (x1 ==n u_id); subst; clean_map_lookups; simpl; eauto.
  - split; [trivial|]; (do 3 eexists); split; eauto.
    split; clean_map_lookups; eauto.
    split; eauto.
    simpl; split; eauto.
    split; eauto.
    split_ors; eauto.
    right; rewrite Exists_exists in *; split_ex; split_ands.
    destruct x1; split_ands.
    eexists; split; eauto.
    simpl; split; eauto.
    unfold msg_signed_addressed in *.
    rewrite andb_true_iff in H10.
    rewrite andb_true_iff; split_ands; split; eauto.
    unfold msg_nonce_same in *; intros; subst.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    simpl in *.
    msg_queue_prop.
    unfold message_queue_ok in H12.
    rewrite Forall_forall in H12; specialize (H12 _ H2); simpl in H12; split_ands.
    context_map_rewrites.
    assert (cs $? c_id0 <> None) by eauto; contradiction.
  - destruct (u_id ==n cipher_to_user x0); subst; clean_map_lookups.
    + split; [trivial|]; (do 3 eexists); split; eauto.
      split; clean_map_lookups; eauto.
      split; eauto.
      simpl; split; eauto.
      split; eauto.
      simpl in *; split_ors; eauto.
      right; rewrite Exists_exists in *; split_ex; split_ands.
      destruct x3; split_ands.
      eexists; split; eauto.
      simpl; split; eauto.
      unfold msg_signed_addressed in *.
      rewrite andb_true_iff in H10.
      rewrite andb_true_iff; split_ands; split; eauto.
      unfold msg_nonce_same in *; intros; subst.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      simpl in *.
      msg_queue_prop.
      unfold message_queue_ok in H12.
      rewrite Forall_forall in H12; specialize (H12 _ H2); simpl in H12; split_ands.
      context_map_rewrites.
      assert (cs $? c_id0 <> None) by eauto; contradiction.
    + split; [trivial|]; (do 3 eexists); split; eauto.
      split; clean_map_lookups; eauto.
      split; eauto.
      simpl; split; eauto.
      split; eauto.
      simpl in *; split_ors; eauto.
      right; rewrite Exists_exists in *; split_ex; split_ands.
      destruct x4; split_ands.
      eexists; split; eauto.
      simpl; split; eauto.
      unfold msg_signed_addressed in *.
      rewrite andb_true_iff in H11.
      rewrite andb_true_iff; split_ands; split; eauto.
      unfold msg_nonce_same in *; intros; subst.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      msg_queue_prop.
      msg_queue_prop.
      unfold message_queue_ok in H14.
      rewrite Forall_forall in H14; specialize (H14 _ H10); simpl in H14; split_ands.
      context_map_rewrites.
      assert (cs $? c_id0 <> None) by eauto; contradiction.
Qed.

Lemma adv_cipher_queue_ok_new_adv_cipher :
  forall {A} (usrs : honest_users A) cs c_id c adv_mycs gks,
    ~ In c_id cs
    (* -> fst (cipher_nonce c) = None *)
    -> cipher_honestly_signed (findUserKeys usrs) c = false
    -> message_queues_ok cs usrs gks
    -> adv_cipher_queue_ok cs usrs adv_mycs
    -> adv_cipher_queue_ok (cs $+ (c_id, c)) usrs (c_id :: adv_mycs).
Proof.
  unfold adv_cipher_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  simpl in *; split_ors; subst; eauto.
  destruct (c_id ==n x); subst; clean_map_lookups; eauto.
  specialize (H2 _ H3); split_ex.
  eexists; split; eauto.
  split_ors; eauto.
  split_ex.
  right.
  split; [trivial|]; (do 3 eexists); split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  split_ors; eauto.
  rewrite Exists_exists in *; split_ex; split_ands.
  destruct x4; split_ands.
  right; eexists; split; eauto.
  simpl; split; eauto.

  unfold msg_signed_addressed in *.
  rewrite andb_true_iff in H11.
  rewrite andb_true_iff; split_ands; split; eauto.
  unfold msg_nonce_same in *; intros; subst.
  destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.

  msg_queue_prop.
  unfold message_queue_ok in H13.
  rewrite Forall_forall in H13; specialize (H13 _ H10); simpl in H13; split_ands.
  context_map_rewrites.
  assert (cs $? c_id0 <> None) by eauto; contradiction.
Qed.

Hint Resolve
     adv_cipher_queue_ok_read_msg
     adv_cipher_queue_ok_msg_send
     adv_cipher_queue_ok_readd_user_same_mycs_froms_msgs
     adv_cipher_queue_ok_new_cipher
     adv_cipher_queue_ok_new_adv_cipher
  : core.

Lemma adv_step_adv_cipher_queue_ok :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) suid
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl suid bd bd'
    -> forall (cmd : user_cmd C),
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> suid = None
      -> ks = adv.(key_heap)
      -> qmsgs = adv.(msg_heap)
      -> mycs = adv.(c_heap)
      -> adv_message_queue_ok usrs cs gks qmsgs
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> adv_no_honest_keys (findUserKeys usrs) ks
      -> message_queues_ok cs usrs gks
      -> adv_cipher_queue_ok cs usrs mycs
      -> forall cmd',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> adv_cipher_queue_ok cs' usrs' mycs'.
Proof.
  induction 1; inversion 1; inversion 10; intros; subst;
    eauto 2; clean_context;
      eauto.

  destruct rec_u;
    eapply adv_cipher_queue_ok_msg_send; eauto.

  eapply adv_cipher_queue_ok_new_adv_cipher; eauto.
  unfold cipher_honestly_signed.
  unfold honest_keyb.
  specialize (H28 k__signid); contra_map_lookup; split_ors; split_ands; context_map_rewrites;
    try contradiction; trivial.

  eapply adv_cipher_queue_ok_new_adv_cipher; eauto.
  unfold cipher_honestly_signed.
  unfold honest_keyb.
  match goal with
  | [ H : adv_no_honest_keys _ _ |- _ ] =>
    specialize (H k_id); contra_map_lookup; split_ors; split_ands; context_map_rewrites;
      try contradiction; trivial
  end.

Qed.



Ltac process_predicate :=
  repeat (
      contradiction
      || discriminate
      || match goal with
         | [ H : msg_to_this_user _ _ _ = true |- _ ] =>
           unfold msg_to_this_user, msg_destination_user in H; context_map_rewrites
         | [ H : (if ?cond then _ else _) = _ |- _ ] => destruct cond; try discriminate; try contradiction
         | [ |- ?c1 /\ _ ] =>
           match c1 with
           (* simplify *)
           | List.In _ (sent_nons ?sents) => is_not_var sents; simpl
           | List.In _ ?arg => match arg with
                               | context [ _ $? _ ] => context_map_rewrites
                               | context [ if ?cond then _ else _ ] => destruct cond
                               end
           (* process *)
           | _ => 
             split; [
               match c1 with
               | (_ $+ (?k1,_) $? ?k2 = _) =>
                 solve [ subst; clean_map_lookups; eauto ]
               | _ => solve [ eauto 2 ]
               end | ]
           end
         | [ H : List.In ?cn _ \/ Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] =>
           split_ors; eauto
         | [ H : Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] =>
           rewrite Exists_exists in *; split_ex
         | [ H : let (_,_) := ?x in msg_signed_addressed _ _ _ _ = true /\ _ |- _ ] => destruct x; split_ands
         | [ H : List.In ?m ?heap |- context [ ?heap ++ _ ] ] => right; simpl; exists m; rewrite in_app_iff; eauto
         end).


Lemma adv_cipher_queue_ok_addnl_honest_key :
  forall {A} (usrs : honest_users A) adv_cs cs gks k_id u_id ks cmd cmd' qmsgs mycs froms sents n adv_ks,
    ~ In k_id gks
    -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
    -> adv_cipher_queue_ok cs usrs adv_cs
    -> keys_and_permissions_good gks usrs adv_ks
    -> usrs $? u_id = Some {|
                          key_heap := ks;
                          protocol := cmd;
                          msg_heap := qmsgs;
                          c_heap := mycs;
                          from_nons := froms;
                          sent_nons := sents;
                          cur_nonce := n |}
    -> adv_cipher_queue_ok cs
                           (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                                              protocol := cmd';
                                              msg_heap := qmsgs;
                                              c_heap := mycs;
                                              from_nons := froms;
                                              sent_nons := sents;
                                              cur_nonce := n |}))
                           adv_cs.
Proof.
  unfold adv_cipher_queue_ok; intros;
    rewrite Forall_forall in *; intros.
  specialize (H1 _ H4); split_ands.

  autorewrite with find_user_keys; split_ex; split_ands; eexists; split; eauto.
  split_ors; split_ex.

  - left; eauto.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    unfold honest_keyb in *.
    destruct (k_id ==n cipher_signing_key x0); subst; clean_map_lookups; eauto.
    exfalso.
    encrypted_ciphers_prop; simpl in *; clean_map_lookups.
    
  - right.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    split.
    unfold honest_keyb in *; destruct (k_id ==n (cipher_signing_key x0)); clean_map_lookups; eauto.
    
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0);
      subst; clean_map_lookups;
        do 3 eexists;
        simpl in *; process_predicate; eauto; simpl.
    * right; eexists; split; eauto.
      keys_and_permissions_prop.
      simpl; split; eauto.
    * right; eexists; split; eauto.
      keys_and_permissions_prop.
      simpl; split; eauto.
    * right; eexists; split; eauto.
      keys_and_permissions_prop.
      simpl; split; eauto.
Qed.

Hint Resolve adv_cipher_queue_ok_addnl_honest_key : core.

Lemma honest_silent_step_adv_cipher_queue_ok :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> message_queues_ok cs usrs gks
        -> adv_cipher_queue_ok cs usrs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                               ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> adv_cipher_queue_ok cs' usrs'' adv'.(c_heap).
Proof.
  induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
    eauto 2; clean_context;
      eauto.

  - unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.
    specialize (H25 _ H4); split_ex; split_ands.
    eexists; split; eauto.
    autorewrite with find_user_keys; split_ors; split_ex.
    + left; eauto.
      rewrite cipher_honestly_signed_honest_keyb_iff in *.
      unfold honest_keyb in *.

      user_cipher_queues_prop.
      clear H5; encrypted_ciphers_prop.
      cases (findKeysMessage msg $? cipher_signing_key x0).
      * specialize (H20 _ _ Heq); split_ands; subst; context_map_rewrites; discriminate.
      * cases (findUserKeys usrs' $? cipher_signing_key x0); try discriminate;
          solve_perm_merges; eauto.
    + right.
      split.
      rewrite cipher_honestly_signed_after_msg_keys; eauto.
      destruct (u_id ==n x1);
        destruct (u_id ==n cipher_to_user x0);
        subst; clean_map_lookups;
          do 3 eexists;
          simpl in *; process_predicate; eauto; simpl.
      all : right; eexists; split; eauto; simpl; split; eauto.
Qed.

(* adv no honest keys *)

Lemma adv_no_honest_keys_after_new_honest_key :
  forall k_id adv_heap honestk gks,
    ~ In k_id gks
    -> adv_no_honest_keys honestk adv_heap
    -> permission_heap_good gks adv_heap
    -> adv_no_honest_keys (honestk $+ (k_id,true)) adv_heap.
Proof.
  intros.
  unfold adv_no_honest_keys; intros.
  specialize (H0 k_id0).
  unfold permission_heap_good in *.
  destruct (k_id ==n k_id0); subst; clean_map_lookups; intuition eauto;
    right; right; split; auto; intros;
      match goal with
      | [ H : (forall kid kp, _ $? kid = Some kp -> _), ARG : adv_heap $? _ = Some _ |- _] => specialize (H _ _ ARG)
      end; split_ex; contra_map_lookup.
Qed.

Lemma adv_no_honest_keys_after_new_adv_key :
  forall k_id adv_heap honestk gks,
    ~ In k_id gks
    -> adv_no_honest_keys honestk adv_heap
    -> permission_heap_good gks honestk
    -> adv_no_honest_keys honestk (adv_heap $+ (k_id,true)).
Proof.
  intros.
  unfold adv_no_honest_keys; intros.
  specialize (H0 k_id0).
  unfold permission_heap_good in *.
  destruct (k_id ==n k_id0); subst; clean_map_lookups; intuition eauto.
Qed.

Hint Resolve adv_no_honest_keys_after_new_honest_key adv_no_honest_keys_after_new_adv_key : core.

Lemma adv_step_adv_no_honest_keys :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl None bd bd'
    -> forall (cmd : user_cmd C) honestk,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> honestk = findUserKeys usrs
      -> ks = adv.(key_heap)
      -> encrypted_ciphers_ok honestk cs gks
      -> adv_no_honest_keys honestk ks
      -> keys_and_permissions_good gks usrs ks
      -> adv_message_queue_ok usrs cs gks qmsgs
      -> forall cmd' honestk',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> honestk' = findUserKeys usrs'
          -> adv_no_honest_keys honestk' ks'.
Proof.
  induction 1; inversion 1; inversion 7; intros; subst;
    eauto 2; autorewrite with find_user_keys; eauto;
      try rewrite add_key_perm_add_private_key; clean_context;
        match goal with
        | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
        end.

  - invert_adv_msg_queue_ok.
    unfold adv_no_honest_keys in *; intros.
    specialize (H23 k_id); intuition idtac.
    right; right; intuition eauto.
    eapply merge_perms_split in H10; split_ors; auto.
    specialize (H4 _ _ H10); split_ands; eauto.
    
  - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
    specialize (ADV k__encid); split_ors; split_ands; try contradiction;
      encrypted_ciphers_prop; clean_map_lookups; intuition idtac;
        unfold adv_no_honest_keys; intros;
          specialize (H23 k_id); clean_map_lookups; intuition idtac;
            right; right; split; eauto; intros;
              eapply merge_perms_split in H10; split_ors;
                try contradiction;
                specialize (H19 _ _ H10); split_ex; split_ands; eauto.

  - eapply adv_no_honest_keys_after_new_adv_key; eauto.

Qed.

Lemma honest_labeled_step_adv_no_honest_keys :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
Proof.
  induction 1; inversion 2; inversion 6; intros; subst;
    try discriminate; eauto 2;
      autorewrite with find_user_keys; eauto;
        clean_context.

  - msg_queue_prop; specialize_msg_ok;
      unfold adv_no_honest_keys, message_no_adv_private in *;
      simpl in *;
      repeat
        match goal with
        | [ RW : honest_keyb ?honk ?kid = _ , H : if honest_keyb ?honk ?kid then _ else _ |- _] => rewrite RW in H
        | [ H : (forall k_id, findUserKeys _ $? k_id = None \/ _) |- (forall k_id, _) ] => intro KID; specialize (H KID)
        | [ |- context [ _ $k++ $0 ] ] => rewrite merge_keys_right_identity
        | [ FK : findKeysCrypto _ ?msg $? ?kid = Some _, H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)
            |- context [ _ $k++ findKeysCrypto _ ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try solve_perm_merges
        | [ FK : findKeysCrypto _ ?msg $? ?kid = None |- context [ ?uks $k++ findKeysCrypto _ ?msg $? ?kid] ] =>
          split_ors; split_ands; solve_perm_merges
        | [ H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeysCrypto ?cs ?msg $? ?kid] ] =>
          match goal with
          | [ H : findKeysCrypto cs msg $? kid = _ |- _ ] => fail 1
          | _ => cases (findKeysCrypto cs msg $? kid)
          end
        end; eauto.

    split_ors; split_ands; contra_map_lookup; eauto.

  - unfold adv_no_honest_keys in *; intros.
    specialize (H24 k_id).
    split_ex; subst; simpl in *.
    assert (List.In x mycs') by eauto.
    user_cipher_queues_prop.
    rewrite cipher_honestly_signed_honest_keyb_iff in H10.
    encrypted_ciphers_prop; eauto.
    intuition idtac.
    right; right; split; eauto; intros.
    solve_perm_merges;
      specialize (H13 _ _ H14); split_ex; discriminate.
Qed.

Lemma honest_silent_step_adv_no_honest_keys :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
Proof.
  induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
    eauto 2; autorewrite with find_user_keys; eauto; clean_context;
      match goal with
      | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
      end; eauto.

  assert (findUserKeys usrs' $? k__encid = Some true) by eauto.
  user_cipher_queues_prop; encrypted_ciphers_prop.
  cases (findUserKeys usrs' $? k__signid); try discriminate; cases b; subst; try discriminate.
  rewrite merge_keys_addnl_honest; eauto.
Qed.

    Lemma adv_no_honest_keys_after_cleaning :
      forall {A} (usrs : honest_users A) honestk honestk' cs adv_keys,
        adv_no_honest_keys honestk adv_keys
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys (clean_users honestk cs usrs)
        -> adv_no_honest_keys honestk' (clean_key_permissions honestk adv_keys).
    Proof.
      unfold adv_no_honest_keys; intros.
      pose proof (findUserKeys_clean_users_correct usrs cs k_id); subst.
      repeat
        match goal with
        | [ K : NatMap.Map.key, H : (forall k : NatMap.Map.key, _) |- _ ] => specialize (H K)
        end.
      split_ors; split_ands;
        match goal with
        | [ H : findUserKeys ?usrs $? ?kid = _ , M : match findUserKeys ?usrs $? ?kid with _ => _ end |- _ ] =>
          rewrite H in M
        end; eauto.

      right; right; split; eauto.
      unfold not; intros.
      eapply clean_key_permissions_inv in H1; split_ands; contradiction.
    Qed.







Lemma cipher_honestly_signed_false_same_msg_recv :
  forall honestk pubk c,
    cipher_honestly_signed honestk c = false
    -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
    -> cipher_honestly_signed (honestk $k++ pubk) c = false.
Proof.
  intros.
  rewrite cipher_honestly_signed_honest_keyb_iff in *.
  unfold honest_keyb in *.
  cases (honestk $? cipher_signing_key c); solve_perm_merges; eauto;
    match goal with
    | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG); split_ands; subst
    end; eauto.
Qed.

Lemma cipher_honestly_signed_false_same_msg_recv' :
  forall honestk pubk c,
    cipher_honestly_signed honestk c = false
    -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true)
    -> cipher_honestly_signed (honestk $k++ pubk) c = false.
Proof.
  intros.
  rewrite cipher_honestly_signed_honest_keyb_iff in *.
  unfold honest_keyb in *.
  cases (honestk $? cipher_signing_key c); solve_perm_merges; eauto;
    match goal with
    | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG); split_ands; subst
    end; clean_map_lookups; eauto.
Qed.

Hint Resolve cipher_honestly_signed_false_same_msg_recv cipher_honestly_signed_false_same_msg_recv' : core.

(* adv message queue ok *)

Lemma adv_message_queue_ok_msg_recv :
  forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs1 qmsgs2 mycs froms sents cur_n adv_msgs,
    message_queues_ok cs usrs gks
    -> msg_honestly_signed (findUserKeys usrs) cs msg = true
    -> (exists c_id c, msg = SignedCiphertext c_id /\ cs $? c_id = Some c /\ ~ List.In (cipher_nonce c) froms)
    -> usrs $? u_id =
       Some
         {|
           key_heap := ks;
           protocol := cmd;
           msg_heap := qmsgs1 ++ (existT _ _ msg) :: qmsgs2;
           c_heap := mycs;
           from_nons := froms;
           sent_nons := sents;
           cur_nonce := cur_n |}
    -> adv_message_queue_ok usrs cs gks adv_msgs
    -> adv_message_queue_ok
         (usrs $+ (u_id,
                   {|
                     key_heap := ks $k++ findKeysCrypto cs msg;
                     protocol := cmd';
                     msg_heap := qmsgs1 ++ qmsgs2;
                     c_heap := findCiphers msg ++ mycs;
                     from_nons := updateTrackedNonce (Some u_id) froms cs msg;
                     sent_nons := sents;
                     cur_nonce := cur_n |})) cs gks adv_msgs.
Proof.
  unfold adv_message_queue_ok; intros.
  msg_queue_prop.
  rewrite Forall_forall in *; intros.
  specialize (H3 _ H10); destruct x1; simpl in *.
  rewrite findUserKeys_readd_user_addnl_keys in *; eauto.
  intuition eauto.

  - specialize (H3 _ _ H13); split_ex; eauto.
  - specialize (H3 _ _ H13); split_ex; subst.
    apply merge_perms_split in H16; split_ors; eauto.
    specialize_simply.
  - specialize (H14 _ H13); split_ex; split_ands; clean_map_lookups.
    eexists; split; eauto.
    split_ors; split_ex; eauto.
    + left.
      eapply cipher_honestly_signed_false_same_msg_recv; eauto.
      specialize_simply; eauto.
      destruct p; specialize_simply; trivial.
      
    + right.
      split.
      rewrite cipher_honestly_signed_after_msg_keys; eauto.
      
      destruct (x3 ==n u_id); subst; clean_map_lookups; eauto.
      * (do 3 eexists); split; eauto.
        split; clean_map_lookups; eauto.
        split; eauto.
        split; eauto.
        split; eauto.
        split_ors; eauto.
        rewrite Exists_exists in *; split_ex; split_ands; destruct x3.
        right; eexists; split; eauto.
        split_ands; split; eauto.
        split_ands; unfold msg_signed_addressed in *.
        rewrite andb_true_iff in *; split_ands; split; eauto.
        specialize_simply; eauto.

      * destruct (u_id ==n cipher_to_user x2); subst; clean_map_lookups.
        ** (do 3 eexists); repeat simple apply conj; simpl; eauto.
           simpl in *; context_map_rewrites.
           split_ors; specialize_simply; eauto.

           *** left.
               cases (cipher_to_user x2 ==n cipher_to_user x0); eauto.
               cases (count_occ msg_seq_eq froms (cipher_nonce x0)); simpl; eauto.
           *** rewrite Exists_exists in *; split_ex.
               simpl in H20; destruct x5.
               eapply in_elt_inv in H1; split_ors; clean_context; specialize_simply; eauto.
               **** generalize (eq_sigT_fst H1); intros; subst.
                    apply inj_pair2 in H1; subst.

                    unfold msg_signed_addressed in H21; rewrite andb_true_iff in H21; split_ands.
                    unfold msg_to_this_user, msg_destination_user in H21;
                      context_map_rewrites.
                    destruct (cipher_to_user x0 ==n cipher_to_user x2); subst; try discriminate.
                    rewrite e.
                    destruct (cipher_to_user x2 ==n cipher_to_user x2); try contradiction.
                    assert (~ List.In (cipher_nonce x0) froms) as NOTIN by eauto.
                    rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in NOTIN.
                    rewrite NOTIN.

                    unfold msg_nonce_same in H22.
                    assert (cipher_nonce x2 = cipher_nonce x0) as EQ by eauto.
                    rewrite EQ.
                    left; eauto.
               **** right; eexists; split; try eassumption.
                    simpl; split; eauto.
                    destruct x0; eauto.
                    
        ** (do 3 eexists); repeat simple apply conj; simpl; eauto.

           split_ors; specialize_simply; eauto.
           right; rewrite Exists_exists in *; split_ex;
             destruct x7.
           eexists; split; eauto.
           split_ex; split; context_map_rewrites; eauto.
           destruct x0; eauto.
Qed.

Hint Resolve adv_message_queue_ok_msg_recv : core.

Lemma adv_message_queue_ok_addnl_honestk_key :
  forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt u_id ks cmd cmd' qmsgs mycs froms sents n adv_keys,
    ~ In k_id gks
    -> adv_message_queue_ok usrs cs gks adv_heap
    -> keys_and_permissions_good gks usrs adv_keys
    -> usrs $? u_id = Some {|
                          key_heap := ks;
                          protocol := cmd;
                          msg_heap := qmsgs;
                          c_heap := mycs;
                          from_nons := froms;
                          sent_nons := sents;
                          cur_nonce := n |}
    -> adv_message_queue_ok
         (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                            protocol := cmd';
                            msg_heap := qmsgs;
                            c_heap := mycs;
                            from_nons := froms;
                            sent_nons := sents;
                            cur_nonce := n |}))
         cs
         (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |}))
         adv_heap.
Proof.
  unfold adv_message_queue_ok; intros;
    rewrite Forall_forall in *; intros.
  specialize (H0 _ H3); destruct x; split_ands;
    repeat (apply conj);
    autorewrite with find_user_keys in *; intros; eauto.

  - destruct (k_id ==n k); subst; clean_map_lookups; split; unfold not; intros; subst;
      try discriminate.
    + specialize (H4 _ _ H7); split_ands; contradiction.
    + specialize (H4 _ _ H7); split_ands; contradiction.
    + specialize (H4 _ _ H7); split_ands.
      assert (findUserKeys usrs $? k <> Some true) by auto; contradiction.
  - destruct (k_id ==n k); subst; clean_map_lookups; eauto.
  - specialize (H6 _ H7); split_ex; split_ands;
      eexists; split; eauto.
    split_ors; split_ex; split_ands; eauto.
    + left; eauto.
      rewrite cipher_honestly_signed_honest_keyb_iff in *.
      unfold honest_keyb in *.
      destruct (k_id ==n cipher_signing_key x0); subst; clean_map_lookups; eauto.
      exfalso.
      destruct c; simpl in *; try contradiction.
      split_ors; subst; try contradiction.
      context_map_rewrites.
      assert (gks $? cipher_signing_key x0 <> None) by eauto; contradiction.
      
    + right; split.
      rewrite cipher_honestly_signed_honest_keyb_iff in *; eauto.
      unfold honest_keyb in *.
      destruct (k_id ==n cipher_signing_key x0); subst; clean_map_lookups; eauto
      ; destruct (u_id ==n x1);
        destruct (u_id ==n cipher_to_user x0);
        subst; clean_map_lookups;
          do 3 eexists;
          simpl in *; process_predicate; eauto; simpl
          ; right; eexists; split; eauto
          ; keys_and_permissions_prop
          ; simpl; split; eauto.
Qed.

Lemma adv_message_queue_ok_addnl_global_key :
  forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt,
    adv_message_queue_ok usrs cs gks adv_heap
    -> ~ In k_id gks
    -> adv_message_queue_ok
         usrs
         cs
         (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |}))
         adv_heap.
Proof.
  intros.
  unfold adv_message_queue_ok in *; apply Forall_forall; intros.
  rewrite Forall_forall in H; specialize (H x); destruct x; intros.
  specialize (H H1); split_ands.
  intuition eauto;
    try specialize (H2 _ _ H5); split_ands; eauto.

  destruct (k_id ==n k); subst; clean_map_lookups; try contradiction.
  destruct (k_id ==n k); subst; clean_map_lookups; try contradiction.
  unfold msg_signing_key in *; destruct c; try discriminate;
    simpl in *.
  assert (cs $? c_id <> None) by eauto;
    cases (cs $? c_id); try discriminate;
      clean_context; eauto.
Qed.

Hint Resolve adv_message_queue_ok_addnl_honestk_key adv_message_queue_ok_addnl_global_key : core.

Lemma adv_message_queue_ok_addnl_cipher :
  forall {A} (usrs : honest_users A) adv_heap cs gks c_id c,
    ~ In c_id cs
    -> adv_message_queue_ok usrs cs gks adv_heap
    -> adv_message_queue_ok usrs (cs $+ (c_id,c)) gks adv_heap.
Proof.
  unfold adv_message_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H0 _ H1).
  destruct x; split_ands.

  intuition (intros; eauto);
    try
      match goal with
      | [ H : context [cs $+ (?cid1,_) $? ?cid2] |- _ ] =>
        destruct (cid1 ==n cid2); subst; clean_map_lookups
      | [ |- context [cs $+ (?cid1,_) $? ?cid2] ] =>
        destruct (cid1 ==n cid2); subst; clean_map_lookups
      end; eauto.

  - unfold findKeysCrypto in H2 , H5; destruct c0; eauto.
    + specialize (H2 _ _ H5); split_ands; eauto.
    + destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      * simpl in *.
        assert (~ In c_id0 cs) by eauto.
        rewrite not_find_in_iff in H7; context_map_rewrites; eauto.
      * specialize (H2 _ _ H5); split_ands; eauto.
  - unfold findKeysCrypto in H2 , H5; destruct c0; subst; eauto.
    + specialize (H2 _ _ H5); split_ands; eauto.
    + destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      * simpl in *.
        assert (~ In c_id0 cs) by eauto.
        rewrite not_find_in_iff in H6; context_map_rewrites; eauto.
      * specialize (H2 _ _ H5); split_ands; eauto.
  - unfold msg_signing_key in H5; destruct c0; try discriminate.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    simpl in *.
    assert (~ In c_id0 cs) by eauto.
    rewrite not_find_in_iff in H5; context_map_rewrites; eauto.
  - eexists; split; intros; eauto.
    specialize (H4 _ H5); split_ex; split_ands.
    exfalso.
    assert (~ In c_id0 cs) by eauto.
    rewrite not_find_in_iff in H7; contra_map_lookup.
  - specialize (H4 _ H5); split_ex.
    eexists; split; eauto.
    split_ors; eauto.
    split_ex; right.
    split; trivial.
    
    do 3 eexists; process_predicate.
    right; eexists; split; eauto.
    simpl; split.
    + unfold msg_signed_addressed in *.
      rewrite andb_true_iff in *; split_ands; split; eauto.
    + unfold msg_nonce_same in *; intros; clean_map_lookups.
      destruct (c_id ==n c_id1); subst; clean_map_lookups; eauto.
      exfalso.
      assert (~ In c_id1 cs) by eauto; clean_map_lookups.
      unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in H13;
        split_ands;
        context_map_rewrites;
        discriminate.
Qed.

Lemma adv_message_queue_ok_users_same_keys_sents :
  forall {A} (usrs : honest_users A) cs gks adv_msgs u_id ks cmd cmd' qmsgs mycs mycs' froms sents n n',
    adv_message_queue_ok usrs cs gks adv_msgs
    -> usrs $? u_id = Some {|
                          key_heap := ks;
                          protocol := cmd;
                          msg_heap := qmsgs;
                          c_heap := mycs;
                          from_nons := froms;
                          sent_nons := sents;
                          cur_nonce := n |}
    ->  adv_message_queue_ok
          (usrs $+ (u_id, {|
                      key_heap := ks;
                      protocol := cmd';
                      msg_heap := qmsgs;
                      c_heap := mycs';
                      from_nons := froms;
                      sent_nons := sents;
                      cur_nonce := n' |})) cs gks adv_msgs.
Proof.
  unfold adv_message_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H _ H1); destruct x;
    split_ands; repeat (apply conj);
      autorewrite with find_user_keys; eauto.

  intros.
  specialize (H4 _ H5); split_ex; eexists; split_ands; split; intros; eauto.
  split_ors; split_ex; split_ands; eauto.
  right.
  split; trivial.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0);
    subst; clean_map_lookups;
      do 3 eexists;
      simpl in *;
      process_predicate.
Qed.

Hint Resolve adv_message_queue_ok_addnl_cipher adv_message_queue_ok_users_same_keys_sents : core.

Lemma updateTrackedNonce_same_or_one_added :
  forall {t} (msg : crypto t) suid froms cs,
    updateTrackedNonce suid froms cs msg = froms
    \/ exists c_id c, msg_cipher_id msg = Some c_id
                      /\ cs $? c_id = Some c
                      /\ ~ List.In (cipher_nonce c) froms
                      /\ updateTrackedNonce suid froms cs msg = cipher_nonce c :: froms.
Proof.
  intros; unfold updateTrackedNonce.
  destruct msg; eauto.
  cases (cs $? c_id); eauto.
  destruct suid; eauto.
  destruct (u ==n cipher_to_user c); eauto.
  cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto.
  rewrite <- count_occ_not_In in Heq0.
  simpl; eauto 8.
Qed.

Lemma adv_message_queue_ok_msg_recv_drop :
  forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
    usrs $? u_id =
    Some
      {|
        key_heap := ks;
        protocol := cmd;
        msg_heap := existT _ _ msg :: qmsgs;
        c_heap := mycs;
        from_nons := froms;
        sent_nons := sents;
        cur_nonce := cur_n |}
    -> adv_message_queue_ok usrs cs gks adv_msgs
    -> adv_message_queue_ok
        (usrs $+ (u_id,
                  {|
                    key_heap := ks;
                    protocol := cmd';
                    msg_heap := qmsgs;
                    c_heap := mycs;
                    from_nons := updateTrackedNonce (Some u_id) froms cs msg;
                    sent_nons := sents;
                    cur_nonce := cur_n |})) cs gks adv_msgs.
Proof.
  unfold adv_message_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H0 _ H1); destruct x; simpl in *.
  autorewrite with find_user_keys.
  split_ands; repeat (apply conj); eauto; intros.

  specialize (H4 _ H5).
  split_ex.
  eexists; split; eauto.
  split_ors; eauto.
  split_ex; right.
  split; trivial.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0);
    subst; clean_map_lookups;
      simpl in *;
      do 3 eexists; process_predicate; eauto; simpl.

  - match goal with
    | [ |- context [ updateTrackedNonce ?suid ?froms ?cs ?msg ]] =>
      pose proof (updateTrackedNonce_same_or_one_added msg suid froms cs)
    end.

    split_ors; split_ex.
    rewrite H12; eauto.
    rewrite H15; eauto.

  - simpl in H11; split_ors.
    + generalize (eq_sigT_fst H11); intros; subst.
      apply inj_pair2 in H11; subst.
      unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in H12;
        rewrite andb_true_iff in H12; split_ands.
      unfold updateTrackedNonce.
      destruct c0; try discriminate.
      cases (cs $? c_id0); try discriminate.
      cases (cipher_to_user c0 ==n cipher_to_user x0); try discriminate.
      rewrite e.
      destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.

      unfold msg_nonce_same in H13.
      assert (cipher_nonce x0 = cipher_nonce c0) as EQ by eauto.
      rewrite EQ.

      cases (count_occ msg_seq_eq froms (cipher_nonce c0)); eauto.
      assert (count_occ msg_seq_eq froms (cipher_nonce c0) > 0) by (rewrite Heq0; apply gt_Sn_O); eauto.
      rewrite <- count_occ_In in H14; eauto.

    + right.
      eexists; split; eauto; simpl.
      split; eauto.

Qed.

Lemma adv_message_queue_ok_msg_recv_drop' :
  forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
    usrs $? u_id =
    Some
      {|
        key_heap := ks;
        protocol := cmd;
        msg_heap := existT _ _ msg :: qmsgs;
        c_heap := mycs;
        from_nons := froms;
        sent_nons := sents;
        cur_nonce := cur_n |}
    -> adv_message_queue_ok usrs cs gks adv_msgs
    -> msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg = false
    -> adv_message_queue_ok
        (usrs $+ (u_id,
                  {|
                    key_heap := ks;
                    protocol := cmd';
                    msg_heap := qmsgs;
                    c_heap := mycs;
                    from_nons := froms;
                    sent_nons := sents;
                    cur_nonce := cur_n |})) cs gks adv_msgs.
Proof.
  unfold adv_message_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H0 _ H2); destruct x; simpl in *.
  autorewrite with find_user_keys.
  split_ands; repeat (apply conj); eauto; intros.

  specialize (H5 _ H6).
  split_ex.
  eexists; split; eauto.
  split_ors; eauto.
  split_ex; right.
  split; trivial.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0);
    subst; clean_map_lookups;
      simpl in *;
      do 3 eexists; process_predicate; eauto; simpl.

  simpl in H12; split_ors.
  - generalize (eq_sigT_fst H12); intros; subst.
    apply inj_pair2 in H12; subst.
    unfold msg_signed_addressed in *.
    rewrite andb_true_iff in H13; split_ands.
    unfold msg_honestly_signed, msg_signing_key, honest_keyb, msg_to_this_user, msg_destination_user in *;
      destruct c0; try discriminate;
        cases (cs $? c_id0); try discriminate;
          cases (findUserKeys usrs $? cipher_signing_key c0); try discriminate;
            destruct b; try discriminate;
              cases (cipher_to_user c0 ==n cipher_to_user x0); try discriminate.

  - right; eexists; split; eauto.
    simpl; split; eauto.

Qed.

Hint Resolve
     adv_message_queue_ok_msg_recv_drop
     adv_message_queue_ok_msg_recv_drop'
  : core.

Lemma adv_message_queue_ok_msg_adv_send :
  forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
    usrs $? u_id =
    Some
      {|
        key_heap := ks;
        protocol := cmd;
        msg_heap := qmsgs;
        c_heap := mycs;
        from_nons := froms;
        sent_nons := sents;
        cur_nonce := cur_n |}
    -> adv_message_queue_ok usrs cs gks adv_msgs
    -> adv_message_queue_ok
        (usrs $+ (u_id,
                  {|
                    key_heap := ks;
                    protocol := cmd';
                    msg_heap := qmsgs ++ [existT _ _ msg];
                    c_heap := mycs;
                    from_nons := froms;
                    sent_nons := sents;
                    cur_nonce := cur_n |})) cs gks adv_msgs.
Proof.
  unfold adv_message_queue_ok; intros.
  rewrite Forall_forall in *; intros.
  specialize (H0 _ H1); destruct x; simpl in *.
  autorewrite with find_user_keys.
  split_ands; repeat (apply conj); eauto; intros.

  specialize (H4 _ H5).
  split_ex.
  eexists; split; eauto.
  split_ors; eauto.
  split_ex; right.
  split; trivial.
  destruct (u_id ==n x1);
    destruct (u_id ==n cipher_to_user x0);
    subst; clean_map_lookups;
      simpl in *;
      do 3 eexists; process_predicate; eauto; simpl.
Qed.

Hint Resolve adv_message_queue_ok_msg_adv_send : core.

Lemma honest_silent_step_adv_message_queue_ok :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok usrs'' cs' gks' adv'.(msg_heap).
Proof.
  induction 1; inversion 2; inversion 7; intros; subst; try discriminate;
    eauto 2; autorewrite with find_user_keys; eauto; clean_context.

  (* From RecvDrop rule *)
  (* - cases (msg_signed_addressed (findUserKeys usrs') cs' (Some u_id) msg); eauto. *)

  - user_cipher_queues_prop.
    encrypted_ciphers_prop.
    unfold adv_message_queue_ok in *;
      rewrite Forall_forall in *; intros.
    specialize (H26 _ H4); destruct x;
      split_ands; repeat (apply conj); eauto; intros; eauto.

    +  specialize (H8 _ _ H11); autorewrite with find_user_keys; split_ands;
         split; intros; eauto.
       specialize (H13 H18); unfold not; intros.
       apply merge_perms_split in H19; split_ors; try contradiction; subst.
       specialize (H17 _ _ H19); split_ands; subst; eauto.
    + specialize (H10 _ H11); split_ex; split_ands;
        eexists; split; eauto; intros.
      split_ors; split_ex; split_ands; autorewrite with find_user_keys; eauto.
      right.
      split.
      rewrite cipher_honestly_signed_after_msg_keys; eauto.
      destruct (u_id ==n x1);
        destruct (u_id ==n cipher_to_user x0);
        subst; clean_map_lookups;
          do 3 eexists;
          process_predicate; eauto; simpl.
      * right; eexists; split; eauto; simpl; eauto.
      * right; eexists; split; eauto; simpl; eauto.
      * right; eexists; split; eauto; simpl; eauto.
Qed.

Lemma adv_step_adv_message_queue_ok :
  forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl None bd bd'
    -> forall (cmd : user_cmd C) honestk,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> honestk = findUserKeys usrs
      -> ks = adv.(key_heap)
      -> qmsgs = adv.(msg_heap)
      -> encrypted_ciphers_ok honestk cs gks
      -> adv_message_queue_ok usrs cs gks qmsgs
      -> forall cmd' honestk',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> honestk' = findUserKeys usrs'
          -> adv_message_queue_ok usrs' cs' gks' qmsgs'.
Proof.
  induction 1; inversion 1; inversion 6; intros; subst;
    eauto 2; try discriminate; eauto;
      clean_context;
      autorewrite with find_user_keys;
      try invert_adv_msg_queue_ok; eauto.

  destruct rec_u; simpl; eauto.
Qed.


Lemma honest_labeled_step_adv_message_queue_ok :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok usrs'' cs' gks' adv'.(msg_heap).
Proof.
  induction 1; inversion 2; inversion 7; intros; subst; try discriminate;
    eauto 2; autorewrite with find_user_keys; eauto;
      clean_context;
      eauto 8. 

  unfold adv_message_queue_ok in *;
    rewrite Forall_forall in *; intros.
  apply in_app_or in H6; simpl in H6; split_ors; subst; try contradiction.
  - specialize (H25 _ H6); destruct x; intuition (split_ex; split_ands; subst; eauto);
      repeat
        match goal with
        | [ H : (forall k v, findKeysCrypto ?cs ?c $? k = Some v -> _ ), ARG : findKeysCrypto ?cs ?c $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG)
        | [ H : (forall c_id, List.In c_id ?lst -> _), ARG : List.In _ ?lst |- _ ] =>
          specialize (H _ ARG)
        end; split_ex; eauto.

    + destruct (rec_u_id ==n u_id); subst; try rewrite map_add_eq in H15;
        autorewrite with find_user_keys in *; eauto.
    + eexists; split; eauto.
      split_ors; autorewrite with find_user_keys; eauto.
      
      right.
      destruct (x3 ==n u_id);
        subst; clean_map_lookups; simpl in *; eauto; split; trivial.

      * destruct (cipher_to_user x1 ==n cipher_to_user x2); clean_map_lookups;
          do 3 eexists; process_predicate.
      * destruct (cipher_to_user x1 ==n x3);
          destruct (u_id ==n cipher_to_user x2);
          destruct (rec_u_id ==n cipher_to_user x2);
          subst; clean_map_lookups;
            do 3 eexists; process_predicate; eauto.

  - autorewrite with find_user_keys; simpl.
    clear H25.
    split_ex; subst; simpl in *.
    repeat (apply conj); intros;
      clean_context;
      clean_map_lookups; eauto.

    + context_map_rewrites.
      destruct x1; clean_map_lookups.
      specialize (H0 _ _ H5);
        split_ors; split_ands; subst;
          keys_and_permissions_prop;
          eauto.

      * specialize (H13 _ _ H0); split_ex; split; intros; clean_map_lookups; subst; eauto.
        assert (List.In x0 mycs') by eauto.
        user_cipher_queues_prop.
        encrypted_ciphers_prop.
        unfold not; intros; eauto.
        specialize (H28 _ _ H5); split_ex; discriminate.

      * specialize (H13 _ _ H0); split_ex; split; intros; clean_map_lookups; eauto.

    + context_map_rewrites; clean_context.
      assert (List.In x0 mycs') by eauto.
      user_cipher_queues_prop.
      unfold cipher_honestly_signed in H10.
      encrypted_ciphers_prop; simpl; clean_map_lookups.

    + split_ors; subst; try contradiction;
        context_map_rewrites.

      eexists; split; eauto.
      right; split.

      unfold cipher_honestly_signed.
      unfold msg_honestly_signed in H
      ; simpl in H
      ; context_map_rewrites
      ; destruct x1
      ; eauto.

      do 3 eexists.
      split; eauto.

      split; clean_map_lookups; eauto.
      unfold msg_to_this_user, msg_destination_user in H4;
        context_map_rewrites.
      cases (cipher_to_user x1 ==n rec_u_id); try discriminate.

      split.
      rewrite e; eauto.

      simpl.
      destruct (rec_u_id ==n cipher_to_user x1); try congruence.

      split; eauto.
      assert (u_id <> cipher_to_user x1).
      rewrite e.
      eauto.
      split; clean_map_lookups; eauto.
      simpl.
      right.
      rewrite Exists_exists.
      match goal with
      | [ |- exists x, List.In x (?msgs ++ [?msg]) /\ _ ] =>
        exists msg
      end.

      rewrite in_app_iff; simpl; split; eauto.
      unfold msg_signed_addressed; rewrite andb_true_iff;
        repeat (apply conj); subst; eauto.

      unfold msg_to_this_user, msg_destination_user
      ; context_map_rewrites.
      destruct (cipher_to_user x1 ==n cipher_to_user x1)
      ; try contradiction; eauto.
      
      unfold msg_nonce_same; intros.
      invert H4; clean_map_lookups; trivial.

      Unshelve.
      all: auto.
Qed.

    Lemma adv_message_queue_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs gks msgs,
        adv_message_queue_ok usrs cs gks msgs
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok
            (clean_users honestk cs usrs)
            (clean_ciphers honestk cs)
            (clean_keys honestk gks)
            (clean_adv_msgs honestk cs msgs).
    Proof.
      unfold adv_message_queue_ok; intros; subst.
      rewrite Forall_forall in *; intros.
      apply filter_In in H0; split_ands; destruct x.
      specialize (H _ H0); simpl in *; split_ands.

      repeat (apply conj); intros;
        repeat
          match goal with
          | [ H : (forall cid, msg_cipher_id ?c = Some cid -> _), ARG : msg_cipher_id ?c = Some _ |- _ ] =>
            specialize (H _ ARG)
          | [ H : (forall k kp, findKeysCrypto ?cs ?c $? k = Some kp -> _), ARG : findKeysCrypto ?cs ?c $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG)
          | [ H : (forall cid, List.In cid ?c -> _), ARG : List.In _ ?c |- _ ] => specialize (H _ ARG)
          | [ H : msg_filter _ _ _ _ _ = _ |- _ ] => unfold msg_filter,msg_honestly_signed in H
          | [ H : match ?arg with _ => _ end = _ |- _ ] => cases arg; try discriminate
          | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] =>
            unfold msg_signed_addressed in H; apply andb_prop in H; split_ands
          end; unfold msg_honestly_signed, msg_signing_key, msg_cipher_id in *; destruct c; try discriminate;
          clean_context.

      - unfold not; intros.
        cases (cs $? cid); try contradiction; clean_context.
        apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; eauto;
          contra_map_lookup.

      - unfold findKeysCrypto in *.
        cases (cs $? c_id); try discriminate.
        cases (clean_ciphers (findUserKeys usrs) cs $? c_id); clean_map_lookups.
        apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; contra_map_lookup; eauto.
        destruct c0; clean_map_lookups; specialize_msg_ok.
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq; split_ands.
        encrypted_ciphers_prop.
        destruct kp;
          match goal with
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _] =>
            specialize (H _ _ ARG)
          end; try contradiction; intuition eauto; try discriminate.
        cases (gks $? k); try contradiction.
        apply clean_keys_keeps_honest_key with (honestk := findUserKeys usrs) in Heq; eauto; contra_map_lookup.

      - cases (cs $? c_id); try discriminate.
        cases ( clean_ciphers (findUserKeys usrs) cs $? c_id ); try discriminate; clean_context.
        eapply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; eauto; clean_map_lookups.
        unfold not; intros.
        assert (gks $? cipher_signing_key c0 <> None) by eauto.
        cases (gks $? cipher_signing_key c0); try contradiction.
        eapply clean_keys_keeps_honest_key with (honestk := findUserKeys usrs) in Heq0; eauto; contra_map_lookup.

      - unfold msg_filter, msg_honestly_signed in *.
        split_ex; split_ands.
        simpl in H6; split_ors; split_ex; split_ands;
          subst; try contradiction; context_map_rewrites;
            eexists; split; eauto.

        + left.
          rewrite cipher_honestly_signed_honest_keyb_iff in *;
            unfold honest_keyb in *.
          cases (findUserKeys usrs $? cipher_signing_key x); try discriminate; destruct b; try discriminate.
          
        + right; split.
          rewrite cipher_honestly_signed_honest_keyb_iff in *;
            unfold honest_keyb in *.
          cases (findUserKeys usrs $? cipher_signing_key x); try discriminate; destruct b; try discriminate.
          pose proof (findUserKeys_clean_users_correct usrs cs (cipher_signing_key x)).
          context_map_rewrites; trivial.

          do 3 eexists; split; eauto.
          split.
          eapply clean_users_cleans_user; eauto.
          split; eauto.
          simpl; split; eauto.
          split.
          eapply clean_users_cleans_user; eauto.
          simpl.

          assert (
              {List.In (cipher_nonce x) (from_nons x2)} + {~ List.In (cipher_nonce x) (from_nons x2)}).
          apply in_dec; eauto using msg_seq_eq.

          destruct H6; eauto.
          split_ors; try contradiction.

          right; rewrite Exists_exists in *.
          split_ex; destruct x3.

          split_ands.
          eapply list_in_msgs_list_in_cleaned_msgs_not_in_froms
            with (honestk := findUserKeys usrs) (honestk' := findUserKeys (clean_users (findUserKeys usrs) cs usrs)) in H6; eauto.
          split_ex; eexists; split; eauto.
          simpl; eauto 9.
    Qed.



(* adv cipher queue ok *)

Lemma honest_labeled_step_adv_cipher_queue_ok :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> message_queues_ok cs usrs gks
        -> honest_nonces_ok cs usrs
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_cipher_queue_ok cs usrs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> adv_cipher_queue_ok cs' usrs'' adv'.(c_heap).
Proof.
  induction 1; inversion 2; inversion 8; intros; subst; try discriminate;
    eauto 2; autorewrite with find_user_keys; eauto;
      clean_context;
      unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.

  - specialize (H27 _ H1); split_ex.
    eexists; repeat simple apply conj; eauto.
    autorewrite with find_user_keys; split_ors; split_ex; subst; eauto.
    + left; eauto.
      assert (@msg_honestly_signed (findUserKeys usrs') t0 cs' (SignedCiphertext x0) = true ) by eauto.
      msg_queue_prop; context_map_rewrites; destruct x1; eauto.
      simpl in *; context_map_rewrites; simpl in *.
      specialize (H11 _ eq_refl); split_ex.
      unfold msg_honestly_signed, msg_signing_key in H0; context_map_rewrites;
        simpl in H0.
      rewrite <- honest_key_honest_keyb in H0.
      specialize (H12 H0); split_ands.

      rewrite cipher_honestly_signed_honest_keyb_iff in *;
        unfold honest_keyb in *.
      unfold message_no_adv_private in H12; simpl in H12; context_map_rewrites.
      cases (findKeysMessage msg $? cipher_signing_key x2).
      * specialize (H12 _ _ Heq); split_ands; subst; context_map_rewrites; discriminate.
      * cases (findUserKeys usrs' $? cipher_signing_key x2); solve_perm_merges;
          eauto.

    + right; split.
      rewrite cipher_honestly_signed_after_msg_keys; eauto.
      destruct (u_id ==n x3);
        [|destruct (u_id ==n cipher_to_user x2)];
        subst; clean_map_lookups; simpl in *;
          do 3 eexists;
          process_predicate; eauto; simpl.

      * right.
        eexists.
        split; eauto.
        simpl.
        context_map_rewrites; destruct x1; eauto.

      * context_map_rewrites.
        destruct (cipher_to_user x2 ==n cipher_to_user x1); eauto.
        rewrite count_occ_not_In in H4; rewrite H4; eauto.
      * context_map_rewrites.
        destruct (cipher_to_user x2 ==n cipher_to_user x1); eauto.
        ** rewrite count_occ_not_In in H4; rewrite H4; eauto.
           eapply in_elt_inv in H0; split_ors.
           *** generalize (eq_sigT_fst H0); intros; subst.
               apply inj_pair2 in H0; subst.
               hnf in H13.
               assert (cipher_nonce x2 = cipher_nonce x1) as EQ by eauto.
               rewrite EQ; eauto.
           *** right; eexists; split; eauto.
               simpl; split; eauto.
               destruct x1; eauto.

        ** eapply in_elt_inv in H0; split_ors.
           *** generalize (eq_sigT_fst H0); intros; subst.
               apply inj_pair2 in H0; subst.
               unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H13;
                 context_map_rewrites;
                 rewrite andb_true_iff in H13;
                 split_ands.
               destruct (cipher_to_user x1 ==n cipher_to_user x2); try discriminate.
               congruence.

           *** right; eexists; split; eauto.
               simpl; split; eauto.
               destruct x1; eauto.

      * right; eexists; split; eauto.
        simpl; context_map_rewrites.
        destruct x1; eauto.

  - specialize (H26 _ H6); split_ex.
    eexists; split; eauto.
    autorewrite with find_user_keys; split_ors; eauto.
    right; subst; simpl in *.

    process_predicate.
    clean_context.
    symmetry in e; subst.
    assert (u_id <> cipher_to_user x1) by eauto; clear H3.

    destruct (cipher_to_user x1 ==n cipher_to_user x2);
      destruct (cipher_to_user x1 ==n x3);
      destruct (u_id ==n x3);
      destruct (u_id ==n cipher_to_user x2);
      subst;
      try contradiction;
      clean_map_lookups;
      do 3 eexists;
      process_predicate; eauto.
Qed.


