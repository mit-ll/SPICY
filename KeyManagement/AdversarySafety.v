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
     Program.Equality (* for dependent induction *)
.

From Coq Require Classical_Prop.

From KeyManagement Require Import
     MyPrelude
     Maps
     Common
     Keys
     Tactics
     Messages
     MessageEq
     MessageEqTheory
     Automation
     Simulation
     AdversaryUniverse
     CipherTheory
     KeysTheory
     MessagesTheory
     UsersTheory
     InvariantsTheory
     SafetyAutomation
     SyntacticallySafe
.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Import SafetyAutomation.

Section UniverseLemmas.
  Import RealWorld.

  Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd (Base B)) :=
    {| users       := U__r.(users)
     ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                       ; msg_heap := U__r.(adversary).(msg_heap)
                       ; protocol := advcode
                       ; c_heap   := U__r.(adversary).(c_heap)
                       ; from_nons := U__r.(adversary).(from_nons)
                       ; sent_nons := U__r.(adversary).(sent_nons)
                       ; cur_nonce := U__r.(adversary).(cur_nonce) |}
     ; all_ciphers := U__r.(all_ciphers)
     ; all_keys    := U__r.(all_keys)
    |}.

  Lemma adv_no_honest_keys_after_honestk_no_private_key_msg :
    forall {t} (msg : crypto t) honestk cs advk,
      adv_no_honest_keys honestk advk
      -> (forall (k_id : NatMap.Map.key) (kp : bool), findKeysCrypto cs msg $? k_id = Some kp -> kp = false)
      -> adv_no_honest_keys (honestk $k++ findKeysCrypto cs msg) advk.
  Proof.
    unfold adv_no_honest_keys; intros; eauto;
      match goal with
      | [ kid : ?T, H : forall _ : ?T, _ \/ _ |- _ ] => specialize (H kid)
      end;
        split_ors; intuition idtac;
        cases (findKeysCrypto cs msg $? k_id);
        try match goal with
            | [ H1 : findKeysCrypto _ _ $? ?k_id = Some ?kp
              , H2 : forall k p, _ |- _ ] => specialize (H2 _ _ H1)
            end;
        subst; solve_perm_merges; auto.
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

  Hint Resolve permission_heap_good_clean_keys.

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

  (* Step user cipher queues ok *)

  Lemma findUserKeys_keys_mine_user :
    forall {A} (usrs : honest_users A) msgk u_id ks qmsgs cmd mycs froms sents cur_n,
      keys_mine ks msgk
      -> usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> keys_mine (findUserKeys usrs) msgk.
  Proof.
    unfold keys_mine; intros.
    specialize (H _ _ H1); split_ors; split_ands; subst; eauto.
    cases kp; subst; eauto.
    assert (findUserKeys usrs $? k_id <> None); eauto.
    cases (findUserKeys usrs $? k_id); clean_map_lookups; try contradiction.
    cases b; eauto.
  Qed.

  Hint Resolve findUserKeys_keys_mine_user.

  Lemma merge_keys_mine :
    forall ks1 ks2,
      keys_mine ks1 ks2
      -> ks1 $k++ ks2 = ks1.
  Proof.
    unfold keys_mine; intros.
    apply map_eq_Equal; unfold Equal; intros.
    solve_perm_merges;
      try match goal with
          | [ H : (forall kid kp, ?ks2 $? kid = Some kp -> _), H1 : ?ks2 $? _ = Some _ |- _ ] =>
            specialize (H _ _ H1); split_ors; split_ands; subst; clean_map_lookups
          end; solve_perm_merges; eauto.
  Qed.

  Lemma adv_cipher_in_cipher_heap :
    forall {A t} (msg : crypto t) (usrs : honest_users A) adv_heap cs cid,
      incl (findCiphers msg) adv_heap
      -> adv_cipher_queue_ok cs usrs adv_heap
      -> msg_cipher_id msg = Some cid
      -> exists c, cs $? cid = Some c.
  Proof.
    intros.
    unfold msg_cipher_id, adv_cipher_queue_ok in *.
    rewrite Forall_forall in H0.
    destruct msg; try discriminate;
      invert H1;
      simpl in *;
      assert (List.In cid adv_heap) as LIN by eauto;
      specialize (H0 _ LIN);
      split_ex; split_ands; eauto.
  Qed.

  Lemma cipher_honestly_signed_false_addnl_honest_key :
    forall honestk c k_id (gks : keys),
      ~ In k_id gks
      -> (forall k, cipher_signing_key c = k -> gks $? k <> None)
      -> cipher_honestly_signed honestk c = false
      -> cipher_honestly_signed (honestk $+ (k_id, true)) c = false.

  Proof.
    intros.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    unfold honest_keyb in *.
    destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups; eauto.

    exfalso.
    assert (gks $? cipher_signing_key c <> None) by eauto.
    contradiction.
  Qed.

  Hint Resolve cipher_honestly_signed_false_addnl_honest_key.



  (* Step adv no honest keys *)

  Lemma users_permission_heaps_good_merged_permission_heaps_good :
    forall {A} (usrs : honest_users A) gks,
      Forall_natmap (fun u : user_data A => permission_heap_good gks (key_heap u)) usrs
      -> permission_heap_good gks (findUserKeys usrs).
  Proof.
    induction usrs using P.map_induction_bis; intros; Equal_eq; eauto.
  Qed.

  Hint Resolve users_permission_heaps_good_merged_permission_heaps_good.

End UniverseLemmas.

Section SingleAdversarySimulates.

  (* If we have a simulation proof, we know that:
   *   1) No receives could have accepted spoofable messages
   *   2) Sends we either of un-spoofable, or were 'public' and are safely ignored
   *
   * This should mean we can write some lemmas that say we can:
   *   safely ignore all adversary messages (wipe them from the universe) -- Adam's suggestion, I am not exactly sure how...
   *   or, prove an appended simulation relation, but I am not sure how to generically express this
   *)
  Hint Resolve accepted_safe_msg_pattern_honestly_signed.
  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Section RealWorldLemmas.
    Import RealWorld.

    Lemma univ_components :
      forall {A B} (U__r : universe A B),
        {| users       := users U__r
         ; adversary   := adversary U__r
         ; all_ciphers := all_ciphers U__r
         ; all_keys    := all_keys U__r
        |} = U__r.
      intros. destruct U__r; simpl; trivial.
    Qed.

    Lemma adduserkeys_keys_idempotent :
      forall {A} (us : user_list (user_data A)) ks uid ud,
        us $? uid = Some ud
        -> exists ud', addUsersKeys us ks $? uid = Some ud'.
    Proof.
      intros.
      (* eexists. *)
      unfold addUsersKeys, addUserKeys.
      apply find_mapsto_iff in H.
      eexists.
      rewrite <- find_mapsto_iff.
      rewrite map_mapsto_iff.
      eexists; intuition. eassumption.
    Qed.


    Lemma honest_heap_private_honestk :
      forall {A} k_id ks u_id (usrs : honest_users A),
        ks $? k_id = Some true
        -> user_keys usrs u_id = Some ks
        -> honest_key (findUserKeys usrs) k_id.
    Proof.
      intros.
      constructor.
      unfold user_keys in *; cases (usrs $? u_id); subst; clean_map_lookups.
      eapply findUserKeys_has_private_key_of_user; eauto.
    Qed.

    Lemma adv_key_not_honestk :
      forall k_id honestk advk,
        advk $? k_id = Some true
        -> adv_no_honest_keys honestk advk
        -> honest_keyb honestk k_id = false.
    Proof.
      unfold adv_no_honest_keys, honest_keyb; intros.
      specialize (H0 k_id); split_ors; split_ands;
        context_map_rewrites; auto;
          contradiction.
    Qed.

    Hint Resolve
         honest_heap_private_honestk
         honest_key_not_cleaned
         adv_key_not_honestk.

    Lemma user_cipher_queue_cleaned_users_nochange :
      forall {A} (usrs : honest_users A) honestk cs u_id,
        user_cipher_queue (clean_users honestk cs usrs) u_id
        = user_cipher_queue usrs u_id.
    Proof.
      unfold user_cipher_queue, clean_users; simpl; intros.
      rewrite mapi_o; intros; subst; auto; unfold option_map; simpl.
      cases (usrs $? u_id); auto.
    Qed.

    Lemma user_in_univ_user_in_stripped_univ :
      forall {A B} (U : universe A B) u_id user_data user_data',
        U.(users) $? u_id = Some user_data
        -> user_data' =
            {| key_heap := clean_key_permissions (findUserKeys U.(users)) user_data.(key_heap)
             ; protocol := user_data.(protocol)
             ; msg_heap := clean_messages (findUserKeys U.(users)) U.(all_ciphers) (Some u_id) user_data.(from_nons) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap)
             ; from_nons := user_data.(from_nons)
             ; sent_nons := user_data.(sent_nons)
             ; cur_nonce := user_data.(cur_nonce) |}
        -> (strip_adversary U).(s_users) $? u_id = Some user_data'.
    Proof.
      unfold strip_adversary, clean_users; destruct user_data; simpl; intros.
      rewrite <- find_mapsto_iff in H.
      rewrite <- find_mapsto_iff, mapi_mapsto_iff; intros;
        subst; auto; eexists; subst; simpl; intuition eauto.
      simpl; trivial.
    Qed.

    Hint Resolve user_in_univ_user_in_stripped_univ.

    Lemma prop_in_adv_message_queues_still_good_after_cleaning :
      forall msgs honestk cs suid froms P,
        Forall P msgs
        -> Forall P (clean_messages honestk cs suid froms msgs).
    Proof.
      induction msgs; intros; eauto.
      invert H.
      unfold clean_messages, clean_messages'; simpl.
      unfold msg_filter at 2; destruct a.
      destruct (msg_signed_addressed honestk cs suid c); eauto; simpl.
      cases (msg_nonce_ok cs froms c); eauto.
      rewrite fold_clean_messages2'.
      rewrite clean_messages'_fst_pull; eauto.
    Qed.

    Hint Resolve prop_in_adv_message_queues_still_good_after_cleaning.

    Hint Resolve honest_cipher_filter_fn_true_honest_signing_key.
    Hint Extern 1 (honest_key _ _) => process_keys_messages.
    Hint Resolve
         msg_honestly_signed_after_without_cleaning
         msg_honestly_signed_before_after_cleaning.
                                               
    Lemma msgCiphersSigned_before_clean_ciphers' :
      forall (msgs : queued_messages) honestk cs,
        Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk (clean_ciphers honestk cs) m = true end) msgs
        -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs.
    Proof.
      induction 1; econstructor; eauto.
      destruct x; intuition eauto.
    Qed.

    Hint Resolve clean_ciphers_keeps_honest_cipher.

    Lemma msgCiphersSigned_after_clean_ciphers' :
      forall (msgs : queued_messages) honestk honestk' cs,
        Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk' (clean_ciphers honestk cs) m = true end) msgs.
    Proof.
      induction 1; econstructor; eauto.
      destruct x.
      eapply msg_honestly_signed_before_after_cleaning in H.
      unfold msg_honestly_signed in *.
      cases ( msg_signing_key (clean_ciphers honestk cs) c ); try discriminate.
      unfold honest_keyb in *.
      cases (honestk $? k); try discriminate; destruct b; try discriminate.
      specialize (H1 _ Heq0); rewrite H1; trivial.
    Qed.

    Lemma msgCiphersSigned_after_clean_ciphers :
      forall {t} (msg : crypto t) honestk honestk' cs,
        msgCiphersSignedOk honestk cs msg
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> msgCiphersSignedOk honestk' (clean_ciphers honestk cs) msg.
    Proof.
      intros; eapply msgCiphersSigned_after_clean_ciphers'; eauto.
    Qed.

    Lemma msgCiphersSigned_before_clean_ciphers :
      forall {t} (msg : crypto t) honestk cs,
        msgCiphersSignedOk honestk (clean_ciphers honestk cs) msg
        -> msgCiphersSignedOk honestk cs msg.
    Proof.
      intros; eapply msgCiphersSigned_before_clean_ciphers'; eauto.
    Qed.

    Hint Resolve
         msgCiphersSigned_after_clean_ciphers
         clean_keys_keeps_honest_key.

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

      - econstructor; eauto using msgCiphersSigned_cleaned_honestk.
        intros * ARG; specialize (H11 _ _ ARG); split_ands; eauto.

      - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto using msgCiphersSigned_cleaned_honestk.
    Qed.

    Hint Resolve clean_ciphers_encrypted_ciphers_ok.

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) b,
          U__r = strip_adversary_univ U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      unfold universe_ok.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac; subst; simpl in *; eauto.
      eapply clean_ciphers_encrypted_ciphers_ok'; eauto using clean_users_no_change_honestk.
    Qed.

    Lemma user_cipher_queue_ok_after_cleaning :
      forall cs honestk honestk' mycs,
        user_cipher_queue_ok cs honestk mycs
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> user_cipher_queue_ok (clean_ciphers honestk cs) honestk' mycs.
    Proof.
      unfold user_cipher_queue_ok; intros; rewrite Forall_forall in *;
        intros.
      specialize (H _ H1); split_ex; split_ands.
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

    Lemma msg_honestly_signed_cipher_honestly_signed :
      forall {t} (msg : crypto t) honestk c cs cid,
        msg_honestly_signed honestk cs msg = true
        -> msg_cipher_id msg = Some cid
        -> cs $? cid = Some c
        (* -> msgCipherOk cs msg *)
        -> honest_keyb honestk (cipher_signing_key c) = true.
    Proof.
      intros.
      unfold msg_honestly_signed, msg_cipher_id in *;
        unfold cipher_signing_key;
        destruct msg; simpl in *; try discriminate; split_ex;
          invert H0;
          rewrite H1 in H;
          destruct c;
          try discriminate;
          eauto.
    Qed.

    Hint Resolve msg_honestly_signed_cipher_honestly_signed.

    Lemma findKeysCrypto_ok_clean_global_keys :
      forall {t} (msg : crypto t) cs gks honestk,
        (forall k kp, findKeysCrypto cs msg $? k = Some kp -> gks $? k <> None)
        -> message_no_adv_private honestk cs msg
        -> (forall k kp, findKeysCrypto cs msg $? k = Some kp -> clean_keys honestk gks $? k <> None).
    Proof.
      unfold message_no_adv_private; intros.
      specialize (H _ _ H1).
      specialize (H0 _ _ H1); split_ands; subst.
      cases (gks $? k); try contradiction.
      unfold not; intros.
      erewrite clean_keys_keeps_honest_key in H2; eauto.
    Qed.
    
    Hint Resolve findKeysCrypto_ok_clean_global_keys.

    Lemma msg_signing_key_same_after_cleaning :
      forall {t} (msg : crypto t) cs honestk k1 k2,
        msg_signing_key cs msg = Some k1
        -> msg_signing_key (clean_ciphers honestk cs) msg = Some k2
        -> k1 = k2.
    Proof.
      unfold msg_signing_key; intros.
      destruct msg; try discriminate.
      - cases (cs $? c_id); cases (clean_ciphers honestk cs $? c_id); try discriminate.
        rewrite <- find_mapsto_iff in Heq0;
          rewrite clean_ciphers_mapsto_iff in Heq0; rewrite find_mapsto_iff in Heq0;
          split_ands; clean_map_lookups.
        destruct c0; try discriminate; clean_context; trivial.
    Qed.

    Lemma clean_messages_list_in_safe :
      forall honestk cs suid sigM msgs froms,
        List.In sigM (clean_messages honestk cs suid froms msgs)
        -> List.In sigM msgs
          /\ match sigM with
            | existT _ _ msg => msg_signed_addressed honestk cs suid msg = true
            end.
    Proof.
      unfold clean_messages, clean_messages'; induction msgs; intros; simpl in H; try contradiction.
      unfold msg_filter at 2 in H.
      destruct a.
      cases (msg_signed_addressed honestk cs suid c).

      - simpl in H; cases (msg_nonce_ok cs froms c).
        + unfold msg_nonce_ok in Heq0; destruct c; try discriminate;
            cases (cs $? c_id); try discriminate;
              cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate;
                clean_context; eauto.

          rewrite !fold_clean_messages2' in *.
          rewrite clean_messages'_fst_pull in H; simpl in H.
          split_ors; subst; eauto.
          specialize (IHmsgs _ H); intuition eauto.
        + unfold msg_nonce_ok in Heq0; destruct c; try discriminate.
          specialize (IHmsgs _ H); intuition eauto.
      - specialize (IHmsgs _ H); intuition eauto.
    Qed.

    Lemma clean_adv_msgs_list_in_safe :
      forall honestk cs sigM msgs,
        List.In sigM (clean_adv_msgs honestk cs msgs)
        -> List.In sigM msgs
          /\ match sigM with
            | existT _ _ msg => msg_honestly_signed honestk cs msg = true
            end.
    Proof.
      unfold clean_adv_msgs; intros.
      apply filter_In in H; destruct sigM; auto.
    Qed.

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

        + eapply clean_keys_inv' in H11; eauto.
          unfold honest_key_filter_fn in *; invert H3; context_map_rewrites; discriminate.

        + unfold message_no_adv_private in *; intros; clean_context; simpl in *.
          context_map_rewrites; eapply clean_ciphers_keeps_honest_cipher in H6;
            eauto; context_map_rewrites.

          destruct c; clean_map_lookups.
          specialize (H9 _ _ H12); intuition eauto.
    Qed.

    Hint Resolve clean_users_no_change_honestk clean_users_no_change_honestk'.

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

    Hint Resolve
         msg_to_this_user_before_after_cleaning
         msg_to_this_user_false_before_after_cleaning.

    Ltac instantiate_cs_lkup :=
      match goal with 
      | [ H : forall c_id c, ?cs $? c_id = Some c -> _ |- _ ] =>
        match goal with
        | [ CS : cs $? _ = Some _ |- _ ] =>
          let INST := fresh "INST" in
          generalize (H _ _ CS); intro INST;
          let toh := type of INST in
          clear INST; match goal with
                      | [ OH : toh |- _ ] => fail 1
                      | _ => generalize (H _ _ CS); intro INST
                      end
        end
      end.

    Ltac instantiate_cs_lkup' :=
      match goal with 
      | [ H : forall c_id c, ?cs $? c_id = Some c -> _ |- _ ] =>
        match goal with
        | [ CS : cs $? _ = Some _ |- _ ] =>
          let INST := fresh "INST" in
          generalize (H _ _ CS); intro INST;
          let toh := type of INST in
          clear INST;
          (assert toh by (solve_simply; assumption); fail 1) || (generalize (H _ _ CS); intros)
        end
      end.

    Ltac instantiate_cs_lkup_uni :=
      match goal with 
      | [ H : forall c_id c, ?cs $? c_id = Some c -> _ |- _ ] =>
        let cid := fresh "cid" in
        let c := fresh "c" in
        evar (cid : cipher_id); evar (c : cipher);
        let cidsome := fresh "CS" in
        let cid' := eval unfold cid in cid in
        let c' := eval unfold c in c in
            clear cid; clear c; evar (cidsome : cs $? cid' = Some c');
        let cidsome' := eval unfold cidsome in cidsome in
            clear cidsome; specialize (H _ _ cidsome')
      end.
        
    Ltac process_nonce_ok1 :=
        match goal with
        | [ H : _ $+ (?uid1,_) $? ?uid2 = _ |- _ ] => destruct (uid1 ==n uid2); subst; clean_map_lookups; simpl
        | [ H : ?cs $? ?cid = _ |- context [ ?cs $? ?cid ] ] => rewrite H
        | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
        | [ H : ~ List.In ?cn ?lst |- context [ count_occ msg_seq_eq ?lst ?cn ] ] =>
          rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H; rewrite H
        | [ |- honest_nonce_tracking_ok _ _ _ _ _ (if ?cond then _ else _) _ ] => destruct cond; subst
        | [ H1 : msg_to_this_user _ _ _ = true, H2 : msg_to_this_user _ _ _ = false |- _ ] =>
          rewrite H1 in H2; invert H2
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some {|
                                     key_heap := _;
                                     protocol := _;
                                     msg_heap := ?qmsgs;
                                     c_heap := _;
                                     from_nons := ?froms;
                                     sent_nons := _;
                                     cur_nonce := _ |}
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ ?froms ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some {|
                                     key_heap := _;
                                     protocol := _;
                                     msg_heap := (_ :: ?qmsgs);
                                     c_heap := _;
                                     from_nons := ?froms;
                                     sent_nons := _;
                                     cur_nonce := _ |}
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ ?froms ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some {|
                                     key_heap := _;
                                     protocol := _;
                                     msg_heap := (_ :: ?qmsgs);
                                     c_heap := _;
                                     from_nons := ?froms;
                                     sent_nons := _;
                                     cur_nonce := _ |}
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ (_ :: ?froms) ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some ?rec_u
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ (from_nons ?rec_u) _ ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : honest_nonce_tracking_ok _ _ _ _ _ _ _ |- honest_nonce_tracking_ok _ _ _ _ _ _ _ ] =>
          unfold honest_nonce_tracking_ok in *; intros
        | [ H : ?arg -> _, ARG : ?arg |- _ ] =>
          match type of arg with
          | Type => fail 1
          | Set => fail 1
          | cipher_id => fail 1
          | user_id => fail 1
          | key_identifier => fail 1
          | nat => fail 1
          | NatMap.Map.key => fail 1
          | _ => specialize (H ARG)
          end
        | [ H : (?arg1 = ?arg2) -> _ |- _ ] => let EQ := fresh "EQ" in
                                            assert (arg1 = arg2) as EQ by solve [ trivial ]; specialize (H EQ)
        | [ H : Forall _ (_ :: _) |- _ ] => invert H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ H : List.In _ (_ :: _) |- _ ] => simpl in H; split_ors
        | [ H : ~ List.In _ (if ?cond then _ else _) |- _ ] => destruct cond; subst; simpl in H
        | [ H : ~ (_ \/ _) |- _ ] => apply Decidable.not_or in H; split_ands
        | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] => eapply accepted_safe_msg_pattern_to_this_user in H; eauto 2
        | [ CS : ?cs $? ?cid = Some ?c , MN : msg_nonce_not_same ?c1 ?cs (SignedCiphertext ?cid) |- _ ] =>
          assert (cipher_nonce c1 <> cipher_nonce c) by eauto; congruence
        | [ |- context [ Forall _ (_ ++ _) ] ] => rewrite Forall_app
        | [ H : msg_to_this_user ?cs ?suid ?msg = true
            |- msg_to_this_user ?cs ?suid ?msg = false \/ msg_nonce_not_same _ _ _ ] =>
          right; unfold msg_nonce_not_same; intros
        | [ |- Forall _ (_ :: _) ] => econstructor
        | [ CS : ?cs $? ?cid = None, IN : List.In ?cid ?cheap
          , USR : ?usrs $? _ = Some ?u, F : user_cipher_queues_ok ?cs _ ?usrs |- _ ] =>
          unify cheap (c_heap u); unfold user_cipher_queues_ok in F;
          rewrite Forall_natmap_forall in F; specialize (F _ _ USR)
        | [ CS : ?cs $? ?cid = None, IN : List.In ?cid ?cheap1
          , F : user_cipher_queue_ok ?cs _ ?cheap2 |- _ ] =>
          unify cheap1 cheap2; unfold user_cipher_queue_ok in F;
          rewrite Forall_forall in F; specialize (F _ IN); split_ex; split_ands; contra_map_lookup
        | [ |- _ -> _ ] => intros
        | [ |- _ /\ _ ] => split
        (* | [ |- ~ List.In _ (_ :: _) ] => simpl; apply Classical_Prop.and_not_or *)
        | [ |- ~ (_ \/ _) ] => apply Classical_Prop.and_not_or
        | [ H : msg_to_this_user _ _ _ = _ |- _ ] =>
          unfold msg_to_this_user, msg_destination_user in H; context_map_rewrites
        | [ H : (if ?cond then _ else _) = _ |- _ ] => destruct cond
        | [ |- Forall _ (if ?cond then _ else _) ] => destruct cond
        | [ IN : List.In (existT _ _ (SignedCiphertext ?cid)) ?msgs |- _ ] =>
          repeat msg_queue_prop;
          match goal with
          | [ MQOK : message_queue_ok _ ?cs msgs _ |- _ ] =>
            unfold message_queue_ok in MQOK; rewrite Forall_forall in MQOK;
            specialize (MQOK _ IN); simpl in MQOK; split_ands;
            assert (cs $? cid <> None) by eauto 2;
            match goal with
            | [ CS : cs $? cid = None |- _ ] => contradiction
            end
          end
        | [ H : _ \/ _ |- _ ] => destruct H
        end.

    Hint Extern 1 (message_queue_ok _ _ _ _) => eassumption || (msg_queue_prop; eassumption).

    Ltac process_nonce_ok :=
      repeat ( simpl in *; clean_map_lookups1 || congruence || discriminate || process_nonce_ok1 || instantiate_cs_lkup' || Nat.order).

    Ltac process_nonce_ok_with_single :=
      repeat ( clean_map_lookups1 || congruence || discriminate || process_nonce_ok1 ||
               match goal with
               | [ H : forall c_id c, ?cs $? c_id = Some c -> _
                 , CS : ?cs $? ?c_id = Some ?c
                   |- _ ] => specialize (H _ _ CS)
               end
             ).

    Lemma clean_ciphers_nochange_cipher :
      forall honestk cs c_id c,
        clean_ciphers honestk cs $? c_id = Some c
        -> cs $? c_id = Some c.
    Proof.
      intros.
      rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H;
        split_ands;
        trivial.
    Qed.

    Hint Resolve clean_ciphers_nochange_cipher.
    
    Lemma honest_nonce_tracking_ok_after_cleaning :
      forall honestk cs me my_sents my_non you your_froms your_msgs,
        honest_nonce_tracking_ok cs me my_sents my_non you your_froms your_msgs
        -> honest_nonce_tracking_ok (clean_ciphers honestk cs) me my_sents my_non
                            you your_froms
                            (clean_messages honestk cs (Some you) your_froms your_msgs).
    Proof.
      unfold honest_nonce_tracking_ok; intros; rewrite !Forall_forall in *; intros; split_ands.
      repeat (apply conj); intros; eauto.

      - destruct x; intros; subst.
        eapply clean_messages_list_in_safe in H3; split_ands.
        specialize (H1 _ H3); simpl in H1.
        eapply H1; eauto.

      - rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H3;
          split_ands.
        specialize (H2 _ _ H3 H4); intuition eauto.
        + rewrite Forall_forall in *; intros.
          eapply clean_messages_list_in_safe in H7; split_ands.
          specialize (H10 _ H7); destruct x.

          split_ors.
          * left; unfold msg_to_this_user, msg_destination_user in *;
              destruct c0; try discriminate.
            unfold msg_signed_addressed in H11; rewrite andb_true_iff in H11; split_ands.
            cases (cs $? c_id0); try discriminate; eauto.
            ** erewrite clean_ciphers_keeps_honest_cipher; eauto.
               unfold honest_cipher_filter_fn, cipher_honestly_signed, msg_honestly_signed, msg_signing_key in *;
                 context_map_rewrites; destruct c0; eauto.
            ** rewrite clean_ciphers_no_new_ciphers; eauto.
          
          * right; unfold msg_nonce_not_same in *; intros; eauto.
    Qed.

    Hint Resolve honest_nonce_tracking_ok_after_cleaning.

    Lemma honest_nonces_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        honest_nonces_ok cs usrs
        -> honestk = findUserKeys usrs
        -> honest_nonces_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs).
    Proof.
      unfold honest_nonces_ok; intros.
      eapply clean_users_cleans_user_inv with (honestk := honestk) in H2; split_ex; split_ands.
      eapply clean_users_cleans_user_inv with (honestk := honestk) in H3; split_ex; split_ands.
      rewrite H7.
      specialize (H _ _ _ _ H1 H2 H3); simpl in *; subst; split_ands; eauto.
    Qed.

    Lemma honest_labeled_step_honest_nonces_ok :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
            -> honestk = findUserKeys usrs
            -> encrypted_ciphers_ok honestk cs gks
            -> honest_nonces_ok cs usrs
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
                    -> honest_nonces_ok cs' usrs''.
    Proof.
      induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
        eauto;
        clean_context;
        split_ex; split_ands; subst;
          unfold honest_nonces_ok in *; intros;
            process_nonce_ok; eauto.
    Qed.

    Lemma honest_nonces_ok_newuser_nochange_froms_sents_msgs :
      forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms sents cur_n,
        honest_nonces_ok cs usrs
        -> usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> honest_nonces_ok cs
                           (usrs $+ (u_id,
                                     {|
                                       key_heap := ks;
                                       protocol := cmd';
                                       msg_heap := qmsgs;
                                       c_heap := mycs';
                                       from_nons := froms;
                                       sent_nons := sents;
                                       cur_nonce := cur_n |})).
    Proof.
      unfold honest_nonces_ok; intros;
        process_nonce_ok; eauto.
    Qed.

  Lemma nonce_not_in_msg_queue_addnl_cipher :
    forall new_cipher c_id c cs qmsgs honestk gks,
      ~ In c_id cs
      -> message_queue_ok honestk cs qmsgs gks
      -> Forall (fun sigM => match sigM with
                         | existT _ _ msg =>
                           msg_to_this_user cs (Some (cipher_to_user new_cipher)) msg = false
                           \/ msg_nonce_not_same new_cipher cs msg
                         end) qmsgs
      -> Forall (fun sigM => match sigM with
                         | existT _ _ msg =>
                           msg_to_this_user (cs $+ (c_id,c)) (Some (cipher_to_user new_cipher)) msg = false
                           \/ msg_nonce_not_same new_cipher (cs $+ (c_id,c)) msg
                         end) qmsgs.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    specialize (H1 _ H2); destruct x.
    split_ors.
    - left; unfold msg_to_this_user, msg_destination_user in *; destruct c0; trivial.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; auto.
      context_map_rewrites.
      unfold message_queue_ok in H0; rewrite Forall_forall in H0;
        specialize (H0 _ H2); simpl in H0; split_ands.
      assert (cs $? c_id0 <> None) by eauto; contradiction.
    - right; unfold msg_nonce_not_same in *; intros.
      destruct  (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      unfold message_queue_ok in H0; rewrite Forall_forall in H0;
        specialize (H0 _ H2); simpl in H0; split_ands.
      assert (cs $? c_id0 <> None) by eauto; contradiction.
  Qed.

  Hint Resolve nonce_not_in_msg_queue_addnl_cipher.
    
  Lemma honest_nonce_tracking_ok_new_msg :
    forall suid sents cur_n cs froms to_usr qmsgs msg,
        honest_nonce_tracking_ok cs suid sents cur_n to_usr froms (msg :: qmsgs)
      -> honest_nonce_tracking_ok cs suid sents cur_n to_usr froms qmsgs.
  Proof.
    unfold honest_nonce_tracking_ok; intros; process_nonce_ok.
  Qed.

  Hint Resolve
       honest_nonce_tracking_ok_new_msg.
  
  Lemma honest_nonces_ok_new_honest_key :
    forall {A} (usrs : honest_users A) k_id cs u_id ks cmd cmd' qmsgs mycs froms sents cur_n,
      honest_nonces_ok cs usrs
      -> usrs $? u_id =
        Some
          {|
            key_heap := ks;
            protocol := cmd;
            msg_heap := qmsgs;
            c_heap := mycs;
            from_nons := froms;
            sent_nons := sents;
            cur_nonce := cur_n |}
      -> honest_nonces_ok cs
                         (usrs $+ (u_id,
                                   {|
                                     key_heap := add_key_perm k_id true ks;
                                     protocol := cmd';
                                     msg_heap := qmsgs;
                                     c_heap := mycs;
                                     from_nons := froms;
                                     sent_nons := sents;
                                     cur_nonce := cur_n |})).
  Proof.
    unfold honest_nonces_ok; intros;
      process_nonce_ok; eauto.
  Qed.

  Hint Resolve
       honest_nonces_ok_newuser_nochange_froms_sents_msgs
       honest_nonces_ok_new_honest_key.

  Lemma sents_ok_increase_nonce :
    forall cur_n cur_n' (sents : sent_nonces),
      cur_n <= cur_n'
      -> Forall (fun non => snd non < cur_n) sents
      -> Forall (fun non => snd non < cur_n') sents.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    specialize (H0 _ H1); Nat.order.
  Qed.

  Lemma froms_ok_increase_nonce :
    forall cur_n cur_n' suid (froms : recv_nonces),
      cur_n <= cur_n'
      -> Forall (fun non => fst non = suid -> snd non < cur_n) froms
      -> Forall (fun non => fst non = suid -> snd non < cur_n') froms.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    specialize (H0 _ H1 H2); Nat.order.
  Qed.

  Lemma msg_queue_values_ok_new_cipher :
    forall cs c newcid newc to_usr honestk qmsgs gks,
      ~ In newcid cs
      -> message_queue_ok honestk cs qmsgs gks
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         msg_to_this_user cs to_usr msg = false
                                       \/ msg_nonce_not_same c cs msg end) qmsgs
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         msg_to_this_user (cs $+ (newcid,newc)) to_usr msg = false
                                       \/ msg_nonce_not_same c (cs $+ (newcid,newc)) msg end) qmsgs.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    specialize (H1 _ H2); destruct x; split_ors.
    - left; unfold msg_to_this_user, msg_destination_user in *;
        destruct c0; eauto;
          cases (cs $? c_id); eauto;
            destruct (newcid ==n c_id); subst; clean_map_lookups; context_map_rewrites; eauto.
      unfold message_queue_ok in H0; rewrite Forall_forall in H0;
        specialize (H0 _ H2); simpl in *; split_ands; context_map_rewrites.
      assert (cs $? c_id <> None) by eauto; contradiction.
    - right; unfold msg_nonce_not_same in *; intros.
      eapply H1; eauto.
      destruct (newcid ==n c_id); subst; clean_map_lookups; eauto.
      unfold message_queue_ok in H0; rewrite Forall_forall in H0;
        specialize (H0 _ H2); simpl in *; split_ands; context_map_rewrites.
      assert (cs $? c_id <> None) by eauto; contradiction.
  Qed.

  Lemma msg_queue_nonces_good_new_cipher :
    forall cs newcid newc to_usr from_usr cur_n cur_n' honestk qmsgs gks,
      ~ In newcid cs
      -> message_queue_ok honestk cs qmsgs gks
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         forall c_id c,
                                           msg = SignedCiphertext c_id
                                           -> cs $? c_id = Some c
                                           -> cipher_to_user c = to_usr
                                           -> fst (cipher_nonce c) = from_usr
                                           -> snd (cipher_nonce c) < cur_n end) qmsgs
      -> cur_n <= cur_n'
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         forall c_id c,
                                           msg = SignedCiphertext c_id
                                           -> cs $+ (newcid, newc) $? c_id = Some c
                                           -> cipher_to_user c = to_usr
                                           -> fst (cipher_nonce c) = from_usr
                                           -> snd (cipher_nonce c) < cur_n' end) qmsgs.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    destruct x; intros.
    destruct (newcid ==n c_id); subst; clean_map_lookups;
      process_nonce_ok; eauto.

    specialize (H1 _ H3); simpl in H1.
    assert (snd (cipher_nonce c0) < cur_n) by eauto.
    Nat.order.
  Qed.

  Hint Resolve
       msg_queue_nonces_good_new_cipher
       msg_queue_values_ok_new_cipher
       sents_ok_increase_nonce
       froms_ok_increase_nonce.

  Lemma nat_lt_nat_plus_one :
    forall n, n < n + 1.
  Proof.
    intros; rewrite Nat.add_1_r; eauto.
  Qed.

  Lemma nat_le_nat_plus_one :
    forall n, n <= n + 1.
  Proof.
    intros; rewrite Nat.add_1_r; eauto.
  Qed.

  Hint Resolve nat_lt_nat_plus_one nat_le_nat_plus_one.

  Lemma honest_silent_step_honest_nonces_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> honest_nonces_ok cs usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> honest_nonces_ok cs' usrs''.
  Proof.
    induction 1; inversion 2; inversion 5; intros; subst; try discriminate;
      eauto; clean_context;
        msg_queue_prop; process_nonce_ok; eauto.

    - cases (msg_signed_addressed (findUserKeys usrs') cs' (Some u_id) msg);
        unfold honest_nonces_ok in *; intros;
          process_nonce_ok; eauto.

      unfold updateTrackedNonce, msg_signed_addressed, msg_honestly_signed, msg_signing_key in *.
      destruct msg; try discriminate.
      cases (cs' $? c_id); try discriminate; simpl in *.
      destruct (rec_u_id ==n cipher_to_user c); subst;
        process_nonce_ok; eauto.

    - unfold honest_nonces_ok in *; intros;
        simpl in *; subst;
          process_nonce_ok; subst; eauto.

      + rewrite Forall_forall in H9; unfold not; intro LIN;
          specialize (H9 _ LIN); simpl in H9; process_nonce_ok.

      + rewrite Forall_forall; intros; destruct x.
        right; unfold msg_nonce_not_same; intros; subst; simpl.
        cases (c_id0 ==n c_id); subst; clean_map_lookups; simpl; process_nonce_ok.
        unfold not; intros; process_nonce_ok.
        rewrite <- H17 in H15; simpl in H15;
          process_nonce_ok.

    - unfold honest_nonces_ok in *; intros;
        process_nonce_ok; eauto.
    - unfold honest_nonces_ok in *; intros;
        process_nonce_ok; eauto.

      + rewrite Forall_forall in H7; unfold not; intro LIN; specialize (H7 _ LIN); simpl in H7;
          specialize (H7 eq_refl); Nat.order.

      + rewrite Forall_forall; intros; destruct x.
        right; unfold msg_nonce_not_same; intros; subst; simpl.
        cases (c_id0 ==n c_id); subst; clean_map_lookups; process_nonce_ok.
        unfold not; intros; process_nonce_ok.
        rewrite <- H14 in H10; simpl in H10;
          process_nonce_ok.
  Qed.

  Lemma honest_nonce_tracking_ok_new_adv_cipher :
    forall cs c_id c me my_sents my_n you your_froms your_msgs honestk gks,
      ~ In c_id cs
      -> message_queue_ok honestk cs your_msgs gks
      -> fst (cipher_nonce c) = None
      -> honest_nonce_tracking_ok cs (Some me) my_sents my_n you your_froms your_msgs
      -> honest_nonce_tracking_ok (cs $+ (c_id,c)) (Some me) my_sents my_n you your_froms your_msgs.
  Proof.
    unfold honest_nonce_tracking_ok; intros; split_ands;
      repeat (apply conj); eauto.

    intros.
    destruct (c_id ==n c_id0); subst; clean_map_lookups.
    - rewrite H1 in H7; invert H7.
    - specialize (H5 _ _ H6 H7); eauto; split_ands; split; eauto; intros.
      specialize (H8 H9 H10); split_ands; split; eauto.
  Qed.

  Lemma honest_nonces_ok_adv_new_cipher :
    forall {A} (usrs : honest_users A) cs c_id c gks,
      ~ In c_id cs
      -> message_queues_ok cs usrs gks
      -> fst (cipher_nonce c) = None
      -> honest_nonces_ok cs usrs
      -> honest_nonces_ok (cs $+ (c_id,c)) usrs.
  Proof.
    unfold honest_nonces_ok; intros.
    specialize (H2 _ _ _ _ H3 H4 H5).
    repeat msg_queue_prop.
    eapply honest_nonce_tracking_ok_new_adv_cipher; eauto.
  Qed.

  Hint Resolve honest_nonces_ok_adv_new_cipher.

  Lemma adv_step_honest_nonces_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' suid,
      step_user lbl suid bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> suid = None
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> froms = adv.(from_nons)
        -> sents = adv.(sent_nons)
        -> cur_n = adv.(cur_nonce)
        -> honest_nonces_ok cs usrs
        -> message_queues_ok cs usrs gks
        -> adv_cipher_queue_ok cs usrs mycs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> honest_nonces_ok cs' usrs'.
  Proof.
    induction 1; inversion 1; inversion 12; intros; subst;
      eauto;
      clean_context.
 
    unfold honest_nonces_ok in *; intros;
      process_nonce_ok; eauto.

    subst.

    unfold adv_cipher_queue_ok in H29;
      rewrite Forall_forall in H29.

    unfold msg_nonce_not_same; destruct msg.
    - right; intros; discriminate.
    - simpl in H1.
      assert (List.In c_id0 (c_heap adv)) as LIN by eauto.
      specialize (H29 _ LIN); split_ex; split_ands.
      unfold msg_to_this_user, msg_destination_user; context_map_rewrites.
      destruct (cipher_to_user x ==n cipher_to_user c); eauto.
      right; intros; process_nonce_ok.
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

        + left; split; eauto.
          rewrite cipher_honestly_signed_honest_keyb_iff in *;
            unfold honest_keyb in *.
          cases (findUserKeys usrs $? cipher_signing_key x); try discriminate; destruct b; try discriminate.
          
        + right; do 3 eexists; split; eauto.
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

    Lemma ok_adv_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : <<(Base B)>>),
          U__r = strip_adversary_univ U__ra b
        -> universe_ok U__ra
        -> adv_universe_ok U__ra
        -> adv_universe_ok U__r.
    Proof.
      unfold adv_universe_ok, universe_ok.
      intros.
      subst; unfold adv_universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        try rewrite clean_users_no_change_findUserKeys;
        subst; simpl in *;
          eauto using user_cipher_queues_ok_after_cleaning
                    , message_queues_ok_after_cleaning
                    , keys_and_permissions_good_clean_keys
                    , honest_nonces_ok_after_cleaning
                    (* , adv_message_queue_ok_after_cleaning *)
                    , adv_no_honest_keys_after_cleaning
                    , honest_users_only_honest_keys_after_cleaning.
      econstructor.
      
      apply adv_message_queue_ok_after_cleaning; eauto using clean_users_no_change_honestk.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         not_in_ciphers_not_in_cleaned_ciphers.

    Lemma cipher_message_keys_already_in_honest :
      forall {A t} (msg : message t) (usrs : honest_users A) honestk cs msg_to nonce c_id k__s k__e gks,
        honestk = findUserKeys usrs
        -> cs $? c_id = Some (SigEncCipher k__s k__e msg_to nonce msg) 
        -> honest_key honestk k__s
        -> honest_key honestk k__e
        -> encrypted_ciphers_ok honestk cs gks
        -> honestk $k++ findKeysMessage msg = honestk.
    Proof.
      intros.
      invert H1; invert H2.
      encrypted_ciphers_prop; eauto.
      rewrite merge_keys_addnl_honest; eauto.
    Qed.

    Ltac solve_clean_keys_clean_key_permissions :=
      match goal with
      | [  |- clean_keys ?honestk ?gks $? ?kid = Some _ ] =>
        match goal with
        | [ H : honestk $? kid = Some true |- _] => idtac
        | _ => assert (honestk $? kid = Some true) by eauto
        end
      | [  |- clean_key_permissions ?honestk ?gks $? ?kid = Some _ ] =>
        match goal with
        | [ H : honestk $? kid = Some true |- _] => idtac
        | _ => assert (honestk $? kid = Some true) by eauto
        end
      end;
      unfold clean_keys, clean_key_permissions;
      rewrite <- find_mapsto_iff, filter_iff; auto; rewrite find_mapsto_iff;
      unfold honest_key_filter_fn, honest_perm_filter_fn;
      intuition context_map_rewrites; eauto.

    Lemma clean_ciphers_new_honest_key_idempotent :
      forall honestk k_id cs gks,
        encrypted_ciphers_ok honestk cs gks
        -> ~ In k_id gks
        -> clean_ciphers (honestk $+ (k_id, true)) cs = clean_ciphers honestk cs.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (cs $? y).
      - case_eq (honest_cipher_filter_fn honestk y c); intros.
        + assert (honest_cipher_filter_fn honestk y c = true) as HCFF by assumption.
          unfold honest_cipher_filter_fn, cipher_honestly_signed in HCFF; encrypted_ciphers_prop;
            erewrite !clean_ciphers_keeps_honest_cipher; eauto.
        + assert (honest_cipher_filter_fn honestk y c = false) as HCFF by assumption.
          unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb in HCFF.
          encrypted_ciphers_prop;
            try
              match goal with
              | [ H : honestk $? _ = _ |- _ ] => rewrite H in HCFF; discriminate
              end.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb;
              solve_simple_maps; eauto.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb;
              solve_simple_maps; eauto.
      - rewrite !clean_ciphers_no_new_ciphers; auto.
    Qed.

    Lemma msg_honestly_signed_nochange_addnl_honest_key :
      forall {t} (msg : crypto t) honestk (gks : keys) cs k_id tf,
        ~ In k_id gks
        -> (forall k_id, msg_signing_key cs msg = Some k_id -> gks $? k_id <> None)
        -> msg_honestly_signed honestk cs msg = tf
        -> msg_honestly_signed (honestk $+ (k_id,true)) cs msg = tf.
    Proof.
      intros.
      unfold msg_honestly_signed in *.
      cases (msg_signing_key cs msg); eauto.
      unfold honest_keyb in *.
      destruct (k_id ==n k); subst; cases (honestk $? k);
        clean_map_lookups; context_map_rewrites; eauto.
      
      assert (Some k = Some k) as SK by trivial; specialize (H0 _ SK); contradiction.
      assert (Some k = Some k) as SK by trivial; specialize (H0 _ SK); contradiction.
    Qed.

    Lemma msg_filter_same_new_honest_key :
      forall msg k_id cs honestk (gks : keys) suid froms tf,
        ~ In k_id gks
        -> msg_filter honestk cs suid froms msg = tf
        -> (match msg with (existT _ _ m) => forall k_id, msg_signing_key cs m = Some k_id -> gks $? k_id <> None end)
        -> msg_filter (honestk $+ (k_id, true)) cs suid froms msg = tf.
    Proof.
      intros;
        unfold msg_filter,msg_signed_addressed in *; destruct msg.

      cases (msg_honestly_signed honestk cs c); simpl in *;
        match goal with
        | [ H : msg_honestly_signed honestk cs c = ?tf |- _] =>
          assert (msg_honestly_signed (honestk $+ (k_id,true)) cs c = tf)
            as MHS by eauto using msg_honestly_signed_nochange_addnl_honest_key
        end; rewrite MHS; simpl; eauto.
    Qed.

    Hint Resolve msg_filter_same_new_honest_key.
    
    Lemma clean_messages_new_honest_key_idempotent :
      forall honestk k_id msgs cs gks suid froms,
           message_queue_ok honestk cs msgs gks
        -> ~ In k_id gks
        -> clean_messages (honestk $+ (k_id, true)) cs suid froms msgs
          = clean_messages honestk cs suid froms msgs.
    Proof.
      unfold clean_messages, clean_messages'; induction msgs; intros; eauto; simpl.
      unfold msg_filter at 2 4; destruct a;
        invert H; split_ands.

      assert (forall k, msg_signing_key cs c = Some k -> gks $? k <> None).
      intros. specialize (H2 _ H3); split_ands; auto.

      unfold msg_signed_addressed.
      cases (msg_honestly_signed honestk cs c); simpl in *;
            match goal with
            | [ H : msg_honestly_signed honestk cs c = ?tf |- _] =>
              assert (msg_honestly_signed (honestk $+ (k_id,true)) cs c = tf)
                as MHS by eauto using msg_honestly_signed_nochange_addnl_honest_key
            end; rewrite MHS; simpl; eauto.

      cases (msg_to_this_user cs suid c); eauto.
      cases (msg_nonce_ok cs froms c); eauto.
      rewrite !fold_clean_messages2', !clean_messages'_fst_pull.
      unfold clean_messages'.
      f_equal; eauto.
    Qed.

    Lemma clean_adv_msgs_new_honest_key_idempotent :
      forall {A} (usrs : honest_users A) k_id msgs cs gks,
           adv_message_queue_ok usrs cs gks msgs
        -> ~ In k_id gks
        -> clean_adv_msgs (findUserKeys usrs $+ (k_id, true)) cs msgs
          = clean_adv_msgs (findUserKeys usrs) cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H; split_ands.
      cases (msg_honestly_signed (findUserKeys usrs) cs c); simpl in *;
            match goal with
            | [ H : msg_honestly_signed (findUserKeys usrs) cs c = ?tf |- _] =>
              assert (msg_honestly_signed (findUserKeys usrs $+ (k_id,true)) cs c = tf)
                as MHS by eauto using msg_honestly_signed_nochange_addnl_honest_key
            end; rewrite MHS; simpl; eauto.
      f_equal; eauto.
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

    Lemma clean_key_permissions_new_honest_key' :
      forall honestk k_id gks,
        gks $? k_id = None
        -> clean_key_permissions (honestk $+ (k_id, true)) gks = clean_key_permissions honestk gks.
    Proof.
      intros.
      unfold clean_key_permissions, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      subst; simpl.

      rewrite fold_add; eauto.
      assert (honest_perm_filter_fn (honestk $+ (k_id,true)) k e = honest_perm_filter_fn honestk k e)
        as RW.

      unfold honest_perm_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      apply find_mapsto_iff in H0; contra_map_lookup.
      rewrite RW; trivial.
    Qed.

    Lemma clean_key_permissions_new_honest_key :
      forall honestk k_id ks,
        ~ In k_id ks
        -> clean_key_permissions (honestk $+ (k_id, true)) (add_key_perm k_id true ks) =
          add_key_perm k_id true (clean_key_permissions honestk ks).
    Proof.
      intros; clean_map_lookups.
      unfold add_key_perm, greatest_permission.
      assert (clean_key_permissions honestk ks $? k_id = None)
        as CKP
          by (apply clean_key_permissions_adds_no_permissions; auto);
        rewrite CKP, H.
      unfold clean_key_permissions at 1; unfold filter; rewrite fold_add; eauto.
      unfold honest_perm_filter_fn; clean_map_lookups; eauto.

      apply map_eq_Equal; unfold Equal; intros.
      destruct (k_id ==n y); subst; clean_map_lookups; eauto.
      pose proof clean_key_permissions_new_honest_key';
        unfold clean_key_permissions, filter, honest_perm_filter_fn in *; eauto.
      rewrite H0; eauto.
    Qed.

    Hint Resolve clean_key_permissions_new_honest_key'.

    Lemma clean_adv_new_honest_key_idempotent :
      forall {A B} (usrs : honest_users A) (adv : user_data B) k_id cs gks b,
        ~ In k_id gks
        -> permission_heap_good gks (key_heap adv)
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> clean_adv adv (findUserKeys usrs $+ (k_id, true)) cs b = clean_adv adv (findUserKeys usrs) cs b.
    Proof.
      intros.
      unfold clean_adv.
      cases (key_heap adv $? k_id).
      specialize (H0 _ _ Heq); split_ex; clean_map_lookups.
      erewrite clean_key_permissions_new_honest_key', clean_adv_msgs_new_honest_key_idempotent; clean_map_lookups; eauto.
    Qed.

    Lemma clean_users_new_honest_key_idempotent :
      forall {A} (usrs : honest_users A) adv_heap honestk k_id cs gks,
        ~ In k_id gks
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv_heap
        -> clean_users (honestk $+ (k_id, true)) cs usrs = clean_users honestk cs usrs.
    Proof.
      intros; subst.
      apply map_eq_Equal; unfold Equal; intros.
      cases (usrs $? y).
      - erewrite !clean_users_cleans_user; eauto.
        unfold keys_and_permissions_good in *; split_ands.
        eapply Forall_natmap_in_prop in H2; eauto.
        msg_queue_prop. unfold permission_heap_good in *.
        cases (key_heap u $? k_id). specialize (H2 _ _ Heq0); split_ex; clean_map_lookups.
        f_equal; symmetry; eauto using clean_messages_new_honest_key_idempotent.
      - rewrite !clean_users_adds_no_users; eauto.
    Qed.

    Hint Resolve clean_keys_new_honest_key.

    Lemma honestly_signed_message_accepted_by_pattern_same_after_cleaning :
      forall {t} (msg : crypto t) cs msg_to froms pat honestk,
        msg_accepted_by_pattern cs froms pat msg_to msg
        -> msg_honestly_signed honestk cs msg = true
        -> msg_accepted_by_pattern (clean_ciphers honestk cs) froms pat msg_to msg.
    Proof.
      intros.
      unfold msg_honestly_signed in *.
      invert H; econstructor; simpl in *; context_map_rewrites; eauto.
    Qed.
    
    Lemma message_not_accepted_by_pattern_same_after_cleaning :
      forall {t} (msg : crypto t) cs msg_to froms pat honestk,
        ~ msg_accepted_by_pattern cs froms pat msg_to msg
        -> ~ msg_accepted_by_pattern (clean_ciphers honestk cs) froms pat msg_to msg.
    Proof.
      unfold not; intros; apply H.
      invert H0; econstructor;
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H2; split_ands; eauto.
    Qed.

    Hint Resolve
         honestly_signed_message_accepted_by_pattern_same_after_cleaning
         message_not_accepted_by_pattern_same_after_cleaning.

    Lemma msg_signed_addressed_nochange_addnl_cipher :
      forall {t} (msg : crypto t) honestk suid cs c_id c tf,
        ~ In c_id cs
        -> (forall cid : cipher_id, msg_cipher_id msg = Some cid -> cs $? cid <> None)
        -> msg_signed_addressed honestk cs suid msg = tf
        -> msg_signed_addressed honestk (cs $+ (c_id,c)) suid msg = tf.
    Proof.
      unfold
        msg_signed_addressed, msg_honestly_signed,
        msg_to_this_user, msg_signing_key, msg_destination_user; intros.

      destruct msg; eauto.
      destruct (c_id ==n c_id0); subst;
        cases (cs $? c_id0); clean_map_lookups;
          context_map_rewrites; eauto.

      exfalso.
      assert (Some c_id0 = Some c_id0) as CID by trivial;
        specialize (H0 _ CID); contradiction.
    Qed.

    Lemma msg_nonce_ok_nochange_addnl_cipher :
      forall {t} (msg : crypto t) froms cs c_id c recv,
        ~ In c_id cs
        -> (forall cid : cipher_id, msg_cipher_id msg = Some cid -> cs $? cid <> None)
        -> msg_nonce_ok cs froms msg = recv
        -> msg_nonce_ok (cs $+ (c_id,c)) froms msg = recv.
    Proof.
      unfold msg_nonce_ok; intros.
      destruct msg; eauto.
      destruct (c_id ==n c_id0); subst;
        cases (cs $? c_id0); clean_map_lookups;
          context_map_rewrites; eauto.

      exfalso.
      assert (Some c_id0 = Some c_id0) as CID by trivial;
        specialize (H0 _ CID); contradiction.
    Qed.

    Lemma clean_messages_addnl_cipher_idempotent :
      forall msgs honestk cs c_id c gks suid froms,
        ~ In c_id cs
        -> message_queue_ok honestk cs msgs gks
        -> clean_messages honestk (cs $+ (c_id,c)) suid froms msgs
          = clean_messages honestk cs suid froms msgs.
    Proof.
      unfold clean_messages, clean_messages'; induction msgs; intros; eauto; simpl.
      unfold msg_filter at 2 4; destruct a;
        invert H0; split_ands.

      cases (msg_signed_addressed honestk cs suid c0); simpl in *;
        match goal with
        | [ H : msg_signed_addressed _ _ _ _ = ?tf |- _ ] =>
          assert (msg_signed_addressed honestk (cs $+ (c_id,c)) suid c0 = tf)
            as MSA by eauto using msg_signed_addressed_nochange_addnl_cipher
        end; rewrite MSA; eauto.

      cases (msg_nonce_ok cs froms c0); simpl in *;
        match goal with
        | [ H : msg_nonce_ok _ _ _ = ?res |- _ ] =>
          assert (msg_nonce_ok (cs $+ (c_id,c)) froms c0 = res)
            as MNOK by eauto using msg_nonce_ok_nochange_addnl_cipher
        end; rewrite MNOK; eauto.

      rewrite !fold_clean_messages2', !clean_messages'_fst_pull.
      unfold clean_messages'.
      f_equal; eauto.
    Qed.

    Lemma clean_adv_msgs_addnl_cipher_idempotent :
      forall {A} (usrs : honest_users A) msgs cs c_id c gks,
        ~ In c_id cs
        -> adv_message_queue_ok usrs cs gks msgs
        -> clean_adv_msgs (findUserKeys usrs) (cs $+ (c_id,c)) msgs
          = clean_adv_msgs (findUserKeys usrs) cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H0; split_ands.
      cases (msg_honestly_signed (findUserKeys usrs) cs c0);
        unfold msg_honestly_signed, msg_signing_key in *;
        destruct c0; try discriminate; eauto;
          cases (cs $? c_id0); try discriminate;
            destruct (c_id ==n c_id0); subst; clean_map_lookups;
              context_map_rewrites; eauto.

      - rewrite Heq; f_equal; eauto.
      - rewrite Heq; eauto.
      - assert (Some c_id0 = Some c_id0) as S by trivial;
          specialize (H0 _ S); contradiction.
    Qed.

    Hint Resolve clean_messages_addnl_cipher_idempotent clean_adv_msgs_addnl_cipher_idempotent.

    Lemma clean_users_addnl_cipher_idempotent :
      forall {A} (usrs : honest_users A) honestk cs c_id c gks,
        ~ In c_id cs
        -> message_queues_ok cs usrs gks
        -> honestk = findUserKeys usrs
        -> clean_users honestk (cs $+ (c_id,c)) usrs = clean_users honestk cs usrs.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      unfold clean_users.
      rewrite !mapi_o; simpl; intros; subst; trivial.
      cases (usrs $? y); eauto; simpl.
      msg_queue_prop.
      f_equal; subst.
      f_equal; eauto.
    Qed.

    Hint Resolve clean_users_addnl_cipher_idempotent.

    Lemma clean_messages_keeps_signed_addressed_unseen_nonce :
      forall t honestk u_id cs c_id c froms msgs,
        @msg_signed_addressed honestk cs (Some u_id) t (SignedCiphertext c_id) = true
        -> cs $? c_id = Some c
        -> ~ List.In (cipher_nonce c) froms
        -> clean_messages honestk cs (Some u_id) froms (existT _ t (SignedCiphertext c_id) :: msgs)
          = existT _ t (SignedCiphertext c_id) ::
                   clean_messages honestk cs (Some u_id) (@updateTrackedNonce t (Some u_id) froms cs (SignedCiphertext c_id)) msgs.
    Proof.
      intros; unfold updateTrackedNonce.
      unfold clean_messages at 1; unfold clean_messages'; simpl.
      rewrite H; context_map_rewrites.
      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H1; rewrite H1.
      unfold msg_signed_addressed in H; rewrite andb_true_iff in H; split_ands.
      unfold msg_to_this_user, msg_destination_user in H2; context_map_rewrites.
      destruct (cipher_to_user c ==n u_id); try discriminate.
      destruct (u_id ==n cipher_to_user c); try discriminate; subst; try contradiction.
      rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; trivial.
    Qed.

    Lemma updateRecvNonce_clean_ciphers_honestly_signed :
      forall t honestk cs suid c_id froms,
        @msg_signed_addressed honestk cs suid t (SignedCiphertext c_id) = true
        -> @updateTrackedNonce t suid froms cs (SignedCiphertext c_id) =
          @updateTrackedNonce t suid froms (clean_ciphers honestk cs) (SignedCiphertext c_id).
    Proof.
      intros; unfold updateTrackedNonce.
      unfold msg_signed_addressed in H; rewrite andb_true_iff in H; split_ands.
      unfold msg_honestly_signed, msg_signing_key in H;
        cases (cs $? c_id); try discriminate.

      apply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq.
      context_map_rewrites; trivial.
      unfold honest_cipher_filter_fn, cipher_honestly_signed; destruct c; eauto.
    Qed.

    Lemma msg_nonce_ok_none_updateTrackedNonce_idempotent :
      forall {t} (msg : crypto t) cs froms suid,
        msg_nonce_ok cs froms msg = None
        -> froms = updateTrackedNonce suid froms cs msg.
    Proof.
      intros.
      unfold updateTrackedNonce;
        unfold msg_nonce_ok in H; destruct msg; try discriminate.
          cases (cs $? c_id); try discriminate; auto;
            cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate; trivial.
          destruct suid; trivial.
          destruct (u ==n cipher_to_user c); trivial.
    Qed.

    Hint Resolve
         clean_messages_keeps_signed_addressed_unseen_nonce
         clean_key_permissions_keeps_honest_permission
         msg_nonce_ok_none_updateTrackedNonce_idempotent
         updateRecvNonce_clean_ciphers_honestly_signed.

    Lemma honest_silent_recv_implies_honest_or_no_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs : honest_users A) (adv : user_data B) usrs__s cs__s
        cs gks  u_id honestk pat ks qmsgs mycs froms froms' sents cur_n b,
        ~ msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> honestk = findUserKeys usrs
        -> froms' = (if msg_signed_addressed honestk cs (Some u_id) msg
                   then updateTrackedNonce (Some u_id) froms cs msg
                   else froms)
        -> cs__s = clean_ciphers honestk cs
        -> usrs__s = clean_users honestk cs usrs
        -> step_user Silent (Some u_id)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs),
                     mycs, froms, sents, cur_n, @Recv t pat)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms' qmsgs, mycs, froms', sents, cur_n, Recv pat)
          \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
             clean_key_permissions honestk ks,
             clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs), mycs, froms, sents, cur_n, @Recv t pat)
            = (clean_users honestk cs usrs, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
               clean_key_permissions honestk ks,
               clean_messages honestk cs (Some u_id) froms' qmsgs, mycs, froms', sents, cur_n, Recv pat).
    Proof.
      intros; subst.
      cases (msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg).

      - cases (msg_nonce_ok cs froms msg).
        + repeat
            match goal with
            | [H : msg_nonce_ok _ _ _ = _ |- _ ] =>
              unfold msg_nonce_ok in H; destruct msg; try discriminate;
                cases (cs $? c_id); try discriminate;
                  cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate; clean_context
            | [ H : count_occ _ _ _ = 0 |- _ ] => 
              rewrite <- count_occ_not_In in H
            end.

          left; econstructor; eauto.
          rewrite msg_signed_addressed_true_after_cipher_cleaning; eauto; intros; eauto.

        + right; simpl.

          unfold clean_messages at 1.
          unfold clean_messages', msg_filter; simpl.
          rewrite Heq , Heq0, fold_clean_messages1', fold_clean_messages.
          repeat f_equal; eauto.
            
      - right; simpl.
        unfold clean_messages at 1.
        unfold clean_messages', msg_filter; simpl.
        rewrite Heq, fold_clean_messages1'; trivial.
    Qed.

    Lemma clean_ciphers_eq_absurd :
      forall cs honestk c_id c,
        ~ In c_id cs
        -> clean_ciphers honestk cs = clean_ciphers honestk cs $+ (c_id, c)
        -> False.
    Proof.
      intros.
      assert (Equal (clean_ciphers honestk cs) (clean_ciphers honestk cs $+ (c_id, c)))
        by (rewrite <- H0; apply Equal_refl).
      unfold Equal in H1; specialize (H1 c_id).
      clean_map_lookups; rewrite clean_ciphers_no_new_ciphers in H1; symmetry in H1; auto; clean_map_lookups.
    Qed.

    Hint Resolve clean_ciphers_eq_absurd.

    Lemma honest_silent_new_key_implies_honest_step_origuniv :
      forall {A B} (usrs : honest_users A) (adv : user_data B) 
        cs gks gks' k_id usage u_id honestk honestk' ks qmsgs mycs froms sents cur_n b keygen_cmd kt,
          gks $? k_id = None
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys usrs $+ (k_id,true)
        -> gks' = gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})
        -> ( (keygen_cmd = GenerateAsymKey usage /\ kt = AsymKey)
          \/ (keygen_cmd = GenerateSymKey usage /\ kt = SymKey) )
        -> message_queues_ok cs usrs gks
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, keygen_cmd)
                    (  clean_users honestk' cs usrs
                     , clean_adv adv honestk' cs b
                     , clean_ciphers honestk' cs
                     , clean_keys honestk' gks'
                     , clean_key_permissions honestk' (add_key_perm k_id true ks)
                     , clean_messages honestk' cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, @Return (Base Access) (k_id,true) ).
    Proof.
      intros; split_ors; subst;
        msg_queue_prop;
        keys_and_permissions_prop;
        erewrite clean_users_new_honest_key_idempotent
        , clean_ciphers_new_honest_key_idempotent
        , clean_messages_new_honest_key_idempotent
        , clean_adv_new_honest_key_idempotent
        , clean_key_permissions_new_honest_key
        ; eauto;
          repeat
            match goal with
            | [ |- step_user _ _ _ _ ] => econstructor
            | [ |- ~ In ?kid ?ks ] => cases (ks $? k_id); clean_map_lookups
            | [ H : permission_heap_good _ ?ks , ARG : ?ks $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG); split_ex; contra_map_lookup
            end; eauto using clean_keys_adds_no_keys.
    Qed.

    Lemma honest_silent_decrypt_implies_honest_step_origuniv :
      forall {t A B} (usrs : honest_users A) (adv : user_data B) (msg : message t)
        cs c_id gks k__encid k__signid kp nonce msg_to u_id honestk honestk' ks qmsgs mycs froms sents cur_n b,
        honestk = findUserKeys usrs
        -> honestk' = honestk $k++ findKeysMessage msg
        -> cs $? c_id = Some (SigEncCipher k__signid k__encid msg_to nonce msg)
        -> ks $? k__signid = Some kp
        -> ks $? k__encid = Some true
        -> List.In c_id mycs
        -> user_cipher_queues_ok cs honestk usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, Decrypt (SignedCiphertext c_id) )
                    (  clean_users honestk' cs usrs
                     , clean_adv adv honestk' cs b
                     , clean_ciphers honestk' cs
                     , clean_keys honestk' gks
                     , clean_key_permissions honestk' (ks $k++ findKeysMessage msg)
                     , clean_messages honestk' cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, @Return (Message t) msg ).
    Proof.
      intros; subst.

      assert (findUserKeys usrs $? k__encid = Some true) by eauto 2.
      user_cipher_queues_prop;
        encrypted_ciphers_prop;
        clean_map_lookups.

      rewrite merge_keys_addnl_honest by eauto.
      econstructor; eauto 2; eauto.

      rewrite clean_key_permissions_distributes_merge_key_permissions.
      apply map_eq_Equal; unfold Equal; intros y.
      solve_perm_merges; eauto;
        repeat match goal with
               | [ H : clean_key_permissions _ (findKeysMessage msg) $? y = Some _ |- _ ] => apply clean_key_permissions_inv in H
               | [ H : clean_key_permissions _ (findKeysMessage msg) $? y = None |- _ ] => eapply clean_key_permissions_inv' in H; eauto 2
               | [ H : (forall _ _, findKeysMessage msg $? _ = Some _ -> _), ARG : findKeysMessage msg $? _ = Some _ |- _ ] =>
                 specialize (H _ _ ARG)
               | [ H : honest_perm_filter_fn _ _ _ = _ |- _] => unfold honest_perm_filter_fn in H; context_map_rewrites
               end; clean_map_lookups; eauto.
    Qed.

    Lemma honest_cipher_filter_fn_nochange_pubk :
      forall honestk pubk k v,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> honest_cipher_filter_fn honestk k v =
          honest_cipher_filter_fn (honestk $k++ pubk) k v.
    Proof.
      unfold honest_cipher_filter_fn; intros;
        unfold cipher_honestly_signed;
        cases v; unfold honest_keyb; simpl;
          solve_perm_merges; auto;
            match goal with
            | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG); split_ands; subst
            end; clean_map_lookups; eauto.
    Qed.

    Lemma clean_ciphers_nochange_pubk :
      forall honestk pubk cs,
        (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
        -> clean_ciphers (honestk $k++ pubk) cs = clean_ciphers honestk cs.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      rewrite fold_add; eauto; simpl.
      erewrite <- honest_cipher_filter_fn_nochange_pubk; eauto.
      subst; trivial.
    Qed.

    Lemma msg_filter_nochange_pubk :
      forall honestk pubk cs m suid froms,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> msg_filter (honestk $k++ pubk) cs suid froms m = msg_filter honestk cs suid froms m.
    Proof.
      unfold
        msg_filter, msg_signed_addressed, msg_honestly_signed, msg_signing_key,
        msg_to_this_user, msg_nonce_ok, msg_destination_user; destruct m;
        intros;
        cases c; unfold honest_keyb; simpl; eauto;
          cases (cs $? c_id); try discriminate; eauto.

      cases (honestk $? cipher_signing_key c); cases (pubk $? cipher_signing_key c);
        solve_perm_merges; eauto;
          match goal with
          | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; split_ands; subst; clean_map_lookups; eauto.
    Qed.

    Lemma clean_messages_nochange_pubk :
      forall honestk pubk cs qmsgs suid froms,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_messages (honestk $k++ pubk) cs suid froms qmsgs = clean_messages honestk cs suid froms qmsgs.
    Proof.
      induction qmsgs; intros; eauto.
      unfold clean_messages, clean_messages'; simpl.
      rewrite !msg_filter_nochange_pubk; auto.
      unfold msg_filter at 2 4.
      destruct a.
      cases (msg_signed_addressed honestk cs suid c); eauto; simpl.
      cases (msg_nonce_ok cs froms c); eauto.
      rewrite !fold_clean_messages2', !clean_messages'_fst_pull.
      f_equal; eauto.
    Qed.

    Lemma clean_adv_msgs_nochange_pubk :
      forall honestk pubk cs qmsgs,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_adv_msgs (honestk $k++ pubk) cs qmsgs = clean_adv_msgs honestk cs qmsgs.
    Proof.
      induction qmsgs; intros; eauto.
      unfold clean_adv_msgs; simpl; destruct a.
      cases (msg_honestly_signed honestk cs c);
        unfold msg_honestly_signed, msg_signing_key in *;
        destruct c; try discriminate; eauto;
          cases (cs $? c_id); try discriminate;
            unfold honest_keyb in *; eauto.

      - cases (honestk $? cipher_signing_key c); try discriminate.
        destruct b; try discriminate.

        assert (honestk $k++ pubk $? cipher_signing_key c = Some true) as RW by solve_perm_merges.
        rewrite RW; f_equal; eauto.

      - cases (honestk $? cipher_signing_key c); try discriminate.
        + destruct b; try discriminate.
          repeat ( maps_equal1 || solve_perm_merges1 );
            f_equal; eauto.
          
          destruct b; solve_perm_merges; eauto.

          match goal with
          | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; split_ands; subst; clean_map_lookups; eauto.
          
       + solve_perm_merges; eauto;
           f_equal; eauto.
         destruct b; solve_perm_merges; eauto.

         match goal with
         | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
         end; split_ands; subst; clean_map_lookups; eauto.
    Qed.

    Lemma clean_key_permissions_nochange_pubk :
      forall honestk pubk perms,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_key_permissions (honestk $k++ pubk) perms = clean_key_permissions honestk perms.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (clean_key_permissions honestk perms $? y).
      - apply clean_key_permissions_inv in Heq; split_ands.
        apply clean_key_permissions_keeps_honest_permission; eauto.
        unfold honest_perm_filter_fn in *.
        cases (honestk $? y); try destruct b0; try discriminate.
        cases (pubk $? y); solve_perm_merges; eauto.
      - cases (perms $? y).
        + eapply clean_key_permissions_inv' in Heq; eauto.
          eapply clean_key_permissions_drops_dishonest_permission; eauto.
          unfold honest_perm_filter_fn in *.
          specialize (H y).
          cases (honestk $? y); try destruct b0; try discriminate.
          cases (pubk $? y);
            match goal with
            | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
              assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
            | _ => solve_perm_merges
            end; eauto.
          cases (pubk $? y);
            match goal with
            | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
              assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
            | _ => solve_perm_merges
            end; eauto.
        + apply clean_key_permissions_adds_no_permissions; eauto.
    Qed.

    Lemma clean_users_nochange_pubk :
      forall {A} (usrs: honest_users A) honestk cs pubk,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_users (honestk $k++ pubk) cs usrs = clean_users honestk cs usrs.
    Proof.
      intros; unfold clean_users.
      eapply map_eq_Equal; unfold Equal; intros.
      rewrite !mapi_o; simpl; intros; subst; trivial.
      cases (usrs $? y); eauto.
      simpl.
      f_equal. f_equal.
      - rewrite clean_key_permissions_nochange_pubk; eauto.
      - rewrite clean_messages_nochange_pubk; trivial.
    Qed.

    Lemma clean_users_nochange_pubk_step :
      forall {A} (usrs: honest_users A) honestk cs pubk u_id ks cmd qmsgs mycs froms sents cur_n u_d u_d',
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> u_d = {| key_heap := ks $k++ pubk
                 ; protocol := cmd
                 ; msg_heap := qmsgs
                 ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        -> u_d' = {| key_heap := clean_key_permissions honestk (ks $k++ pubk)
                  ; protocol := cmd
                  ; msg_heap := clean_messages honestk cs (Some u_id) froms qmsgs
                  ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        -> clean_users (honestk $k++ pubk) cs (usrs $+ (u_id,u_d)) =
          clean_users honestk cs usrs $+ (u_id,u_d').
    Proof.
      intros.
      eapply map_eq_Equal; unfold Equal; intros.
      cases (u_id ==n y); subst; clean_map_lookups.
      + erewrite clean_users_cleans_user; clean_map_lookups; eauto. simpl.
        f_equal.
        rewrite clean_key_permissions_nochange_pubk; eauto.
        rewrite clean_messages_nochange_pubk; auto.
      + unfold clean_users.
        rewrite !mapi_o; intros; subst; trivial.
        clean_map_lookups.

        cases (usrs $? y); simpl; auto.
        f_equal. f_equal.
        rewrite clean_key_permissions_nochange_pubk; eauto.
        rewrite clean_messages_nochange_pubk; auto.
    Qed.

    Lemma clean_keys_nochange_pubk :
      forall honestk pubk ks,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_keys (honestk $k++ pubk) ks = clean_keys honestk ks.
    Proof.
      intros; unfold clean_keys, filter.

      induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
      rewrite !fold_add; eauto.
      rewrite IHks; trivial.

      assert (honest_key_filter_fn (honestk $k++ pubk) x e = honest_key_filter_fn honestk x e).
      unfold honest_key_filter_fn.
      specialize (H x).
      cases (honestk $? x); cases (pubk $? x); subst;
            try match goal with
                | [ PUB : pubk $? x = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
                  assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; try discriminate
                end;
            solve_perm_merges; eauto.

      rewrite H1; trivial.
    Qed.

    Lemma honest_labeled_step_nochange_clean_ciphers_users_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a b,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                /\ clean_users (findUserKeys usrs'') cs' usrs'' =
                  clean_users (findUserKeys usrs') cs' usrs' $+ (u_id, {| key_heap := clean_key_permissions (findUserKeys usrs') ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                                                                    ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                /\ clean_adv adv' (findUserKeys usrs'') cs' b = clean_adv adv' (findUserKeys usrs) cs' b
                /\ clean_keys (findUserKeys usrs'') gks' = clean_keys (findUserKeys usrs') gks'.

    Proof.
      induction 1; inversion 4; inversion 2; intros; subst; try discriminate;
        eauto 2;
        autorewrite with find_user_keys;
        clean_context;
        simpl.

      - msg_queue_prop.
        split_ands; specialize_msg_ok.
        intuition eauto using clean_ciphers_nochange_pubk
                            , clean_messages_nochange_pubk
                            , clean_users_nochange_pubk_step
                            , clean_key_permissions_nochange_pubk
                            , clean_keys_nochange_pubk.
        unfold clean_adv; f_equal; eauto using clean_key_permissions_nochange_pubk, clean_adv_msgs_nochange_pubk.

      - destruct rec_u; simpl in *.
        intuition idtac.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups.
        * erewrite clean_users_cleans_user; clean_map_lookups; eauto.
        * unfold clean_users; rewrite !mapi_o; intros; subst; clean_map_lookups; trivial.
    Qed.

    Lemma honest_labeled_step_encrypted_ciphers_ok :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs' gks'.
    Proof.
      induction 1; inversion 5; inversion 2; intros; subst; try discriminate;
        eauto 2; autorewrite with find_user_keys;
          clean_context; eauto.

      msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
      specialize_msg_ok; eauto.
    Qed.

    Locate action_adversary_safe.

    Lemma honest_labeled_step_univ_ok :
      forall {A B} (U U' : universe A B) uid a__r,
        universe_ok U
        -> step_universe (Some uid) U (Action (uid, a__r)) U'
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r
        -> message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        -> universe_ok U'.
    Proof.
      unfold universe_ok; intros.
      invert H0.
      destruct U; destruct userData.
      unfold buildUniverse, build_data_step in *; simpl in *.
      eapply honest_labeled_step_encrypted_ciphers_ok; eauto.
      unfold mkULbl in H7; destruct lbl; invert H7; trivial.
    Qed.

    Lemma honest_message_findKeysCrypto_same_after_cleaning :
      forall {t} (msg : crypto t) honestk cs,
        msg_honestly_signed honestk cs msg = true
        -> findKeysCrypto cs msg = findKeysCrypto (clean_ciphers honestk cs) msg.
    Proof.
      intros.
      unfold message_no_adv_private, msg_honestly_signed, findKeysCrypto in *.
      destruct msg; eauto.
      cases (cs $? c_id); simpl in *; context_map_rewrites.
      - destruct c; eauto;
          eapply clean_ciphers_reduces_or_keeps_same_ciphers with (honestk := honestk) in Heq;
          eauto; simpl in *; split_ors; split_ands; context_map_rewrites; eauto.
        rewrite H in H1; discriminate.
              
      - eapply clean_ciphers_no_new_ciphers with (honestk := honestk) in Heq.
        rewrite Heq; trivial.
    Qed.

    Lemma updateTrackedNonce_clean_ciphers_idempotent_honest_msg :
      forall {t} (msg : crypto t) suid froms cs honestk,
        msg_honestly_signed honestk cs msg = true
        -> updateTrackedNonce suid froms cs msg = updateTrackedNonce suid froms (clean_ciphers honestk cs) msg.
    Proof.
      unfold updateTrackedNonce; intros.
      destruct msg; eauto.
      cases (cs $? c_id).
      - eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto.
        context_map_rewrites; trivial.
        unfold msg_honestly_signed in H; simpl in *; context_map_rewrites.
        unfold honest_cipher_filter_fn, cipher_honestly_signed;
          destruct c; eauto.

      - eapply clean_ciphers_no_new_ciphers with (honestk := honestk) in Heq;
          context_map_rewrites; eauto.
    Qed.

    Lemma updateSentNonce_clean_ciphers_idempotent_honest_msg :
      forall {t} (msg : crypto t) suid froms cs honestk,
        msg_honestly_signed honestk cs msg = true
        -> updateSentNonce suid froms cs msg = updateSentNonce suid froms (clean_ciphers honestk cs) msg.
    Proof.
      unfold updateSentNonce; intros.
      destruct msg; eauto.
      cases (cs $? c_id).
      - eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto.
        context_map_rewrites; trivial.
        unfold msg_honestly_signed in H; simpl in *; context_map_rewrites.
        unfold honest_cipher_filter_fn, cipher_honestly_signed;
          destruct c; eauto.

      - eapply clean_ciphers_no_new_ciphers with (honestk := honestk) in Heq;
          context_map_rewrites; eauto.
    Qed.

    Hint Resolve
         updateSentNonce_clean_ciphers_idempotent_honest_msg
         updateTrackedNonce_clean_ciphers_idempotent_honest_msg
         : core.


    Lemma clean_messages_keeps_hon_signed :
      forall {t} qmsgs (msg : crypto t) honestk cs rec_u_id froms u_id sents n,
        honest_nonce_tracking_ok cs u_id sents n rec_u_id froms qmsgs
        -> msg_signed_addressed honestk cs (Some rec_u_id) msg = true
        -> (exists c_id c,
              msg = SignedCiphertext c_id /\ cs $? c_id = Some c
              /\ fst (cipher_nonce c) = u_id /\ ~ List.In (cipher_nonce c) sents)
        -> clean_messages honestk cs (Some rec_u_id) froms (qmsgs ++ [existT _ _ msg])
          = clean_messages honestk cs (Some rec_u_id) froms qmsgs ++ [existT _ _ msg].
    Proof.
      unfold clean_messages; induction qmsgs; simpl;
        intros; split_ex; split_ands; subst; eauto;
          unfold honest_nonce_tracking_ok in *; split_ands.

      - unfold clean_messages'; simpl; rewrite H0;
          context_map_rewrites; process_nonce_ok; eauto.
        unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H0; rewrite andb_true_iff in H0;
          context_map_rewrites;
          split_ands.
        destruct (cipher_to_user x0 ==n rec_u_id); try discriminate;
          process_nonce_ok; trivial.

      - unfold clean_messages'; simpl.
        unfold msg_filter at 2 4; destruct a.
        cases (msg_signed_addressed honestk cs (Some rec_u_id) c); simpl; eauto.
            
        + cases (msg_nonce_ok cs froms c); eauto.
          * invert H3.
            unfold msg_nonce_ok in Heq0; destruct c; clean_context; eauto.
            cases (cs $? c_id); try discriminate.
            cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate;
              clean_context.

            rewrite !fold_clean_messages2', !clean_messages'_fst_pull.
            simpl; f_equal.
            eapply IHqmsgs; eauto 6.
            split; eauto.
            split.
            ** econstructor; process_nonce_ok; eauto.
            ** split; eauto.
               intros.
               specialize (H5 _ _ H3 H6); split_ands; split; eauto.
               intros.
               specialize (H7 H10 H11); split_ands.
               invert H12.
               split; eauto.
               unfold not; intros.
               unfold msg_signed_addressed in Heq; rewrite andb_true_iff in Heq;
                 split_ands.
               split_ors.
               rewrite H14 in H13; invert H13.
               unfold msg_nonce_not_same in H14; assert ( cipher_nonce c0 <> cipher_nonce c ) by eauto.
               simpl in H10; split_ors; congruence.
                   
          * invert H3.
            eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.
              
        + invert H3.
          eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.

    Qed.

    Ltac count_occ_list_in1 :=
      match goal with
      | [ H : ~ List.In ?x ?xs |- context [ count_occ _ ?xs ?x ] ] => rewrite count_occ_not_In in H; rewrite H
      | [ H : count_occ _ ?xs ?x = 0 |- context [ ~ List.In ?x ?xs ] ] => rewrite count_occ_not_In
      end.

    Lemma honestly_signed_message_to_this_user_None_always_true :
      forall {t} (msg : crypto t) honestk cs,
        msg_honestly_signed honestk cs msg = true
        -> msg_to_this_user cs None msg = true.
    Proof.
      intros.
      unfold msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in *.
      destruct msg; try discriminate.
      cases (cs $? c_id); try discriminate; trivial.
    Qed.

    Hint Resolve honestly_signed_message_to_this_user_None_always_true.

    Lemma clean_adv_msgs_keeps_honest_msg :
      forall {t} (msg : crypto t) honestk cs msgs,
        msg_honestly_signed honestk cs msg = true
        -> clean_adv_msgs honestk cs (msgs ++ [existT _ _ msg])
          = clean_adv_msgs honestk cs msgs ++ [existT _ _ msg].
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; simpl; eauto.
      - rewrite H; trivial.
      - destruct a.
        cases (msg_honestly_signed honestk cs c); eauto.
        rewrite <- app_comm_cons; f_equal; eauto.
    Qed.

    Hint Resolve clean_adv_msgs_keeps_honest_msg.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv' :
      forall {A B C} cs cs' lbl u_id suid (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a a' (b : <<(Base B)>>) honestk,

        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> honestk = findUserKeys usrs
        -> action_adversary_safe honestk cs a
        -> honest_nonces_ok cs usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C) cs__s usrs__s,
            cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall cmd' cs__s' usrs__s' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Action a
              -> forall cmdc,
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                         ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> a' = strip_action (findUserKeys usrs) cs a
                  -> step_user (Action a') suid
                              (usrs__s, clean_adv adv (findUserKeys usrs) cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks, clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs__s', clean_adv adv' (findUserKeys usrs) cs' b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks', clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd').
    Proof.
      induction 1; inversion 9; inversion 4; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
          autorewrite with find_user_keys.

      - assert ( msg_honestly_signed (findUserKeys usrs') cs' msg = true ) as MHS by eauto.
        assert ( msg_to_this_user cs' (Some u_id) msg = true ) as MSGTO by eauto.
        split_ex; split_ands.
        unfold clean_messages at 1; unfold clean_messages'; simpl.
        unfold msg_signed_addressed; rewrite MHS, MSGTO; simpl.

        unfold msg_nonce_ok; subst; context_map_rewrites.
        count_occ_list_in1.

        econstructor; eauto.

        + simpl; context_map_rewrites.
          unfold msg_to_this_user, msg_destination_user in MSGTO;
            context_map_rewrites.
          destruct (cipher_to_user x0 ==n u_id); subst; try discriminate.
          destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
          rewrite H2; simpl.
          rewrite fold_clean_messages2', clean_messages'_fst_pull.
          trivial.

        +  rewrite clean_key_permissions_distributes_merge_key_permissions.
            
           assert (clean_key_permissions (findUserKeys usrs') (@findKeysCrypto t0 cs' (SignedCiphertext x))
                   = @findKeysCrypto t0 (clean_ciphers (findUserKeys usrs') cs') (SignedCiphertext x)) as RW.

            unfold msg_honestly_signed in MHS; simpl in *;
              context_map_rewrites.
            assert (cs' $? x = Some x0) as CS by assumption.
            apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs') in CS; eauto.
            context_map_rewrites.

            msg_queue_prop. specialize_msg_ok.
            unfold message_no_adv_private in H12; simpl in H12; context_map_rewrites.
            destruct x0; eauto.
            apply map_eq_Equal; unfold Equal; intros.
            cases (findKeysMessage msg $? y); eauto.
            ** apply clean_key_permissions_keeps_honest_permission; eauto.
               unfold honest_perm_filter_fn.
               simpl in H0; context_map_rewrites.
               encrypted_ciphers_prop.
               specialize (H24 _ _ Heq); split_ands; context_map_rewrites; trivial.
            ** apply clean_key_permissions_adds_no_permissions; auto.
            ** rewrite RW; trivial.

      - eapply StepSend with (rec_u0 := {| key_heap := clean_key_permissions (findUserKeys usrs) rec_u.(key_heap)
                                         ; protocol := rec_u.(protocol)
                                         ; msg_heap := clean_messages (findUserKeys usrs) cs' (Some rec_u_id) rec_u.(from_nons) rec_u.(msg_heap)
                                         ; c_heap   := rec_u.(c_heap)
                                         ; from_nons := rec_u.(from_nons)
                                         ; sent_nons := rec_u.(sent_nons)
                                         ; cur_nonce := rec_u.(cur_nonce) |});
          try (erewrite <- honest_message_findKeysCrypto_same_after_cleaning by solve [ eauto ] );
          eauto.

        + unfold keys_mine in *; intros.

          split_ex; subst.
          specialize (H0 _ _ H7).

          unfold msg_honestly_signed, msg_signing_key in H; context_map_rewrites.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups;
            match goal with
            | [ H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _), ARG : findKeysMessage _ $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG)
            end; split_ors; subst; eauto.

        + eapply clean_users_cleans_user; eauto.
        + simpl.
          rewrite clean_users_add_pull; simpl; eauto.
          erewrite clean_messages_keeps_hon_signed; eauto.
          (* unfold honest_nonces_ok in H9; process_nonce_ok. *)
          unfold msg_signed_addressed.
          rewrite andb_true_iff; split_ex; subst; eauto.
          
        + unfold clean_adv, addUserKeys; simpl.

          f_equal; eauto.
          rewrite clean_key_permissions_distributes_merge_key_permissions.
          apply map_eq_Equal; unfold Equal; intros.

          assert (clean_key_permissions (findUserKeys usrs) (findKeysCrypto cs' msg) $? y
                  = findKeysCrypto cs' msg $? y) as RW.

          split_ex.
          rewrite H6 in H; unfold msg_honestly_signed in H.
          match goal with
          | [ H : match ?mtch with _ => _ end = _ |- _ ] => cases mtch; try discriminate
          end.
          subst.
          simpl in Heq; context_map_rewrites; clean_context.
          encrypted_ciphers_prop; simpl in *; context_map_rewrites; eauto.
          cases (findKeysMessage msg $? y); eauto using clean_key_permissions_adds_no_permissions.
          specialize (H15 _ _ Heq); split_ands; subst; eauto.

          * cases ( clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y );
              cases ( findKeysCrypto cs' msg $? y );
              solve_perm_merges; eauto.
    Qed.

    Hint Resolve honest_users_only_honest_keys_nochange_keys.

    Lemma merge_perms_true_either_true :
      forall ks1 ks2 k_id,
        ks1 $? k_id = Some true \/ ks2 $? k_id = Some true
        -> ks1 $k++ ks2 $? k_id = Some true.
    Proof.
      intros; split_ors; solve_perm_merges.
    Qed.

    Hint Resolve merge_perms_true_either_true.

    Hint Resolve honest_users_only_honest_keys_gen_key.

    Lemma next_action_next_cmd_safe :
      forall honestk cs uid froms sents {A} (cmd : user_cmd A) {B} (cmd__n : user_cmd B),
        nextAction cmd cmd__n
        -> next_cmd_safe honestk cs uid froms sents cmd
        -> next_cmd_safe honestk cs uid froms sents cmd__n.
    Proof.
      intros.
      unfold next_cmd_safe in *; intros.
      specialize (H0 _ _ H).
      apply nextAction_couldBe in H.
      cases cmd__n; try contradiction; invert H1; eauto.
    Qed.

    Lemma next_action_next_cmd_safe_bind :
      forall honestk cs uid froms sents {A B} (cmd1 : user_cmd A) (cmd2 : <<A>> -> user_cmd B),
        next_cmd_safe honestk cs uid froms sents (x <- cmd1 ; cmd2 x)
        -> next_cmd_safe honestk cs uid froms sents cmd1.
    Proof.
      intros.
      unfold next_cmd_safe in *; intros; eauto.
      eapply H; econstructor; eauto.
    Qed.

    Hint Resolve
         next_action_next_cmd_safe
         next_action_next_cmd_safe_bind.

    Ltac process_next_cmd_safe :=
      try
        match goal with
        | [ H : next_cmd_safe _ _ _ _ _ ?c |- _] =>
          let NA := fresh "NA" in 
          match c with
          | (Bind (Return ?r) ?c2) =>
            assert (nextAction c (Return r)) as NA by (repeat econstructor)
          | _ =>
            assert (nextAction c c) as NA by econstructor
          end
          ; specialize (H _ _ NA)
          ; simpl in H
          ; split_ex
        end.

    Lemma honest_users_only_honest_keys_honest_steps :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
          honestk = findUserKeys usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honest_users_only_honest_keys usrs
          -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok  cs honestk usrs
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_nons := froms
                                       ; sent_nons := sents
                                       ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_nons := froms'
                                              ; sent_nons := sents'
                                              ; cur_nonce := cur_n' |})
                  -> honest_users_only_honest_keys usrs''.
    Proof.
      induction 1; inversion 3; inversion 5; intros;
        subst;
        autorewrite with find_user_keys;
        process_next_cmd_safe;
        eauto;
        clean_context.

      - unfold honest_users_only_honest_keys in *; intros.
        destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto;
          simpl in *;
          rewrite findUserKeys_readd_user_addnl_keys; eauto.

        specialize (H10 _ _ H26); simpl in *.
        solve_perm_merges;
          try
            match goal with
            | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
            end; clean_map_lookups; eauto;
            assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by eauto.

        + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
          unfold msg_cipher_id in H2; destruct msg; try discriminate;
            clean_context; simpl in *.
          cases (cs' $? x); try discriminate.
          clean_context; invert MHS.
          destruct c; simpl in *; clean_map_lookups; eauto.
          encrypted_ciphers_prop; eauto.
          specialize (H12 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

        + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
          unfold msg_cipher_id in H2; destruct msg; try discriminate;
            clean_context; simpl in *.
          cases (cs' $? x); try discriminate.
          clean_context; invert MHS.
          destruct c; simpl in *; clean_map_lookups; eauto.
          encrypted_ciphers_prop; eauto.
          specialize (H12 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

      - unfold honest_users_only_honest_keys in *; intros.
        assert (rec_u_id <> u_id) by eauto.
        destruct (u_id ==n u_id0); destruct (u_id ==n rec_u_id);
          subst;
          try contradiction;
          clean_map_lookups;
          simpl in *;
          eauto.

        + specialize (H10 _ _ H26 _ _ H12).
          autorewrite with find_user_keys; eauto.

        + destruct (u_id0 ==n rec_u_id); subst;
            clean_map_lookups;
            autorewrite with find_user_keys;
            eauto 2.

      - user_cipher_queues_prop.
        encrypted_ciphers_prop.
        unfold honest_users_only_honest_keys in *; intros.
        rewrite findUserKeys_readd_user_addnl_keys; eauto.
        destruct (u_id ==n u_id0);
          subst;
          try contradiction;
          clean_map_lookups;
          simpl in *;
          eauto.

        apply merge_perms_split in H6; split_ors;
          match goal with
          | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; eauto.
    Qed.

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

    Lemma honest_cmd_implies_safe_action :
      forall {A B C} (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
                u_id suid bd bd' lbl a__r (cmd cmd' : user_cmd C)
                ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        step_user lbl suid bd bd'
      -> suid = Some u_id
      -> lbl = Action a__r
      -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc,
          usrs $? u_id = Some {| key_heap := ks
                                 ; protocol := cmdc
                                 ; msg_heap := qmsgs
                                 ; c_heap := mycs
                                 ; from_nons := froms
                                 ; sent_nons := sents
                                 ; cur_nonce := cur_n |}
          -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd
          -> action_adversary_safe (findUserKeys usrs) cs a__r.
    Proof.
      induction 1; inversion 3; inversion 1; intros;
        try discriminate; subst;
          process_next_cmd_safe;
          eauto;
          clean_context;
          eauto 12.
    Qed.

    Lemma honest_cmds_implies_safe_actions :
      forall {A B} (U U' : universe A B) uid a__r,
        step_universe (Some uid) U (Action (uid,a__r)) U'
        -> honest_cmds_safe U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r.
    Proof.
      invert 1; intros; eauto.
      unfold honest_cmds_safe in H.
      destruct U; destruct userData; simpl in *.
      specialize (H _ _ _ eq_refl H1); simpl in *.
      destruct lbl; invert H4.
      eapply honest_cmd_implies_safe_action; eauto.
      reflexivity.
    Qed.

    Lemma labeled_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B) lbl uid a,
        step_universe (Some uid) U lbl U'
        -> lbl = Action (uid,a)
        -> honest_cmds_safe U
        -> universe_ok U
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      subst.
      generalize (honest_cmds_implies_safe_actions H H1); intros.
      invert H; try discriminate.
      unfold universe_ok, adv_universe_ok in *.
      destruct U; destruct userData.
      unfold build_data_step in *; simpl in *.
      split_ands.
      specialize (H1 _ _ _ eq_refl H5);
        simpl in *.

      destruct lbl; invert H8.

      repeat simple apply conj.
      
      eapply honest_labeled_step_keys_and_permissions_good; eauto.
      eapply honest_labeled_step_user_cipher_queues_ok; eauto.
      eapply honest_labeled_step_message_queues_ok; eauto.
      eapply honest_labeled_step_adv_cipher_queue_ok; eauto.
      eapply honest_labeled_step_adv_message_queue_ok; eauto.
      eapply honest_labeled_step_adv_no_honest_keys; eauto.
      eapply honest_labeled_step_honest_nonces_ok; eauto.

      eapply honest_users_only_honest_keys_honest_steps; eauto.
    Qed.

    Lemma silent_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B) suid,
        step_universe suid U Silent U'
        -> honest_cmds_safe U
        -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers) U.(all_keys)
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      unfold honest_cmds_safe in *.
      
      invert H;
        unfold adv_universe_ok in *;
        destruct U; [destruct userData | destruct adversary];
          unfold build_data_step in *; simpl in *;
            destruct lbl;
            repeat
              match goal with
              | [ H : Silent = mkULbl (Action _) _  |- _ ] => unfold mkULbl in H; simpl in H; discriminate
              end;
            intuition idtac.

      eapply honest_silent_step_keys_good; eauto.
      eapply honest_silent_step_user_cipher_queues_ok; eauto.
      eapply honest_silent_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good;
        unfold keys_and_permissions_good in *; split_ands; eauto.
      eapply honest_silent_step_adv_cipher_queue_ok; eauto.
      eapply honest_silent_step_adv_message_queue_ok; eauto.
      eapply honest_silent_step_adv_no_honest_keys; eauto.
      eapply honest_silent_step_honest_nonces_ok; eauto.

      specialize (H0 _ _ _ eq_refl H3); simpl in H0.
      eapply honest_users_only_honest_keys_honest_steps; eauto.
      
      eapply adv_step_keys_good; eauto.
      eapply adv_step_user_cipher_queues_ok; eauto.
      
      eapply adv_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good; unfold keys_and_permissions_good in *; split_ands; eauto.
      unfold keys_and_permissions_good in *; split_ands; eauto.
      
      eapply adv_step_adv_cipher_queue_ok; eauto.
      eapply adv_step_adv_message_queue_ok; eauto.
      eapply adv_step_adv_no_honest_keys; eauto.
      eapply adv_step_honest_nonces_ok; eauto.
      eapply honest_users_only_honest_keys_adv_steps; eauto.

      eapply adv_step_keys_good; eauto.
      eapply adv_step_user_cipher_queues_ok; eauto.
      
      eapply adv_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good; unfold keys_and_permissions_good in *; split_ands; eauto.
      unfold keys_and_permissions_good in *; split_ands; eauto.
      
      eapply adv_step_adv_cipher_queue_ok; eauto.
      eapply adv_step_adv_message_queue_ok; eauto.
      eapply adv_step_adv_no_honest_keys; eauto.
      eapply adv_step_honest_nonces_ok; eauto.
      eapply honest_users_only_honest_keys_adv_steps; eauto.
    Qed.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto;
        match goal with [H : Action _ = _ |- _] => invert H end.
    Qed.

    Lemma honest_labeled_step_nochange_adversary_protocol :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> adv.(protocol) = adv'.(protocol).
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
    Qed.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> forall u_id' u_d,
              usrs' $? u_id' = Some u_d
              -> usrs $? u_id' <> None.
    Proof.
      induction 1; inversion 1; inversion 1; intros; subst; eauto;
        repeat match goal with
               | [ H : ?us $? ?uid = Some _ |- ?us $? ?uid <> None ] => solve [ rewrite H; intro C; invert C ]
               end.

       case (u_id' ==n rec_u_id); intro; subst; unfold not; intros; clean_map_lookups.
    Qed.

    Lemma labeled_univ_step_inv :
      forall {A B} (U U' : universe A B) a
        (usrs : honest_users A) (adv : user_data B) gks cs uid,
        step_universe (Some uid) U (Action (uid,a)) U'
        -> U = {| users        := usrs
               ; adversary    := adv
               ; all_ciphers  := cs
               ; all_keys     := gks
              |}
        -> exists (u_id : user_id) u_d u_d' usrs' adv' cs' gks' ks' qmsgs' froms' sents' cur_n' mycs' cmd',
            usrs $? u_id = Some u_d
          /\ step_user (Action a) (Some u_id) (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          /\ U' = {| users        := usrs' $+ (u_id, u_d')
                  ; adversary    := adv'
                  ; all_ciphers  := cs'
                  ; all_keys     := gks'
                 |}
          /\ U'.(users) $? u_id = Some u_d'
          /\ u_d' = {| key_heap := ks'
                    ; protocol := cmd'
                    ; msg_heap := qmsgs'
                    ; c_heap   := mycs'
                    ; from_nons := froms'
                    ; sent_nons := sents'
                    ; cur_nonce := cur_n'
                   |}.
    Proof.
      intros.
      invert H; eauto.
      destruct lbl; invert H5.
      unfold build_data_step; simpl.
      repeat eexists; intuition eauto.
    Qed.

    Lemma labeled_indexed_univ_step_inv :
      forall {A B} (U U' : universe A B) uid a
        (usrs : honest_users A) (adv : user_data B) gks cs,
        indexedRealStep uid (Action a) U U'
        -> U = {| users        := usrs
               ; adversary    := adv
               ; all_ciphers  := cs
               ; all_keys     := gks
              |}
        -> exists u_d u_d' usrs' adv' cs' gks' ks' qmsgs' froms' sents' cur_n' mycs' cmd',
            usrs $? uid = Some u_d
          /\ step_user (Action a) (Some uid) (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          /\ U' = {| users        := usrs' $+ (uid, u_d')
                  ; adversary    := adv'
                  ; all_ciphers  := cs'
                  ; all_keys     := gks'
                 |}
          /\ U'.(users) $? uid = Some u_d'
          /\ u_d' = {| key_heap := ks'
                    ; protocol := cmd'
                    ; msg_heap := qmsgs'
                    ; c_heap   := mycs'
                    ; from_nons := froms'
                    ; sent_nons := sents'
                    ; cur_nonce := cur_n'
                   |}.
    Proof.
      intros.
      invert H; eauto; simpl in *.
      unfold build_data_step; simpl.
      repeat eexists; intuition eauto.
    Qed.

    Lemma honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                ->  clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs'
                /\ clean_users (findUserKeys usrs'') cs' usrs' = clean_users (findUserKeys usrs') cs' usrs'.
    Proof.
      induction 1; inversion 2; inversion 6; intros; try discriminate; subst;
        autorewrite with find_user_keys; eauto; clean_context.

      - user_cipher_queues_prop; erewrite cipher_message_keys_already_in_honest; eauto.

      - msg_queue_prop.
        intuition eauto using clean_ciphers_new_honest_key_idempotent
                            , clean_messages_new_honest_key_idempotent
                            , clean_users_new_honest_key_idempotent.
      - msg_queue_prop.
        intuition eauto using clean_ciphers_new_honest_key_idempotent
                            , clean_messages_new_honest_key_idempotent
                            , clean_users_new_honest_key_idempotent.

        Unshelve.
        auto.
    Qed.

    Lemma honest_silent_step_nochange_clean_adv_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> clean_adv_msgs (findUserKeys usrs'') cs'  adv'.(msg_heap) = clean_adv_msgs (findUserKeys usrs'') cs  adv'.(msg_heap).
    Proof.
      induction 1; inversion 2; inversion 7; intros; try discriminate; subst;
        autorewrite with find_user_keys; eauto; clean_context;
          eauto using
                clean_adv_msgs_new_honest_key_idempotent
              , clean_adv_msgs_addnl_cipher_idempotent.
    Qed.

    Lemma indexed_labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) uid act b,
        universe_ok U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        -> honest_nonces_ok U.(all_ciphers) U.(users)
        -> indexedRealStep uid (Action act) U U'
        -> indexedRealStep uid
                        (Action (strip_action (findUserKeys U.(users)) U.(all_ciphers) act))
                        (strip_adversary_univ U b)
                        (strip_adversary_univ U' b).
    Proof.
      intros.

      assert (universe_ok U) as UNIV_OK by assumption.
      assert (universe_ok (strip_adversary_univ U b)) as STRIP_UNIV_OK by eauto using ok_universe_strip_adversary_still_ok.

      remember U as UU; destruct U; rename UU into U.

      match goal with
      | [ H : indexedRealStep _ _ _ _ |- _ ] => eapply labeled_indexed_univ_step_inv in H; eauto
      end; split_ex.

      rename H into for_split.
      unfold universe_ok in for_split; split_ands; simpl in *.
      destruct x0; simpl in *.

      rewrite HeqUU in H4; unfold build_data_step in H4; simpl in *.
      rewrite HeqUU; unfold strip_adversary_univ; simpl; econstructor; simpl in *.
      - eapply clean_users_cleans_user; eauto.
      - unfold build_data_step; simpl.
        destruct x; simpl in *.
        eapply honest_labeled_step_advuniv_implies_honest_step_origuniv'; subst; simpl in *; eauto.

      - unfold buildUniverse; subst; simpl in *.
        subst; simpl in *.
        remember (x1 $+ (uid, {| key_heap := x5
                                 ; protocol := x11
                                 ; msg_heap := x6
                                 ; from_nons := x7
                                 ; sent_nons := x8
                                 ; cur_nonce := x9
                                 ; c_heap := x10 |})) as usrs''.

        assert (clean_ciphers (findUserKeys usrs'') x3 = clean_ciphers (findUserKeys x1) x3
              /\ clean_messages (findUserKeys usrs'') x3 (Some uid) x7 x6 = clean_messages (findUserKeys x1) x3 (Some uid) x7 x6
              /\ clean_users (findUserKeys usrs'') x3 usrs'' =
                clean_users (findUserKeys x1) x3 x1 $+ (uid, {| key_heap := clean_key_permissions (findUserKeys x1) x5
                                                         ; protocol := x11
                                                         ; msg_heap := clean_messages (findUserKeys x1) x3 (Some uid) x7 x6
                                                         ; from_nons := x7
                                                         ; sent_nons := x8
                                                         ; cur_nonce := x9
                                                         ; c_heap := x10 |})
              /\ clean_adv x2 (findUserKeys usrs'') x3 b = clean_adv x2 (findUserKeys users) x3 b
              /\ clean_keys (findUserKeys usrs'') x4 = clean_keys (findUserKeys x1) x4 ).
        destruct x; simpl in *; clean_map_lookups; clean_context.
        invert H7.
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.

        invert H7; split_ex.

        f_equal; auto.
    Qed.

    Hint Resolve dishonest_cipher_cleaned.

    Lemma  adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' froms' sents' cur_n' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> cs__s = clean_ciphers honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.
    Qed.

    Lemma clean_keys_drops_added_dishonest_key :
      forall honestk gks k_id ku kt,
        ~ In k_id gks
        -> honestk $? k_id = None
        -> clean_keys honestk (gks $+ (k_id, {| keyId := k_id; keyUsage := ku; keyType := kt |}))
          = clean_keys honestk gks.
    Proof.
      intros; unfold clean_keys, filter; apply map_eq_Equal; unfold Equal; intros.
      rewrite fold_add; eauto.
      unfold honest_key_filter_fn; context_map_rewrites; trivial.
    Qed.

    Hint Resolve clean_keys_drops_added_dishonest_key.

    Lemma adv_step_implies_no_new_keys_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' froms' sents' cur_n' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk gks__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> honestk = findUserKeys usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)

          -> gks__s = clean_keys honestk gks
          -> forall cmd' honestk' gks__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> gks__s' = clean_keys honestk' gks'
              -> gks__s = gks__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        autorewrite with find_user_keys; eauto; clean_context;
          assert (~ In k_id gks) by (clean_map_lookups; auto);
          unfold keys_and_permissions_good in *; split_ands;
            assert (permission_heap_good gks (findUserKeys usrs')) as PHG by eauto;
            symmetry;
            cases (findUserKeys usrs' $? k_id); eauto;
              match goal with
              | [ H : findUserKeys _ $? _ = Some _ |- _ ] => specialize (PHG _ _ H); split_ex; contra_map_lookup; eauto
              end.
    Qed.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' froms' sents' cur_n' bd bd' suid,
        step_user lbl suid bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
          bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> suid = None
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> message_queues_ok cs usrs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> adv_cipher_queue_ok cs usrs adv.(c_heap)
          -> honest_nonces_ok cs usrs
          -> usrs__s = clean_users honestk cs usrs
          -> forall cmd' honestk' usrs__s',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 9; intros; subst; eauto;
        autorewrite with find_user_keys;
        clean_context;
        try erewrite clean_users_addnl_cipher_idempotent; eauto.

      (* Send *)
      rewrite clean_users_add_pull; simpl.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.

      erewrite clean_users_cleans_user; eauto; f_equal.

      cases (msg_signed_addressed (findUserKeys usrs) cs' (Some rec_u_id) msg);
        eauto using clean_messages_drops_msg_signed_addressed_false.

      assert (msg_signed_addressed (findUserKeys usrs) cs' (Some rec_u_id) msg = true) as MSA by assumption.
      
      unfold msg_signed_addressed in Heq;
        rewrite andb_true_iff in Heq;
        split_ands.
      unfold msg_honestly_signed, msg_signing_key in H;
        destruct msg; try discriminate;
          cases (cs' $? c_id); try discriminate.

      unfold adv_cipher_queue_ok in H24; rewrite Forall_forall in H24.
      simpl in H1; assert (List.In c_id (c_heap adv)) as LIN by eauto.
      specialize (H24 _ LIN); split_ex; split_ands.
      clean_map_lookups; rewrite <- honest_key_honest_keyb in H; invert H.
      unfold msg_to_this_user in H4; simpl in H4; context_map_rewrites;
        cases (cipher_to_user c ==n rec_u_id); subst; try discriminate.

      unfold clean_messages at 1; unfold clean_messages'.
      rewrite fold_left_app; simpl.
      rewrite MSA; context_map_rewrites.
      rewrite !fold_clean_messages2', !fold_clean_messages.

      match goal with
      | [ |- context [match (match ?mtc with _ => _ end) with _ => _ end ] ] => cases mtc
      end; eauto; simpl.

      exfalso.
      
      split_ors; split_ex; split_ands.
      - unfold msg_signed_addressed in MSA; rewrite andb_true_iff in MSA; split_ands.
        unfold msg_honestly_signed, msg_signing_key, cipher_signing_key in H8; context_map_rewrites.
        unfold cipher_honestly_signed in H6; destruct c; simpl in H6; rewrite H6 in H8; discriminate.
      - clean_context.
        unfold honest_nonces_ok in H25.
        specialize (H25 _ _ _ _ H8 H6 H2).
        unfold honest_nonce_tracking_ok in H25; split_ands.
        specialize (H14 _ _ H5 H); split_ands.
        rewrite Forall_forall in H4; specialize (H4 _ H9).

        apply count_occ_eq_0_clean_msgs in Heq.

        split_ex; split_ands; clean_map_lookups.
        split_ors; try contradiction.
        rewrite Exists_exists in H10; split_ex; split_ands.
        rewrite Forall_forall in H17; specialize (H17 _ H10); destruct x2; split_ands; eauto.
        specialize (H17 H11).
        unfold msg_nonce_not_same in H17; unfold msg_nonce_same in H18.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in H11;
          context_map_rewrites; destruct c0; try discriminate;
            cases (cs' $? c_id0); try discriminate.
        assert (cipher_nonce c <> cipher_nonce c0) by eauto.
        assert (cipher_nonce c = cipher_nonce c0) by eauto.
        congruence.
    Qed.
    
    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : simpl_universe A -> IdealWorld.universe A -> Prop)
        (cmd : user_cmd (Base B)) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs froms sents cur_n,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> R (strip_adversary U__r) U__i

        -> keys_and_permissions_good U__r.(all_keys) U__r.(users) U__r.(adversary).(key_heap)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))

        -> message_queues_ok U__r.(all_ciphers) U__r.(users) U__r.(all_keys)
        -> encrypted_ciphers_ok (findUserKeys (users U__r)) U__r.(all_ciphers) U__r.(all_keys)
        -> adv_cipher_queue_ok U__r.(all_ciphers) U__r.(users) U__r.(adversary).(c_heap)
        -> honest_nonces_ok U__r.(all_ciphers) U__r.(users)

                             
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := ks
                                                            ; protocol := cmd
                                                            ; msg_heap := qmsgs
                                                            ; c_heap   := mycs
                                                            ; from_nons := froms
                                                            ; sent_nons := sents
                                                            ; cur_nonce := cur_n |})) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.

      Hint Resolve
           adv_step_implies_no_user_impact_after_cleaning
           adv_step_implies_no_new_keys_after_cleaning
           adv_step_implies_no_new_ciphers_after_cleaning.

      (* some rewrites to get the goal matching the R assumption *)
      match goal with
      | [ H : R {| s_users := ?us ; s_all_ciphers := ?cs ; s_all_keys := ?ks |} _
          |- R {| s_users := ?us' ; s_all_ciphers := ?cs' ; s_all_keys := ?ks' |} _ ] =>
        assert (cs = cs') as CS by eauto;
          assert (us = us') as US by eauto;
          assert (ks = ks') as KS by eauto
      end;
        rewrite <- CS, <- US, <- KS;
        trivial.
    Qed.

    Hint Resolve encrypted_ciphers_ok_new_honest_key_adv_univ.
    Hint Resolve users_permission_heaps_good_merged_permission_heaps_good.
    
    Lemma honest_silent_step_adv_univ_enc_ciphers_ok :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
            -> honestk = findUserKeys usrs
            -> encrypted_ciphers_ok honestk cs gks
            -> user_cipher_queues_ok cs honestk usrs
            -> keys_and_permissions_good gks usrs adv.(key_heap)
            -> next_cmd_safe honestk cs u_id froms sents cmd
            -> lbl = Silent
            -> forall cmd' usrs'',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
                -> forall cmdc cmdc' honestk',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 7; intros; subst;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        keys_and_permissions_prop;
        clean_context;
        process_next_cmd_safe;
        eauto.

      - econstructor; eauto.
        eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto 2.
      - user_cipher_queues_prop; encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.
      - econstructor; eauto.
        econstructor; eauto 2.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
    Qed.

    Ltac new_key_not_in_honestk :=
      repeat
          match goal with
          | [ H : keys_and_permissions_good ?global_keys ?honusrs _ |- _ ] =>
            assert (permission_heap_good global_keys (findUserKeys honusrs))
              by (unfold keys_and_permissions_good in *; split_ands; eauto using users_permission_heaps_good_merged_permission_heaps_good);
            clear H
          | [ H1 : findUserKeys ?honusrs $? ?kid = Some _
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- _ ] =>
            specialize (H2 _ _ H1); split_ex; contra_map_lookup
          | [ H1 : ?global_keys $? ?kid = None
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- ~ In ?kid (findUserKeys ?honusrs) ] =>
            cases (findUserKeys honusrs $? kid); clean_map_lookups; eauto 2
          end.

    Lemma action_adversary_safe_after_before_cleaning' :
      forall honestk honestk' cs a,
        (forall k_id, honestk' $? k_id = Some true -> honestk $? k_id = Some true)
        -> action_adversary_safe honestk' (clean_ciphers honestk cs) a
        -> action_adversary_safe honestk  cs a.
    Proof.
      intros * HONK AA.
      destruct a; unfold action_adversary_safe in *; split_ex; subst; eauto.

      - split; eauto 8.
        invert H; econstructor; eauto.
      - repeat (apply conj); eauto 8.
        + invert H.
          rewrite H4.
          rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H3;
            unfold honest_cipher_filter_fn in H3; split_ands.
          unfold msg_honestly_signed, msg_signing_key in *; context_map_rewrites.
          rewrite cipher_honestly_signed_honest_keyb_iff in H2; auto.

        + unfold msg_to_this_user in *; simpl in *; context_map_rewrites.
          match goal with
          | [ H : clean_ciphers _ _ $? _ = Some _ |- _ ] => apply clean_ciphers_inv in H
          end; simpl; context_map_rewrites; eauto.

        + unfold msgCiphersSignedOk in *; rewrite Forall_forall in *; intros; eauto.
          destruct x1; simpl in *.
          specialize (H1 _ H2); simpl in *; eauto.
          unfold msg_honestly_signed in *.
          unfold msg_signing_key in *; simpl in *; destruct c;
            try discriminate;
            context_map_rewrites.

          cases (clean_ciphers honestk cs $? c_id); try discriminate.
          repeat
          match goal with
          | [ H : clean_ciphers _ _ $? _ = Some _ |- _ ] => apply clean_ciphers_inv in H
          end; simpl; context_map_rewrites; eauto.
    Qed.

    Lemma action_adversary_safe_after_before_cleaning :
      forall {A} (usrs : honest_users A) cs a,
          action_adversary_safe (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_ciphers (findUserKeys usrs) cs) a
        -> action_adversary_safe (findUserKeys usrs) cs a.
    Proof.
      intros; eapply action_adversary_safe_after_before_cleaning'; swap 1 2; eauto.
    Qed.

    Hint Resolve
         (* cipher_action_safe_after_before_cleaning *)
         action_adversary_safe_after_before_cleaning.

    Lemma honest_silent_new_cipher_implies_honest_step_origuniv' :
      forall {t A B} (msg : message t) (msg_c : crypto t) (usrs : honest_users A) (adv : user_data B) 
        cs cs' c_id c gks u_id honestk ks qmsgs mycs froms sents cur_n b k__signid msg_to enc_cmd kt,
        ~ In c_id cs
        -> honestk = findUserKeys usrs
        -> cs' = cs $+ (c_id,c)
        -> msg_c = SignedCiphertext c_id
        -> ks $? k__signid = Some true
        -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt)
        -> ( ( enc_cmd = Sign k__signid msg_to msg
              /\ c = SigCipher k__signid msg_to (Some u_id,cur_n) msg
              /\ keys_mine ks (findKeysMessage msg)
            )
          \/ ( exists k__encid kp kt__e,
                  enc_cmd = SignEncrypt k__signid k__encid msg_to msg
                /\ ks $? k__encid = Some kp
                /\ gks $? k__encid = Some (MkCryptoKey k__encid Encryption kt__e)
                /\ keys_mine ks (findKeysMessage msg)
                /\ c = SigEncCipher k__signid k__encid msg_to (Some u_id,cur_n) msg)
          )
        -> message_queues_ok cs usrs gks
        -> next_cmd_safe honestk cs u_id froms sents enc_cmd
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, enc_cmd)
                    (  clean_users honestk cs' usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs'
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs' (Some u_id) froms qmsgs
                     , (c_id :: mycs), froms, sents, 1+cur_n, @Return (Crypto t) msg_c ).
    Proof.
      intros; split_ex; subst.
      assert (findUserKeys usrs $? k__signid = Some true) by eauto 2.

      split_ors; subst;
        erewrite clean_messages_addnl_cipher_idempotent, clean_users_addnl_cipher_idempotent; eauto;
          process_next_cmd_safe;
          econstructor; eauto.

      unfold keys_mine in *; intros. 
      repeat
        match goal with
        | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG)
        end.
      split_ors; assert (findUserKeys usrs $? k_id = Some true) by eauto; eauto.

      unfold keys_mine in *; intros. 
      repeat
        match goal with
        | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG)
        end.
      split_ors; assert (findUserKeys usrs $? k_id = Some true) by eauto; eauto.
    Qed.

    Lemma msg_accepted_by_pattern_after_cleaning_honest_key :
      forall {t} (msg : crypto t) cs u_id froms pat k_id c_id honestk,
        msg = SignedCiphertext c_id
        -> msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> msg_signing_key cs msg = Some k_id
        -> honest_key honestk k_id
        -> msg_accepted_by_pattern (clean_ciphers honestk cs) (Some u_id) froms pat msg.
    Proof.
      intros.
      invert H0; econstructor; eauto; clean_context.
      - eapply clean_ciphers_keeps_honest_cipher; eauto.
        invert H2.
        unfold msg_signing_key in H1; context_map_rewrites; clean_context.
        unfold honest_cipher_filter_fn, cipher_honestly_signed.
        unfold honest_keyb; context_map_rewrites; eauto.
      - eapply clean_ciphers_keeps_honest_cipher; eauto.
        invert H2.
        unfold msg_signing_key in H1; context_map_rewrites; clean_context.
        unfold honest_cipher_filter_fn, cipher_honestly_signed.
        unfold honest_keyb; context_map_rewrites; eauto.
    Qed.

    Hint Resolve msg_accepted_by_pattern_after_cleaning_honest_key.

    Lemma honest_labeled_recv_implies_honest_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs: honest_users A) (adv : user_data B) usrs__s cs__s
        cs gks u_id honestk honestk' pat ks qmsgs mycs froms froms' sents cur_n pubk b,
          msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> honestk = findUserKeys usrs
        -> froms' = updateTrackedNonce (Some u_id) froms cs msg
        -> cs__s = clean_ciphers honestk cs
        -> usrs__s = clean_users honestk cs usrs
        -> pubk = findKeysCrypto cs msg
        -> honestk' = findUserKeys usrs $k++ pubk
        -> message_queue_ok honestk cs (existT _ _ msg :: qmsgs) gks
        -> next_cmd_safe honestk cs u_id froms sents (@Recv t pat)
        -> step_user (Action (Input msg pat froms)) (Some u_id)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs),
                     mycs, froms, sents, cur_n, @Recv t pat)
                    (clean_users honestk' cs usrs,
                     clean_adv adv honestk' cs b,
                     clean_ciphers honestk' cs,
                     clean_keys honestk' gks,
                     clean_key_permissions honestk' (ks $k++ pubk),
                     clean_messages honestk' cs (Some u_id) froms' qmsgs,
                     findCiphers msg ++ mycs,
                     updateTrackedNonce (Some u_id) froms cs msg, sents, cur_n, @Return (Crypto t) msg).
    Proof.
      intros; process_next_cmd_safe; subst.

      assert (msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg = true)
        as MSA by (unfold msg_signed_addressed; eauto using accepted_safe_msg_pattern_honestly_signed
                                                          , accepted_safe_msg_pattern_to_this_user).
      unfold clean_messages at 1.
      unfold clean_messages', msg_filter; simpl.
      rewrite !MSA.

      generalize MSA; intros MSA'; unfold msg_signed_addressed in MSA'; apply andb_true_iff in MSA'; split_ands.
      pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ H0); split_ands; split_ex.
      eapply msg_honestly_signed_signing_key_honest in H0; eauto.

      generalize (accepted_safe_msg_pattern_replay_safe H7 H); intros; split_ex;
        subst.
      unfold msg_nonce_ok at 2; context_map_rewrites.
      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H8;
        rewrite H8.
      rewrite fold_clean_messages1' , clean_messages'_fst_pull, fold_clean_messages.
      invert H6; split_ands.

      specialize (H9 _ H2); split_ands.
      specialize (H10 H0); split_ands.
      unfold message_no_adv_private in H10.

      match goal with
      | [ |- context [ findUserKeys usrs $k++ ?pubk ]] => 
        assert (findUserKeys usrs $k++ pubk = findUserKeys usrs) as MKRW
      end.
      maps_equal; solve_perm_merges;
        repeat
          match goal with
          | [ H : (forall _ _, findKeysCrypto _ _ $? _ = Some _ -> _), ARG : findKeysCrypto _ _ $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          end; clean_map_lookups; eauto.

      rewrite MKRW.
      eapply StepRecv; eauto.

      * unfold updateTrackedNonce; context_map_rewrites.
        unfold msg_to_this_user, msg_destination_user in H1; context_map_rewrites.
        destruct (cipher_to_user x2 ==n u_id); subst; try discriminate.
        destruct (cipher_to_user x2 ==n cipher_to_user x2); try contradiction.
        rewrite H8 ; trivial.
      * rewrite clean_key_permissions_distributes_merge_key_permissions.
        match goal with
        | [ |- context [ ?same $k++ ?fst = ?same $k++ ?snd ]] => assert (fst = snd)
        end.
        maps_equal.
        cases (@findKeysCrypto t0 cs (SignedCiphertext x1) $? y).
        ** specialize (H10 _ _ Heq0); split_ands; subst.
           erewrite clean_key_permissions_keeps_honest_permission; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq0; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.
           unfold honest_cipher_filter_fn, cipher_honestly_signed;
             destruct x2; eauto.
           unfold msg_signing_key in H2; context_map_rewrites; clean_context.
           invert H0.
           unfold honest_keyb; context_map_rewrites; trivial.
        ** rewrite clean_key_permissions_adds_no_permissions; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq0; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.
           unfold msg_signing_key in H2; context_map_rewrites; clean_context.
           eapply honest_cipher_filter_fn_true_honest_signing_key; eauto.
        ** rewrite H13; trivial.
           
    Qed.

    Lemma keys_mine_after_cleaning :
      forall honestk ks chkkeys,
        keys_mine ks chkkeys
        -> (forall k_id kp, ks $? k_id = Some kp -> honestk $? k_id = Some true)
        -> keys_mine (clean_key_permissions honestk ks) chkkeys.
    Proof.
      unfold keys_mine; intros * KM KH * ARG.
      specialize (KM _ _ ARG); split_ors;
        match goal with
        | [ ARG : ?ks $? _ = Some _, H : (forall _ _, ?ks $? _ = Some _ -> _) |- _ ] => specialize (H _ _ ARG)
        end; erewrite clean_key_permissions_keeps_honest_permission; eauto.
    Qed.

    Hint Resolve keys_mine_after_cleaning.
    
    Lemma honest_labeled_send_implies_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs: honest_users A) (adv : user_data B) rec_u
        cs gks u_id rec_u_id honestk ks qmsgs mycs froms sents cur_n b,
        keys_mine ks (findKeysCrypto cs msg)
        -> incl (findCiphers msg) mycs
        -> usrs $? rec_u_id = Some rec_u
        -> Some rec_u_id <> Some u_id
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> honest_nonces_ok cs usrs
        -> honest_users_only_honest_keys usrs
        -> next_cmd_safe honestk cs u_id froms sents (Send rec_u_id msg)
        -> forall cmdc,
            usrs $? u_id =
            Some
              {|
                key_heap := ks;
                protocol := cmdc;
                msg_heap := qmsgs;
                c_heap := mycs;
                from_nons := froms;
                sent_nons := sents;
                cur_nonce := cur_n |}
            -> step_user (Action (Output msg (Some u_id) (Some rec_u_id) sents))
                    (Some u_id)
                    (clean_users honestk cs usrs,
                     clean_adv adv honestk cs b,
                     clean_ciphers honestk cs,
                     clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms qmsgs, mycs,
                     froms, sents, cur_n, Send rec_u_id msg)
                    (clean_users honestk cs
                                 (usrs $+ (rec_u_id,
                                           {|
                                             key_heap := key_heap rec_u;
                                             protocol := protocol rec_u;
                                             msg_heap := msg_heap rec_u ++ [existT _ _ msg];
                                             c_heap := c_heap rec_u;
                                             from_nons := from_nons rec_u;
                                             sent_nons := sent_nons rec_u;
                                             cur_nonce := cur_nonce rec_u |})),
                     clean_adv
                       {| key_heap := key_heap adv $k++ findKeysCrypto cs msg;
                          protocol := protocol adv;
                          msg_heap := msg_heap adv ++ [existT _ _ msg];
                          c_heap := c_heap adv;
                          from_nons := from_nons adv;
                          sent_nons := sent_nons adv;
                          cur_nonce := cur_nonce adv |} honestk cs b,
                     clean_ciphers honestk cs,
                     clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms qmsgs,
                     mycs, froms,
                     updateSentNonce (Some rec_u_id) sents cs msg, cur_n, ret tt).
    Proof.
      intros; subst; eauto.
      process_next_cmd_safe; subst.
      econstructor; eauto using clean_users_cleans_user; simpl.

      - simpl in *.
        assert (List.In x mycs) by eauto; user_cipher_queues_prop.
        erewrite clean_ciphers_keeps_honest_cipher; eauto 3.

      - simpl. rewrite clean_users_add_pull; simpl.
        erewrite clean_messages_keeps_hon_signed; eauto 8.
        unfold msg_signed_addressed; eauto.

      - unfold clean_adv; simpl.
        simpl in H0; assert (List.In x mycs) by eauto; 
          user_cipher_queues_prop.
        rewrite clean_adv_msgs_keeps_honest_msg; eauto.
        rewrite clean_key_permissions_distributes_merge_key_permissions.
        erewrite clean_ciphers_keeps_honest_cipher; eauto.

        unfold cipher_honestly_signed in H16; destruct x1; eauto.
        encrypted_ciphers_prop.

        assert(clean_key_permissions (findUserKeys usrs) (findKeysMessage msg) = findKeysMessage msg)
          as RW.
        maps_equal.
        cases (findKeysMessage msg $? y); eauto 12 using clean_key_permissions_adds_no_permissions.
        eapply clean_key_permissions_keeps_honest_permission; eauto.
        unfold honest_perm_filter_fn.
        specialize (H24 _ _ Heq); split_ands; context_map_rewrites; trivial.

        rewrite RW; trivial.
    Qed.

    Hint Resolve
         updateTrackedNonce_clean_ciphers_idempotent_honest_msg
         updateSentNonce_clean_ciphers_idempotent_honest_msg
         : core.

    Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv'' :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' (b: <<Base B>>),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
          -> honest_users_only_honest_keys usrs
          -> honest_nonces_ok cs usrs
          -> next_cmd_safe honestk cs u_id froms sents cmd
          -> forall cmd' cs__s' usrs__s' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_nons := froms
                                       ; sent_nons := sents
                                       ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_nons := froms'
                                              ; sent_nons := sents'
                                              ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' cs' usrs'
                  -> step_user lbl suid
                              (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks,
                               clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs__s', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks',
                               clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd')
                  \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                    = (clean_users honestk' cs' usrs', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                       clean_key_permissions honestk' ks',
                       clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd').
    Proof.
      induction 1; inversion 5; inversion 9; intros; subst; clean_context;
        autorewrite with find_user_keys in *;
        try solve [ left; econstructor; eauto;
                    user_cipher_queues_prop; eauto;
                    try solve_clean_keys_clean_key_permissions];
        eauto using honest_silent_recv_implies_honest_or_no_step_origuniv;
        try solve [ left; 
                    eauto 12 using honest_labeled_send_implies_step_origuniv
                    , honest_silent_new_cipher_implies_honest_step_origuniv'
                    , honest_silent_decrypt_implies_honest_step_origuniv
                    , honest_silent_new_key_implies_honest_step_origuniv].

      - apply next_action_next_cmd_safe_bind in H23.

        remember (findUserKeys usrs) as honestk.
        remember (usrs' $+ (u_id, {| key_heap := ks'
                                   ; protocol := cmdc'
                                   ; msg_heap := qmsgs'
                                   ; c_heap := mycs'
                                   ; from_nons := froms'
                                   ; sent_nons := sents'
                                   ; cur_nonce := cur_n' |})) as usrs''.
        remember (findUserKeys usrs'') as honestk'.

        specialize (IHstep_user _ _ _ _
                                b eq_refl
                                _ _ _ _
                                Heqhonestk
                                eq_refl
                                eq_refl
                                eq_refl
                                H5
                                H17
                                H18
                                H19
                                H20
                                H21
                                H22
                                H23
                                _ _ _ _
                                eq_refl
                                _ _ _
                                H25
                                Hequsrs''
                                Heqhonestk'
                                eq_refl
                                eq_refl

                 ); split_ors; clean_context.
        + left; econstructor; eauto.
        + right; unfold clean_adv; simpl.
          inversion H0; clear H0; subst.
          assert (clean_users (findUserKeys usrs) cs usrs
                  = clean_users
                      (findUserKeys
                         (usrs' $+ (u_id,
                                    {|
                                      key_heap := ks';
                                      protocol := cmdc';
                                      msg_heap := qmsgs';
                                      c_heap := mycs';
                                      from_nons := froms';
                                      sent_nons := sents';
                                      cur_nonce := cur_n' |}))) cs' usrs')
                 as USRSRW
                 by (unfold clean_users, mapi; eauto using map_eq_fields_eq).
          rewrite USRSRW; f_equal.

      - left; eapply honest_labeled_recv_implies_honest_step_origuniv; eauto 12.
        unfold message_queues_ok in H25; rewrite Forall_natmap_forall in H25.
        specialize (H25 _ _ H32); eauto.
    Qed.

    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
        universe_ok U
        -> adv_universe_ok U
        -> user_cipher_queues_ok U.(all_ciphers) (findUserKeys U.(users)) U.(users)
        -> U.(users) $? u_id = Some userData
        -> step_user Silent (Some u_id)
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        -> honest_users_only_honest_keys U.(users)
        -> honest_cmds_safe U
        -> step_universe (Some u_id) (strip_adversary_univ U b) Silent (strip_adversary_univ U' b)
        \/ strip_adversary_univ U b = strip_adversary_univ U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H3 as RW. clear HeqRW.

      unfold adv_universe_ok, universe_ok in *; split_ands; simpl in *.
      unfold honest_cmds_safe in *; simpl in H.
      specialize (H6 _ _ _ eq_refl H2).
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv'' in RW; eauto.

      split_ors.
      - destruct adversary; unfold strip_adversary_univ; simpl in *.
        left.
        eapply StepUser; simpl; eauto.
        + eapply clean_users_cleans_user; eauto.
        + unfold build_data_step; simpl.
          unfold clean_adv; simpl.
          eauto.

        + unfold buildUniverse, clean_adv; simpl.
          f_equal.
          rewrite clean_users_add_pull; simpl.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          f_equal.

          assert (step_user Silent (Some u_id)
                            (users,
                             {|
                               key_heap := key_heap0;
                               protocol := protocol0;
                               msg_heap := msg_heap0;
                               c_heap := c_heap0;
                               from_nons := from_nons0;
                               sent_nons := sent_nons0;
                               cur_nonce := cur_nonce0 |}, all_ciphers, all_keys, key_heap, msg_heap,
                             c_heap, from_nons, sent_nons, cur_nonce, protocol)
                            (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)) as STEP by assumption.
          eapply honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs in H3; eauto; split_ands.

          eapply honest_silent_step_nochange_clean_adv_messages.
          exact STEP.
          all: (reflexivity || eassumption).
        + trivial.

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        inversion H13; subst.
        unfold clean_adv; simpl; f_equal.
        + rewrite clean_users_add_pull; simpl.
          assert (clean_users (findUserKeys users) all_ciphers users =
                  clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}))) cs usrs).
          unfold clean_users, map; apply map_eq_elements_eq; simpl; auto.
          rewrite <- H14.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          eapply clean_users_cleans_user; eauto.
          f_equal; eauto.
        + f_equal; eauto.
          rewrite H17.
          symmetry; eapply honest_silent_step_nochange_clean_adv_messages.
          exact H3.
          all : (reflexivity || eassumption).
          Unshelve. eauto.
    Qed.

    Lemma honest_cmd_safe_advuniv :
      forall {A} (cmd : RealWorld.user_cmd A) honestk honestk' cs u_id froms sents,
        next_cmd_safe honestk' (clean_ciphers honestk cs) u_id froms sents cmd
        -> (forall k_id, honestk' $? k_id = Some true -> honestk $? k_id = Some true)
        -> next_cmd_safe honestk cs u_id froms sents cmd.
    Proof.
      unfold next_cmd_safe; intros.
      specialize (H _ _ H1).

      cases cmd__n; split_ex; subst; intros; eauto;
        repeat simple apply conj; intros; eauto 8.

      - eapply msg_honestly_signed_after_without_cleaning; eauto.
        unfold RealWorld.msg_honestly_signed, RealWorld.msg_signing_key in *;
          context_map_rewrites;
          unfold RealWorld.honest_keyb in *.
        cases (honestk' $? RealWorld.cipher_signing_key x0); try discriminate;
          destruct b; try discriminate.
        specialize (H0 _ Heq); context_map_rewrites; eauto.

      - unfold RealWorld.msg_to_this_user, RealWorld.msg_destination_user in *;
          context_map_rewrites.
        erewrite clean_ciphers_inv; eauto.

      - eapply msgCiphersSigned_before_clean_ciphers; eauto.
        unfold RealWorld.msgCiphersSignedOk in *; simpl in *.
        invert H3; econstructor; eauto.
        unfold RealWorld.msg_honestly_signed, RealWorld.msg_signing_key in *;
          context_map_rewrites;
          unfold RealWorld.honest_keyb in *.
        cases (honestk' $? RealWorld.cipher_signing_key x0); try discriminate;
          destruct b; try discriminate.
        specialize (H0 _ Heq); context_map_rewrites; eauto.

      - invert H; econstructor; eauto.
      - specialize (H _ _ H2); split_ands; eauto.
    Qed.

    Ltac dt bd :=
      destruct bd as [[[[[[[[[[?usrs ?adv] ?cs] ?gks] ?ks] ?qmsgs] ?mycs] ?froms] ?sents] ?cur_n] ?cmd].
  
    Lemma honest_cmds_safe_advuniv :
      forall {A B} (U__ra : RealWorld.universe A B) b,
        honest_cmds_safe (strip_adversary_univ U__ra b)
        -> honest_cmds_safe U__ra.
    Proof.
      unfold honest_cmds_safe; intros. 
      generalize H1; intros CLEAN_USER;
      eapply clean_users_cleans_user
        with (honestk := RealWorld.findUserKeys U__ra.(RealWorld.users))
             (cs := U__ra.(RealWorld.all_ciphers))
        in CLEAN_USER; eauto.
      
      specialize (H _ _ _ eq_refl CLEAN_USER); simpl in *.
      eapply honest_cmd_safe_advuniv with
          (honestk' := (findUserKeys (clean_users (findUserKeys (users U__ra)) (all_ciphers U__ra) (users U__ra)))); eauto.
    Qed.
    (* Hint Resolve honest_cmds_safe_advuniv. *)

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl suid,
        step_universe suid U lbl U'
        -> lbl = Silent
        -> adv_universe_ok U
        -> honest_cmds_safe U
        -> universe_ok U
        -> universe_ok U'.
     Proof.
       intros A B U U' lbl SUID STEP e AUOK HCS UOK;
         rewrite e in *; clear e.

       unfold adv_universe_ok in AUOK; split_ands.
       invert STEP; eauto.

       - match goal with
         | [ H : users U $? _ = Some ?ud |- _ ] =>
           destruct U; destruct ud;
             unfold build_data_step, buildUniverse in *; simpl in *
         end.

         generalize (clean_users_cleans_user (findUserKeys users) all_ciphers users u_id H7 eq_refl);
           intros CLEAN_USER; simpl in CLEAN_USER.

         unfold honest_cmds_safe in HCS;
           specialize (HCS _ _ _ eq_refl H7); simpl in HCS.
         eapply honest_silent_step_adv_univ_enc_ciphers_ok; simpl; eauto.
         unfold mkULbl in H10; destruct lbl0; try discriminate; trivial.
       
       - destruct U.
         unfold build_data_step, buildUniverseAdv in *; simpl in *.
         eapply adv_step_encrypted_ciphers_ok; eauto.
     Qed.
     
  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user.

  Hint Extern 1 (RealWorld.step_user _ _ (RealWorld.build_data_step _ _) _) =>
    progress unfold RealWorld.build_data_step.

  Hint Extern 1 (RealWorld.step_user _ _ (_, _, _ , RealWorld.protocol _) _) => 
    match goal with
    | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H
    end.

  Hint Extern 1 (_ = _) => progress m_equal.
  Hint Extern 1 (_ = _) => progress f_equal.
  Hint Extern 1 (_ = _) =>
    progress unfold RealWorld.build_data_step, RealWorld.buildUniverse; simpl.
  Hint Extern 1 (_ = _) =>
    match goal with
    | [ H : RealWorld.adversary _ = _ |- _ ] => rewrite <- H
    end.
  Hint Extern 1 (_ = RealWorld.adversary _) => solve [ symmetry ; assumption ].

  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_silent_step (lameAdv b) R
      -> honest_actions_safe B R
      (* -> honest_users_only_honest_keys U__ra.(RealWorld.users) *)
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> forall suid U__ra',
          RealWorld.step_universe suid U__ra Silent U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 (* /\ universe_ok U__ra' *)
                 /\ R (strip_adversary U__ra') U__i'.
  Proof.
    intros.

    assert (universe_ok (strip_adversary_univ U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok U__ra) as AOK by assumption;
      unfold adv_universe_ok in AOK; split_ands.

    assert (adv_universe_ok (strip_adversary_univ U__ra b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.

    remember (strip_adversary_univ U__ra b) as U__r.
    assert (honest_cmds_safe U__r) as HCS by debug eauto.

    match goal with
    | [ H : RealWorld.step_universe _ _ _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
        as U__ra'.

      apply honest_cmds_safe_advuniv in HCS.
      unfold RealWorld.mkULbl in H16; destruct lbl; try discriminate.
      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H2 H6 H13 H14 HeqU__ra' H12 HCS); split_ors.

      + assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
          as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).

        specialize (H _ _ H3 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ _ H4); split_ex; split_ands; eauto.

      + exists U__i; intuition idtac; eauto.
        destruct U__ra; destruct U__ra'; simpl in *.
        unfold strip_adversary_univ in *; unfold strip_adversary in *; simpl in *.
        invert H4; eauto.
        assert (clean_users (RealWorld.findUserKeys users) all_ciphers users = clean_users (RealWorld.findUserKeys users0) all_ciphers0 users0)
          as CLEAN_USERS by (unfold clean_users, mapi; auto).
        rewrite <- CLEAN_USERS; auto.

    (* Adversary step *)
    - exists U__i; intuition auto.
      eapply adv_step_stays_in_R; eauto.

  Qed.

  Lemma honest_key_is_honest_clean_key :
    forall {A} (us : RealWorld.honest_users A) k cs,
      RealWorld.honest_key (RealWorld.findUserKeys us) k
      -> RealWorld.honest_key (RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys us) cs us)) k.
  Proof.
    intros; invert H. pose proof @findUserKeys_clean_users_correct A us cs k; rewrite H0 in H; constructor. assumption.
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

  Lemma msg_not_honestly_signed_before_after_cleaning :
    forall {t} (msg : RealWorld.crypto t) honestk cs,
      RealWorld.msg_honestly_signed honestk cs msg = false
      -> RealWorld.msg_honestly_signed honestk (clean_ciphers honestk cs) msg = false.
  Proof.
    intros.
    unfold RealWorld.msg_honestly_signed in *.
    cases (RealWorld.msg_signing_key cs msg); 
      unfold RealWorld.msg_signing_key in *; destruct msg; try discriminate; eauto;
        cases (cs $? c_id); try discriminate.

    - invert Heq.
      erewrite clean_ciphers_eliminates_dishonest_cipher; eauto.
    - erewrite clean_ciphers_no_new_ciphers; eauto.
  Qed.

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
    unfold honest_cipher_filter_fn, RealWorld.cipher_honestly_signed; destruct c; eauto.
  Qed.

  Lemma rewrite_clean_messages_cons :
    forall cs honestk uid froms msgs t (msg : RealWorld.crypto t) c n,
      not_replayed cs honestk uid froms msg = true
      -> match msg with
        | RealWorld.SignedCiphertext cid => cs $? cid = Some c /\ RealWorld.cipher_nonce c = n
        | _ => False
        end
      -> clean_messages honestk cs (Some uid) froms ((existT _ _ msg) :: msgs)
        = (existT _ _ msg) :: clean_messages honestk cs (Some uid) (n :: froms) msgs.
  Proof.
    intros; unfold clean_messages at 1, clean_messages'.
    simpl.
    unfold not_replayed in H; rewrite !andb_true_iff in H; split_ex.
    cases (msg_nonce_ok cs froms msg); try discriminate.
    unfold RealWorld.msg_signed_addressed.
    rewrite H, H2; simpl.
    destruct msg; try contradiction; split_ex; subst; trivial.
    rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; simpl.
    unfold msg_nonce_ok in Heq; context_map_rewrites.
    cases (count_occ RealWorld.msg_seq_eq froms (RealWorld.cipher_nonce c)); try discriminate.
    invert Heq; trivial.
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
    pose proof (clean_messages_cons_split cs honestk uid froms msgs _ _ c eq_refl);
      split_ors; split_ex.

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
    pose proof (clean_messages_cons_split cs honestk uid froms msgs _ _ c eq_refl);
      split_ors; split_ex.

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

  Lemma action_matches_strip :
    forall cs gks honestk uid ra ia,
      action_matches (clean_ciphers honestk cs) (clean_keys honestk gks)
                     (uid, strip_action honestk cs ra) ia
      -> action_matches cs gks (uid,ra) ia.
  Proof.
    intros.
    Hint Constructors action_matches : core.

    invert H;
      repeat
        match goal with
        | [ H : _ = strip_action _ _ ?ra |- _ ] =>
          unfold strip_action in H; destruct ra; try discriminate
        | [ H : RealWorld.Input _ _ _ = RealWorld.Input _ _ _ |- _ ] =>
          invert H
        | [ H : RealWorld.Output _ _ _ _ = RealWorld.Output _ _ _ _ |- _ ] =>
          invert H
        | [ H : clean_ciphers _ _ $? _ = Some _ |- _ ] =>
          eapply clean_ciphers_inv in H
        end; eauto using content_eq_strip_keys.
  Qed.
  
  Hint Resolve action_matches_strip.

  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_labeled_step (lameAdv b) R
      -> honest_actions_safe B R
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      -> forall uid U__ra' a__r,
          indexedRealStep uid (Action a__r) U__ra U__ra'
          -> exists a__i U__i' U__i'',
            (indexedIdealStep uid Silent) ^* U__i U__i'
            /\ indexedIdealStep uid (Action a__i) U__i' U__i''
            /\ action_matches U__ra.(RealWorld.all_ciphers) U__ra.(RealWorld.all_keys) (uid,a__r) a__i
              /\ R (strip_adversary U__ra') U__i''.
  Proof.
    intros.

    assert (universe_ok (strip_adversary_univ U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok (strip_adversary_univ U__ra b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.

    unfold adv_universe_ok in H3; split_ands.

    assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
      as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).

    assert ( indexedRealStep uid
                             (Action (strip_action (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.all_ciphers) a__r))
                             (strip_adversary_univ U__ra b)
                             (strip_adversary_univ U__ra' b)) as UNIV_STEP.

    remember (strip_adversary_univ U__ra b) as U__r.
    assert (honest_cmds_safe U__r) as HCS by eauto.
    rewrite HeqU__r in HCS.
    apply honest_cmds_safe_advuniv in HCS.
    subst.
    eapply indexed_labeled_honest_step_advuniv_implies_stripped_univ_step; eauto using honest_cmds_implies_safe_actions.
    invert H4; eapply honest_cmds_implies_safe_actions; eauto.
    econstructor 1; eauto.

    specialize (H _ _ H1 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ _ _ UNIV_STEP); split_ex.
    do 3 eexists; intuition idtac; eauto.

    unfold strip_adversary_univ in H13; simpl in H13; eauto.
    
  Qed.

  Definition ciphers_honestly_signed (honestk : key_perms) (cs : RealWorld.ciphers) :=
    Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) cs.

  Definition keys_honest (honestk : key_perms) (ks : keys) :=
    Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) ks.

  Definition universe_starts_ok {A B} (U : RealWorld.universe A B) :=
    let honestk := RealWorld.findUserKeys U.(RealWorld.users)
    in  (forall u_id u,
            U.(RealWorld.users) $? u_id = Some u
            -> u.(RealWorld.msg_heap) = []
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
      /\ ciphers_honestly_signed honestk U.(RealWorld.all_ciphers)
      /\ keys_honest honestk U.(RealWorld.all_keys)
  .

  Lemma universe_starts_ok_clean_ciphers_idempotent :
    forall honestk cs,
      Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) cs
      -> clean_ciphers honestk cs = cs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in H.
    apply map_eq_Equal; unfold Equal; intros.

    cases (cs $? y); auto.
    - eapply clean_ciphers_keeps_honest_cipher; auto.
      unfold honest_cipher_filter_fn; eauto.
    - apply clean_ciphers_no_new_ciphers; auto.
  Qed.

  Hint Unfold honest_cipher_filter_fn.

  Lemma universe_starts_ok_clean_keys_idempotent :
    forall honestk ks,
      Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) ks
      -> (forall k_id k,
            ks $? k_id = Some k
            -> keyId k = k_id)
      -> clean_keys honestk ks = ks.
  Proof.
    intros.
    rewrite Forall_natmap_forall in H.
    apply map_eq_Equal; unfold Equal; intros.
    cases (ks $? y); eauto using clean_keys_adds_no_keys.
    eapply clean_keys_keeps_honest_key; eauto.
    specialize (H _ _ Heq); invert H.
    specialize (H0 _ _ Heq).
    unfold honest_key_filter_fn; rewrite H0 in H1; context_map_rewrites; trivial.
  Qed.

  Lemma universe_starts_ok_clean_key_permissions_idempotent :
    forall honestk perms,
      (forall k_id kp, perms $? k_id = Some kp -> honestk $? k_id = Some true)
      -> clean_key_permissions honestk perms = perms.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (perms $? y); eauto using clean_key_permissions_adds_no_permissions.
    assert (honestk $? y = Some true) as HONK by eauto.
    eapply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial.
  Qed.

  Lemma universe_starts_ok_clean_users_idempotent :
    forall {A} (usrs : RealWorld.honest_users A) honestk cs,
      honestk = RealWorld.findUserKeys usrs
      -> (forall u_id u,
            usrs $? u_id = Some u
            -> u.(RealWorld.msg_heap) = []
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
      -> clean_users honestk cs usrs = usrs.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal, clean_users; intros; rewrite mapi_o; intros; subst; trivial.
    cases (usrs $? y); auto.
    specialize (H0 _ _ Heq); split_ands.
    destruct u; simpl in *; subst.
    f_equal; f_equal; eauto using universe_starts_ok_clean_key_permissions_idempotent.
  Qed.

  Lemma simulates_start_ok_adding_adversary :
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) b advcode,
        lameAdv b U__r.(RealWorld.adversary)
      -> U__ra = add_adversary U__r advcode
      -> R (RealWorld.peel_adv U__r) U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> universe_starts_ok U__r
      -> R (strip_adversary U__ra) U__i
      /\ universe_ok U__ra
      /\ adv_universe_ok U__ra.
  Proof.
    intros.
    unfold universe_ok, adv_universe_ok, lameAdv, RealWorld.peel_adv in *; split_ands; subst; simpl in *.
    destruct U__r; destruct adversary; simpl in *.
    intuition eauto.

    unfold strip_adversary; subst; simpl.

    unfold universe_starts_ok in *;
      split_ands.
    rewrite clean_ciphers_idempotent
          , universe_starts_ok_clean_keys_idempotent
          , universe_starts_ok_clean_users_idempotent;
      unfold keys_and_permissions_good in *; split_ands;
      auto.
  Qed.

  Lemma strip_adv_simpl_peel_same_as_strip_adv :
    forall {A B} (U : RealWorld.universe A B),
      strip_adversary_simpl (RealWorld.peel_adv U) = strip_adversary U.
  Proof.
    unfold strip_adversary, strip_adversary_simpl, RealWorld.peel_adv; intros.
    trivial.
  Qed.

  Lemma strip_adversary_same_as_peel_strip_simpl :
    forall {A B} (U : RealWorld.universe A B) b,
      strip_adversary U = RealWorld.peel_adv (strip_adversary_univ U b).
  Proof.
    unfold strip_adversary, strip_adversary_simpl, RealWorld.peel_adv; intros.
    trivial.
  Qed.

  Lemma strip_adv_simpl_strip_adv_idempotent :
    forall {A B} (U : RealWorld.universe A B),
      strip_adversary_simpl (strip_adversary U) = strip_adversary U.
  Proof.
    unfold strip_adversary_simpl, strip_adversary; simpl; intros.
    f_equal; eauto using clean_users_idempotent'
                       , clean_keys_ok_extra_user_cleaning
                       , clean_ciphers_ok_extra_user_cleaning.
  Qed.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates (lameAdv b) R U__r U__i
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__ra advcode R',
          U__ra = add_adversary U__r advcode
          -> R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
          -> simulates (@awesomeAdv B) R' U__ra U__i.
    intros.
    inversion H as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__honactsafe H__o]; clear H__s.
    inversion H__o as [R__start OK__start]; clear H__o.

    unfold simulates; rewrite H5.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, honest_actions_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.

    - subst.
      unfold honest_actions_safe; intros.

      apply honest_cmds_safe_advuniv with (b0:=b).
      eapply H__honactsafe;
        eauto using ok_universe_strip_adversary_still_ok
                  , ok_adv_universe_strip_adversary_still_ok.
  Qed.

  Theorem simulates_ok_with_adversary' :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : RealWorld.denote (RealWorld.Base B)),
        U__r <| U__i \ lameAdv b
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i \ @awesomeAdv B.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__honactsafe H__o]; clear H__s.
    inversion H__o as [R__start OK__start]; clear H__o.

    unfold refines.

    exists (fun ur ui => R (strip_adversary_simpl ur) ui);
      eauto using simulates_ok_with_adversary.
  Qed.

End SingleAdversarySimulates.

Inductive rCouldGenerate : forall {A B},
    RealWorld.universe A B -> list RealWorld.uaction -> Prop :=
| RCgNothing : forall A B (U : RealWorld.universe A B),
    rCouldGenerate U []
| RCgSilent : forall A B (U U' : RealWorld.universe A B) suid acts,
      RealWorld.step_universe suid U Silent U'
    -> rCouldGenerate U' acts
    -> rCouldGenerate U acts
| RCgLabeled : forall A B (U U' : RealWorld.universe A B) suid acts a,
      RealWorld.step_universe suid U (Action a) U'
    -> rCouldGenerate U' acts
    -> rCouldGenerate U (a :: acts)
.

Inductive iCouldGenerate : forall {A},
    IdealWorld.universe A -> list IdealWorld.action -> Prop :=
| ICgNothing : forall A (U : IdealWorld.universe A),
    iCouldGenerate U []
| ICgSilent : forall A (U U' : IdealWorld.universe A) acts,
      istepSilent U U'
    -> iCouldGenerate U' acts
    -> iCouldGenerate U acts
| ICgLabeled : forall A (U U' : IdealWorld.universe A) acts a,
      IdealWorld.lstep_universe U (Action a) U'
    -> iCouldGenerate U' acts
    -> iCouldGenerate U (a :: acts)
.

Hint Constructors rCouldGenerate iCouldGenerate.

Lemma ideal_multi_silent_stays_could_generate :
  forall {A} (U__i U__i' : IdealWorld.universe A),
      istepSilent ^* U__i U__i'
      -> forall acts__i,
        iCouldGenerate U__i' acts__i
      -> iCouldGenerate U__i acts__i.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma labeled_real_step_implies_indexed_step :
  forall A B U U' uid a,
    @RealWorld.step_universe A B (Some uid) U (Action (uid,a)) U'
    -> indexedRealStep uid (Action a) U U'.
Proof.
  intros * STEP.
  invert STEP.
  econstructor; intuition eauto.
  unfold RealWorld.mkULbl in H3; destruct lbl; try discriminate.
  invert H3; eauto.
Qed.

Lemma indexed_ideal_multi_silent_stays_could_generate :
  forall {A} (U__i U__i' : IdealWorld.universe A) uid,
      (indexedIdealStep uid Silent) ^* U__i U__i'
      -> forall acts__i,
        iCouldGenerate U__i' acts__i
      -> iCouldGenerate U__i acts__i.
Proof.
  induction 1; intros; eauto.
  eapply indexedIdealStep_ideal_step in H; eauto.
Qed.

Hint Resolve
     ideal_multi_silent_stays_could_generate
     indexed_ideal_multi_silent_stays_could_generate : core.

Inductive traceMatches : list RealWorld.uaction -> list IdealWorld.action -> Prop :=
| TrMatchesNothing :
    traceMatches [] []
| TrMatchesLabel : forall {A B}(U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r acts__r a__i acts__i,
      traceMatches acts__r acts__i
    -> action_matches U__r.(RealWorld.all_ciphers) U__r.(RealWorld.all_keys) a__r a__i
    -> traceMatches (a__r :: acts__r) (a__i :: acts__i)
.

Hint Constructors traceMatches.
Hint Resolve
     silent_step_adv_univ_implies_adv_universe_ok
     silent_step_advuniv_implies_univ_ok
     honest_labeled_step_univ_ok
     labeled_step_adv_univ_implies_adv_universe_ok
     action_adversary_safe_after_before_cleaning.

Lemma simulation_relation_multi_stripped :
  forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A)
          (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) R',

    R' = (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui)
    -> R (strip_adversary_simpl (RealWorld.peel_adv U__r)) U__i
    -> R' (strip_adversary U__r) U__i.
Proof.
  intros; subst.
  rewrite strip_adv_simpl_strip_adv_idempotent.
  rewrite strip_adv_simpl_peel_same_as_strip_adv in H0.
  assumption.
Qed.

Lemma labeled_step_uid_same :
  forall t__hon t__adv uid1 uid2 U U' a,
    @RealWorld.step_universe t__hon t__adv (Some uid1) U (Action (uid2,a)) U'
    -> uid1 = uid2.
Proof.
  intros.
  invert H.
  unfold RealWorld.mkULbl in H4; destruct lbl; invert H4; trivial.
Qed.

Lemma simulates_could_generate :
  forall A B (R R' : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
    R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
    -> simulates_silent_step (awesomeAdv (B:=B)) R'
    -> simulates_labeled_step (awesomeAdv (B:=B)) R'
    -> honest_actions_safe B R'
    -> forall (U__r : RealWorld.universe A B) acts__r,
        universe_ok U__r
        -> adv_universe_ok U__r
        -> rCouldGenerate U__r acts__r
        -> forall U__i,
            R' (RealWorld.peel_adv U__r) U__i
            -> exists acts__i,
                iCouldGenerate U__i acts__i
              /\ traceMatches acts__r acts__i.
Proof.
  induction 8; intros; subst; intuition eauto;
    assert (awesomeAdv (RealWorld.adversary U)) as AWE by (unfold awesomeAdv; trivial).

  - generalize (H0 _ _ H7 H3 H4 AWE _ _ H5); intro STEPPED;
      destruct STEPPED as [U__i' STEPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H8.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H8.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.
    assert (R' (RealWorld.peel_adv U') U__i') as INR' by (subst; eauto).

    assert (universe_ok U') as UOK.
    eapply silent_step_advuniv_implies_univ_ok; eauto.

    eapply H2; [rewrite HeqR' | ..]; eauto.
    
    assert (adv_universe_ok U') as AUOK.
    subst.
    unfold honest_actions_safe in *.
    eapply silent_step_adv_univ_implies_adv_universe_ok; eauto.
    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK AUOK _ INR'); split_ex; split_ands.

    eapply ideal_multi_silent_stays_could_generate with (acts__i:=x) in H; eauto.

  - destruct a, suid; [ | invert H5].
    assert (u0 = u) by (eauto using labeled_step_uid_same); subst.
    generalize (labeled_real_step_implies_indexed_step H5); intros; split_ex.
    generalize (H1 _ _ H7 H3 H4 AWE _ _ _ H); intro STEPPED;
      destruct STEPPED as [a__i STEPPED];
      destruct STEPPED as [U__i' STEPPED];
      destruct STEPPED as [U__i'' STEPPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H11.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H11.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.

    assert (R' (RealWorld.peel_adv U') U__i'') as INR' by (subst; eauto).
    assert (R' (RealWorld.peel_adv (strip_adversary_univ U b)) U__i) as INR.
    rewrite HeqR'.
    rewrite <- strip_adversary_same_as_peel_strip_simpl
          , strip_adv_simpl_strip_adv_idempotent
          , strip_adversary_same_as_peel_strip_simpl with (b0:=b).
    rewrite strip_adv_simpl_peel_same_as_strip_adv in H7; assumption.

    assert (universe_ok (strip_adversary_univ U b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok (strip_adversary_univ U b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.

    generalize (H2 _ _ INR STRIP_UNIV_OK STRIP_ADV_UNIV_OK); simpl; intros ACT_SAFE.
    clear STRIP_UNIV_OK STRIP_ADV_UNIV_OK.

    apply honest_cmds_safe_advuniv in ACT_SAFE.

    assert (universe_ok U') as UOK.
    generalize H5; intros STEP.
    (* invert STEP; simpl in *. *)
    invert H; simpl in *.
    specialize (ACT_SAFE _ _ _ eq_refl H12).
    eapply honest_labeled_step_univ_ok;
      unfold adv_universe_ok in *;
      split_ands; eauto.

    destruct userData.
    eapply honest_cmd_implies_safe_action; eauto.
    reflexivity.

    assert (adv_universe_ok U') as AUOK by eauto.

    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK AUOK _ INR'); split_ex; split_ands.

    eapply indexedIdealStep_ideal_step in H9.
    exists (a__i :: x); split; eauto using indexed_ideal_multi_silent_stays_could_generate.
Qed.

Notation "u1 <<| u2 " :=
  (exists b, lameAdv b u1.(RealWorld.adversary)
      /\ refines (lameAdv b) u1 u2) (no associativity, at level 70).

Theorem refines_could_generate :
  forall A B (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
    U__r <<| U__i
    -> universe_starts_ok U__r
    -> forall U__ra advcode acts__r,
      U__ra = add_adversary U__r advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate U__i acts__i
        /\ traceMatches acts__r acts__i.
Proof.
  intros.
  unfold refines in H.
  destruct H as [b [LAME [R H]]].

  assert (simulates (lameAdv b) R U__r U__i) as SIM by assumption;
    unfold simulates in SIM; split_ands.
  assert (simulates (lameAdv b) R U__r U__i) as SIM by assumption;
    eapply simulates_ok_with_adversary in SIM; eauto.
  2: reflexivity.

  unfold simulates in SIM; split_ands.
  eapply simulates_could_generate
    with (R := R)
         (B := B)
         (U__r := U__ra)
         (R' := (fun ur ui => R (strip_adversary_simpl ur) ui)); auto.
Qed.

Inductive inout :=
| SendAct (uid : user_id)
| RecAct (uid : user_id).

Definition iaction_inout (a : IdealWorld.action) : inout :=
  match a with
  | IdealWorld.Input  _ uid _ _ _ => RecAct uid
  | IdealWorld.Output _ uid _ _ _ => SendAct uid
  end.

Definition uaction_inout (a : RealWorld.uaction) : inout :=
  match a with
  | (uid,RealWorld.Input  _ _ _) => RecAct uid
  | (uid,RealWorld.Output _ _ _ _) => SendAct uid
  end.

Inductive rCouldGen : forall {A B},
    RealWorld.universe A B -> list inout -> Prop :=
| RcgNothing : forall A B (U : RealWorld.universe A B),
    rCouldGen U []
| RcgSilent : forall A B (U U' : RealWorld.universe A B) suid uids,
      RealWorld.step_universe suid U Silent U'
    -> rCouldGen U' uids
    -> rCouldGen U uids
| RcgLabeled : forall A B (U U' : RealWorld.universe A B) suid uids a,
      RealWorld.step_universe suid U (Action a) U'
    -> rCouldGen U' uids
    -> rCouldGen U (uaction_inout a :: uids)
.

Inductive iCouldGen : forall {A},
    IdealWorld.universe A -> list inout -> Prop :=
| IcgNothing : forall A (U : IdealWorld.universe A),
    iCouldGen U []
| IcgSilent : forall A (U U' : IdealWorld.universe A) uids,
      istepSilent U U'
    -> iCouldGen U' uids
    -> iCouldGen U uids
| IcgLabeled : forall A (U U' : IdealWorld.universe A) uids a,
    IdealWorld.lstep_universe U (Action a) U'
    -> iCouldGen U' uids
    -> iCouldGen U (iaction_inout a :: uids)
.

Hint Constructors rCouldGen iCouldGen.

Lemma real_labeled_step_in_out :
  forall {A B C} lbl suid bd bd',
    RealWorld.step_user lbl suid bd bd'
              
    -> forall (usrs usrs' : RealWorld.honest_users A) (adv adv' : RealWorld.user_data B) cs cs' gks gks'
        uid ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : RealWorld.user_cmd C) a,
      
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid
      -> lbl = Action a
      -> (exists t msg rec_u_id, a = @RealWorld.Output t msg suid (Some rec_u_id) sents)
      \/ (exists t msg pat, a = @RealWorld.Input t msg pat froms).
Proof.
  induction 1; inversion 1; inversion 1; invert 2; try discriminate; subst; eauto.
Qed.

Lemma more_complicated_trace_ex :
  forall t__hon t__adv U tr,
    @rCouldGen t__hon t__adv U tr
    -> exists tr', rCouldGenerate U tr'
           /\ tr = List.map uaction_inout tr'.
Proof.
  induction 1; split_ex; eauto.
  subst.
  invert H.
  unfold RealWorld.mkULbl in H5; destruct lbl; invert H5.
  generalize H3; intros; eapply real_labeled_step_in_out in H3; eauto; try reflexivity.

  split_ors; split_ex;
    exists ((u_id,a0) :: x); subst; simpl; split; eauto.

  eapply RCgLabeled; eauto.
  econstructor; eauto.

  eapply RCgLabeled; eauto.
  econstructor; eauto.
Qed.

Lemma icouldgetnerate_icouldgen :
  forall t__hon U acts__i,
    @iCouldGenerate t__hon U acts__i
    -> forall acts__r,
      traceMatches acts__r acts__i
      -> iCouldGen U (List.map uaction_inout acts__r).
Proof.
  induction 1; intros; eauto.
  - destruct acts__r; [|invert H]; simpl; eauto.
  - destruct acts__r; [invert H1|].
    invert H1.
    eapply IHiCouldGenerate in H5.
    simpl.

    assert (uaction_inout u = iaction_inout a) as RW.
    invert H7; trivial.
    
    rewrite RW; eauto.
Qed.

Theorem refines_could_gen :
  forall A B (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
    U__r <<| U__i
    -> universe_starts_ok U__r
    -> forall U__ra advcode,
        U__ra = add_adversary U__r advcode
        -> forall acts,
          rCouldGen U__ra acts
          -> iCouldGen U__i acts.
Proof.
  intros.
  eapply more_complicated_trace_ex in H2; eauto; split_ex; subst.

  eapply refines_could_generate in H2; eauto.
  split_ex.

  eapply icouldgetnerate_icouldgen; eauto.
Qed.

Print Assumptions refines_could_generate.
