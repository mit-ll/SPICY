(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

From SPICY Require Import
     MyPrelude
     Maps
     Common
     Keys
     Tactics
     Messages
     MessageEq
     Automation
     Simulation
     AdversaryUniverse
     SafetyAutomation
     SyntacticallySafe

     Theory.CipherTheory
     Theory.InvariantsTheory
     Theory.KeysTheory
     Theory.MessageEqTheory
     Theory.MessagesTheory
     Theory.NonceTracking
     Theory.UsersTheory
.

From SPICY Require
     IdealWorld
     RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Import SafetyAutomation.

Ltac dt bd :=
  destruct bd as [[[[[[[[[[?usrs ?adv] ?cs] ?gks] ?ks] ?qmsgs] ?mycs] ?froms] ?sents] ?cur_n] ?cmd].

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

End UniverseLemmas.

Section SingleAdversarySimulates.

  Hint Resolve
       accepted_safe_msg_pattern_honestly_signed
       encrypted_ciphers_ok_addnl_cipher : core.

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

    Lemma honest_heap_private_honestk :
      forall {A} k_id ks u_id (usrs : honest_users A),
        ks $? k_id = Some true
        -> user_keys usrs u_id = Some ks
        -> honest_key (findUserKeys usrs) k_id.
    Proof.
      intros.
      unfold user_keys in *; cases (usrs $? u_id); subst; clean_map_lookups.
      eapply findUserKeys_has_private_key_of_user; eauto.
    Qed.

    Hint Resolve
         honest_heap_private_honestk
         honest_key_not_cleaned
         adv_key_not_honestk
    : core.

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

    Hint Resolve user_in_univ_user_in_stripped_univ : core.

    Hint Resolve
         honest_cipher_filter_fn_true_honest_signing_key
         msg_honestly_signed_after_without_cleaning
         msg_honestly_signed_before_after_cleaning
         clean_keys_keeps_honest_key
         clean_ciphers_encrypted_ciphers_ok
      : core.

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : <<(Base B)>>),
          U__r = strip_adversary_univ U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      unfold universe_ok.
      intros.
      subst; destruct U__ra; simpl in *; intuition idtac;
        try rewrite clean_users_no_change_findUserKeys;
        subst; simpl in *;
          eauto using user_cipher_queues_ok_after_cleaning
                    , message_queues_ok_after_cleaning
                    , keys_and_permissions_good_clean_keys
                    , honest_nonces_ok_after_cleaning
                    , adv_no_honest_keys_after_cleaning
                    , honest_users_only_honest_keys_after_cleaning.

      - eapply clean_ciphers_encrypted_ciphers_ok'; eauto using clean_users_no_change_honestk.
      - econstructor.
      - apply adv_message_queue_ok_after_cleaning; eauto using clean_users_no_change_honestk.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         not_in_ciphers_not_in_cleaned_ciphers
      : core.

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


    Hint Resolve msg_filter_same_new_honest_key : core.
    Hint Resolve clean_key_permissions_new_honest_key' : core.

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

    Hint Resolve
         clean_keys_new_honest_key
         clean_messages_addnl_cipher_idempotent
         clean_adv_msgs_addnl_cipher_idempotent
         clean_messages_keeps_signed_addressed_unseen_nonce
         clean_key_permissions_keeps_honest_permission
         msg_nonce_ok_none_updateTrackedNonce_idempotent
         updateRecvNonce_clean_ciphers_honestly_signed
      : core.

    Lemma honest_silent_new_key_implies_honest_step_origuniv :
      forall {A B} (usrs : honest_users A) (adv : user_data B) 
        cs gks gks' k_id usage u_id honestk honestk' ks qmsgs mycs froms sents cur_n b kt,
          gks $? k_id = None
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys usrs $+ (k_id,true)
        -> gks' = gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})
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
                     , mycs, froms, sents, cur_n, GenerateKey kt usage )
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
        split_ex; specialize_msg_ok.
        
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

    Hint Resolve honestly_signed_message_to_this_user_None_always_true : core.

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

    Hint Resolve clean_adv_msgs_keeps_honest_msg : core.



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
        split_ex.
        pose proof clean_messages_elt_same.
        generalize MHS; intros MHS1; eapply H3 in MHS1; eauto; split_ex.
        2 : {
          unfold honest_nonces_ok in *; split_ex; eauto.
        }
                 
        rewrite H4.
        rewrite H5.

        econstructor; eauto.

        + rewrite clean_key_permissions_distributes_merge_key_permissions.
          subst.
          
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
             specialize (H27 _ _ Heq); split_ex; context_map_rewrites; trivial.
          ** apply clean_key_permissions_adds_no_permissions; auto.
          ** rewrite RW; trivial.

        + apply updateTrackedNonce_clean_ciphers_idempotent_honest_msg; eauto.

        + rewrite Forall_forall in H7 |- *; intros.
          destruct x2; intros.
          eapply clean_messages_list_in_safe in H8; split_ex.
          eapply H7 in H8; split_ex; eauto 8.

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
          specialize (H0 _ _ H6).

          unfold msg_honestly_signed, msg_signing_key in H; context_map_rewrites.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups;
            match goal with
            | [ H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _), ARG : findKeysMessage _ $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG)
            end; split_ors; subst; eauto.

        + eapply clean_users_cleans_user; eauto.
        + apply updateSentNonce_clean_ciphers_idempotent_honest_msg; eauto.
 
        + simpl.
          rewrite clean_users_add_pull; simpl; eauto.
          unfold honest_nonces_ok in H10; split_ex.
          erewrite clean_messages_keeps_hon_signed; eauto.
          
          (* unfold honest_nonces_ok in H9; process_nonce_ok. *)
          unfold msg_signed_addressed.
          rewrite andb_true_iff; split_ex; subst; eauto.

          simpl; eauto 12.
          
        + unfold clean_adv, addUserKeys; simpl.

          f_equal; eauto.
          rewrite clean_key_permissions_distributes_merge_key_permissions.
          apply map_eq_Equal; unfold Equal; intros.

          assert (clean_key_permissions (findUserKeys usrs) (findKeysCrypto cs' msg) $? y
                  = findKeysCrypto cs' msg $? y) as RW.

          split_ex.
          rewrite H5 in H; unfold msg_honestly_signed in H.
          match goal with
          | [ H : match ?mtch with _ => _ end = _ |- _ ] => cases mtch; try discriminate
          end.
          subst.
          simpl in Heq; context_map_rewrites; clean_context.
          encrypted_ciphers_prop; simpl in *; context_map_rewrites; eauto.
          cases (findKeysMessage msg $? y); eauto using clean_key_permissions_adds_no_permissions.
          specialize (H14 _ _ Heq); split_ands; subst; eauto.

          * cases ( clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y );
              cases ( findKeysCrypto cs' msg $? y );
              solve_perm_merges; eauto.
    Qed.

    Hint Resolve honest_users_only_honest_keys_nochange_keys : core.

    Lemma merge_perms_true_either_true :
      forall ks1 ks2 k_id,
        ks1 $? k_id = Some true \/ ks2 $? k_id = Some true
        -> ks1 $k++ ks2 $? k_id = Some true.
    Proof.
      intros; split_ors; solve_perm_merges.
    Qed.

    Hint Resolve
         merge_perms_true_either_true
         honest_users_only_honest_keys_gen_key
      : core.

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
         next_action_next_cmd_safe_bind
      : core.

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
        destruct (u_id ==n u_id0)
        ; subst
        ; clean_map_lookups
        ; rewrite findUserKeys_readd_user_addnl_keys by eauto
        ; simpl in *
        ; eauto.

        specialize (H11 _ _ H27); simpl in *.
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
          specialize (H13 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

        + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
          unfold msg_cipher_id in H2; destruct msg; try discriminate;
            clean_context; simpl in *.
          cases (cs' $? x); try discriminate.
          clean_context; invert MHS.
          destruct c; simpl in *; clean_map_lookups; eauto.
          encrypted_ciphers_prop; eauto.
          specialize (H13 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

      - unfold honest_users_only_honest_keys in *; intros.
        assert (rec_u_id <> u_id) by eauto.
        destruct (u_id ==n u_id0); destruct (u_id ==n rec_u_id)
        ; subst
        ; try contradiction
        ; clean_map_lookups
        ; simpl in *
        ; eauto.

        + specialize (H10 _ _ H26 _ _ H11).
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

    Lemma labeled_step_adv_univ_implies_universe_ok :
      forall {A B} (U U' : universe A B) lbl uid a,
        step_universe (Some uid) U lbl U'
        -> lbl = Action (uid,a)
        -> honest_cmds_safe U
        -> universe_ok U
        -> universe_ok U'.
    Proof.
      intros.
      subst.
      generalize (honest_cmds_implies_safe_actions H H1); intros.
      invert H; try discriminate.
      unfold universe_ok in *.
      destruct U; destruct userData.
      unfold build_data_step in *; simpl in *.
      split_ex.
      specialize (H1 _ _ _ eq_refl H4);
        simpl in *.

      destruct lbl; invert H7.

      repeat simple apply conj.
      
      eapply honest_labeled_step_encrypted_ciphers_ok; eauto.
      eapply honest_labeled_step_keys_and_permissions_good; eauto.
      eapply honest_labeled_step_user_cipher_queues_ok; eauto.
      eapply honest_labeled_step_message_queues_ok; eauto.
      eapply honest_labeled_step_adv_cipher_queue_ok; eauto.
      eapply honest_labeled_step_adv_message_queue_ok; eauto.
      eapply honest_labeled_step_adv_no_honest_keys; eauto.
      eapply honest_labeled_step_honest_nonces_ok; eauto.

      eapply honest_users_only_honest_keys_honest_steps; eauto.
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

    Hint Resolve
         clean_ciphers_eliminates_dishonest_cipher
         clean_ciphers_eliminates_added_dishonest_cipher
         dishonest_cipher_cleaned : core.

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
      induction 1; inversion 1; inversion 4; intros; subst; eauto.

      erewrite <- findUserKeys_readd_user_same_keys_idempotent by eauto
      ; eauto.
    Qed.

    Hint Resolve clean_keys_drops_added_dishonest_key : core.

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
            cases (findUserKeys usrs' $? k_id)
            ; eauto.
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
      
      split_ors; split_ex.
      - unfold msg_signed_addressed in MSA; rewrite andb_true_iff in MSA; split_ex.
        rewrite cipher_honestly_signed_honest_keyb_iff in H
        ; unfold honest_keyb in H
        ; context_map_rewrites
        ; discriminate.

      - clean_context.
        unfold honest_nonces_ok in H25; split_ex.
        clean_map_lookups.
        specialize (H14 _ _ _ _ H9 H7 H2).
        unfold honest_nonce_tracking_ok in H14; split_ex.
        specialize (H15 _ _ H5); specialize_simply; split_ex.
        specialize (H13 _ _ H7); unfold honest_user_nonces_ok in H13; split_ex.
        rewrite Forall_forall in H16; specialize (H16 _ H10).

        apply count_occ_eq_0_clean_msgs in Heq.

        split_ex; clean_map_lookups.
        split_ors; try contradiction.
        rewrite Exists_exists in H12; split_ex.
        rewrite Forall_forall in H18; specialize (H18 _ H12); destruct x2; split_ands; eauto.
        specialize_simply.
        unfold msg_nonce_not_same in H18; unfold msg_nonce_same in H20.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in H19;
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
           adv_step_implies_no_new_ciphers_after_cleaning
        : core.

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

    Hint Resolve
         encrypted_ciphers_ok_new_honest_key_adv_univ
         users_permission_heaps_good_merged_permission_heaps_good
      : core.
    
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

    Qed.

    Lemma silent_step_adv_univ_implies_universe_ok :
      forall {A B} (U U' : universe A B) suid,
        step_universe suid U Silent U'
        -> honest_cmds_safe U
        -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers) U.(all_keys)
        -> universe_ok U
        -> universe_ok U'.
    Proof.
      intros.
      unfold honest_cmds_safe in *.
      
      invert H;
        unfold universe_ok in *;
        destruct U; [destruct userData | destruct adversary];
          unfold build_data_step in *; simpl in *;
            destruct lbl;
            repeat
              match goal with
              | [ H : Silent = mkULbl (Action _) _  |- _ ] => unfold mkULbl in H; simpl in H; discriminate
              end;
            intuition idtac.

      eapply honest_silent_step_adv_univ_enc_ciphers_ok; eauto.
      specialize (H0 _ _ _ eq_refl H3); eauto.
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
      
      eapply adv_step_encrypted_ciphers_ok; eauto.
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

      eapply adv_step_encrypted_ciphers_ok; eauto.
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

      - split.
        invert H; econstructor; eauto.
        (do 2 eexists); repeat simple apply conj; eauto.
        
      - repeat (apply conj); eauto 8.
        invert H.
        rewrite H3.
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H2;
          unfold honest_cipher_filter_fn in H2; split_ex.
        unfold msg_to_this_user, msg_destination_user in *
        ; context_map_rewrites.
        eapply clean_ciphers_keeps_honest_cipher in H; eauto.
        context_map_rewrites; eauto.
    Qed.

    Lemma action_adversary_safe_after_before_cleaning :
      forall {A} (usrs : honest_users A) cs a,
          action_adversary_safe (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_ciphers (findUserKeys usrs) cs) a
        -> action_adversary_safe (findUserKeys usrs) cs a.
    Proof.
      intros; eapply action_adversary_safe_after_before_cleaning'; swap 1 2; eauto.
    Qed.

    Hint Resolve
         action_adversary_safe_after_before_cleaning : core.

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

    Hint Resolve msg_accepted_by_pattern_after_cleaning_honest_key : core.

    Lemma honest_labeled_recv_implies_honest_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs: honest_users A) (adv : user_data B) usrs__s cs__s
        cs gks u_id honestk honestk' pat ks qmsgs1 qmsgs2 mycs froms froms' sents cur_n pubk b,
          msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> honestk = findUserKeys usrs
        -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs (Some u_id) froms pat msg') qmsgs1
        -> froms' = updateTrackedNonce (Some u_id) froms cs msg
        -> cs__s = clean_ciphers honestk cs
        -> usrs__s = clean_users honestk cs usrs
        -> pubk = findKeysCrypto cs msg
        -> honestk' = findUserKeys usrs $k++ pubk
        -> message_queue_ok honestk cs (qmsgs1 ++ (existT _ _ msg) :: qmsgs2) gks
        -> honest_nonces_unique cs honestk
        -> next_cmd_safe honestk cs u_id froms sents (@Recv t pat)
        -> step_user (Action (Input msg pat froms)) (Some u_id)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms (qmsgs1 ++ (existT _ _ msg) :: qmsgs2),
                     mycs, froms, sents, cur_n, @Recv t pat)
                    (clean_users honestk' cs usrs,
                     clean_adv adv honestk' cs b,
                     clean_ciphers honestk' cs,
                     clean_keys honestk' gks,
                     clean_key_permissions honestk' (ks $k++ pubk),
                     clean_messages honestk' cs (Some u_id) froms' (qmsgs1 ++ qmsgs2),
                     findCiphers msg ++ mycs,
                     updateTrackedNonce (Some u_id) froms cs msg, sents, cur_n, @Return (Crypto t) msg).
    Proof.
      intros; process_next_cmd_safe; subst.

      assert (msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg = true)
        as MSA by (unfold msg_signed_addressed; eauto using accepted_safe_msg_pattern_honestly_signed
                                                , accepted_safe_msg_pattern_to_this_user).

      generalize (accepted_safe_msg_pattern_replay_safe H9 H); intros; split_ex;
        subst.

      pose proof clean_messages_elt_same.
      generalize MSA; intros MSA1; unfold msg_signed_addressed in MSA1
      ; rewrite andb_true_iff in MSA1
      ; destruct MSA1 as [MHS MA].
      generalize MHS; intros MHS1; eapply H0 with (msgs2 := qmsgs2) in MHS1; eauto.
      split_ex.

      unfold message_queue_ok in H7; rewrite Forall_forall in H7.
      assert (List.In (existT _ t0 (SignedCiphertext x))
                      (qmsgs1 ++ existT _ t0 (SignedCiphertext x) :: qmsgs2)) by eauto using in_elt.
      eapply H7 in H6; split_ex.
      pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ands; split_ex.
      eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
      eapply H11 in H12; eauto; split_ex.
      specialize_simply.
      unfold message_no_adv_private in *.

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

      rewrite !MKRW.

      eapply StepRecv; eauto.

      * rewrite clean_key_permissions_distributes_merge_key_permissions.
        match goal with
        | [ |- context [ ?same $k++ ?fst = ?same $k++ ?snd ]] => assert (fst = snd)
        end.
        maps_equal.
        invert H13.
        unfold msg_signed_addressed in MSA; rewrite andb_true_iff in MSA; split_ex.
        unfold msg_honestly_signed, msg_signing_key in H13; context_map_rewrites; clean_context.
        cases (@findKeysCrypto t0 cs (SignedCiphertext x2) $? y).
        ** specialize (H14 _ _ Heq); split_ex; subst.
           erewrite clean_key_permissions_keeps_honest_permission; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.

        ** rewrite clean_key_permissions_adds_no_permissions; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.

        ** rewrite H15; trivial.
      * rewrite Forall_forall in H1 |- *.
        intros * LIN.
        destruct x4.
        eapply clean_messages_list_in_safe in LIN; split_ex.
        eapply H1 in H15; split_ex; eauto 8.
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

    Hint Resolve keys_mine_after_cleaning : core.
    
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

      - assert ( clean_ciphers (findUserKeys usrs) cs $? x = Some x0 ).
        apply clean_ciphers_keeps_honest_cipher; try assumption.
        assert (List.In x mycs) by eauto.
        user_cipher_queues_prop.
        unfold honest_cipher_filter_fn; eauto.
        context_map_rewrites; trivial.

      - simpl. rewrite clean_users_add_pull; simpl.
        unfold honest_nonces_ok in *; split_ex.
        erewrite clean_messages_keeps_hon_signed; eauto 8.
        unfold msg_signed_addressed; eauto.

      - unfold clean_adv; simpl.
        simpl in H0; assert (List.In x mycs) by eauto; 
          user_cipher_queues_prop.
        rewrite clean_adv_msgs_keeps_honest_msg; eauto.
        rewrite clean_key_permissions_distributes_merge_key_permissions.
        erewrite clean_ciphers_keeps_honest_cipher; eauto.

        unfold cipher_honestly_signed in H15; destruct x1; eauto.
        encrypted_ciphers_prop.

        assert(clean_key_permissions (findUserKeys usrs) (findKeysMessage msg) = findKeysMessage msg)
          as RW.
        maps_equal.
        cases (findKeysMessage msg $? y); eauto 12 using clean_key_permissions_adds_no_permissions.
        eapply clean_key_permissions_keeps_honest_permission; eauto.
        unfold honest_perm_filter_fn.
        specialize (H23 _ _ Heq); split_ex; context_map_rewrites; trivial.

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

      Ltac solve_clean_keys_clean_key_permissions' :=
        match goal with
        | [  |- clean_keys ?honestk ?gks $? ?kid = Some _ ] =>
          match goal with
          | [ H : honestk $? kid = Some true |- _] => idtac
          | [ H : honest_key honestk kid |- _] => idtac
          | _ => assert (honest_key honestk kid) by eauto
          end
        | [  |- clean_key_permissions ?honestk ?gks $? ?kid = Some _ ] =>
          match goal with
          | [ H : honestk $? kid = Some true |- _] => idtac
          | [ H : honest_key honestk kid |- _] => idtac
          | _ => assert (honest_key honestk kid) by eauto
          (* | _ => assert (honestk $? kid = Some true) by eauto *)
          end
        end;
        unfold clean_keys, clean_key_permissions;
        rewrite <- find_mapsto_iff, filter_iff; auto; rewrite find_mapsto_iff;
        unfold honest_key_filter_fn, honest_perm_filter_fn;
        intuition context_map_rewrites; eauto.
      
      induction 1; inversion 5; inversion 9; intros; subst; clean_context
      ; autorewrite with find_user_keys in *
      ; try
          match goal with
          | [ H : (Some _ <> None) -> ?msg_nonce = (?uid, ?cur_n) |- _ ] =>
            assert (msg_nonce = (uid,cur_n)) by (eapply H; congruence)
            ; clear H
            ; subst
          end
      ; try solve [ left; econstructor; eauto;
                    user_cipher_queues_prop; eauto;
                    try solve_clean_keys_clean_key_permissions']
      ; try solve [ left
                    ; eauto 12 using honest_labeled_send_implies_step_origuniv
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
        unfold message_queues_ok in H26; rewrite Forall_natmap_forall in H26.
        specialize (H26 _ _ H33); eauto.
        unfold honest_nonces_ok in *; split_ex; trivial.
    Qed.

    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
        universe_ok U
        -> U.(users) $? u_id = Some userData
        -> step_user Silent (Some u_id)
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        (* -> honest_users_only_honest_keys U.(users) *)
        -> honest_cmds_safe U
        -> step_universe (Some u_id) (strip_adversary_univ U b) Silent (strip_adversary_univ U' b)
        \/ strip_adversary_univ U b = strip_adversary_univ U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H1 as RW. clear HeqRW.

      unfold universe_ok in *; split_ex; simpl in *.
      unfold honest_cmds_safe in *; simpl in *.
      specialize (H3 _ _ _ eq_refl H0).
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
          eapply honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs in H1; eauto; split_ands.

          eapply honest_silent_step_nochange_clean_adv_messages.
          exact STEP.
          all: (reflexivity || eassumption).
        + trivial.

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        inversion H11; subst.
        unfold clean_adv; simpl; f_equal.
        + rewrite clean_users_add_pull; simpl.
          assert (clean_users (findUserKeys users) all_ciphers users =
                  clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}))) cs usrs).
          unfold clean_users, map; apply map_eq_elements_eq; simpl; auto.
          rewrite <- H12.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          eapply clean_users_cleans_user; eauto.
          f_equal; eauto.
        + f_equal; eauto.
          rewrite H15.
          symmetry; eapply honest_silent_step_nochange_clean_adv_messages.
          exact H1.
          all : (reflexivity || eassumption).
          Unshelve. eauto.
    Qed.


    Lemma cleaned_universe_step_implies_orig_univ_step :
      forall {A B C} lbl__s suid bd bd',
        @step_user A B C lbl__s suid bd bd'

        -> forall cs__s cs__s' (usrs__s usrs__s' : honest_users A) (adv__s adv__s' : user_data B) uid
            gks__s gks__s' ks__s ks__s' qmsgs__s qmsgs__s' mycs__s mycs__s' froms__s froms__s' sents__s sents__s' cur_n cur_n' cmd cmd',

          suid = Some uid
          -> bd = (usrs__s, adv__s, cs__s, gks__s, ks__s, qmsgs__s, mycs__s, froms__s, sents__s, cur_n, cmd)
          -> bd' = (usrs__s', adv__s', cs__s', gks__s', ks__s', qmsgs__s', mycs__s', froms__s', sents__s', cur_n', cmd')
          -> forall cs usrs adv gks ks qmsgs mycs froms sents cur_n honestk b lbl cmdc,
              cs__s = clean_ciphers honestk cs
              -> usrs__s = clean_users honestk cs usrs
              -> gks__s = clean_keys honestk gks
              -> adv__s = clean_adv adv honestk cs b
              -> lbl = lbl__s
              -> honestk = findUserKeys usrs
              -> user_cipher_queue_ok cs honestk mycs
              -> next_cmd_safe honestk cs uid froms sents cmd
              -> honest_nonces_ok cs usrs
              -> usrs__s $? uid = Some (mkUserData ks__s cmdc qmsgs__s mycs__s froms__s sents__s cur_n)
              -> usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
              -> exists bd'',
                  step_user lbl suid
                            (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                            bd''.
    Proof.
      Ltac xx :=
        repeat 
          match goal with
          | [ H : clean_users _ _ _ $? _ = Some _ |- _ ] => 
            apply clean_users_cleans_user_inv in H
            ; clean_map_lookups
            ; simpl in *
            ; subst
          | [ H : clean_keys _ _ $? _ = _ |- _ ] =>
            apply clean_keys_inv in H; split_ex
          | [ H : clean_key_permissions _ _ $? _ = _ |- _ ] =>
            apply clean_key_permissions_inv in H; split_ex
          | [ H : keys_mine _ ?fkm |- keys_mine _ ?fkm ] =>
            let FKM := fresh "FKM"
            in  unfold keys_mine; intros * FKM; apply H in FKM; split_ors
        end.

      induction 1; inversion 2; inversion 1; intros; subst; eauto
      ; try solve [ xx; eexists; econstructor; eauto ]
      ; clean_context.

      - generalize H35; eapply IHstep_user in H35; eauto; intros.
        split_ex.
        xx.
        dt x.
        eexists; econstructor; eauto.

      - xx.

        assert (msg_accepted_by_pattern cs0 (Some uid) froms0 pat msg) as MABP.
        invert H6; [ econstructor 1
                   | econstructor 2
                   | econstructor 3]; eauto.
        clear H6.

        assert (List.In (existT _ _ msg) (msgs__front ++ existT _ _ msg :: msgs__back))
          as LIN by eauto using in_elt.
        rewrite H1 in LIN.

        apply clean_messages_list_in_safe in LIN; split_ex.

        unfold honest_nonces_ok in *; split_ex.
        assert (nextAction (@Recv t0 pat) (@Recv t0 pat)) as na by (econstructor).
        apply H40 in na.
        assert (msg_honestly_signed (findUserKeys usrs0) cs0 msg = true) as MHS by eauto.

        eapply in_cleaned_message_queue_must_in_message_queue'' in H0; eauto.

        split_ex.
        clear H7 H1.
        eexists; econstructor; (try reflexivity || eassumption).

      - xx.
        eexists; econstructor; eauto; try congruence.
        unfold keys_mine; intros.
        unfold findKeysCrypto in H0, H5.
        destruct msg; eauto.
        apply H0 in H5; split_ors; xx; eauto.
        cases (cs0 $? c_id); clean_map_lookups.
        assert (List.In c_id mycs0) by eauto.
        unfold user_cipher_queue_ok in H38
        ; rewrite Forall_forall in H38
        ; specialize (H38 _ H7)
        ; split_ex
        ; clean_map_lookups.

        erewrite clean_ciphers_keeps_honest_cipher in H0; eauto.
        apply H0 in H5; split_ors; xx; eauto.

      - xx.
        eexists; eapply StepEncrypt with (c_id0 := next_key cs0); eauto.
        clean_map_lookups; apply next_key_not_in; trivial.
        xx; eauto.

      - xx.
        eexists; eapply StepSign with (c_id0 := next_key cs0); eauto.
        clean_map_lookups; apply next_key_not_in; trivial.
        xx; eauto.

      - xx.
        eexists; eapply StepGenerateKey with (k_id0 := next_key gks0); eauto.
        clean_map_lookups; apply next_key_not_in; trivial.

        Unshelve.
        eauto.

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

      - unfold RealWorld.msg_to_this_user, RealWorld.msg_destination_user in *;
          context_map_rewrites.
        erewrite clean_ciphers_inv; eauto.

      - invert H; econstructor; eauto.
      - specialize (H _ _ H2); split_ands; eauto.
    Qed.

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

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl suid,
        step_universe suid U lbl U'
        -> lbl = Silent
        -> honest_cmds_safe U
        -> universe_ok U
        -> universe_ok U'.
     Proof.
       intros A B U U' lbl SUID STEP e HCS UOK;
         rewrite e in *; clear e.

       invert STEP; eauto.

       - match goal with
         | [ H : users U $? _ = Some ?ud |- _ ] =>
           destruct U; destruct ud;
             unfold build_data_step, buildUniverse in *; simpl in *
         end.

         generalize (clean_users_cleans_user (findUserKeys users) all_ciphers users u_id H eq_refl);
           intros CLEAN_USER; simpl in CLEAN_USER.

         eapply silent_step_adv_univ_implies_universe_ok; simpl; eauto.
         eapply RealWorld.StepUser; eauto.
         unfold universe_ok in *; simpl in *; split_ex; eauto.
       
       - destruct U.
         unfold build_data_step, buildUniverseAdv in *; simpl in *.
         eapply silent_step_adv_univ_implies_universe_ok; simpl; eauto.
         eapply StepAdversary; simpl; eauto.
         simpl; unfold universe_ok in *; simpl in *
         ; split_ex
         ; eauto.
     Qed.
     
  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user : core.

  Hint Extern 1 (RealWorld.step_user _ _ (RealWorld.build_data_step _ _) _) =>
    progress unfold RealWorld.build_data_step : core.

  Hint Extern 1 (RealWorld.step_user _ _ (_, _, _ , RealWorld.protocol _) _) => 
    match goal with
    | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H
    end : core.

  Hint Extern 1 (_ = _) => progress m_equal : core.
  Hint Extern 1 (_ = _) => progress f_equal : core.
  Hint Extern 1 (_ = _) =>
    progress unfold RealWorld.build_data_step, RealWorld.buildUniverse; simpl : core.
  Hint Extern 1 (_ = _) =>
    match goal with
    | [ H : RealWorld.adversary _ = _ |- _ ] => rewrite <- H
    end : core.
  Hint Extern 1 (_ = RealWorld.adversary _) => solve [ symmetry ; assumption ] : core.

  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_silent_step (lameAdv b) R
      -> honest_actions_safe B R
      -> universe_ok U__ra
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

    remember (strip_adversary_univ U__ra b) as U__r.
    assert (honest_cmds_safe U__r) as HCS by eauto.

    match goal with
    | [ H : RealWorld.step_universe _ _ _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
        as U__ra'.

      apply honest_cmds_safe_advuniv in HCS.
      unfold RealWorld.mkULbl in H7; destruct lbl; try discriminate.
      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H4 H5 HeqU__ra' HCS).

      assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
        as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).
      specialize (H _ _ H2 STRIP_UNIV_OK LAME).

      split_ors.
      + specialize (H _ _ H3); split_ex; eauto.
      + exists U__i; intuition idtac; eauto.
        destruct U__ra; destruct U__ra'; simpl in *.
        unfold strip_adversary_univ in *; unfold strip_adversary in *; simpl in *.
        invert H3; eauto.
        assert (clean_users (RealWorld.findUserKeys users) all_ciphers users = clean_users (RealWorld.findUserKeys users0) all_ciphers0 users0)
          as CLEAN_USERS by (unfold clean_users, mapi; auto).
        rewrite <- CLEAN_USERS; auto.

    (* Adversary step *)
    - unfold universe_ok in *; simpl in *.
      exists U__i; intuition auto.
      eapply adv_step_stays_in_R; eauto.

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
  
  Hint Resolve action_matches_strip : core.

  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_labeled_step (lameAdv b) R
      -> honest_actions_safe B R
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> universe_ok U__ra
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

    generalize H2; unfold universe_ok in H2; split_ex; intros.

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
    eapply indexed_labeled_honest_step_advuniv_implies_stripped_univ_step
    ; eauto using honest_cmds_implies_safe_actions.

    invert H3
    ; eapply honest_cmds_implies_safe_actions; eauto.
    econstructor 1; eauto.

    specialize (H _ _ H1 STRIP_UNIV_OK LAME _ _ _ UNIV_STEP); split_ex.
    do 3 eexists; intuition idtac; eauto.

    unfold strip_adversary_univ in H14; simpl in H14; eauto.
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

  Hint Unfold honest_cipher_filter_fn : core.

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
    specialize (H _ _ Heq).
    specialize (H0 _ _ Heq).
    unfold honest_key_filter_fn; rewrite H0 in H; context_map_rewrites; trivial.
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
      -> universe_starts_ok U__r
      -> R (strip_adversary U__ra) U__i
      /\ universe_ok U__ra
  .
  Proof.
    intros.
    unfold universe_ok, lameAdv, RealWorld.peel_adv in *; split_ands; subst; simpl in *.
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

  Lemma next_cmd_safe_before_after_cleaning' :
    forall A (usrs : RealWorld.honest_users A) cs uid froms sents t cmd honestk honestk',
      @next_cmd_safe honestk' (clean_ciphers honestk cs) uid froms sents t cmd
      -> (forall kid, honestk' $? kid = Some true -> honestk $? kid = Some true)
      -> next_cmd_safe honestk cs uid froms sents cmd.
  Proof.
    unfold next_cmd_safe; intros.
    apply H in H1.
    destruct cmd__n
    ; split_ex; subst
    ; repeat simple apply conj; eauto.

    - unfold RealWorld.msg_honestly_signed, RealWorld.msg_signing_key in *.
      cases (clean_ciphers honestk cs $? x); try discriminate.
      apply clean_ciphers_inv in Heq; context_map_rewrites.
      rewrite <- honest_key_honest_keyb in *; eauto.

    - unfold RealWorld.msg_to_this_user, RealWorld.msg_destination_user in *.
      cases (clean_ciphers honestk cs $? x); try discriminate.
      apply clean_ciphers_inv in Heq; context_map_rewrites; eauto.

    - apply clean_ciphers_inv in H4.
      (do 2 eexists); eauto.

    - invert H1; [ econstructor 1
                 | econstructor 2 ]
      ; eauto.

    - intros.
      apply H1 in H2; split_ex; eauto.
  Qed.

  Lemma next_cmd_safe_before_after_cleaning :
    forall A (usrs : RealWorld.honest_users A) cs uid froms sents t cmd,
      @next_cmd_safe (RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys usrs) cs usrs))
                     (clean_ciphers (RealWorld.findUserKeys usrs) cs) uid froms sents t cmd
      -> next_cmd_safe (RealWorld.findUserKeys usrs) cs uid froms sents cmd.
  Proof.
    intros; eapply next_cmd_safe_before_after_cleaning'; eauto using clean_users_no_change_honestk''.
  Qed.
    
  Hint Resolve next_cmd_safe_before_after_cleaning : core.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates (lameAdv b) R U__r U__i
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
      -> forall U__ra advcode R',
          U__ra = add_adversary U__r advcode
          -> R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
          -> simulates (@awesomeAdv B) R' U__ra U__i.
    intros.
    inversion H as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__honactsafe H__o]; clear H__s.
    inversion H__o as [R__final H__f]; clear H__o.
    inversion H__f as [R__start OK__start]; clear H__f.

    unfold simulates; rewrite H4.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_start_ok_adding_adversary
      : core.

    unfold simulates_silent_step, simulates_labeled_step, honest_actions_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.

    - subst.
      unfold honest_actions_safe; intros.

      apply honest_cmds_safe_advuniv with (b0:=b).
      eapply H__honactsafe;
        eauto using ok_universe_strip_adversary_still_ok.

    - subst.
      unfold ri_final_actions_align in *; intros.
      
      rewrite strip_adv_simpl_peel_same_as_strip_adv
      , strip_adversary_same_as_peel_strip_simpl with (b0 := b) in H3.

      assert (universe_ok (strip_adversary_univ U__r0 b)) as UOK__stripped
          by eauto using ok_universe_strip_adversary_still_ok.

      specialize (H__honactsafe _ _ H3 UOK__stripped).

      specialize (R__final _ _ H3 UOK__stripped).
      eapply R__final.
      
      + intros * STEP.
        
        destruct U__r0.
        invert STEP.
        unfold RealWorld.build_data_step, strip_adversary_univ, clean_adv in H12
        ; simpl in *.

        unfold universe_ok in *; split_ex.
        destruct userData; simpl in *.
        generalize H11; apply clean_users_cleans_user_inv in H11; intros
        ; split_ex
        ; simpl in *
        ; subst.

        eapply cleaned_universe_step_implies_orig_univ_step in H12; eauto.
        2: reflexivity.
        split_ex.

        dt x1.
        eapply H5.
        econstructor; eauto.

        user_cipher_queues_prop
        ; user_cipher_queues_prop
        ; eauto.

        eapply H__honactsafe in H54; eauto.
        
      + eapply clean_users_cleans_user; eauto.
      + trivial.

  Qed.

  Theorem refines_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : RealWorld.denote (RealWorld.Base B)),
        U__r <| U__i \ lameAdv b
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
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

Hint Constructors rCouldGenerate iCouldGenerate : core.

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

Hint Constructors traceMatches : core.
Hint Resolve
     silent_step_advuniv_implies_univ_ok
     labeled_step_adv_univ_implies_universe_ok
     action_adversary_safe_after_before_cleaning
  : core.

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
        -> rCouldGenerate U__r acts__r
        -> forall U__i,
            R' (RealWorld.peel_adv U__r) U__i
            -> exists acts__i,
                iCouldGenerate U__i acts__i
              /\ traceMatches acts__r acts__i.
Proof.
  induction 7; intros; subst; intuition eauto;
    assert (awesomeAdv (RealWorld.adversary U)) as AWE by (unfold awesomeAdv; trivial).

  - generalize (H0 _ _ H6 H3 AWE _ _ H4); intro STEPPED;
      destruct STEPPED as [U__i' STEPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H7.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H7.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.
    assert (R' (RealWorld.peel_adv U') U__i') as INR' by (subst; eauto).

    assert (universe_ok U') as UOK.
    eapply silent_step_advuniv_implies_univ_ok; eauto.

    eapply H2; [rewrite HeqR' | ..]; eauto.
    
    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK _ INR'); split_ex.
    eapply ideal_multi_silent_stays_could_generate with (acts__i:=x) in H; eauto.

  - destruct a, suid; [ | invert H4].
    assert (u0 = u) by (eauto using labeled_step_uid_same); subst.
    generalize (labeled_real_step_implies_indexed_step H4); intros; split_ex.
    generalize (H1 _ _ H6 H3 AWE _ _ _ H); intro STEPPED;
      destruct STEPPED as [a__i STEPPED];
      destruct STEPPED as [U__i' STEPPED];
      destruct STEPPED as [U__i'' STEPPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H10.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H10.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.

    assert (R' (RealWorld.peel_adv U') U__i'') as INR' by (subst; eauto).
    assert (R' (RealWorld.peel_adv (strip_adversary_univ U b)) U__i) as INR.
    rewrite HeqR'.
    rewrite <- strip_adversary_same_as_peel_strip_simpl
          , strip_adv_simpl_strip_adv_idempotent
          , strip_adversary_same_as_peel_strip_simpl with (b0:=b).
    rewrite strip_adv_simpl_peel_same_as_strip_adv in H6; assumption.

    assert (universe_ok (strip_adversary_univ U b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    generalize (H2 _ _ INR STRIP_UNIV_OK); simpl; intros ACT_SAFE.
    clear STRIP_UNIV_OK.

    apply honest_cmds_safe_advuniv in ACT_SAFE.

    assert (universe_ok U') as UOK.
    generalize H4; intros STEP.
    invert H; simpl in *.
    specialize (ACT_SAFE _ _ _ eq_refl H11); eauto.

    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK _ INR'); split_ex.

    eapply indexedIdealStep_ideal_step in H8.
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

Hint Constructors rCouldGen iCouldGen : core.

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
