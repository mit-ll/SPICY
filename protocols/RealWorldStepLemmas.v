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
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     Tactics
     Simulation
     RealWorld
     AdversarySafety.

From protocols Require Import
     ProtocolAutomation
     SafeProtocol
.

Lemma universe_predicates_preservation :
  forall {A B} (U U' : universe A B) lbl,
    universe_ok U
    -> adv_universe_ok U
    -> honest_cmds_safe U
    -> step_universe U lbl U'
    -> universe_ok U'
      /\ adv_universe_ok U'.
Proof.
  intros * UOK AUOK HCS STEP.
  destruct lbl;
    intuition eauto.

  unfold adv_universe_ok in *; split_ands;
    eapply honest_labeled_step_univ_ok;
    eauto using honest_cmds_implies_safe_actions.
Qed.

Lemma step_user_nochange_that_user_in_honest_users :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall u_id1 ud1,
          suid = Some u_id1
          -> usrs $? u_id1 = Some ud1
          -> usrs' $? u_id1 = Some ud1.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst; eauto.
Qed.

Lemma step_back_into_other_user :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc u_id1 u_id2 ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2,
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs' $? u_id2 = Some {| key_heap := ks2;
                                     protocol := cmdc2;
                                     msg_heap := qmsgs2;
                                     c_heap   := mycs2;
                                     from_nons := froms2;
                                     sent_nons := sents2;
                                     cur_nonce := cur_n2 |}
          -> usrs $? u_id2 = Some {| key_heap := ks2;
                                    protocol := cmdc2;
                                    msg_heap := qmsgs2;
                                    c_heap   := mycs2;
                                    from_nons := froms2;
                                    sent_nons := sents2;
                                    cur_nonce := cur_n2 |}
            \/ exists m qmsgs2',
              qmsgs2 = qmsgs2' ++ [m]
              /\ usrs $? u_id2 = Some {| key_heap := ks2;
                                        protocol := cmdc2;
                                        msg_heap := qmsgs2';
                                        c_heap   := mycs2;
                                        from_nons := froms2;
                                        sent_nons := sents2;
                                        cur_nonce := cur_n2 |}.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst; eauto.

  destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; eauto.
  destruct rec_u; eauto.
Qed.

Lemma silent_step_nochange_other_user' :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc cmdc' u_id1 u_id2 ud2 usrs'',
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some ud2
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> usrs'' $? u_id2 = Some ud2.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst;
      try discriminate;
      try solve [ clean_map_lookups; trivial ].
  specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _
                          _ _ _ _ _ _ _ _ _ _ _
                          eq_refl eq_refl eq_refl).
  specialize (IHstep_user cmdc cmdc').
  specialize (IHstep_user _ _ _ _ eq_refl H26 H27 H28 eq_refl).
  clean_map_lookups; eauto.
Qed.

Lemma silent_step_nochange_other_user :
  forall {A B} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        cmd cmd' ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall u_id1 u_id2 ud2 usrs'',
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmd;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some ud2
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmd';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> usrs'' $? u_id2 = Some ud2.
Proof.
  intros; subst; eapply silent_step_nochange_other_user'; eauto.
Qed.

(* need to know that msg, if cipher, is in cs *)
Lemma findKeysCrypto_addnl_cipher :
  forall {t} (msg : crypto t) cs c_id c,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> findKeysCrypto cs msg = findKeysCrypto (cs $+ (c_id,c)) msg.
Proof.
  intros.
  unfold findKeysCrypto.
  destruct msg; eauto.
  destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
  simpl in *.
  specialize (H0 _ eq_refl); contradiction.
Qed.

Lemma merge_findKeysCrypto_addnl_cipher :
  forall {t} (msg : crypto t) cs c_id c ks,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> ks $k++ findKeysCrypto cs msg = ks $k++ findKeysCrypto (cs $+ (c_id,c)) msg.
Proof.
  intros.
  erewrite findKeysCrypto_addnl_cipher; trivial.
Qed.

Lemma msg_signed_addressed_addnl_cipher :
  forall {t} (msg : crypto t) cs c_id c honestk suid,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> msg_signed_addressed honestk cs suid msg =
      msg_signed_addressed honestk (cs $+ (c_id,c)) suid msg.
Proof.
  intros.
  match goal with
  | [ |- msg_signed_addressed ?honk ?cs ?suid ?msg = _ ] =>
    case_eq (msg_signed_addressed honk cs suid msg)
  end; intros; symmetry; eauto using msg_signed_addressed_nochange_addnl_cipher.
Qed.

Lemma msg_signed_addressed_nochange_addnl_honest_key :
  forall {t} (msg : crypto t) (gks : keys) honestk cs suid k_id tf,
    ~ In k_id honestk
    -> gks $? k_id = None
    -> (forall k, msg_signing_key cs msg = Some k ->
            gks $? k <> None /\
            (honest_key honestk k ->
             message_no_adv_private honestk cs msg /\ msgCiphersSignedOk honestk cs msg))
    -> msg_signed_addressed honestk cs suid msg = tf
    -> msg_signed_addressed (honestk $+ (k_id,true)) cs suid msg = tf.
Proof.
  destruct tf; eauto using msg_signed_addressed_addnl_honest_key; intros.
  unfold msg_signed_addressed in *; intros.
  rewrite andb_false_iff in *; split_ors; eauto.
  left.
  unfold msg_honestly_signed in *.
  destruct (msg_signing_key cs msg); eauto.
  unfold honest_keyb in *.
  destruct (k_id ==n k); subst; clean_map_lookups; eauto.
  specialize (H1 _ eq_refl); split_ands; contradiction.
Qed.

Lemma honestk_merge_new_msgs_keys_same :
  forall honestk cs  {t} (msg : crypto t),
    message_no_adv_private honestk cs msg
    -> (honestk $k++ findKeysCrypto cs msg) = honestk.
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros.
  solve_perm_merges; eauto;
    specialize (H _ _ Heq0); clean_map_lookups; eauto.
Qed.

Lemma honestk_merge_new_msgs_keys_dec_same :
  forall honestk {t} (msg : message t),
    (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
    -> (honestk $k++ findKeysMessage msg) = honestk.
Proof.
  intros.
  apply map_eq_Equal; unfold Equal; intros.
  solve_perm_merges; eauto;
    specialize (H _ _ Heq0); clean_map_lookups; eauto.
Qed.

(* need to know that msg, if cipher, is in cs *)
Lemma updateTrackedNonce_addnl_cipher :
  forall suid nons cs {t} (msg : crypto t) c_id c,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> updateTrackedNonce suid nons cs msg =
      updateTrackedNonce suid nons (cs $+ (c_id, c)) msg.
Proof.
  intros.
  unfold updateTrackedNonce.
  destruct msg; eauto.
  destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
  specialize (H0 _ eq_refl); contradiction.
Qed.

Lemma msg_not_accepted_pattern_addnl_cipher :
  forall {t} (msg : crypto t) cs suid froms pat c_id c,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> ~ msg_accepted_by_pattern cs suid froms pat msg
    -> ~ msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg.
Proof.
  intros.
  unfold not.
  destruct pat; intros; eauto;
    repeat
      match goal with
      | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] => invert H
      | [ H : _ $+ (?cid1,_) $? ?cid2 = _ |- _ ] => destruct (cid1 ==n cid2); subst; clean_map_lookups
      | [ H : ?cs $? ?cid = None,
              H1 : (forall c_id, _ = Some c_id -> ?cs $? c_id <> None) |- _ ] => simpl in H1; specialize (H1 _ eq_refl); contradiction
      | [ H : ~ msg_accepted_by_pattern ?cs ?to ?froms ?pat ?m |- _ ] =>
        assert (msg_accepted_by_pattern cs to froms pat m) by (econstructor; eauto); contradiction
      end.
Qed.

Lemma msg_accepted_pattern_addnl_cipher :
  forall {t} (msg : crypto t) cs suid froms pat c_id c,
    ~ In c_id cs
    -> msg_accepted_by_pattern cs suid froms pat msg
    -> msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg.
Proof.
  intros * NOTIN H; invert H; eauto.
Qed.


Lemma msg_accepted_pattern_addnl_cipher_inv :
  forall {t} (msg : crypto t) cs suid froms pat c_id c,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg
    -> msg_accepted_by_pattern cs suid froms pat msg.
Proof.
  intros * NOTIN INCS H; invert H; eauto;
    destruct (c_id ==n c_id0); subst;
      clean_map_lookups; eauto;
        simpl in INCS; specialize (INCS _ eq_refl);
          contradiction.
Qed.

Lemma findKeysCrypto_addnl_cipher' :
  forall cs cid1 c cid2 t,
    cid1 <> cid2
    -> @findKeysCrypto t (cs $+ (cid1, c)) (SignedCiphertext cid2) =
      @findKeysCrypto t cs (SignedCiphertext cid2).
Proof.
  intros.
  unfold findKeysCrypto in *; clean_map_lookups; eauto.
Qed.

Lemma updateTrackedNonce_addnl_cipher' :
  forall cs cid1 c cid2 t nons suid,
    cid1 <> cid2
    -> @updateTrackedNonce t suid nons cs (SignedCiphertext cid2) =
      @updateTrackedNonce t suid nons (cs $+ (cid1, c)) (SignedCiphertext cid2).
Proof.
  intros.
  unfold updateTrackedNonce; clean_map_lookups; eauto.
Qed.

Hint Resolve
     findKeysCrypto_addnl_cipher
     merge_findKeysCrypto_addnl_cipher
     updateTrackedNonce_addnl_cipher
     updateTrackedNonce_addnl_cipher'
     msg_signed_addressed_addnl_cipher
     msg_signed_addressed_nochange_addnl_honest_key
     msg_accepted_pattern_addnl_cipher
     msg_accepted_pattern_addnl_cipher_inv
     msg_not_accepted_pattern_addnl_cipher
  : core.


Lemma step_limited_change_other_user' :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc cmdc' u_id1 u_id2 usrs'' ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2,
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some {| key_heap := ks2;
                                    protocol := cmdc2;
                                    msg_heap := qmsgs2;
                                    c_heap   := mycs2;
                                    from_nons := froms2;
                                    sent_nons := sents2;
                                    cur_nonce := cur_n2 |}
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> (forall cid c, cs $? cid = Some c -> cs' $? cid = Some c)
            /\ ( usrs'' $? u_id2 = Some {| key_heap := ks2;
                                          protocol := cmdc2;
                                          msg_heap := qmsgs2;
                                          c_heap   := mycs2;
                                          from_nons := froms2;
                                          sent_nons := sents2;
                                          cur_nonce := cur_n2 |}
                \/ exists m,
                  usrs'' $? u_id2 = Some {| key_heap := ks2;
                                            protocol := cmdc2;
                                            msg_heap := qmsgs2 ++ [m];
                                            c_heap   := mycs2;
                                            from_nons := froms2;
                                            sent_nons := sents2;
                                            cur_nonce := cur_n2 |} )
.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst;
      try solve [ split; [intros | left; clean_map_lookups; trivial]; eauto ].
  
  - specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _
                            _ _ _ _ _ _ _ _ _ _ _
                            eq_refl eq_refl).
    specialize (IHstep_user cmdc cmdc').
    specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ eq_refl H25 H26 H27 eq_refl).
    split_ors; eauto.

  - split; [ | clean_context; clean_map_lookups]; eauto.
    destruct (rec_u_id ==n u_id2); subst; eauto.
Qed.

Lemma step_limited_change_other_user :
  forall {A B} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        cmd cmd' ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall u_id1 u_id2 usrs'' ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmd;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some {| key_heap := ks2;
                                    protocol := cmd2;
                                    msg_heap := qmsgs2;
                                    c_heap   := mycs2;
                                    from_nons := froms2;
                                    sent_nons := sents2;
                                    cur_nonce := cur_n2 |}
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmd';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> (forall cid c, cs $? cid = Some c -> cs' $? cid = Some c)
            /\ ( usrs'' $? u_id2 = Some {| key_heap := ks2;
                                          protocol := cmd2;
                                          msg_heap := qmsgs2;
                                          c_heap   := mycs2;
                                          from_nons := froms2;
                                          sent_nons := sents2;
                                          cur_nonce := cur_n2 |}
                \/ exists m,
                  usrs'' $? u_id2 = Some {| key_heap := ks2;
                                            protocol := cmd2;
                                            msg_heap := qmsgs2 ++ [m];
                                            c_heap   := mycs2;
                                            from_nons := froms2;
                                            sent_nons := sents2;
                                            cur_nonce := cur_n2 |})
.
Proof.
  intros; subst; eapply step_limited_change_other_user'; eauto.
Qed.
