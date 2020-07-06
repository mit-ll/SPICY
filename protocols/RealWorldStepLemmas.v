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
     MessageEq
     MessageEqTheory
     Tactics
     Simulation
     RealWorld
     AdversaryUniverse
     AdversarySafety.

From protocols Require Import
     ProtocolAutomation
     SafeProtocol
.

Ltac dismiss_adv :=
  repeat
    match goal with
    | [ LAME : lameAdv _ (adversary ?ru), STEP : step_user _ None _ _ |- _ ] =>
      destruct ru; unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
    | [ LAME : lameAdv _ _, STEP : step_user _ None _ _ |- _ ] =>
      unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
    | [ ADVP : protocol ?adv = Return _, STEP : step_user _ None (_,_,_,_,_,_,_,_,_,_,protocol ?adv) _ |- _ ] =>
      rewrite ADVP in STEP; invert STEP
    end.

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

Lemma updateSentNonce_addnl_cipher :
  forall suid nons cs {t} (msg : crypto t) c_id c,
    ~ In c_id cs
    -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
    -> updateSentNonce suid nons cs msg =
      updateSentNonce suid nons (cs $+ (c_id, c)) msg.
Proof.
  intros.
  unfold updateSentNonce.
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

Lemma updateSentNonce_addnl_cipher' :
  forall cs cid1 c cid2 t nons suid,
    cid1 <> cid2
    -> @updateSentNonce t suid nons cs (SignedCiphertext cid2) =
      @updateSentNonce t suid nons (cs $+ (cid1, c)) (SignedCiphertext cid2).
Proof.
  intros.
  unfold updateSentNonce; clean_map_lookups; eauto.
Qed.

Hint Resolve
     findKeysCrypto_addnl_cipher
     merge_findKeysCrypto_addnl_cipher
     updateTrackedNonce_addnl_cipher
     updateTrackedNonce_addnl_cipher'
     updateSentNonce_addnl_cipher
     updateSentNonce_addnl_cipher'
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

Section MessageEqLemmas.

  Import AdversarySafety.Automation.

  Lemma message_content_eq_addnl_key :
    forall t__rw m__rw  t__iw m__iw gks kid k,
      @content_eq t__rw t__iw m__rw m__iw gks
      -> ~ In kid gks
      -> content_eq m__rw m__iw (gks $+ (kid, k)).
  Proof.
    induct m__rw; intros; eauto.
    - destruct m__iw; simpl in *; eauto.
      destruct acc, acc0.
      destruct (kid ==n k0); subst; clean_map_lookups; eauto.
    - destruct m__iw; simpl in *; eauto; split_ands; eauto.
  Qed.

  Lemma perm_merge_same :
    forall kid kp ks1 ks2 ks3 ks1' ks2' ks3',
      ks1 $k++ ks2 $k++ ks3 $? kid = Some kp
      -> ks1 $? kid = ks1' $? kid
      -> ks2 $? kid = ks2' $? kid
      -> ks3 $? kid = ks3' $? kid
      -> ks1' $k++ ks2' $k++ ks3' $? kid = Some kp.
  Proof.
    intros * KS1 KS2 KS3 H.
    solve_perm_merges; eauto.
  Qed.

  Lemma message_content_eq_addnl_key_inv :
    forall t__rw m__rw  t__iw m__iw gks kid k,
      content_eq m__rw m__iw (gks $+ (kid, k))
      -> (forall k_id kp, findKeysMessage m__rw $? k_id = Some kp -> gks $? k_id <> None)
      -> ~ In kid gks
      -> @content_eq t__rw t__iw m__rw m__iw gks.
  Proof.
    induct m__rw; intros; eauto.
    - destruct m__iw; simpl in *; eauto.
      destruct acc, acc0.
      destruct (kid ==n k0); subst; clean_map_lookups; eauto.
      simpl in H0; specialize (H0 k0); rewrite add_eq_o in H0 by trivial.
      specialize (H0 _ eq_refl); contradiction.
    - destruct m__iw; simpl in *; eauto; split_ands.

      assert (FKML : forall k_id kp, findKeysMessage m__rw1 $? k_id = Some kp -> gks $? k_id <> None) by
          (intros; cases (findKeysMessage m__rw2 $? k_id); eapply H0; solve_perm_merges; eauto).
      assert (FKMR : forall k_id kp, findKeysMessage m__rw2 $? k_id = Some kp -> gks $? k_id <> None) by
          (intros; cases (findKeysMessage m__rw1 $? k_id); eapply H0; solve_perm_merges; eauto).

      split; eauto.
  Qed.

  Lemma message_eq_user_add_nochange_cs_ks_msgs :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks
      ks cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks |} m__iw iu chid.
  Proof using All.
    intros.

    invert H0; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto;
        destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; eauto;
          match goal with
          | [ ARG : ?usrs $? ?uid = Some _,
                    IARG : IdealWorld.users _ $? ?uid = Some _,
                           H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] =>
            eapply H in ARG
          end; eauto.

    all: 
      invert H; [ econstructor 1 | econstructor 2 ]; eauto.
  Qed.

  Lemma message_eq_user_add_nochange_drop_not_signed_addressed_msg :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks
      ks cmd t (msg : crypto t) qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      usrs $? uid = Some (mkUserData ks cmd (existT _ _ msg :: qmsgs) mycs froms sents cur_n)
      -> msg_signed_addressed (findUserKeys usrs) cs (Some uid) msg = false
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks |} m__iw iu chid.
  Proof.
    intros.

    assert ( KPMQ : key_perms_from_message_queue cs (findUserKeys usrs) (existT _ _ msg :: qmsgs) uid froms $0
                    = key_perms_from_message_queue cs (findUserKeys usrs) qmsgs uid froms $0).
    unfold key_perms_from_message_queue.
    pose proof (clean_messages_cons_split cs (findUserKeys usrs) uid froms qmsgs _ _ msg eq_refl); split_ors; subst.
    rewrite H2; trivial.

    unfold not_replayed, msg_signed_addressed in * |- .
    rewrite andb_false_iff in H0; rewrite !andb_true_iff in H3; split_ex; split_ors.
    rewrite H0 in H3; discriminate.
    unfold msg_to_this_user, msg_destination_user in *; context_map_rewrites;
      destruct (cipher_to_user x1 ==n uid); subst; discriminate.

    invert H1; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto;
        destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; eauto;
          match goal with
          | [ ARG : ?usrs $? ?uid = Some _,
                    IARG : IdealWorld.users _ $? ?uid = Some _,
                           H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] =>
            eapply H in ARG
          end; eauto.

    all: 
      invert H; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      rewrite <- KPMQ; eauto.
  Qed.

  (* Lemma message_eq_user_add_nochange_drop_signed_addressed_msg : *)
  (*   forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks *)
  (*     ks cmd t (msg : crypto t) qmsgs mycs froms sents cur_n cmd' sents' cur_n' *)
  (*     t (m__rw : crypto t) m__iw iu chid uid, *)

  (*     usrs $? uid = Some (mkUserData ks cmd (existT _ _ msg :: qmsgs) mycs froms sents cur_n) *)
  (*     -> msg_signed_addressed (findUserKeys usrs) cs (Some uid) msg = true *)
  (*     -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid *)
  (*     -> message_eq *)
  (*         m__rw *)
  (*         {| users := *)
  (*              usrs $+ (uid, *)
  (*                       {| key_heap := ks; *)
  (*                          protocol := cmd'; *)
  (*                          msg_heap := qmsgs; *)
  (*                          c_heap := mycs; *)
  (*                          from_nons := updateTrackedNonce (Some uid) froms cs msg; *)
  (*                          sent_nons := sents'; *)
  (*                          cur_nonce := cur_n' |}); *)
  (*            adversary := adv'; *)
  (*            all_ciphers := cs; *)
  (*            all_keys := gks |} m__iw iu chid. *)
  (* Proof. *)
  (*   intros. *)

  (*   unfold msg_signed_addressed in H0; rewrite andb_true_iff in H0; split_ex. *)

  (*   pose proof (clean_messages_cons_split cs (findUserKeys usrs) uid froms qmsgs _ _ msg eq_refl); split_ors; subst. *)
  
  (*   - unfold not_replayed in H4; rewrite H0 in H4. *)
  (*     unfold msg_to_this_user, msg_destination_user in *; *)
  (*       destruct msg; try discriminate; *)
  (*         cases (cs $? c_id); try discriminate; *)
  (*           cases (cipher_to_user c ==n uid); try discriminate. *)
  (*     simpl in *; unfold AdversaryUniverse.msg_nonce_ok in H4; context_map_rewrites. *)
  (*     cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate. *)
  (*     rewrite e; destruct (uid ==n uid); try contradiction. *)
  
  (*     invert H1; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; eauto; *)
  (*         destruct (u ==n cipher_to_user c); subst; clean_map_lookups; eauto; simpl; eauto; *)
  (*           match goal with *)
  (*           | [ ARG : ?usrs $? ?uid = Some _, *)
  (*                     IARG : IdealWorld.users _ $? ?uid = Some _, *)
  (*                            H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] => *)
  (*             eapply H in ARG *)
  (*           end; eauto. *)

  (*     1-2:  *)
  (*       invert H; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       unfold key_perms_from_message_queue in *; *)
  (*       rewrite H3, key_perms_from_message_queue_notation in *; eauto. *)

  (*   - unfold  updateTrackedNonce; context_map_rewrites. *)
  (*     unfold not_replayed in H4; rewrite H0 in H4. *)
  (*     unfold msg_to_this_user, msg_destination_user in *; context_map_rewrites. *)
  (*     destruct (cipher_to_user x1 ==n uid); try discriminate; rewrite e. *)
  (*     destruct (uid ==n uid); try contradiction. *)
  (*     simpl in *; context_map_rewrites. *)
  (*     cases (count_occ msg_seq_eq froms (cipher_nonce x1)); try discriminate. *)

  (*     invert H1; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; eauto; *)
  (*         destruct (u ==n cipher_to_user x1); subst; clean_map_lookups; eauto; simpl; eauto; *)
  (*           match goal with *)
  (*           | [ ARG : ?usrs $? ?uid = Some _, *)
  (*                     IARG : IdealWorld.users _ $? ?uid = Some _, *)
  (*                            H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] => *)
  (*             eapply H in ARG *)
  (*           end; eauto; clean_map_lookups. *)
  
  (*     + invert H; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto. *)
  (*       unfold key_perms_from_message_queue in *. *)
  (*       rewrite H3, key_perms_from_message_queue_notation in *. *)
  (*       simpl in H15; context_map_rewrites. *)
  (*       rewrite key_perms_from_message_queue_notation in H15. *)

  (*       destruct x1; eauto; simpl in *. *)
  (*       rewrite key_perms_from_message_queue_pull_merge in H15. *)
  (* Admitted. *)

  Lemma key_perms_from_known_ciphers_idempotent_addnl_cipher :
    forall cs cs' mycs ks honestk c_id c,
      ~ In c_id cs
      -> cs' = cs $+ (c_id,c)
      -> user_cipher_queue_ok cs honestk mycs
      -> key_perms_from_known_ciphers cs mycs ks
        = key_perms_from_known_ciphers cs' mycs ks.
  Proof.
    induction mycs; intros; subst; eauto.
    invert H1; split_ex.
    simpl.
    destruct (c_id ==n a); subst; clean_map_lookups; eauto.
  Qed.

  Lemma key_perms_from_known_ciphers_user_new_cipher :
    forall cs cs' mycs ks honestk c_id c,
      ~ In c_id cs
      -> cs' = cs $+ (c_id,c)
      -> user_cipher_queue_ok cs honestk mycs
      -> key_perms_from_known_ciphers cs' (c_id :: mycs) ks
        = key_perms_from_known_ciphers cs mycs ks $k++
                                       match c with
                                       | SigCipher _ _ _ m | SigEncCipher _ _ _ _ m => findKeysMessage m
                                       end.
  Proof.
    induction mycs; intros; subst; simpl; clean_map_lookups; eauto.
    - destruct c; trivial.

    - invert H1; split_ex.
      destruct (c_id ==n a); subst; clean_map_lookups.
      assert (user_cipher_queue_ok cs honestk mycs) by (unfold user_cipher_queue_ok; trivial).
      eapply IHmycs in H2; eauto; simpl in H2; clean_map_lookups.
      destruct x; destruct c;
        rewrite key_perms_from_known_ciphers_pull_merge;
        rewrite H2;
        rewrite key_perms_from_known_ciphers_pull_merge;
        rewrite merge_perms_assoc, merge_perms_sym with (ks1 := findKeysMessage msg0), <- merge_perms_assoc;
        trivial.
  Qed.

  Lemma not_replayed_same_addnl_cipher :
    forall cs cs' honestk uid froms c_id c t (msg : crypto t),
      ~ In c_id cs
      -> cs' = cs $+ (c_id,c)
      -> (forall cid : cipher_id, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> not_replayed cs honestk uid froms msg
        = not_replayed cs' honestk uid froms msg
  .
  Proof.
    unfold not_replayed; intros; subst.
    unfold msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user, msg_nonce_ok.
    destruct msg; eauto.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    specialize (H1 _ eq_refl); contradiction.
  Qed.

  Lemma not_replayed_same_addnl_key :
    forall cs honestk uid froms kid t (msg : crypto t) gks,
      ~ In kid gks
      -> encrypted_ciphers_ok honestk cs gks
      -> not_replayed cs honestk uid froms msg
        = not_replayed cs (honestk $+ (kid,true)) uid froms msg
  .
  Proof.
    unfold not_replayed; intros; subst.
    unfold msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user, msg_nonce_ok.
    destruct msg; eauto.
    cases (cs $? c_id); eauto.
    assert (cipher_signing_key c <> kid).
    destruct (cipher_signing_key c ==n kid); subst; encrypted_ciphers_prop; simpl; clean_map_lookups; eauto.
    cases (if cipher_to_user c ==n uid then true else false); simpl; eauto.
    2: rewrite !andb_false_r, !andb_false_l; trivial.
    cases (count_occ msg_seq_eq froms (cipher_nonce c)).
    2: rewrite !andb_false_r; trivial.
    unfold honest_keyb.
    cases (honestk $? cipher_signing_key c); clean_map_lookups; eauto.
  Qed.

  Lemma findKeysCrypto_same_new_cipher :
    forall cs t (msg : crypto t) c_id c,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> findKeysCrypto (cs $+ (c_id,c)) msg = findKeysCrypto cs msg.
  Proof.
    intros; unfold findKeysCrypto.
    destruct msg; eauto; simpl in *.
    cases (cs $? c_id0); eauto;
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    specialize (H0 _ eq_refl); contradiction.
  Qed.

  Lemma key_perms_from_message_queue_idempotent_addnl_cipher :
    forall cs cs' qmsgs gks ks honestk uid froms c_id c,
      ~ In c_id cs
      -> cs' = cs $+ (c_id,c)
      -> message_queue_ok honestk cs qmsgs gks
      -> key_perms_from_message_queue cs honestk qmsgs uid froms ks
        = key_perms_from_message_queue (cs $+ (c_id, c)) honestk qmsgs uid froms ks.
  Proof.
    induction qmsgs; intros; subst; eauto.
    unfold key_perms_from_message_queue in *.
    destruct a.
    pose proof (clean_messages_cons_split cs honestk uid froms qmsgs _ _ c0 eq_refl); intros.
    pose proof (clean_messages_cons_split (cs $+ (c_id,c)) honestk uid froms qmsgs _ _ c0 eq_refl); intros.
    invert H1;
      assert ( message_queue_ok honestk cs qmsgs gks ) by (unfold message_queue_ok; eassumption).
    split_ex.
    clear H3 H5 H6.
    split_ors; split_ex;
      match goal with
      | [ H1 : not_replayed ?cs _ _ _ _ = ?tf1, H2 : not_replayed (?cs $+ (_,_)) _ _ _ _ = ?tf2 |- _ ] =>
        assert (tf1 <> tf2) by discriminate
        ; idtac H1 H2
        ; erewrite not_replayed_same_addnl_cipher in H1 by eauto
        ; rewrite H1 in H2
        ; discriminate
      | [ H1 : clean_messages _ ?cs _ _ _ = _, H2 : clean_messages _ (?cs $+ (_,_)) _ _ _ = _ |- _ ] =>
        rewrite H1, H2
      end; eauto.

    simpl; erewrite IHqmsgs; eauto.
    rewrite findKeysCrypto_same_new_cipher; eauto.
    subst.
    invert H5; simpl in *.
    specialize (H4 _ eq_refl).
    destruct (c_id ==n x1); subst; clean_map_lookups; eauto.
  Qed.

  Lemma key_perms_from_message_queue_idempotent_addnl_key :
    forall cs qmsgs gks ks honestk uid froms kid,
      ~ In kid gks
      -> encrypted_ciphers_ok honestk cs gks
      -> message_queue_ok honestk cs qmsgs gks
      -> key_perms_from_message_queue cs honestk qmsgs uid froms ks
        = key_perms_from_message_queue cs (honestk $+ (kid,true)) qmsgs uid froms ks.
  Proof.
    induction qmsgs; intros; subst; eauto.
    unfold key_perms_from_message_queue in *.
    destruct a.
    pose proof (clean_messages_cons_split cs honestk uid froms qmsgs _ _ c eq_refl); intros.
    pose proof (clean_messages_cons_split cs (honestk $+ (kid,true)) uid froms qmsgs _ _ c eq_refl); intros.
    invert H1;
      assert ( message_queue_ok honestk cs qmsgs gks ) by (unfold message_queue_ok; eassumption).
    split_ex.
    (* clear H3 H5 H6. *)
    split_ors; split_ex;
      match goal with
      | [ H1 : not_replayed _ ?honk _ _ _ = ?tf1, H2 : not_replayed _ (?honk $+ (_,_)) _ _ _ = ?tf2 |- _ ] =>
        assert (tf1 <> tf2) by discriminate
        ; idtac H1 H2
        ; erewrite not_replayed_same_addnl_key in H1 by eauto
        ; rewrite H1 in H2
        ; discriminate
      | [ H1 : clean_messages ?honk _ _ _ _ = _, H2 : clean_messages (?honk $+ (_,_)) _ _ _ _ = _ |- _ ] =>
        rewrite H1, H2
      end; eauto.

    simpl; erewrite IHqmsgs; eauto.
    subst.
    invert H9; simpl in *.
    clean_map_lookups; eauto.
  Qed.

  Lemma message_eq_user_add_addnl_cipher :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs cs' cid c gks
      ks cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      ~ In cid cs
      -> cs' = cs $+ (cid,c)
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> message_queues_ok cs usrs gks
      -> match c with
        | @SigCipher t _ _ _ m | @SigEncCipher t _ _ _ _ m => keys_mine ks (findKeysMessage m)
        end
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := cid :: mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs';
             all_keys := gks |} m__iw iu chid.
  Proof.
    intros; subst.

    invert H6; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto;
        destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; eauto;
          match goal with
          | [ ARG : ?usrs $? ?uid = Some _,
                    IARG : IdealWorld.users _ $? ?uid = Some _,
                           H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] =>
            generalize ARG; intros; eapply H in ARG
          end; eauto;
            destruct (c_id ==n cid); subst; clean_map_lookups.

    - invert H1; [ econstructor 1 | econstructor 2 ]; eauto; simpl in *; clean_map_lookups.
      msg_queue_prop.
      user_cipher_queues_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher; eauto.
      assert (RW : key_perms_from_known_ciphers (cs $+ (cid, c)) (cid :: mycs) $0
                   = key_perms_from_known_ciphers (cs $+ (cid, c)) mycs
                                                  match c with
                                                  | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => $0 $k++ findKeysMessage m
                                                  end) by (simpl; clean_map_lookups; trivial).
      rewrite <- RW; clear RW.
      erewrite key_perms_from_known_ciphers_user_new_cipher; eauto.
      rewrite merge_perms_sym with (ks1 := key_perms_from_known_ciphers cs mycs $0), <- merge_perms_assoc.
      eapply perm_merge_same with (ks1' := ks $k++ match c with
                                                   | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => findKeysMessage m
                                                   end); eauto.
      destruct c; rewrite merge_keys_mine; trivial.
      
    - invert H0; [ econstructor 1 | econstructor 2 ]; eauto; simpl in *; clean_map_lookups.
      msg_queue_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher; eauto.
      user_cipher_queues_prop.
      erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher; eauto.

    - invert H1; [ econstructor 1 | econstructor 2 ]; eauto; simpl in *; clean_map_lookups;
        msg_queue_prop;
        user_cipher_queues_prop;
        erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher; eauto.

      + assert (RW : key_perms_from_known_ciphers (cs $+ (cid, c)) (cid :: mycs) $0
                     = key_perms_from_known_ciphers (cs $+ (cid, c)) mycs
                                                    match c with
                                                    | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => $0 $k++ findKeysMessage m
                                                    end) by (simpl; clean_map_lookups; trivial).
        rewrite <- RW; clear RW.
        erewrite key_perms_from_known_ciphers_user_new_cipher; eauto.
        rewrite merge_perms_sym with (ks1 := key_perms_from_known_ciphers cs mycs $0), <- merge_perms_assoc.
        eapply perm_merge_same with (ks1' := ks $k++ match c with
                                                     | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => findKeysMessage m
                                                     end); eauto.
        destruct c; rewrite merge_keys_mine; trivial.
        
      + assert (RW : key_perms_from_known_ciphers (cs $+ (cid, c)) (cid :: mycs) $0
                     = key_perms_from_known_ciphers (cs $+ (cid, c)) mycs
                                                    match c with
                                                    | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => $0 $k++ findKeysMessage m
                                                    end) by (simpl; clean_map_lookups; trivial).
        rewrite <- RW; clear RW.
        erewrite key_perms_from_known_ciphers_user_new_cipher; eauto.
        rewrite merge_perms_sym with (ks1 := key_perms_from_known_ciphers cs mycs $0), <- merge_perms_assoc.
        eapply perm_merge_same with (ks1' := ks $k++ match c with
                                                     | @SigCipher t0 _ _ _ m | @SigEncCipher t0 _ _ _ _ m => findKeysMessage m
                                                     end); eauto.
        destruct c; rewrite merge_keys_mine; trivial.

    - invert H0; [ econstructor 1 | econstructor 2 ]; eauto; simpl in *; clean_map_lookups;
        user_cipher_queues_prop;
        msg_queue_prop;
        erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher; eauto;
          erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher; eauto.
  Qed.

  Lemma message_eq_user_add_addnl_key :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks gks'
      ks ks' kid k cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      ~ In kid gks
      -> ks' = add_key_perm kid true ks
      -> gks' = gks $+ (kid,k)
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> keys_and_permissions_good gks usrs adv.(key_heap)
      (* -> user_cipher_queues_ok cs (findUserKeys usrs) usrs *)
      -> message_queues_ok cs usrs gks
      (* -> message_queue_ok (findUserKeys usrs) cs qmsgs gks *)
      (* -> keys_mine ks (findKeysCrypto cs c) *)
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks';
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks' |} m__iw iu chid.
  Proof.
    intros; subst.

    invert H6; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto using message_content_eq_addnl_key;
        destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; eauto;
          assert (k__sign <> kid) by (encrypted_ciphers_prop; destruct (k__sign ==n kid); subst; clean_map_lookups; eauto);
          clean_map_lookups;
          match goal with
          | [ ARG : ?usrs $? ?uid = Some _,
                    IARG : IdealWorld.users _ $? ?uid = Some _,
                           H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] =>
            generalize ARG; intros; eapply H in ARG
          end;
          try
            match goal with
            | [ H : honest_key (?ks $+ (?kid1,_)) ?kid |- honest_key ?ks ?kid ] =>
              assert (kid <> kid1) by (encrypted_ciphers_prop; destruct (kid ==n kid1); subst; clean_map_lookups; eauto);
                invert H; constructor; clean_map_lookups; trivial
            end; eauto.

    - invert H2; [ econstructor 1; swap 1 2 | econstructor 2; swap 1 2 ]; eauto; simpl in *; clean_map_lookups; eauto.
      keys_and_permissions_prop.
      unfold add_key_perm.
      cases (ks $? kid).
      apply H14 in Heq; clean_map_lookups.
      msg_queue_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.

      eapply perm_merge_same; eauto.

    - invert H0; [ econstructor 1; swap 1 2 | econstructor 2; swap 1 2 ]; eauto; simpl in *; clean_map_lookups; eauto.
      keys_and_permissions_prop.
      unfold add_key_perm.
      cases (data__rw.(key_heap) $? kid).
      apply H16 in Heq; clean_map_lookups.
      msg_queue_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.

    - invert H2; [ econstructor 1; swap 1 2 | econstructor 2; swap 1 2 ];
        eauto; simpl in *; clean_map_lookups; eauto;
          keys_and_permissions_prop;
          unfold add_key_perm;
          cases (ks $? kid).

      apply H16 in Heq; clean_map_lookups.

      msg_queue_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.
      eapply perm_merge_same; eauto.

      apply H16 in Heq; clean_map_lookups.

      msg_queue_prop.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.
      eapply perm_merge_same; eauto.
      assert (k__enc0 <> kid) by (encrypted_ciphers_prop; destruct (k__enc0 ==n kid); subst; clean_map_lookups; eauto);
        cases (kid ==n k__enc0); subst; clean_map_lookups; eauto.

    - invert H0; [ econstructor 1; swap 1 2 | econstructor 2; swap 1 2 ]; eauto; simpl in *; clean_map_lookups; eauto;
        keys_and_permissions_prop;
        msg_queue_prop.

      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.
      erewrite <- key_perms_from_message_queue_idempotent_addnl_key; eauto.

  Qed.

  Lemma message_eq_user_decrypt_msg :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks
      ks ks' cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid cid k__s k__e uid' mseq t__m (msg : message t__m),

      cs $? cid = Some (SigEncCipher k__s k__e uid' mseq msg)
      -> List.In cid mycs
      -> ks' = ks $k++ findKeysMessage msg
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks';
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks |} m__iw iu chid.
  Proof.
    intros; subst.

    assert (honest_key (findUserKeys usrs) k__s) by ( user_cipher_queues_prop; constructor; eauto ).
    invert H1; encrypted_ciphers_prop; simpl in *; eauto.

    invert H5; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto;
        destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; eauto;
          match goal with
          | [ ARG : ?usrs $? ?uid = Some _,
                    IARG : IdealWorld.users _ $? ?uid = Some _,
                           H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] =>
            generalize ARG; intros; eapply H in ARG
          end;
          rewrite honestk_merge_new_msgs_keys_dec_same with (honestk := findUserKeys usrs) in * by eauto;
          eauto.

    eapply ch_keys_from_cipher with (c_id' := cid); eauto; simpl; eauto.
    eapply ch_keys_from_cipher with (c_id' := cid); eauto; simpl; eauto.

  Qed.


  (* Lemma message_eq_user_add : *)
  (*   forall A B (usrs : honest_users A) (adv adv' : user_data B) cs cs' gks gks' *)
  (*     ks ks' cmd qmsgs mycs froms sents cur_n cmd' qmsgs' mycs' froms' sents' cur_n' *)
  (*     t (m__rw : crypto t) m__iw iu chid uid, *)

  (*     usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n) *)
  (*     -> (cs' = cs \/ (exists cid c, ~ In cid cs /\ cs' = cs $+ (cid,c))) *)
  (*     -> ((ks' = ks /\ gks' = gks) \/ (exists kid k ky, ~ In kid gks /\ ks' = ks $k++ ($0 $+ (kid,k)) /\ gks' = gks $+ (kid,ky))) *)
  (*     -> encrypted_ciphers_ok (findUserKeys usrs) cs gks *)
  (*     -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid *)
  (*     -> message_eq *)
  (*         m__rw *)
  (*         {| users := *)
  (*              usrs $+ (uid, *)
  (*                       {| key_heap := ks'; *)
  (*                          protocol := cmd'; *)
  (*                          msg_heap := qmsgs'; *)
  (*                          c_heap := mycs'; *)
  (*                          from_nons := froms'; *)
  (*                          sent_nons := sents'; *)
  (*                          cur_nonce := cur_n' |}); *)
  (*            adversary := adv'; *)
  (*            all_ciphers := cs'; *)
  (*            all_keys := gks' |} m__iw iu chid. *)
  (* Proof. *)
  (*   intros. *)
  (*   split_ors; split_ex; subst. *)

  (*   - invert H3; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; *)
  (*       destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; *)
  (*         match goal with *)
  (*         | [ ARG : ?usrs $? ?uid = Some _, *)
  (*                   IARG : IdealWorld.users _ $? ?uid = Some _, *)
  (*                          H : (forall _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] => *)
  (*           eapply H in ARG *)
  (*         end; eauto. *)

  (*     invert H; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto. *)

  (*   - invert H3; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; *)
  (*       destruct (u ==n uid); subst; clean_map_lookups; eauto; simpl; *)
  (*         match goal with *)
  (*         | [ ARG : ?usrs $? ?uid = Some _, *)
  (*                   IARG : IdealWorld.users _ $? ?uid = Some _, *)
  (*                          H : (forall _ _ _ _ _, ?usrs $? _ = Some _ -> _) |- _ ] => *)
  (*           eapply H in ARG *)
  (*         end; eauto. *)
  
  (*   - invert H3; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; *)
  (*       eauto using message_content_eq_addnl_key. *)

  (*     + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2. *)
  (*       eapply H2 in H10; eauto. *)
  (*       assert (x <> k__sign) by (invert H10; destruct (k__sign ==n x); clean_map_lookups; eauto). *)

  (*       invert H4; solve_perm_merges; eauto; simpl. *)

  (*       assert (RW: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign). *)
  (*       cases (ks $? k__sign). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       rewrite !RW. *)
  (*       eapply H13 in H; eauto. *)

  (*     + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2. *)
  (*       eapply H2 in H10; eauto. *)
  (*       assert (x <> k__sign) by (invert H10; destruct (k__sign ==n x); clean_map_lookups; eauto). *)
  (*       assert (x <> k__enc) by (invert H10; destruct (k__enc ==n x); clean_map_lookups; eauto). *)

  (*       invert H4; invert H5; solve_perm_merges; eauto; simpl. *)

  (*       assert (RW1: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign). *)
  (*       cases (ks $? k__sign). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       assert (RW2: ks $k++ ($0 $+ (x, x0)) $? k__enc = ks $? k__enc). *)
  (*       cases (ks $? k__enc). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       rewrite !RW1, !RW2. *)
  (*       eapply H13 in H; eauto. *)
  
  (*   - invert H3; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; *)
  (*       eauto using message_content_eq_addnl_key. *)

  (*     + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2. *)
  (*       eapply H2 in H11; eauto. *)
  (*       assert (x <> k__sign) by (invert H11; destruct (k__sign ==n x); clean_map_lookups; eauto). *)

  (*       invert H5; solve_perm_merges; eauto; simpl. *)

  (*       assert (RW: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign). *)
  (*       cases (ks $? k__sign). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       rewrite !RW. *)
  (*       eapply H14 in H; eauto. *)

  (*     + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2. *)
  (*       eapply H2 in H11; eauto. *)
  (*       assert (x <> k__sign) by (invert H11; destruct (k__sign ==n x); clean_map_lookups; eauto). *)
  (*       assert (x <> k__enc) by (invert H11; destruct (k__enc ==n x); clean_map_lookups; eauto). *)

  (*       invert H5; invert H6; solve_perm_merges; eauto; simpl. *)

  (*       assert (RW1: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign). *)
  (*       cases (ks $? k__sign). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       assert (RW2: ks $k++ ($0 $+ (x, x0)) $? k__enc = ks $? k__enc). *)
  (*       cases (ks $? k__enc). *)
  (*       eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto. *)
  (*       eapply merge_perms_adds_no_new_perms; eauto. *)

  (*       rewrite !RW1, !RW2. *)
  (*       eapply H14 in H; eauto. *)

  (* Qed. *)

  (* Lemma message_eq_user_add_inv : *)
  (*   forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks *)
  (*     ks cmd qmsgs mycs froms sents cur_n cmd' qmsgs' mycs' froms' sents' cur_n' *)
  (*     t (m__rw : crypto t) m__iw iu chid uid, *)

  (*     usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n) *)
  (*     -> message_eq *)
  (*         m__rw *)
  (*         {| users := *)
  (*              usrs $+ (uid, *)
  (*                       {| key_heap := ks; *)
  (*                          protocol := cmd'; *)
  (*                          msg_heap := qmsgs'; *)
  (*                          c_heap := mycs'; *)
  (*                          from_nons := froms'; *)
  (*                          sent_nons := sents'; *)
  (*                          cur_nonce := cur_n' |}); *)
  (*            adversary := adv'; *)
  (*            all_ciphers := cs; *)
  (*            all_keys := gks |} m__iw iu chid *)
  (*     -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid. *)
  (* Proof. *)
  (*   intros. *)
  
  (*   invert H0; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*     intros; *)
  (*     autorewrite with find_user_keys in *; *)
  (*     destruct (u ==n uid); subst; clean_map_lookups; eauto; *)
  (*       simpl. *)

  (*   specialize (H11 uid (mkUserData ks cmd' qmsgs' mycs' froms' sents' cur_n') data__iw). *)
  (*   rewrite add_eq_o in H11 by trivial. *)
  (*   eapply H11 in H2; eauto. *)

  (*   specialize (H11 u data__rw data__iw). *)
  (*   rewrite add_neq_o in H11 by congruence; eauto. *)

  (*   specialize (H11 uid (mkUserData ks cmd' qmsgs' mycs' froms' sents' cur_n') data__iw). *)
  (*   rewrite add_eq_o in H11 by trivial. *)
  (*   eapply H11 in H4; eauto. *)

  (*   specialize (H11 u data__rw data__iw). *)
  (*   rewrite add_neq_o in H11 by congruence; eauto. *)
  (* Qed. *)

  (* Hint Resolve message_eq_user_add message_eq_user_add_inv : core. *)


  Lemma cipher_keys_known :
    forall A (usrs : honest_users A) cs gks advk cid k__enc k__sign t (m : message t) uid seq,
      cs $? cid = Some (SigEncCipher k__sign k__enc uid seq m)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> keys_and_permissions_good gks usrs advk
      -> forall kid kp,
          findKeysMessage m $? kid = Some kp
          -> gks $? kid <> None.
  Proof.
    intros.
    unfold keys_and_permissions_good in H1; split_ex.
    assert (permission_heap_good gks (findUserKeys usrs)) by eauto.
    unfold permission_heap_good in H4.

    unfold encrypted_ciphers_ok in H0; rewrite Forall_natmap_forall in H0;
      apply H0 in H; invert H;
        intros FM.

    - apply H15 in H2; split_ex; subst; clean_map_lookups.
    - apply H16 in H2.
      apply H5 in H2; split_ex; clean_map_lookups.
  Qed.

  Lemma cipher_keys_known' :
    forall A (usrs : honest_users A) cs gks advk cid k__sign t (m : message t) uid seq,
      cs $? cid = Some (SigCipher k__sign uid seq m)
      -> findUserKeys usrs $? k__sign = Some true
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> keys_and_permissions_good gks usrs advk
      -> forall kid kp,
          findKeysMessage m $? kid = Some kp
          -> gks $? kid <> None.
  Proof.
    intros.
    unfold keys_and_permissions_good in H2; split_ex.
    assert (permission_heap_good gks (findUserKeys usrs)) by eauto.
    unfold permission_heap_good in H6.

    unfold encrypted_ciphers_ok in H1; rewrite Forall_natmap_forall in H1;
      apply H1 in H; invert H;
        eauto.

    apply H14 in H3; split_ex; subst.
    apply H6 in H; split_ex.
    unfold not; intros; clean_map_lookups.
  Qed.

  Lemma message_eq_user_add_nochange_cs_ks_msgs_inv :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks
      ks cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks |} m__iw iu chid
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid.
  Proof using All.
    intros.

    invert H0; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *; eauto;
        repeat
          match goal with
          | [ H : (forall _ _ _, _ $+ (?u,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
            specialize (H u); rewrite add_eq_o in H by trivial; specialize (H _ _ eq_refl IW)
          | [ H : (forall _ _ _, _ $+ (?u1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u2 = Some _, NE : ?u1 <> ?u2 |- _ ] =>
            specialize (H u2); rewrite add_neq_o in H by congruence; eapply H in IW; eauto
          | [ H : (forall _ _ _, _ $+ (?uid1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
            destruct (uid1 ==n u); subst; clean_map_lookups
          end;
        specialize_simply.

    all: 
      invert H11; [ econstructor 1 | econstructor 2 ]; eauto.
  Qed.

  Lemma message_eq_user_add_addnl_cipher_inv :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs cs' cid c gks
      ks cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid,

      ~ In cid cs
      -> cs' = cs $+ (cid,c)
      -> (forall cid, msg_cipher_id m__rw = Some cid -> cs $? cid <> None)
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> message_queues_ok cs usrs gks
      -> match c with
        | @SigCipher t _ _ _ m | @SigEncCipher t _ _ _ _ m => keys_mine ks (findKeysMessage m)
        end
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks;
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := cid :: mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs';
             all_keys := gks |} m__iw iu chid
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid.
  Proof.
    intros.

    invert H7; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      autorewrite with find_user_keys in *;
      specialize (H1 _ eq_refl);
      destruct (cid ==n c_id); subst; clean_map_lookups; trivial;
        intros;
        repeat
          match goal with
          | [ H : (forall _ _ _, _ $+ (?u,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
            specialize (H u); rewrite add_eq_o in H by trivial; specialize (H _ _ eq_refl IW)
          | [ H : (forall _ _ _, _ $+ (?u1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u2 = Some _, NE : ?u1 <> ?u2 |- _ ] =>
            specialize (H u2); rewrite add_neq_o in H by congruence; eapply H in IW; eauto
          | [ H : (forall _ _ _, _ $+ (?uid1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
            destruct (uid1 ==n u); subst; clean_map_lookups
          end;
        specialize_simply; eauto.


    msg_queue_prop; user_cipher_queues_prop.
    invert H18; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; clean_map_lookups.
    erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher in H15; eauto.
    erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher in H15; eauto.
    destruct c;
      rewrite key_perms_from_known_ciphers_pull_merge,
      merge_perms_sym with (ks2 := findKeysMessage msg),
                           <- merge_perms_assoc,
                           merge_keys_mine with (ks2 := findKeysMessage msg) in H15 by eauto; eauto.

    msg_queue_prop; user_cipher_queues_prop.
    invert H1; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; clean_map_lookups.
    erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher in H17; eauto.
    erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher in H17; eauto.

    msg_queue_prop; user_cipher_queues_prop.
    invert H18; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; clean_map_lookups;
      erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher in * by eauto;
      erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher in * by eauto;
      destruct c;
      rewrite key_perms_from_known_ciphers_pull_merge,
      merge_perms_sym with (ks2 := findKeysMessage msg),
                           <- merge_perms_assoc,
                           merge_keys_mine with (ks2 := findKeysMessage msg) in * by eauto; eauto.

    msg_queue_prop; user_cipher_queues_prop.
    invert H1; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; clean_map_lookups;
      erewrite <- key_perms_from_message_queue_idempotent_addnl_cipher in * by eauto;
      erewrite <- key_perms_from_known_ciphers_idempotent_addnl_cipher in * by eauto;
      eauto.
  Qed.

  (* Lemma message_eq_user_add_addnl_key_inv : *)
  (*   forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks gks' *)
  (*     ks ks' kid k cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n' *)
  (*     t (m__rw : crypto t) m__iw iu chid uid, *)

  (*     ~ In kid gks *)
  (*     -> ks' = add_key_perm kid true ks *)
  (*     -> gks' = gks $+ (kid,k) *)
  (*     -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n) *)
  (*     -> encrypted_ciphers_ok (findUserKeys usrs) cs gks *)
  (*     -> keys_and_permissions_good gks usrs adv.(key_heap) *)
  (*     -> message_queues_ok cs usrs gks *)
  (*     -> message_eq *)
  (*         m__rw *)
  (*         {| users := *)
  (*              usrs $+ (uid, *)
  (*                       {| key_heap := ks'; *)
  (*                          protocol := cmd'; *)
  (*                          msg_heap := qmsgs; *)
  (*                          c_heap := mycs; *)
  (*                          from_nons := froms; *)
  (*                          sent_nons := sents'; *)
  (*                          cur_nonce := cur_n' |}); *)
  (*            adversary := adv'; *)
  (*            all_ciphers := cs; *)
  (*            all_keys := gks' |} m__iw iu chid *)
  (*     -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid. *)
  (* Proof. *)
  (*   intros; subst. *)
  
  (*   invert H6; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto; *)
  (*     autorewrite with find_user_keys in *. *)
  (*   eapply message_content_eq_addnl_key_inv; eauto. *)
  (*   encrypted_ciphers_prop; eauto. *)
  (*   admit. *)

  (* Admitted. *)

  Lemma message_eq_user_decrypt_msg_inv :
    forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks
      ks ks' cmd qmsgs mycs froms sents cur_n cmd' sents' cur_n'
      t (m__rw : crypto t) m__iw iu chid uid cid k__s k__e uid' mseq t__m (msg : message t__m),

      cs $? cid = Some (SigEncCipher k__s k__e uid' mseq msg)
      -> List.In cid mycs
      -> ks' = ks $k++ findKeysMessage msg
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> message_eq
          m__rw
          {| users :=
               usrs $+ (uid,
                        {| key_heap := ks';
                           protocol := cmd';
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents';
                           cur_nonce := cur_n' |});
             adversary := adv';
             all_ciphers := cs;
             all_keys := gks |} m__iw iu chid
      -> message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid.
  Proof.
    intros.

    invert H5; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto;
      autorewrite with find_user_keys in *;
      (* destruct (cid ==n c_id); subst; clean_map_lookups; trivial; *)
      intros;
      repeat
        match goal with
        | [ H : (forall _ _ _, _ $+ (?u,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
          specialize (H u); rewrite add_eq_o in H by trivial; specialize (H _ _ eq_refl IW)
        | [ H : (forall _ _ _, _ $+ (?u1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u2 = Some _, NE : ?u1 <> ?u2 |- _ ] =>
          specialize (H u2); rewrite add_neq_o in H by congruence; eapply H in IW; eauto
        | [ H : (forall _ _ _, _ $+ (?uid1,_) $? _ = Some _ -> _), IW : IdealWorld.users _ $? ?u = Some _ |- _ ] =>
          destruct (uid1 ==n u); subst; clean_map_lookups
        | [ HK : honest_key ?honk ?k, H : honest_key (?honk $k++ ?newk) ?k -> _ |- _ ] =>
          assert (honest_key (honk $k++ newk) k) by eauto using honest_key_after_new_keys; specialize_simply
        end; eauto using honest_key_after_new_keys.

    clear H13; user_cipher_queues_prop; encrypted_ciphers_prop;
      rewrite honestk_merge_new_msgs_keys_dec_same with (honestk := findUserKeys usrs) in * by eauto.
    eapply ch_keys_from_cipher_inv with (c_id' := cid); simpl; eauto.


    clear H1 H13; user_cipher_queues_prop; encrypted_ciphers_prop;
      rewrite honestk_merge_new_msgs_keys_dec_same with (honestk := findUserKeys usrs) in * by eauto; eauto.

    clear H13; user_cipher_queues_prop; encrypted_ciphers_prop;
      rewrite honestk_merge_new_msgs_keys_dec_same with (honestk := findUserKeys usrs) in * by eauto.
    eapply ch_keys_from_cipher_inv with (c_id' := cid); simpl; eauto.
    
    clear H1 H13; user_cipher_queues_prop; encrypted_ciphers_prop;
      rewrite honestk_merge_new_msgs_keys_dec_same with (honestk := findUserKeys usrs) in * by eauto; eauto.
  Qed.


End MessageEqLemmas.

Section Lameness.
    Lemma adversary_remains_lame_user_step :
    forall {A B} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd (Base A))
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' b,

      lameAdv b adv
      -> step_user lbl (Some u_id)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lameAdv b adv'.
  Proof.
    unfold lameAdv; intros; simpl in *.

    - destruct lbl.
      + eapply honest_silent_step_nochange_adversaries in H0; eauto.
        subst; eauto.
      + eapply honest_labeled_step_nochange_adversary_protocol in H0; eauto.
        rewrite <- H0; auto.
  Qed.

  Lemma adversary_remains_lame :
    forall A B (U U' : universe A B) b lbl,
      lameAdv b U.(adversary)
      -> step_universe U lbl U'
      -> lameAdv b U'.(adversary).
  Proof.
    inversion 2; subst; simpl in *; subst; 
      unfold build_data_step, buildUniverse, buildUniverseAdv in *; simpl in *;
        eauto using adversary_remains_lame_user_step.

    dismiss_adv.
  Qed.

  Lemma adversary_remains_lame_step :
    forall t__hon t__adv st st' b,
      lameAdv b (fst st).(adversary)
      -> (@step t__hon t__adv) st st'
      -> lameAdv b (fst st').(adversary).
  Proof.
    invert 2; simpl in *; eauto using adversary_remains_lame.
  Qed.

End Lameness.

Section OtherUserStep.
  Hint Constructors step_user : core.

  Lemma impact_from_other_user_step :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
                
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
          u_id1 u_id2 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C),
        
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> suid1 = Some u_id1
        -> u_id1 <> u_id2
        -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
            usrs $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists m,
              usrs' $? u_id2 = Some (mkUserData ks2 cmd2 (qmsgs2 ++ m) mycs2 froms2 sents2 cur_n2).
  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end;
      clean_map_lookups;
      try solve [ exists []; rewrite app_nil_r; trivial ];
      eauto.

    destruct (rec_u_id ==n u_id2); subst; clean_map_lookups;
      repeat simple apply conj; trivial; eauto.
    exists []; rewrite app_nil_r; trivial.
  Qed.

  Lemma step_addnl_msgs :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
                
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
          u_id1 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C) ms,
        
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> suid1 = Some u_id1
        -> step_user lbl suid1
                    (usrs, adv, cs, gks, ks, qmsgs ++ ms, mycs, froms, sents, cur_n, cmd)
                    (usrs', adv', cs', gks', ks', qmsgs' ++ ms, mycs', froms', sents', cur_n', cmd').

  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end;
      clean_map_lookups;
      eauto.

    rewrite <- app_comm_cons; eauto.
    rewrite <- app_comm_cons; eauto.
    econstructor; eauto.
    congruence.
  Qed.
End OtherUserStep.
