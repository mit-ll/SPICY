(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Classical
     Permutation
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

From SPICY Require Import
     MyPrelude
     Maps
     Messages
     MessageEq
     Common
     Keys
     Automation
     Tactics
     RealWorld
     AdversaryUniverse
     Simulation

     Theory.CipherTheory
.

Set Implicit Arguments.

Ltac count_occ_list_in1 :=
  match goal with
  | [ H : ~ List.In ?x ?xs |- context [ count_occ _ ?xs ?x ] ] => rewrite count_occ_not_In in H; rewrite H
  | [ H : count_occ _ ?xs ?x = 0 |- context [ ~ List.In ?x ?xs ] ] => rewrite count_occ_not_In
  end.

Lemma accepted_safe_msg_pattern_msg_filter_true :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to froms pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to froms pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true
    /\ RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros.
  destruct msg;
    repeat match goal with
           | [ H : RealWorld.msg_pattern_safe _ _ |- _] => invert H
           | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _] => invert H
           end;
    unfold RealWorld.msg_honestly_signed, RealWorld.msg_to_this_user;
    simpl; context_map_rewrites; unfold RealWorld.cipher_to_user;
      destruct (msg_to0 ==n msg_to0); subst; try contradiction;
      rewrite <- honest_key_honest_keyb; auto.
Qed.

Lemma accepted_safe_msg_pattern_honestly_signed :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to froms pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to froms pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Lemma accepted_safe_msg_pattern_to_this_user :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to froms pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to froms pat msg
    -> RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Lemma accepted_safe_msg_pattern_replay_safe :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to froms pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to froms pat msg
    -> exists c_id c, msg = SignedCiphertext c_id
              /\ cs $? c_id = Some c
              /\ ~ List.In (cipher_nonce c) froms.
Proof.
  intros.
  destruct msg;
    repeat match goal with
           | [ H : RealWorld.msg_pattern_safe _ _ |- _] => invert H
           | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _] => invert H
           | [ H : count_occ _ _ _ = 0 |- _] => rewrite <- count_occ_not_In in H
           end; eauto.
Qed.

Hint Resolve
     accepted_safe_msg_pattern_honestly_signed
     accepted_safe_msg_pattern_to_this_user
     accepted_safe_msg_pattern_replay_safe
  : core.

Section CleanMessages.

  Lemma msg_honestly_signed_after_without_cleaning :
    forall {t} (msg : crypto t) honestk honestk' cs,
      msg_honestly_signed honestk' (clean_ciphers honestk cs) msg = true
      -> (forall kid, honestk' $? kid = Some true -> honestk $? kid = Some true)
      -> msg_honestly_signed honestk cs msg = true.
  Proof.
    intros.
    unfold msg_honestly_signed in *.
    cases (msg_signing_key (clean_ciphers honestk cs) msg); try discriminate.
    unfold msg_signing_key in *; destruct msg; try discriminate.
    - cases (clean_ciphers honestk cs $? c_id); try discriminate.
      rewrite <- find_mapsto_iff in Heq0;
        rewrite clean_ciphers_mapsto_iff in Heq0;
        rewrite find_mapsto_iff in Heq0; split_ex.
      context_map_rewrites.
      invert Heq.
      unfold honest_keyb in *.
      cases (honestk' $? cipher_signing_key c); try discriminate.
      destruct b; try discriminate.
      eapply H0 in Heq; context_map_rewrites; eauto.
  Qed.

  Lemma honest_cipher_filter_fn_true_honest_signing_key :
    forall honestk c_id c k,
      cipher_signing_key c = k
      -> honest_key honestk k
      -> honest_cipher_filter_fn honestk c_id c = true.
  Proof.
    intros.
    unfold honest_cipher_filter_fn, cipher_honestly_signed, cipher_signing_key in *;
      subst;
      destruct c; rewrite <- honest_key_honest_keyb; eauto.
  Qed.
  
  Hint Resolve honest_cipher_filter_fn_true_honest_signing_key : core.

  Lemma msg_honestly_signed_before_after_cleaning :
    forall {t} (msg : crypto t) honestk cs,
      msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed honestk (clean_ciphers honestk cs) msg = true.
  Proof.
    intros.
    unfold msg_honestly_signed in *.
    cases (msg_signing_key cs msg); try discriminate.
    unfold msg_signing_key in *; destruct msg; try discriminate.
    - cases (cs $? c_id); try discriminate.
      erewrite clean_ciphers_keeps_honest_cipher; clean_context; eauto.
      unfold honest_cipher_filter_fn, cipher_honestly_signed; destruct c; eauto.
  Qed.

  Lemma msg_honestly_signed_before_after_cleaning' :
    forall {t} (msg : crypto t) honestk honestk' cs,
      msg_honestly_signed honestk cs msg = true
      -> (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> msg_honestly_signed honestk' (clean_ciphers honestk cs) msg = true.
  Proof.
    intros.
    assert (msg_honestly_signed honestk (clean_ciphers honestk cs) msg = true ) by eauto using msg_honestly_signed_before_after_cleaning.
    unfold msg_honestly_signed in *; cases (msg_signing_key (clean_ciphers honestk cs) msg); eauto.
    unfold honest_keyb in *.
    cases (honestk $? k); clean_map_lookups; destruct b; try discriminate.
    specialize (H0 _ Heq0); context_map_rewrites; trivial.
  Qed.

  Lemma msg_to_this_user_before_after_cleaning :
    forall {t} (msg : crypto t) honestk cs msg_to,
      msg_honestly_signed honestk cs msg = true
      -> msg_to_this_user cs msg_to msg = true
      -> msg_to_this_user (clean_ciphers honestk cs) msg_to msg = true.
  Proof.
    intros.
    unfold msg_honestly_signed, msg_to_this_user in *.
    cases (msg_signing_key cs msg); try discriminate.
    cases (msg_destination_user cs msg); try discriminate.
    destruct msg_to; [destruct (u ==n u0); try discriminate; subst |];
      unfold msg_signing_key, msg_destination_user in *; destruct msg; try discriminate;
        cases (cs $? c_id); try discriminate; clean_context;
          erewrite clean_ciphers_keeps_honest_cipher; clean_context; eauto;
      destruct (cipher_to_user c ==n cipher_to_user c); try contradiction; trivial;
      unfold honest_cipher_filter_fn, cipher_honestly_signed; destruct c; eauto.
  Qed.

  Lemma msg_to_this_user_false_before_after_cleaning :
    forall {t} (msg : crypto t) honestk cs msg_to,
      msg_honestly_signed honestk cs msg = true
      -> msg_to_this_user cs msg_to msg = false
      -> msg_to_this_user (clean_ciphers honestk cs) msg_to msg = false.
  Proof.
    intros.
    unfold msg_honestly_signed, msg_to_this_user in *.
    unfold msg_signing_key in *; destruct msg; try discriminate.
    cases (cs $? c_id); try discriminate.
    unfold msg_destination_user in *; context_map_rewrites.
    apply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq.
    - rewrite Heq; eauto.
    - unfold honest_cipher_filter_fn, cipher_honestly_signed; destruct c; auto.
  Qed.

  Hint Resolve
       msg_to_this_user_before_after_cleaning
       msg_honestly_signed_after_without_cleaning
       msg_honestly_signed_before_after_cleaning
       msg_honestly_signed_before_after_cleaning'
    : core.

  Lemma message_not_replayed_addnl_destruct :
    forall {t1 t2} (msg1 : crypto t1) (msg2 : crypto t2) to_usr cs froms msgs,
      msg_not_replayed to_usr cs froms msg1 (existT _ _ msg2 :: msgs)
      -> msg_not_replayed to_usr cs froms msg1 msgs.
  Proof.
    intros.
    unfold msg_not_replayed in *; intros; split_ex; split_ands; subst; eauto.
    invert H2; eauto 8.
  Qed.

  Hint Resolve message_not_replayed_addnl_destruct : core.

  Lemma fold_msg_filter :
    forall honestk cs to_usr sigM acc,
      match sigM with
      | existT _ _ msg =>
        if msg_honestly_signed honestk cs msg && msg_to_this_user cs to_usr msg
        then match msg_nonce_ok cs (snd acc) msg with
             | None => acc
             | Some froms => (fst acc ++ [sigM], froms)
             end
        else acc
      end = msg_filter honestk cs to_usr acc sigM.
  Proof.  unfold msg_filter; trivial. Qed.

  Lemma fold_clean_messages1' :
    forall honestk cs to_usr froms msgs0 msgs,
      List.fold_left (fun acc sigM =>
                         match sigM with
                         | existT _ _ msg =>
                           if msg_signed_addressed honestk cs to_usr msg
                           then match msg_nonce_ok cs (snd acc) msg with
                                | None => acc
                                | Some froms => (fst acc ++ [sigM], froms)
                                end
                           else acc
                         end) msgs (msgs0, froms)
      = clean_messages' honestk cs to_usr froms msgs0 msgs.
  Proof. unfold clean_messages' , msg_filter; trivial. Qed.

  Lemma fold_clean_messages2' :
    forall honestk cs to_usr froms msgs0 msgs,
      List.fold_left (msg_filter honestk cs to_usr) msgs (msgs0, froms)
      = clean_messages' honestk cs to_usr froms msgs0 msgs.
  Proof. unfold clean_messages'; trivial. Qed.

  Lemma fold_clean_messages :
    forall honestk cs to_usr froms msgs,
      fst (clean_messages' honestk cs to_usr froms [] msgs)
      = clean_messages honestk cs to_usr froms msgs.
  Proof.
    unfold clean_messages; trivial. Qed.

  Ltac message_cleaning :=
    repeat
      match goal with
      | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] => apply andb_prop in H; split_ands
      | [ MHS : msg_honestly_signed _ _ _ = true, MNOK : msg_nonce_ok _ _ _ = _ |- _ ] =>
        unfold msg_nonce_ok, msg_honestly_signed in MHS, MNOK
      | [ H : match ?c with | Content _ => _ | _ => _ end = _ |- _ ] => destruct c; try discriminate
      | [ H : match ?cs $? ?cid with _ => _ end = _ |- _ ] => cases (cs $? cid); try discriminate
      | [ IH : forall kid froms _ froms_non _, froms $? kid = Some froms_non
        , H : _ $? _ = Some _ |- _ ] => specialize (IH _ _ _ _ _ H)
      | [ IH : forall froms acc, snd (fold_left _ ?msgs (acc,froms)) $? ?kid = ?ans -> _
         , H : snd (fold_left _ ?msgs ?arg) $? ?kid = ?ans
           |- _ ] =>
        match arg with
        | (_,_) => specialize (IH _ _ H); split_ands
        | if ?ifarg then _ else _ => cases ifarg
        | match ?matcharg with _ => _ end => cases matcharg
        end
      | [ H : (if ?n1 <=? ?n2 then _ else _) = _ |- _ ] => cases (n1 <=? n2); try discriminate
      | [ H : _ $+ (?kid1,_) $? ?kid2 = None |- _ ] => destruct (kid1 ==n kid2); subst; clean_map_lookups
      | [ H : msg_signing_key _ _ = _ |- _ ] => unfold msg_signing_key in H
      | [ H : msg_signed_addressed _ _ _ _ = _ |- _ ] => unfold msg_signed_addressed in H
      | [ H : ?arg && _ = _, ARG : ?arg = _ |- _ ] => rewrite ARG in H; simpl in H
      | [ H : _ && ?arg = _, ARG : ?arg = _ |- _ ] => rewrite ARG in H; simpl in H
      | [ H1 : ?op = ?res1, H2 : ?op = ?res2 |- _ ] => rewrite H1 in H2; discriminate
      end
    || (progress clean_context)
    || (repeat
         match goal with
         | [ |- _ /\ _ ] => split
         | [ |- Forall _ (?x :: ?xs) ] => econstructor
         | [ |- _ -> _ ] => intros
         | [ |- _ <> _ ] => unfold not; intros
         end); simpl; eauto; contra_map_lookup.

  Ltac map_lkup_ok :=
    repeat
      match goal with
      | [ |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => progress clean_map_lookups
      | [ RW : ?lkup = ?k1 |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => rewrite <- RW in *; clean_map_lookups
      | [ RW : ?k1 = ?lkup |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => rewrite RW in *; clean_map_lookups
      | [ RW : ?k1 <> ?lkup |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => clean_map_lookups
      | [ RW : ?lkup <> ?k1 |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => clean_map_lookups
      | [ |- context [ _ $+ (?k1,_) $? ?lkup = _ ]] => idtac "newone" k1 lkup; destruct (k1 ==n lkup)
      end; trivial.
  
  Lemma msg_nonce_ok_inv :
    forall {t} (msg : crypto t) cs froms r,
      msg_nonce_ok cs froms msg = r
      -> r = Some froms
      \/ r = None
      \/ exists c_id c,
          msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ count_occ msg_seq_eq froms (cipher_nonce c) = 0
        /\ r = Some (cipher_nonce c :: froms).
  Proof.
    unfold msg_nonce_ok; intros.
    destruct msg; eauto.
    cases (cs $? c_id); eauto.
    cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto.
    subst; eauto 9.
  Qed.

  Lemma count_occ_gt_0_clean_msgs :
    forall honestk cs to_usr msgs froms acc c n,
      count_occ msg_seq_eq (snd (clean_messages' honestk cs to_usr froms acc msgs)) (cipher_nonce c) = S n
      -> (exists n__init, count_occ msg_seq_eq froms (cipher_nonce c) = S n__init)
      \/ Exists (fun sigM => match sigM with (existT _ _ m) => msg_honestly_signed honestk cs m = true
                                                        /\ msg_nonce_same c cs m end) msgs.
  Proof.
    unfold clean_messages'; induction msgs; simpl; intros; try count_occ_list_in1; eauto.
    unfold msg_filter at 2 in H; destruct a.
    repeat (simpl in *; eauto;
      clean_map_lookups1 ||
      match goal with
      | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
      | [ H : context [ if ?cond then _ else _ ] |- _ ] => cases cond
      | [ H : context [ msg_nonce_ok ?cs ?froms ?c ] |- _ ] =>
        assert (exists r, msg_nonce_ok cs froms c = r) as MNOK by eauto;
          destruct MNOK as [r MNOK];
          rewrite MNOK in H;
          apply msg_nonce_ok_inv in MNOK;
            split_ors; split_ex; split_ands; subst
      | [ H : context [ if msg_seq_eq ?cn1 ?cn2 then _ else _ ] |- _ ] => destruct (msg_seq_eq cn1 cn2)
      | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] =>
        unfold msg_signed_addressed in H; rewrite andb_true_iff in H; split_ands
      | [ IH : forall _ _ c n, count_occ _ _ (cipher_nonce c) = S n -> _, H : count_occ _ _ (cipher_nonce _) = S _ |- _ ] =>
        specialize (IH _ _ _ _ H); (solve [ intuition eauto ] || split_ors; split_ex)
      | [ H : msg_honestly_signed _ _ (SignedCiphertext ?cid) = true |- context [ Exists _ ((existT _ _ (SignedCiphertext ?cid)) :: _) ]] =>
        rewrite Exists_exists; right; eexists; simpl; split
      | [ |- context [ let (_,_) := _ in _]  ] => simpl
      | [ |- _ /\ _ ] => split
      | [ |- msg_nonce_same _ _ _ ] => unfold msg_nonce_same; intros
      end).
  Qed.


  Lemma count_occ_eq_0_clean_msgs :
    forall honestk cs to_usr msgs froms acc c,
      count_occ msg_seq_eq (snd (clean_messages' honestk cs to_usr froms acc msgs)) (cipher_nonce c) = 0
      -> ~ List.In (cipher_nonce c) froms
      /\ Forall (fun sigM => match sigM with (existT _ _ m) => msg_signed_addressed honestk cs to_usr m = true -> msg_nonce_not_same c cs m end) msgs.
  Proof.
    unfold clean_messages'; induction msgs; simpl; intros; try count_occ_list_in1; eauto.
    unfold msg_filter at 2 in H; destruct a.
    repeat
      match goal with
      | [ H : context [ if ?cond then _ else _ ] |- _ ] => cases cond
      (* | [ H : context [ msg_nonce_ok ?cs ?froms ?c ] |- _ ] => *)
      (*   assert (exists r, msg_nonce_ok cs froms c = r) as MNOK by eauto; *)
      (*     destruct MNOK as [r MNOK]; *)
      (*     rewrite MNOK in H; *)
      (*     apply msg_nonce_ok_inv in MNOK; *)
      (*       split_ors; split_ex; split_ands; subst *)
      (* | [ IH : forall _ _ c, count_occ _ _ (cipher_nonce c) = 0 -> _, H : count_occ _ _ (cipher_nonce _) = 0 |- _ ] => *)
      (*   specialize (IH _ _ _ H); (solve [ intuition eauto ] || split_ands) *)
      end; simpl in *; eauto.


    - unfold msg_nonce_ok in H.
      unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in Heq;
        rewrite andb_true_iff in Heq; split_ands.
      destruct c0; try discriminate.
      cases (cs $? c_id); try discriminate.
      cases (count_occ msg_seq_eq froms (cipher_nonce c0)); eauto;
        generalize (IHmsgs _ _ _ H); intros; split_ands; split; eauto.
      + unfold not; intros; simpl in *.
        apply Decidable.not_or in H2; split_ands.
        econstructor; eauto; intros.
        unfold msg_nonce_not_same; intros.
        invert H6; clean_map_lookups.
        unfold not; intros; eauto.
        
      + econstructor; eauto; intros.
        unfold msg_nonce_not_same; intros.
        invert H5; clean_map_lookups.

        destruct (msg_seq_eq (cipher_nonce c) (cipher_nonce c1)); eauto.
        exfalso.
        rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H2.
        rewrite e in H2.
        rewrite Heq0 in H2; discriminate.

    - specialize (IHmsgs _ _ _ H); intuition eauto.
      econstructor; eauto; intros.
      rewrite Heq in H2; discriminate.
  Qed.

  Lemma msg_nonce_same_after_cleaning :
    forall {t} (msg : crypto t) c cs honestk,
      msg_nonce_same c cs msg 
      -> msg_signed_addressed honestk cs (Some (cipher_to_user c)) msg = true
      -> msg_nonce_same c (clean_ciphers honestk cs) msg.
  Proof.
    unfold msg_nonce_same; intros.
    subst.
    rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H2;
      split_ands; eauto.
  Qed.

  Hint Resolve msg_nonce_same_after_cleaning : core.

  Lemma msg_nonce_same_not_same_contra :
    forall {t} (msg : crypto t) honestk cs c,
        msg_honestly_signed honestk cs msg = true
      -> msg_nonce_same c cs msg
      -> msg_nonce_not_same c cs msg
      -> False.
  Proof.
    unfold msg_nonce_same, msg_nonce_not_same; intros.
    unfold msg_honestly_signed, msg_signing_key in *.
    destruct msg; try discriminate.
    cases (cs $? c_id); try discriminate.
    assert (cipher_nonce c = cipher_nonce c0) by eauto.
    assert (cipher_nonce c <> cipher_nonce c0) by eauto.
    contradiction.
  Qed.

  Hint Resolve msg_nonce_same_not_same_contra : core.

  Ltac process_clean_messages :=
    repeat (
        clean_map_lookups1 ||
        match goal with
        | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
        | [ H : ~ List.In ?x ?xs |- context [ count_occ _ ?xs ?x ] ] => rewrite count_occ_not_In in H; rewrite H
        | [ H : ~ List.In ?x ?xs |- _ ] => rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H
        | [ H : Forall _ (_ :: _) |- _ ] => invert H
        | [ H : msg_not_replayed _ _ _ _ (_ :: _) |- _ ] => unfold msg_not_replayed in H; split_ex; split_ands
        | [ |- context [ count_occ msg_seq_eq ?froms ?cn ] ] => cases (count_occ msg_seq_eq froms cn)
        | [ |- context [ ?msgs = ?msgs ++ _ ] ] => exfalso
        | [ H : count_occ _ (_ :: _) _ = _ |- _ ] =>
          (rewrite count_occ_cons_eq in H by equality)
          || (rewrite count_occ_cons_neq in H by equality)
        | [ H : count_occ msg_seq_eq ?froms ?cn = S _ |- _ ] => apply count_occ_gt_0_clean_msgs in H; split_ors; split_ex
        | [ H1 : count_occ ?deq ?froms ?cn = S _, H2 : count_occ ?deq ?froms ?cn = 0 |- False ] =>
          rewrite H1 in H2; invert H2
        | [ CS : ?cs $? ?cid = Some ?c
          , H : msg_nonce_not_same ?x ?cs (SignedCiphertext ?cid) |- _ ] =>
          match goal with
          | [ H : cipher_nonce x <> cipher_nonce c |- _ ] => fail 1
          | _ => assert (cipher_nonce x <> cipher_nonce c) by (eapply H; eauto 2)
          end
        | [ FA : Forall _ ?xs, IN : List.In _ ?xs |- _ ] => rewrite Forall_forall in FA; generalize (FA _ IN); clear IN; rewrite <- Forall_forall in FA
        | [ EX : Exists _ _ |- _ ] => rewrite Exists_exists in EX
        | [ H : let (_,_) := ?x in _ |- _ ] => progress (simpl in H) || destruct x
        end; split_ex; split_ands; eauto 2).

  Lemma clean_messages_drops_msg_signed_addressed_false :
    forall {t} (msg : crypto t) msgs honestk to_usr froms cs,
        msg_signed_addressed honestk cs to_usr msg = false
        -> clean_messages honestk cs to_usr froms (msgs ++ [existT _ _ msg])
          = clean_messages honestk cs to_usr froms msgs.
  Proof.
    unfold clean_messages, clean_messages';
      induction msgs; intros; intros; simpl; eauto.
    - rewrite H; trivial.
    - rewrite fold_left_app; simpl.
      rewrite H; trivial.
  Qed.

  Lemma clean_messages'_fst :
    forall honestk cs msg_to msgs msg acc froms,
      exists fltrd,
        fst (clean_messages' honestk cs msg_to froms (msg :: acc) msgs) = msg :: fltrd.
  Proof.
    induction msgs; unfold clean_messages'; intros; simpl; eauto.
    unfold msg_filter at 2.
    destruct a; simpl.

    destruct (msg_signed_addressed honestk cs msg_to c); eauto.
    cases (msg_nonce_ok cs froms c); eauto.
  Qed.

  Lemma clean_messages'_fst_pull :
    forall honestk cs msg_to msgs a acc froms,
      fst (clean_messages' honestk cs msg_to froms (a::acc) msgs) =
      a :: fst (clean_messages' honestk cs msg_to froms acc msgs).
  Proof.
    induction msgs; unfold clean_messages'; intros; simpl; eauto.
    unfold msg_filter at 2 4; destruct a; simpl.
    destruct (msg_signed_addressed honestk cs msg_to c); eauto.
    cases (msg_nonce_ok cs froms c); eauto.
  Qed.

  Lemma honest_cipher_signing_key_cipher_filter_fn_true :
    forall honestk cs c_id c,
      honest_keyb honestk (cipher_signing_key c) = true
      -> cs $? c_id = Some c
      -> honest_cipher_filter_fn honestk c_id c = true.
  Proof.
    unfold honest_cipher_filter_fn, cipher_honestly_signed, cipher_signing_key;
      intros; destruct c; eauto.
  Qed.

  Hint Resolve honest_cipher_signing_key_cipher_filter_fn_true : core.

  Lemma msg_signed_addressed_true_after_cipher_cleaning :
    forall {t} honestk honestk' cs msg_to (msg : crypto t),
      (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> msg_signed_addressed honestk cs msg_to msg = true
      -> msg_signed_addressed honestk' (clean_ciphers honestk cs) msg_to msg = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands.
    unfold msg_honestly_signed, msg_to_this_user, msg_signing_key, msg_destination_user in *;
      simpl in *; destruct msg; try discriminate;
        cases (cs $? c_id); try discriminate.

    erewrite clean_ciphers_keeps_honest_cipher; eauto.
    unfold honest_keyb in *; intuition eauto.
    cases (honestk $? cipher_signing_key c); try discriminate; destruct b; try discriminate.
    specialize (H _ Heq0); context_map_rewrites; trivial.
  Qed.

  Lemma msg_nonce_ok_after_cipher_cleaning :
    forall {t} honestk cs froms msg_to r (msg : crypto t),
        msg_signed_addressed honestk cs msg_to msg = true
      -> msg_nonce_ok cs froms msg = r
      -> msg_nonce_ok (clean_ciphers honestk cs) froms msg = r.
  Proof.
    unfold msg_nonce_ok, msg_signed_addressed; intros.
    rewrite andb_true_iff in H; split_ands.
    unfold msg_honestly_signed, msg_signing_key in *.
    destruct msg; eauto.
    cases (cs $? c_id); try discriminate.
    erewrite clean_ciphers_keeps_honest_cipher; eauto.
  Qed.


  Hint Resolve
       msg_signed_addressed_true_after_cipher_cleaning
       msg_nonce_ok_after_cipher_cleaning
    : core.

  Lemma clean_messages_idempotent' :
    forall msgs honestk honestk' cs msg_to acc froms,
      (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> fst (clean_messages' honestk' (clean_ciphers honestk cs) msg_to froms acc
                        (fst (clean_messages' honestk cs msg_to froms [] msgs)))
        = fst (clean_messages' honestk cs msg_to froms acc msgs).
  Proof.
    induction msgs; intros; simpl; eauto.

    unfold clean_messages' at 2 3; simpl.
    unfold msg_filter at 2 4.
    destruct a; simpl.

    destruct (msg_signed_addressed honestk cs msg_to c) eqn:SGN; eauto.
    cases (msg_nonce_ok cs froms c); eauto.
    rewrite !fold_clean_messages2'.
    rewrite clean_messages'_fst_pull; simpl.
    unfold clean_messages' at 1. simpl.
    rewrite msg_signed_addressed_true_after_cipher_cleaning; eauto.
    erewrite msg_nonce_ok_after_cipher_cleaning; eauto.
    simpl.
    rewrite !fold_clean_messages2'; eauto.
  Qed.


  Lemma clean_messages_idempotent :
    forall msgs honestk honestk' cs msg_to froms,
      (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> clean_messages honestk cs msg_to froms msgs =
        clean_messages honestk' (clean_ciphers honestk cs) msg_to froms ((clean_messages honestk cs msg_to froms msgs)).
  Proof.
    intros; unfold clean_messages.
    rewrite clean_messages_idempotent'; eauto.
  Qed.

  Lemma list_in_msgs_list_in_cleaned_msgs_not_in_froms' :
    forall {t} (msg : crypto t) c qmsgs1 qmsgs2 qmsgs honestk honestk' froms cs,
        qmsgs = qmsgs1 ++ (existT _ _ msg) :: qmsgs2
      -> (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> msg_signed_addressed honestk cs (Some (cipher_to_user c)) msg = true
      -> msg_nonce_same c cs msg
      -> honest_key honestk (cipher_signing_key c)
      -> ~ List.In (cipher_nonce c) froms
      -> exists t' (msg' : crypto t'),
          List.In (existT _ _ msg') (clean_messages honestk cs (Some (cipher_to_user c)) froms qmsgs)
          /\ msg_signed_addressed honestk' (clean_ciphers honestk cs) (Some (cipher_to_user c)) msg' = true
          /\ msg_nonce_same c (clean_ciphers honestk cs) msg'.
  Proof.
    unfold clean_messages, clean_messages'; induction qmsgs1; intros; eauto.
    - rewrite app_nil_l in H; subst; simpl.
      rewrite H1.
      unfold msg_nonce_ok.
      generalize H1;  intros MSA.
      unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in MSA;
        rewrite andb_true_iff in MSA; split_ands.
      destruct msg; try discriminate.
      cases (cs $? c_id); try discriminate.
      generalize H2; intros MNS.
      unfold msg_nonce_same in MNS.
      assert (cipher_nonce c = cipher_nonce c0) as RW by eauto.
      rewrite RW, count_occ_not_In with (eq_dec := msg_seq_eq) in H4.
      rewrite H4.
      rewrite fold_clean_messages2', clean_messages'_fst_pull.
      do 2 eexists.
      split.
      apply in_eq.
      eauto.

    - subst.
      simpl.
      unfold msg_filter at 2; destruct a.
      cases (msg_signed_addressed honestk cs (Some (cipher_to_user c)) c0); eauto.
      simpl.

      unfold msg_nonce_ok.
      generalize Heq; intro MSA.
      unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in MSA;
        rewrite andb_true_iff in MSA; split_ands.
      destruct c0; try discriminate.
      cases (cs $? c_id); try discriminate.
      cases (count_occ msg_seq_eq froms (cipher_nonce c0)); eauto.
      rewrite fold_clean_messages2', clean_messages'_fst_pull.
      destruct (msg_seq_eq (cipher_nonce c0) (cipher_nonce c)).
      + do 2 eexists.
        split.
        apply in_eq.
        split; eauto.
        unfold msg_nonce_same; intros.
        invert H6; eauto.
        eapply clean_ciphers_keeps_honest_cipher in Heq0; eauto; clean_map_lookups; eauto.

      + assert (~ List.In (cipher_nonce c) (cipher_nonce c0 :: froms)) as NLIN.
        intros NLIN; simpl in NLIN; split_ors; try contradiction.
        remember (qmsgs1 ++ existT crypto t0 msg :: qmsgs2) as qmsgs.
        specialize (IHqmsgs1 _ _ _ _ _ _ Heqqmsgs H0 H1 H2 H3 NLIN).
        split_ex.
        rewrite fold_clean_messages2' in H6; eauto.
        do 2 eexists; split.
        apply in_cons; eauto.
        eauto.

  Qed.

  Lemma list_in_msgs_list_in_cleaned_msgs_not_in_froms :
    forall {t} (msg : crypto t) c qmsgs honestk honestk' froms cs,
      List.In (existT _ _ msg) qmsgs
      -> (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> msg_signed_addressed honestk cs (Some (cipher_to_user c)) msg = true
      -> msg_nonce_same c cs msg
      -> honest_key honestk (cipher_signing_key c)
      -> ~ List.In (cipher_nonce c) froms
      -> exists t' (msg' : crypto t'),
          List.In (existT _ _ msg') (clean_messages honestk cs (Some (cipher_to_user c)) froms qmsgs)
          /\ msg_signed_addressed honestk' (clean_ciphers honestk cs) (Some (cipher_to_user c)) msg' = true
          /\ msg_nonce_same c (clean_ciphers honestk cs) msg'.
  Proof.
    intros.
    apply in_split in H; split_ex.
    eapply list_in_msgs_list_in_cleaned_msgs_not_in_froms'; eauto.
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

  Lemma count_occ_permuted_froms_same' :
    forall froms froms',
      Permutation froms froms'
      -> forall f n,
        count_occ msg_seq_eq froms f = n
        -> count_occ msg_seq_eq froms' f = n.
  Proof.
    intros * PERM.
    induction PERM using Permutation_ind_bis; eauto; intros; simpl in *.

    - destruct (msg_seq_eq x f); eauto.
      rewrite <- H.
      f_equal.
      remember (count_occ msg_seq_eq l f) as sn.
      symmetry in Heqsn; eauto.

    - destruct (msg_seq_eq x f)
      ; destruct (msg_seq_eq y f)
      ; subst
      ; eauto.
  Qed.
  
  Lemma count_occ_permuted_froms_same :
    forall froms froms' f,
      Permutation froms froms'
      -> count_occ msg_seq_eq froms f =
        count_occ msg_seq_eq froms' f.
  Proof.
    intros.
    remember (count_occ msg_seq_eq froms f) as n.
    symmetry in Heqn.
    eapply count_occ_permuted_froms_same' in Heqn; eauto.
  Qed.

  Lemma clean_messages_permuted_froms_same :
    forall honestk cs uid msgs froms froms',
      Permutation froms froms'
      -> clean_messages honestk cs (Some uid) froms  msgs =
        clean_messages honestk cs (Some uid) froms' msgs.
  Proof.
    induction msgs; eauto; intros.
    unfold clean_messages, clean_messages'; simpl.
    unfold msg_filter at 2 4
    ; destruct a
    ; cases ( msg_signed_addressed honestk cs (Some uid) c ); eauto.

    unfold msg_nonce_ok.
    unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in *.
    destruct c; try discriminate.
    cases (cs $? c_id); try discriminate.
    simpl.
    erewrite count_occ_permuted_froms_same by eauto.
    cases (count_occ msg_seq_eq froms' (cipher_nonce c)); eauto.
    rewrite !fold_clean_messages2' , !clean_messages'_fst_pull, !fold_clean_messages; eauto.
    erewrite IHmsgs; eauto.
  Qed.

  Lemma msg_honestly_signed_signing_key_honest :
    forall {t} (msg : crypto t) honestk cs k,
      msg_honestly_signed honestk cs msg = true
      -> msg_signing_key cs msg = Some k
      -> honest_key honestk k.
  Proof.
    unfold msg_honestly_signed, msg_signing_key; intros.
    destruct msg; try discriminate
    ; cases (cs $? c_id)
    ; try discriminate.

    invert H0.
    unfold honest_keyb in H
    ; cases (honestk $? cipher_signing_key c)
    ; try discriminate
    ; destruct b
    ; try discriminate
    ; econstructor; eauto.
  Qed.

  Lemma message_honestly_signed_msg_signing_key_honest :
    forall {t} (msg : crypto t) honestk cs,
      msg_honestly_signed honestk cs msg  = true
      -> exists k,
        msg_signing_key cs msg = Some k
        /\ honest_key honestk k.
  Proof.
    intros.
    unfold msg_honestly_signed in *; destruct msg; try discriminate;
      repeat
        match goal with
        | [ H : (match ?m with _ => _ end) = _ |- _ ] => cases m; try discriminate; simpl in *
        | [ H : Some _ = Some _ |- _ ] => invert H
        | [ H : honest_keyb _ _ = true |- _] => rewrite <- honest_key_honest_keyb in H
        end; eauto.
  Qed.

  Lemma msg_honestly_signed_has_signing_key_cipher_id :
    forall {t} (msg : crypto t) honestk cs,
      msg_honestly_signed honestk cs msg = true
      -> (exists k, msg_signing_key cs msg = Some k)
        /\ (exists cid, msg_cipher_id msg = Some cid).
  Proof.
    unfold msg_honestly_signed, msg_signing_key, msg_cipher_id; intros.
    destruct msg; try discriminate
    ; cases (cs $? c_id)
    ; try discriminate.

    unfold honest_keyb in H
    ; cases (honestk $? cipher_signing_key c)
    ; try discriminate
    ; destruct b
    ; try discriminate
    ; eauto.
  Qed.
  
  Lemma clean_messages_elt_same :
    forall t honestk cs uid msgs1 (msg : crypto t) froms msgs2 pat cid c,
      Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs (Some uid) froms pat msg') msgs1
      -> msg_honestly_signed honestk cs msg = true
      -> msg_to_this_user cs (Some uid) msg = true
      -> msg = SignedCiphertext cid
      -> cs $? cid = Some c
      -> ~ List.In (cipher_nonce c) froms
      -> msg_accepted_by_pattern cs (Some uid) froms pat msg
      -> (forall cid1 cid2 c1 c2,
            cid1 <> cid2
            -> cs $? cid1 = Some c1
            -> cs $? cid2 = Some c2
            -> honestk $? (cipher_signing_key c1) = Some true
            -> honestk $? (cipher_signing_key c2) = Some true
            -> cipher_nonce c1 <> cipher_nonce c2)
      -> exists froms',
          clean_messages honestk cs (Some uid) froms (msgs1 ++ (existT _ _ msg) :: msgs2) = 
          clean_messages honestk cs (Some uid) froms msgs1
                         ++ (existT _ _ msg)
                         :: clean_messages honestk cs (Some uid) froms' msgs2
          /\ clean_messages honestk cs (Some uid) (updateTrackedNonce (Some uid) froms cs msg) (msgs1 ++ msgs2) =
            clean_messages honestk cs (Some uid) froms msgs1 ++
                           clean_messages honestk cs (Some uid) froms' msgs2
  .
  Proof.
    induction msgs1; intros; eauto.
    - eexists.
      simpl.
      unfold clean_messages at 1; unfold clean_messages'; simpl.
      unfold msg_signed_addressed.
      rewrite H0, H1; simpl.
      unfold msg_nonce_ok; subst; context_map_rewrites.
      count_occ_list_in1.
      rewrite fold_clean_messages2',
      clean_messages'_fst_pull,
      fold_clean_messages; split; eauto.
      unfold updateTrackedNonce
      ; unfold msg_to_this_user, msg_destination_user in H1
      ; context_map_rewrites.
      destruct ( cipher_to_user c ==n uid ); [|discriminate]; subst.
      destruct ( cipher_to_user c ==n cipher_to_user c ); [|contradiction].
      rewrite H4; trivial.

    - invert H.
      rewrite <- !app_comm_cons.

      unfold clean_messages at 1 2 4 5, clean_messages'; simpl.
      unfold msg_filter at 2 4 6 8; destruct a.

      generalize (IHmsgs1 _ _ msgs2 _ _ _ H10 H0 H1 eq_refl H3 H4 H5 H6); intros.
      split_ex.
      cases (msg_signed_addressed honestk cs (Some uid) c0); eauto.
      progress simpl.

      unfold msg_signed_addressed, msg_honestly_signed, msg_to_this_user, msg_destination_user in Heq
      ; simpl in Heq
      ; context_map_rewrites.

      unfold msg_nonce_ok; dependent destruction c0; simpl in *; try discriminate.

      cases (cs $? c_id); try discriminate; context_map_rewrites.
      destruct (cipher_to_user c0 ==n uid); rewrite ?andb_true_r,?andb_false_r in Heq; try discriminate; subst.

      generalize H1; intros
      ; unfold msg_to_this_user, msg_destination_user in H1
      ; simpl in H1
      ; context_map_rewrites
      ; destruct (cipher_to_user c ==n cipher_to_user c0); [|discriminate].
      rewrite e in *.
      destruct (cipher_to_user c0 ==n cipher_to_user c0); [|contradiction].
      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H4.
      rewrite !H4 in *.

      (* Set Printing Implicit. *)

      destruct (cid ==n c_id); subst; clean_map_lookups.
      assert (@msg_accepted_by_pattern cs (Some (cipher_to_user c0)) froms t1 pat (SignedCiphertext c_id)).
      invert H5; econstructor; eauto.
      contradiction.

      rewrite <- honest_key_honest_keyb in Heq
      ; invert Heq.
      pose proof (msg_honestly_signed_has_signing_key_cipher_id (@SignedCiphertext t0 cid) _ _ H0)
      ; split_ex.
      pose proof (msg_honestly_signed_signing_key_honest (@SignedCiphertext t0 cid) honestk cs H0 H1).
      invert H11; subst.
      unfold msg_signing_key in H1
      ; context_map_rewrites
      ; invert H1.
      generalize (H6 _ _ _ _ n H3 Heq0 H12 H8); intros.

      assert (count_occ msg_seq_eq (cipher_nonce c :: froms) (cipher_nonce c0) =
              count_occ msg_seq_eq froms (cipher_nonce c0)) as RWCOUNT
          by (simpl; destruct (msg_seq_eq (cipher_nonce c) (cipher_nonce c0)); [contradiction|]; trivial).

      assert (count_occ msg_seq_eq (cipher_nonce c0 :: froms) (cipher_nonce c) =
              count_occ msg_seq_eq froms (cipher_nonce c)) as RWCOUNT'
          by (simpl; destruct (msg_seq_eq (cipher_nonce c0) (cipher_nonce c)); [congruence|]; trivial).

      rewrite !RWCOUNT in *.
      cases (count_occ msg_seq_eq froms (cipher_nonce c0)); eauto.

      rewrite !fold_clean_messages2',
      !clean_messages'_fst_pull,
      !fold_clean_messages.

      eapply IHmsgs1 with (froms := cipher_nonce c0 :: froms) (pat := pat) in H0
      ; clear IHmsgs1; eauto.
      split_ex; rewrite H0.
      
      2 : {
        rewrite Forall_forall in H10 |- *.
        intros * LIN.
        destruct x1.
        eapply H10 in LIN; split_ex.
        unfold not; intros.
        assert (msg_accepted_by_pattern cs (Some (cipher_to_user c0)) froms pat c1).
        invert H11; econstructor; eauto; destruct chk; eauto; rewrite <- count_occ_not_In in *.
        apply not_in_cons in H15; split_ex; eauto.
        apply not_in_cons in H15; split_ex; eauto.
        contradiction.
      }

      2 : {
        rewrite <- count_occ_not_In in *.
        apply not_in_cons in RWCOUNT; split_ex.
        eapply not_in_cons; eauto.
      }

      2 : {
        invert H5; econstructor; eauto; destruct chk; eauto; rewrite <- count_occ_not_In in *
        ; clean_map_lookups
        ; simpl in *
        ; unfold not
        ; intros; split_ors; eauto.
      }

      unfold updateTrackedNonce in H11
      ; context_map_rewrites
      ; rewrite e in H11
      ; destruct (cipher_to_user c0 ==n cipher_to_user c0); [|contradiction].

      eexists; split; try reflexivity.
      rewrite <- app_comm_cons.
      rewrite <- H11.
      f_equal.
      eapply clean_messages_permuted_froms_same; eauto.
      eapply perm_swap.
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


End CleanMessages.



  Lemma msg_honestly_signed_new_msg_keys :
    forall {t} (msg : crypto t) {t1} (c : crypto t1) honestk cs,
      message_no_adv_private honestk cs msg
      -> msg_honestly_signed honestk cs c = true
      -> msg_honestly_signed (honestk $k++ findKeysCrypto cs msg) cs c = true.
  Proof.
    unfold message_no_adv_private, msg_honestly_signed, msg_signing_key, honest_keyb; intros;
      destruct c; try discriminate;
        cases (cs $? c_id); try discriminate.
    cases (honestk $? cipher_signing_key c);
      cases (findKeysCrypto cs msg $? cipher_signing_key c);
      try discriminate; solve_perm_merges; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_new_msg_keys : core.

  Lemma msg_signed_addressed_new_msg_keys :
    forall {t} (msg : crypto t) {t1} (c : crypto t1) honestk cs suid,
      message_no_adv_private honestk cs msg
      -> msg_signed_addressed honestk cs suid c = true
      -> msg_signed_addressed (honestk $k++ findKeysCrypto cs msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros;
      rewrite andb_true_iff in *; split_ands; split; eauto.
  Qed.

  Hint Resolve msg_signed_addressed_new_msg_keys : core.

  Lemma msg_signed_addressed_new_msg_keys' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; split; eauto.
    unfold msg_honestly_signed, msg_signing_key in *;
      destruct c; try discriminate.
    cases (cs $? c_id);
      try discriminate.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); try discriminate.
    destruct b; try discriminate.
    cases (findKeysMessage msg $? cipher_signing_key c);
      solve_perm_merges; eauto.
  Qed.

  Lemma msg_signed_addressed_new_msg_keys'' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    intros; apply msg_signed_addressed_new_msg_keys'; eauto.
  Qed.

  Lemma msg_signed_addressed_new_msg_keys''' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; split; eauto.
    unfold msg_honestly_signed, msg_signing_key in *;
      destruct c; try discriminate.
    cases (cs $? c_id);
      try discriminate.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); try discriminate.
    destruct b; try discriminate.
    cases (findKeysMessage msg $? cipher_signing_key c);
      solve_perm_merges; eauto.
  Qed.

  Hint Resolve
       msg_signed_addressed_new_msg_keys'
       msg_signed_addressed_new_msg_keys''
       msg_signed_addressed_new_msg_keys'''
    : core.
  
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

  Hint Resolve
       msg_honestly_signed_addnl_cipher
       msg_honestly_signed_addnl_honest_key
    : core.

  Lemma msg_signed_addressed_addnl_honest_key :
    forall {t} (msg : crypto t) honestk cs suid k_id,
      ~ In k_id honestk
      -> msg_signed_addressed honestk cs suid msg = true
      -> msg_signed_addressed (honestk $+ (k_id,true)) cs suid msg = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; eauto using msg_honestly_signed_addnl_honest_key.
  Qed.

  Hint Resolve msg_signed_addressed_addnl_honest_key : core.

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

    Lemma clean_adv_msgs_new_honest_key_idempotent :
      forall {A} (usrs : honest_users A) k_id msgs cs gks,
        adv_message_queue_ok usrs cs gks msgs
        -> ~ In k_id gks
        -> clean_adv_msgs (findUserKeys usrs $+ (k_id, true)) cs msgs
          = clean_adv_msgs (findUserKeys usrs) cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H; split_ands.
      cases (msg_honestly_signed (findUserKeys usrs) cs c); simpl in *
      ; match goal with
        | [ H : msg_honestly_signed (findUserKeys usrs) cs c = ?tf |- _] =>
          assert (msg_honestly_signed (findUserKeys usrs $+ (k_id,true)) cs c = tf)
            as MHS by eauto using msg_honestly_signed_nochange_addnl_honest_key
      end; rewrite MHS; simpl; eauto.
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

    Ltac specialize_msg_queue_ok :=
      repeat
        match goal with
        | [ H : (forall k, msg_signing_key _ ?msg = Some k -> _) |- _] =>
          match goal with
          | [ MSK : msg_signing_key _ msg = Some _ |- _ ] => specialize (H _ MSK); split_ands
          | [ MHS : msg_honestly_signed ?honk _ msg = true |- _ ] =>
            apply message_honestly_signed_msg_signing_key_honest in MHS; split_ex; split_ands
          end
        | [ HK : honest_key ?honk ?k, H : (honest_key ?honk ?k -> _) |- _ ] => specialize (H HK); split_ands
        end.

  Ltac specialize_msg_ok :=
    repeat 
      match goal with
      (* | [ H : (?arg -> _) , ARG : ?arg |- _ ] => specialize (H ARG) *)
      | [ H : (forall k, msg_signing_key ?cs ?msg = Some k -> _)
      , MSK : msg_signing_key ?cs ?msg = Some _ |- _ ] => specialize (H _ MSK); split_ands
      | [ H : (forall cid, msg_cipher_id ?msg = Some cid -> _)
      , MCID : msg_cipher_id ?msg = Some _ |- _ ] => specialize (H _ MCID); split_ands
      | [ H1 : (forall k, msg_signing_key ?cs ?msg = Some k -> _)
        , H2 : (forall cid, msg_cipher_id ?msg = Some cid -> _)
       , MHS : msg_honestly_signed _ _ _ = true |- _ ] => 
        generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex
      | [ MPS : msg_pattern_safe ?honk _
        , MAP :  msg_accepted_by_pattern ?cs _ _ _ ?msg |- _ ] =>
        assert_if_new (msg_honestly_signed honk cs msg = true) eauto
      | [ H1 : msg_honestly_signed ?honk _ ?msg = true, H2 : msg_signing_key _ ?msg = Some ?k |- _ ] =>
        assert_if_new (honest_key honk k) eauto
      | [ H : (forall k kp, findKeysCrypto ?cs ?msg $? k = Some kp -> _), ARG : findKeysCrypto ?cs ?msg $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG)
      | [ HK : honest_key ?honk ?k, H : (honest_key ?honk ?k -> _) |- _] => specialize (H HK); split_ands
      | [ HL : ?honk $? ?k = Some true, H : (honest_key ?honk ?k -> _) |- _] =>
        assert (honest_key honk k) as HK by (constructor; auto); specialize (H HK); split_ands
      | [ PK : ?pubk $? _ = Some _, H : (forall k p, ?pubk $? k = Some p -> _) |- _ ] => specialize (H _ _ PK); split_ands
      | [ MC : msg_cipher_id ?c = Some _, H : (forall cid, msg_cipher_id ?c = Some cid -> _) |- _ ] =>
        specialize (H _ MC); split_ands
      end.

  Lemma break_msg_queue_prop :
    forall elt e (l1 l2 : list elt) P,
      Forall (fun x => P x) (l1 ++ e :: l2)
      -> P e
        /\ Forall (fun x => P x) (l1 ++ l2)
  .
  Proof.
    intros * H
    ; rewrite List.Forall_app in *
    ; destruct H as [H H']
    ; invert H'
    ; eauto.
  Qed.

  Ltac user_queue_lkup TAG :=
    match goal with
    | [ H : user_queue ?usrs ?uid = Some ?qmsgs |- _ ] =>
      assert (exists cmd mycs ks froms sents cur_n,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_nons := froms
                                     ; sent_nons := sents
                                     ; cur_nonce := cur_n |})
        as TAG by (unfold user_queue in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists t v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.
  
  Ltac msg_queue_prop :=
    match goal with
    | [ OK : message_queues_ok ?cs ?us ?gks |- _ ] =>
      match goal with
      | [ H : us $? _ = Some ?u |- _ ] =>
        prop_not_unifies (message_queue_ok (findUserKeys us) cs (msg_heap u) gks);
        generalize (Forall_natmap_in_prop _ OK H); simpl; intros
      | _ => let USR := fresh "USR"
            in user_queue_lkup USR;
               do 6 (destruct USR as [?x USR]);
               generalize (Forall_natmap_in_prop _ OK USR); simpl; intros
      end
    end;
    repeat
      match goal with
      | [ H : message_queue_ok _ _ (_ :: _) _ |- _ ] => invert H; split_ands
      | [ H : message_queue_ok _ _ (?msgs1 ++ ?msg :: ?msgs2) _ |- _ ] =>
        unfold message_queue_ok in H
        ; eapply break_msg_queue_prop in H
        ; split_ex
      | [ H : (forall k, msg_signing_key ?msg = Some k -> _) |- _] =>
        specialize_msg_queue_ok
      | [ MHS : msg_honestly_signed _ _ ?msg = _ , MTCH : match ?msg with _ => _ end |- _ ] =>
        unfold msg_honestly_signed in MHS; destruct msg; try discriminate; rewrite MHS in *;
        split_ands; simpl in *
      end.

  Hint Resolve clean_ciphers_keeps_honest_cipher : core.


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
         message_not_accepted_by_pattern_same_after_cleaning
      : core.

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

    Hint Resolve
         clean_ciphers_keeps_honest_cipher
         honest_cipher_filter_fn_true_honest_signing_key : core.
                                                                     
        Lemma not_accepted_ok :
      forall honestk cs uid froms pat (msgs : queued_messages),
        Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern (clean_ciphers honestk cs) (Some uid) froms pat msg') msgs
        -> msg_pattern_safe honestk pat
        -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs (Some uid) froms pat msg') msgs.
    Proof.
      intros
      ; rewrite Forall_forall in *
      ; intros.

      destruct x.
      apply H in H1.

      unfold not in H1 |- *; intros.
      apply H1; clear H1.

      destruct H2
      ; invert H0
      ; [ econstructor 2
        | econstructor 3]; eauto.
      
    Qed.

    Lemma msg_honestly_signed_pattern_safe_stuff :
      forall honestk cs t msg pat froms uid,
        @msg_honestly_signed honestk t cs msg = true
        -> msg_pattern_safe honestk pat
        -> msg_accepted_by_pattern cs (Some uid) froms pat msg
        -> exists cid c,
            msg = SignedCiphertext cid
            /\ cs $? cid = Some c
            /\ ~ List.In (cipher_nonce c) froms.
    Proof.
      intros * MHS MPS MABP.
      unfold msg_honestly_signed, msg_signing_key in MHS.
      destruct msg; try discriminate.
      cases (cs $? c_id); try discriminate.
      invert MABP
      ; invert MPS
      ; rewrite <- count_occ_not_In in H1.

      (do 2 eexists); eauto.
      (do 2 eexists); eauto.
    Qed.

    Lemma in_cleaned_message_queue_must_in_message_queue :
      forall msgs t (msg : crypto t) cs suid pat froms,

        List.In (existT _ _ msg) msgs
        -> msg_accepted_by_pattern cs suid froms pat msg
        -> exists msgs1 t' (msg' : crypto t') msgs2,
            msg_accepted_by_pattern cs suid froms pat msg'
            /\ msgs = msgs1 ++ (existT _ _ msg') :: msgs2
            /\ Forall (fun '(existT _ _ m) => ~ msg_accepted_by_pattern cs suid froms pat m) msgs1.
    Proof.
      induction msgs; intros; eauto.
      invert H.
      simpl in H; split_ors; subst.

      - exists []; (do 3 eexists); repeat simple apply conj;
          try rewrite app_nil_l; eauto.

      - destruct a.
        destruct (
            classic (
                msg_accepted_by_pattern cs suid froms pat c
          )).

        + exists []; (do 3 eexists); repeat simple apply conj;
            try rewrite app_nil_l; eauto.

        + eapply IHmsgs in H; eauto.
          split_ex; subst.
          exists (existT _ _ c :: x0); (do 3 eexists); repeat simple apply conj; eauto.
          rewrite app_comm_cons; reflexivity.
    Qed.

    Lemma mabp_fewer_nons :
      forall t (msg : crypto t) cs uid froms pat n,
        msg_accepted_by_pattern cs (Some uid) (n :: froms) pat msg
        -> msg_accepted_by_pattern cs (Some uid) froms pat msg.
    Proof.
      intros * MABP.
      invert MABP; [ econstructor 1
                   | econstructor 2
                   | econstructor 3 ]; eauto.

      destruct chk; eauto
      ; rewrite <- count_occ_not_In in *
      ; unfold not
      ; intros
      ; apply H1
      ; simpl
      ; eauto.

      destruct chk; eauto
      ; rewrite <- count_occ_not_In in *
      ; unfold not
      ; intros
      ; apply H1
      ; simpl
      ; eauto.
    Qed.

    Lemma mabp_addnl_nons :
      forall t (msg : crypto t) cs uid froms pat n honestk,
        msg_accepted_by_pattern cs (Some uid) froms pat msg
        -> msg_honestly_signed honestk cs msg = true
        -> honest_nonces_unique cs honestk
        -> forall cid1 cid2 c1 c2, msg = SignedCiphertext cid1
        -> cs $? cid1 = Some c1
        -> cs $? cid2 = Some c2
        -> cid1 <> cid2
        -> honestk $? cipher_signing_key c1 = Some true
        -> honestk $? cipher_signing_key c2 = Some true
        -> n = cipher_nonce c2
        -> msg_accepted_by_pattern cs (Some uid) (n :: froms) pat msg.
    Proof.
      intros * MABP NR HNU; intros.
      invert MABP; [ econstructor 1
                   | econstructor 2
                   | econstructor 3 ]; eauto.

      - destruct chk; eauto.
        invert H6; clean_map_lookups; simpl in *.
        eapply HNU in H2.
        specialize (H2 H0 H1 H3 H4); simpl in H2.
        destruct (msg_seq_eq (cipher_nonce c2) nonce); try congruence.

      - destruct chk; eauto.
        invert H6; clean_map_lookups; simpl in *.
        eapply HNU in H2.
        specialize (H2 H0 H1 H3 H4); simpl in H2.
        destruct (msg_seq_eq (cipher_nonce c2) nonce); try congruence.
    Qed.

    Hint Resolve mabp_fewer_nons mabp_addnl_nons : core.

    Lemma forall_not_mabp_extra_nons :
      forall cs uid froms pat n (msgs : queued_messages),
        Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern cs (Some uid) froms pat msg) msgs
        -> Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern cs (Some uid) (n :: froms) pat msg) msgs.
    Proof.
      intros.
      rewrite Forall_forall in *; intros.
      destruct x; unfold not; intros; eauto.
      apply H in H0.
      apply H0; eauto.
    Qed.

    Lemma forall_not_mabp_fewer_nons :
      forall cs uid froms pat n (msgs : queued_messages) honestk,
        Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern cs (Some uid) (n :: froms) pat msg) msgs
        -> honest_nonces_unique cs honestk
        -> msg_pattern_safe honestk pat
        -> forall cid c, cs $? cid = Some c
        -> honestk $? cipher_signing_key c = Some true
        -> n = cipher_nonce c
        -> Forall (fun '(existT _ _ msg) => forall cid c, msg = SignedCiphertext cid -> cs $? cid = Some c -> cipher_nonce c <> n) msgs
        -> Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern cs (Some uid) froms pat msg) msgs.
    Proof.
      intros.
      rewrite Forall_forall in *; intros.
      destruct x; unfold not; intros; eauto.
      specialize (H5 _ H6).
      apply H in H6.
      apply H6.
      assert (msg_honestly_signed honestk cs c0 = true) as MHS by eauto.
      pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ex.
      eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
      invert MHS; subst.

      unfold msg_cipher_id in H9
      ; destruct c0
      ; try discriminate.

      unfold msg_signing_key in H8
      ; invert H9
      ; cases (cs $? x0); try discriminate
      ; invert H8.

      specialize (H5 _ _ eq_refl Heq).
      
      destruct (cid ==n x0); clean_map_lookups; eauto.
    Qed.

    Hint Resolve forall_not_mabp_extra_nons forall_not_mabp_fewer_nons : core.

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

    Hint Constructors msg_accepted_by_pattern : core.

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

    Lemma in_cleaned_message_queue_must_in_message_queue' :
      forall msgs t (msg : crypto t) cs uid pat froms,

        List.In (existT _ _ msg) msgs
        -> msg_accepted_by_pattern cs (Some uid) froms pat msg
        -> forall ms1 ms2 honestk, clean_messages honestk cs (Some uid) froms msgs = ms1 ++ existT _ _ msg :: ms2
        -> Forall (fun '(existT _ _ m) => ~ msg_accepted_by_pattern cs (Some uid) froms pat m) ms1
        -> msg_pattern_safe honestk pat
        -> honest_nonces_unique cs honestk
        -> exists msgs1 msgs2,
              msgs = msgs1 ++ (existT _ _ msg) :: msgs2
            /\ ms1 = clean_messages honestk cs (Some uid) froms msgs1
            /\ Forall (fun '(existT _ _ m) =>
                        msg_accepted_by_pattern cs (Some uid) froms pat m
                        -> List.In (existT _ _ m) ms1
                     ) msgs1
    .
    Proof.
      induction msgs; intros; eauto;
        simpl in H; try contradiction; split_ors; subst; eauto.

      - exists []; eexists; repeat simple apply conj;
          try rewrite app_nil_l; eauto.

        destruct ms1; eauto.
        assert (msg_honestly_signed honestk cs msg = true) as MHS by eauto.
        unfold msg_honestly_signed, msg_signing_key in MHS
        ; destruct msg; try discriminate
        ; cases (cs $? c_id); try discriminate
        ; clear MHS.
        assert (msg_honestly_signed honestk cs (@SignedCiphertext t0 c_id) = true) as MHS by eauto.

        generalize H0; intros; invert H0; invert H3
        ; repeat
            match goal with
            | [ H : count_occ _ _ _ = 0 |- _ ] => rewrite <- count_occ_not_In in H
            | [ H : Some _ = Some _ |- _ ] => invert H
            end
        ; erewrite clean_messages_keeps_signed_addressed_unseen_nonce in H1; simpl; eauto.

        rewrite <- app_comm_cons in H1
        ; invert H1
        ; invert H2
        ; contradiction.
        
        unfold msg_signed_addressed; clean_map_lookups; simpl
        ; rewrite MHS
        ; unfold msg_to_this_user, msg_destination_user
        ; context_map_rewrites
        ; simpl
        ; destruct (msg_to ==n msg_to); try contradiction
        ; trivial.
        
        rewrite <- app_comm_cons in H1
        ; invert H1
        ; invert H2
        ; contradiction.
        
        unfold msg_signed_addressed; clean_map_lookups; simpl
        ; rewrite MHS
        ; unfold msg_to_this_user, msg_destination_user
        ; context_map_rewrites
        ; simpl
        ; destruct (msg_to ==n msg_to); try contradiction
        ; trivial.
        
      - destruct a.
        symmetry in H1
        ; apply clean_messages_cons_split in H1
        ; split_ors
        ; symmetry in H1.

        + generalize H1; intros CME; eapply IHmsgs with (pat := pat) in H1; eauto.
          clear IHmsgs.
          split_ex.
          subst.
          exists (existT crypto x c :: x0); eexists; repeat simple apply conj.
          rewrite app_comm_cons; trivial.


          unfold not_replayed in H5.
          unfold clean_messages at 2, clean_messages', msg_filter; simpl.
          cases (msg_signed_addressed honestk cs (Some uid) c); eauto.
          unfold msg_signed_addressed in Heq; rewrite andb_true_iff in Heq; destruct Heq as [RW1 RW2].
          rewrite RW1 in H5
          ; rewrite RW2 in H5
          ; simpl in H5.
          destruct (msg_nonce_ok cs froms c); try discriminate.
          rewrite fold_clean_messages1', fold_clean_messages; trivial.

          econstructor; eauto.
          intros.
          exfalso.

          unfold not_replayed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in H5
          ; invert H3; invert H1
          ; context_map_rewrites
          ; simpl in *
          ; context_map_rewrites
          ; simpl in *
          ; repeat
              match goal with
              | [ H : honest_key _ _ |- _ ] => rewrite honest_key_honest_keyb in H
              | [ H : Some _ = Some _ |- _ ] => invert H
              end
          ; destruct (msg_to ==n msg_to); try contradiction
          .

          rewrite H6, H12 in H5; simpl in H5; discriminate.
          rewrite H6, H13 in H5; simpl in H5; discriminate.

        + subst.
          
          destruct ms1.
          * rewrite app_nil_l in H1
            ; invert H1.

            exists []; eexists; repeat simple apply conj; try rewrite app_nil_l; eauto.
            
          * rewrite <- app_comm_cons in H1
            ; invert H1.
            invert H2.

            generalize H5; intros
            ; unfold not_replayed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in H5
            ; context_map_rewrites
            ; rewrite !andb_true_iff in H5; split_ex
            .

            assert (msg_honestly_signed honestk cs msg = true) as MHS by eauto
            ; unfold msg_honestly_signed, msg_signing_key in MHS
            ; destruct msg; try discriminate
            ; cases (cs $? c_id); try discriminate
            ; rewrite <- honest_key_honest_keyb in *
            ; invert H1; invert MHS
            .

            destruct (x1 ==n c_id); subst.
            exfalso.
            
            assert (msg_accepted_by_pattern cs (Some uid) froms pat (@SignedCiphertext x c_id)).
            invert H0; [ econstructor 1
                       | econstructor 2
                       | econstructor 3]; eauto.
            contradiction.

            invert H2.
            
            generalize H9; intros CME; eapply IHmsgs with (pat := pat) in H9; eauto. 
            clear IHmsgs.
            split_ex.
            subst.

            exists (existT crypto x (SignedCiphertext x1) :: x0); eexists; repeat simple apply conj.
            rewrite app_comm_cons; trivial.

            unfold not_replayed in H12
            ; rewrite !andb_true_iff in H12
            ; split_ex
            ; unfold msg_nonce_ok in H5
            ; context_map_rewrites
            ; destruct (count_occ msg_seq_eq froms (cipher_nonce x2)) eqn:COUNT ; try discriminate
            ; generalize COUNT; rewrite <- count_occ_not_In in COUNT; intros COUNT'
            .
            erewrite clean_messages_keeps_signed_addressed_unseen_nonce; eauto.
            2: {
              unfold msg_signed_addressed; rewrite H1, H12; trivial.
            }

            unfold updateTrackedNonce
            ; context_map_rewrites
            ; destruct (cipher_to_user x2 ==n uid); try discriminate; subst
            ; destruct (cipher_to_user x2 ==n cipher_to_user x2); try contradiction
            ; rewrite COUNT'
            .  
            
            trivial.

            econstructor; eauto.
            rewrite Forall_forall in H9 |- *; intros.
            destruct x4.
            apply H9 in H1; intros; clear H9.
            assert (cipher_nonce x2 <> cipher_nonce c) as NE by (eapply H4; eauto).

            assert ( msg_signed_addressed honestk cs (Some uid) c0 = true ).
            invert H2
            ; invert H3
            (* ; invert H9 *)
            ; unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user
            ; context_map_rewrites
            ; simpl
            ; match goal with
              | [ H : Some _ = Some _ |- _ ] => invert H
              end
            ; rewrite honest_key_honest_keyb in *
            ; destruct (msg_to ==n msg_to); try contradiction
            ; eauto.

            rewrite andb_true_r; auto.
            rewrite andb_true_r; auto.

            generalize H9
            ; unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key
                   , msg_to_this_user, msg_destination_user in H9
            ; destruct c0; try discriminate
            ; cases (cs $? c_id0); try discriminate
            ; intros.

            destruct (c_id0 ==n x1)
            ; subst; clean_map_lookups.
            exfalso; apply H8.
            invert H2; eauto.

            assert (cipher_nonce c0 <> cipher_nonce x2) as NE2.
            eapply H4; eauto.
            rewrite andb_true_iff in H9; split_ex.
            rewrite <- honest_key_honest_keyb in H9; invert H9; eauto.

            assert ( msg_accepted_by_pattern cs (Some uid) (cipher_nonce x2 :: froms) pat (@SignedCiphertext t1 c_id0) ).
            invert H2; invert H3; [ econstructor 2 | econstructor 3]; eauto
            ; clean_map_lookups; simpl in *
            ; destruct ( msg_seq_eq (cipher_nonce x2) nonce ); try congruence.

            apply H1 in H15; eauto.
    Qed.

    Lemma in_cleaned_message_queue_must_in_message_queue'' :
      forall msgs t (msg : crypto t) cs uid pat froms,

        List.In (existT _ _ msg) msgs
        -> msg_accepted_by_pattern cs (Some uid) froms pat msg
        -> forall ms1 ms2 honestk, clean_messages honestk cs (Some uid) froms msgs = ms1 ++ existT _ _ msg :: ms2
        -> Forall (fun '(existT _ _ m) => ~ msg_accepted_by_pattern cs (Some uid) froms pat m) ms1
        -> msg_pattern_safe honestk pat
        -> honest_nonces_unique cs honestk
        -> exists msgs1 msgs2,
              msgs = msgs1 ++ (existT _ _ msg) :: msgs2
            /\ Forall (fun '(existT _ _ m) => ~ msg_accepted_by_pattern cs (Some uid) froms pat m) msgs1.
    Proof.
      intros.

      eapply in_cleaned_message_queue_must_in_message_queue' in H; eauto
      ; split_ex.

      subst.
      (do 2 eexists); split.
      reflexivity.
      rewrite Forall_forall in *; intros.
      destruct x1.

      specialize (H6 _ H); simpl in H6.
      unfold not; intros.
      specialize (H6 H5).
      specialize (H2 _ H6); simpl in H2.
      contradiction.
    Qed.

    Lemma all_not_accepted_by_pattern_cleaned_not_cleaned_ciphers :
      forall cs uid froms pat (msgs : queued_messages) honestk,
        Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern (clean_ciphers honestk cs) (Some uid)  froms pat msg) msgs
        -> msg_pattern_safe honestk pat
        -> Forall (fun '(existT _ _ msg) => ~ msg_accepted_by_pattern cs (Some uid) froms pat msg) msgs.
    Proof.
      intros.
      rewrite Forall_forall in *; intros.
      destruct x.
      apply H in H1; unfold not in *; intros.
      apply H1; clear H1.

      invert H2
      ; invert H0 ; [ econstructor 2
                    | econstructor 3]; eauto.
    Qed.

    Hint Resolve all_not_accepted_by_pattern_cleaned_not_cleaned_ciphers : core.

