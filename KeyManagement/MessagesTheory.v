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
        Automation
        Tactics
        RealWorld
        AdversaryUniverse
        CipherTheory
        Simulation.

Set Implicit Arguments.

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
     accepted_safe_msg_pattern_replay_safe.

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
  
  Hint Resolve honest_cipher_filter_fn_true_honest_signing_key.
  (* Hint Extern 1 (honest_key _ _) => process_keys_messages. *)

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
       msg_honestly_signed_before_after_cleaning'.

  Lemma message_not_replayed_addnl_destruct :
    forall {t1 t2} (msg1 : crypto t1) (msg2 : crypto t2) to_usr cs froms msgs,
      msg_not_replayed to_usr cs froms msg1 (existT _ _ msg2 :: msgs)
      -> msg_not_replayed to_usr cs froms msg1 msgs.
  Proof.
    intros.
    unfold msg_not_replayed in *; intros; split_ex; split_ands; subst; eauto.
    invert H2; eauto 8.
  Qed.

  Hint Resolve message_not_replayed_addnl_destruct.

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

  (* Hint Resolve message_not_replayed_cons_split. *)

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
  
  Ltac count_occ_list_in1 :=
    match goal with
    | [ H : ~ List.In ?x ?xs |- context [ count_occ _ ?xs ?x ] ] => rewrite count_occ_not_In in H; rewrite H
    | [ H : count_occ _ ?xs ?x = 0 |- context [ ~ List.In ?x ?xs ] ] => rewrite count_occ_not_In
    end.

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

  Hint Resolve msg_nonce_same_after_cleaning.

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

  Hint Resolve msg_nonce_same_not_same_contra.

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

  Hint Resolve honest_cipher_signing_key_cipher_filter_fn_true.

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
       msg_nonce_ok_after_cipher_cleaning.

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

  Hint Resolve msg_honestly_signed_new_msg_keys.

  Lemma msg_signed_addressed_new_msg_keys :
    forall {t} (msg : crypto t) {t1} (c : crypto t1) honestk cs suid,
      message_no_adv_private honestk cs msg
      -> msg_signed_addressed honestk cs suid c = true
      -> msg_signed_addressed (honestk $k++ findKeysCrypto cs msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros;
      rewrite andb_true_iff in *; split_ands; split; eauto.
  Qed.

  Hint Resolve msg_signed_addressed_new_msg_keys.

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

  Hint Resolve msg_signed_addressed_new_msg_keys' msg_signed_addressed_new_msg_keys'' msg_signed_addressed_new_msg_keys'''.
  
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

  Hint Resolve msg_honestly_signed_addnl_cipher.
  Hint Resolve msg_honestly_signed_addnl_honest_key.

  Lemma msg_signed_addressed_addnl_honest_key :
    forall {t} (msg : crypto t) honestk cs suid k_id,
      ~ In k_id honestk
      -> msg_signed_addressed honestk cs suid msg = true
      -> msg_signed_addressed (honestk $+ (k_id,true)) cs suid msg = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; eauto using msg_honestly_signed_addnl_honest_key.
  Qed.

  Hint Resolve msg_signed_addressed_addnl_honest_key.
