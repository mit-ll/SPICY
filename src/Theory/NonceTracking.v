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

From Coq Require Import
     List
     Lia
     (* Morphisms *)
     (* Eqdep *)
     (* Permutation *)
     (* Classical *)
     (* Program.Equality (* for dependent induction *) *)
     Classical_Prop
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
     RealWorld

     Theory.CipherTheory
     Theory.KeysTheory
     Theory.MessagesTheory
     Theory.UsersTheory
.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Import SafetyAutomation.

Set Implicit Arguments.

Inductive HNOK {A} (usrs : honest_users A) (cs : ciphers) : Prop :=
| HOK : 
    honest_nonces_ok cs usrs
    -> HNOK usrs cs
.

Ltac process_nonce_ok1 :=
  match goal with
  | [ H : _ $+ (?uid1,_) $? ?uid2 = _ |- _ ] => destruct (uid1 ==n uid2); subst; clean_map_lookups; simpl
  | [ H : ?cs $? ?cid = _ |- context [ ?cs $? ?cid ] ] => rewrite H
  | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
  | [ H : ~ List.In ?cn ?lst |- context [ count_occ msg_seq_eq ?lst ?cn ] ] =>
    rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H; rewrite H
  | [ H : Some _ <> None -> ?non = (Some ?uid, ?curn) |- _ ] =>
    assert (non = (Some uid,curn)) by (eapply H; congruence); subst; clear H
  | [ |- honest_nonce_tracking_ok _ _ _ _ _ _ (if ?cond then _ else _) _ ] => destruct cond; subst
  | [ H1 : msg_to_this_user _ _ _ = true, H2 : msg_to_this_user _ _ _ = false |- _ ] =>
    rewrite H1 in H2; invert H2
  | [ H : forall _ _ _ _, _ <> _ -> _ -> _ -> honest_nonce_tracking_ok ?cs _ _ _ _ _ _ _
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
        |- honest_nonce_tracking_ok _ _ (Some ?uid1) _ _ _ ?froms ?qmsgs ] =>
    assert (OK : HNOK usrs cs) by (constructor; assumption)
    ; specialize (H _ _ _ _ NE U1 U2); simpl in H
  | [ H : forall _ _ _ _, _ <> _ -> _ -> _ -> honest_nonce_tracking_ok ?cs _ _ _ _ _ _ _
                                                              (* | [ H : forall _ _ _ _, _ <> _ -> _ *)
      , NE: ?uid1 <> ?uid2
      , U1 : ?usrs $? ?uid1 = _
      , U2 : ?usrs $? ?uid2 = Some {|
                                  key_heap := _;
                                              protocol := _;
                                                          msg_heap := (?qmsgs1 ++ _ :: ?qmsgs2);
                                                                      c_heap := _;
                                                                                from_nons := ?froms;
                                                                                             sent_nons := _;
                                                                                                          cur_nonce := _ |}
        |- honest_nonce_tracking_ok _ _ (Some ?uid1) _ _ _ ?froms (?qmsgs1 ++ ?qmsgs2) ] =>
    assert (OK : HNOK usrs cs) by (constructor; assumption)
    ; specialize (H _ _ _ _ NE U1 U2); simpl in H
  | [ H : forall _ _ _ _, _ <> _ -> _ -> _ -> honest_nonce_tracking_ok ?cs _ _ _ _ _ _ _
                                                              (* | [ H : forall _ _ _ _, _ <> _ -> _ *)
      , NE: ?uid1 <> ?uid2
      , U1 : ?usrs $? ?uid1 = _
      , U2 : ?usrs $? ?uid2 = Some {|
                                  key_heap := _;
                                              protocol := _;
                                                          msg_heap := (?qmsgs1 ++ _ :: ?qmsgs2);
                                                                      c_heap := _;
                                                                                from_nons := ?froms;
                                                                                             sent_nons := _;
                                                                                                          cur_nonce := _ |}
        |- honest_nonce_tracking_ok _ _ (Some ?uid1) _ _ _ (_ :: ?froms) (?qmsgs1 ++ ?qmsgs2) ] =>
    assert (OK : HNOK usrs cs) by (constructor; assumption)
    ; specialize (H _ _ _ _ NE U1 U2); simpl in H
  | [ H : forall _ _ _ _, _ <> _ -> _ -> _ -> honest_nonce_tracking_ok ?cs _ _ _ _ _ _ _
      , NE: ?uid1 <> ?uid2
      , U1 : ?usrs $? ?uid1 = _
      , U2 : ?usrs $? ?uid2 = Some ?rec_u
        |- honest_nonce_tracking_ok _ _ (Some ?uid1) _ _ _ (from_nons ?rec_u) _ ] =>
    assert (OK : HNOK usrs cs) by (constructor; assumption)
    ; specialize (H _ _ _ _ NE U1 U2); simpl in H
  | [ H : honest_nonce_tracking_ok _ _ _ _ _ _ _ _ |- honest_nonce_tracking_ok _ _ _ _ _ _ _ _ ] =>
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
  | [ H : Forall _ (_ ++ _ :: _) |- _ ] => eapply break_msg_queue_prop in H
  | [ H : Forall _ (_ :: _) |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : List.In _ (_ ++ _ :: _) |- _ ] => eapply in_elt_inv in H; split_ex
  | [ H : List.In _ (_ :: _) |- _ ] => simpl in H; split_ors
  | [ H : ~ List.In _ (if ?cond then _ else _) |- _ ] => destruct cond; subst; simpl in H
  | [ H : ~ (_ \/ _) |- _ ] => apply Decidable.not_or in H; split_ands
  | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] =>
    let HH := fresh "H"
    in  generalize H
        ; intros HH
        ; eapply accepted_safe_msg_pattern_msg_filter_true in H; eauto 2
        ; eapply accepted_safe_msg_pattern_replay_safe in HH; eauto 2
        ; split_ex
  | [ H1 : msg_signing_key _ _ = Some ?k
           , H2 : _ $? ?k = Some true |- _ ] =>
    unfold msg_signing_key in H1
    ; context_map_rewrites
    ; invert H1
  | [ H1 : msg_honestly_signed ?honk ?cs (SignedCiphertext ?cid) = true
           , H2 : ?honk $? cipher_signing_key ?c = Some true -> _
                  , H3 : ?cs $? ?cid = Some ?c |- _ ] =>
    match goal with
    | [ ARG : honk $? cipher_signing_key c = Some true |- _ ] =>
      progress specialize_simply
    | _ => generalize H1; intros
          ; eapply message_honestly_signed_msg_signing_key_honest in H1
          ; let H := fresh "H" in destruct H1 as [?k [H1 H]]
                                  ; invert H
    end
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
  | [ |- ~ (_ \/ _) ] => apply and_not_or
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

Hint Extern 1 (message_queue_ok _ _ _ _) => eassumption || (msg_queue_prop; eassumption) : core.

Ltac process_message_queue :=
  repeat 
    match goal with
    | [ H : message_queue_ok _ _ (_ ++ _ :: _) _ |- context [ findKeysCrypto _ _ ] ] =>
      eapply break_msg_queue_prop in H
      ; split_ex
    | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] =>
      let HH := fresh "H"
      in  generalize H
          ; intros HH
          ; eapply accepted_safe_msg_pattern_msg_filter_true in H; eauto 2
          ; eapply accepted_safe_msg_pattern_replay_safe in HH; eauto 2
          ; split_ex
    | [ H1 : msg_honestly_signed _ _ ?msg = true
             , H2 : (forall _, msg_signing_key _ ?msg = Some _ -> _) |- context [ findKeysCrypto _ _ ]] =>
      progress specialize_simply
    | [ H : message_no_adv_private _ _ ?msg |- context [ findKeysCrypto _ ?msg ]] =>
      rewrite honestk_merge_new_msgs_keys_same in * by (assumption)
    end.

Ltac instantiate_cs_lkup' :=
  match goal with 
  | [ H : forall c_id c, SignedCiphertext _ = SignedCiphertext _ -> ?cs $? c_id = Some c -> _ |- _ ] =>
    match goal with
    | [ CS : cs $? _ = Some _ |- _ ] =>
      let INST := fresh "INST" in
      generalize (H _ _ eq_refl CS); intro INST;
      let toh := type of INST in
      clear INST;
      (assert toh by (solve_simply; assumption); fail 1) || (generalize (H _ _ eq_refl CS); intros)
    end
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

Ltac process_nonce_ok :=
  process_message_queue;
  repeat ( simpl in *;
           clean_map_lookups1 || congruence || discriminate || assumption
           || process_nonce_ok1 || instantiate_cs_lkup' || Nat.order ).

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

Hint Resolve clean_ciphers_nochange_cipher : core.

Lemma honest_nonce_tracking_ok_after_cleaning :
  forall honestk honestk' cs me my_sents my_non you your_froms your_msgs,
    honest_nonce_tracking_ok cs honestk me my_sents my_non you your_froms your_msgs
    -> (forall kid, honestk' $? kid = Some true -> honestk $? kid = Some true)
    -> honest_nonce_tracking_ok (clean_ciphers honestk cs) honestk' me my_sents my_non
                               you your_froms
                               (clean_messages honestk cs (Some you) your_froms your_msgs).
Proof.
  unfold honest_nonce_tracking_ok; intros; rewrite !Forall_forall in *; intros; split_ands.
  repeat (apply conj); intros; eauto.

  - destruct x; intros; subst.
    eapply clean_messages_list_in_safe in H3; split_ex.
    specialize (H1 _ H3); simpl in H1; eauto.

  - rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H3;
      split_ands.
    eapply H0 in H4.
    specialize (H2 _ _ H3 H4); intuition eauto.
    rewrite Forall_forall in *; intros.
    eapply clean_messages_list_in_safe in H9; split_ex.
    specialize (H10 _ H9); destruct x.

    intros.
    eapply msg_honestly_signed_after_without_cleaning in H12; eauto.
    specialize_simply; split_ors.
    * left; unfold msg_to_this_user, msg_destination_user in *;
        destruct c0; try discriminate.
      unfold msg_signed_addressed in H11; rewrite andb_true_iff in H11; split_ex.
      cases (cs $? c_id0); try discriminate; eauto.
      ** erewrite clean_ciphers_keeps_honest_cipher; eauto.
         unfold honest_cipher_filter_fn, cipher_honestly_signed, msg_honestly_signed, msg_signing_key in *;
           context_map_rewrites; destruct c0; eauto.
      ** rewrite clean_ciphers_no_new_ciphers; eauto.
         
    * right; unfold msg_nonce_not_same in *; intros; eauto.
Qed.

Lemma honest_nonces_unique_after_cleaning :
  forall cs honestk honestk',
    honest_nonces_unique cs honestk
    -> (forall kid, honestk' $? kid = Some true -> honestk $? kid = Some true)
    -> honest_nonces_unique (clean_ciphers honestk cs) honestk'.
Proof.
  unfold honest_nonces_unique; intros.

  eapply clean_ciphers_inv in H2.
  eapply clean_ciphers_inv in H3.

  match goal with
  | [ H : forall _, honestk' $? _ = Some true -> honestk $? _ = Some true |- _ ] =>
    repeat match goal with
           | [ ARG : honestk' $? _ = Some _ |- _ ] => apply H in ARG
           end
  end
  ; context_map_rewrites
  ; eauto.
Qed.

Lemma honest_user_nonces_ok_after_cleaning :
  forall cs honestk honestk' uid sents curn,
    honest_user_nonces_ok cs honestk (Some uid) sents curn
    -> (forall kid, honestk' $? kid = Some true -> honestk $? kid = Some true)
    -> honest_user_nonces_ok (clean_ciphers honestk cs) honestk' (Some uid) sents curn.
Proof.
  unfold honest_user_nonces_ok; intros; split_ex; split; eauto.
Qed.

Hint Resolve
     honest_nonce_tracking_ok_after_cleaning
     honest_user_nonces_ok_after_cleaning
     honest_nonces_unique_after_cleaning : core.

Hint Resolve clean_users_no_change_honestk clean_users_no_change_honestk' : core.

Lemma honest_nonces_ok_after_cleaning :
  forall {A} (usrs : honest_users A) honestk cs,
    honest_nonces_ok cs usrs
    -> honestk = findUserKeys usrs
    -> honest_nonces_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs).
Proof.
  unfold honest_nonces_ok; intros
  ; repeat simple apply conj
  ; intros; subst; split_ex; eauto.

  - eapply clean_users_cleans_user_inv in H1; split_ex.
    eapply H0 in H1; eauto.

  - eapply clean_users_cleans_user_inv in H2; split_ex.
    eapply clean_users_cleans_user_inv in H3; split_ex.
    rewrite H8.
    eapply honest_nonce_tracking_ok_after_cleaning; eauto.
    eapply H4 in H1; eauto; simpl in *; eauto.
Qed.

Lemma honest_nonce_tracking_ok_new_msg :
  forall honestk suid sents cur_n cs froms to_usr qmsgs1 qmsgs2 msg,
    honest_nonce_tracking_ok cs honestk suid sents cur_n to_usr froms (qmsgs1 ++ msg :: qmsgs2)
    -> honest_nonce_tracking_ok cs honestk suid sents cur_n to_usr froms (qmsgs1 ++ qmsgs2).
Proof.
  unfold honest_nonce_tracking_ok; intros; process_nonce_ok.
Qed.

(* TODO tbraje: move this? *)
Lemma msg_honestly_signed_cipher_honestly_signed :
  forall {t} (msg : crypto t) honestk c cs cid,
    msg_honestly_signed honestk cs msg = true
    -> msg_cipher_id msg = Some cid
    -> cs $? cid = Some c
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

Hint Resolve msg_honestly_signed_cipher_honestly_signed : core.

Lemma honest_nonce_tracking_ok_new_read_msg :
  forall honestk suid sents cur_n cs froms to_usr qmsgs qmsgs1 qmsgs2 t (msg : crypto t) cid c,
    honest_nonce_tracking_ok cs honestk suid sents cur_n to_usr froms qmsgs
    -> qmsgs = qmsgs1 ++ existT _ _ msg :: qmsgs2
    -> cs $? cid = Some c
    -> msg = SignedCiphertext cid
    -> count_occ msg_seq_eq froms (cipher_nonce c) = 0
    -> honest_nonces_unique cs honestk
    -> honest_user_nonces_ok cs honestk suid sents cur_n
    -> msg_honestly_signed honestk cs msg = true
    -> honest_nonce_tracking_ok cs honestk suid sents cur_n to_usr (cipher_nonce c :: froms) (qmsgs1 ++ qmsgs2).
Proof.
  unfold honest_nonce_tracking_ok; intros; split_ex; subst.
  repeat simple apply conj; eauto.

  - process_nonce_ok.
    unfold honest_user_nonces_ok in H5.
    eapply H5 in H1; eauto.
  - process_nonce_ok.

  - intros.
    generalize (H8 _ _ H0); intros; specialize_simply; eauto.
    2: process_nonce_ok.
    
    unfold not; intros LIN; simpl in LIN; split_ors; eauto.
    destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
    process_nonce_ok.
    symmetry in H14; generalize H14.
    eapply H4; eauto.
    eapply msg_honestly_signed_cipher_honestly_signed in H1; eauto.
    rewrite <- honest_key_honest_keyb in H1; invert H1; trivial.
Qed.

Hint Resolve
     honest_nonce_tracking_ok_new_msg
     honest_nonce_tracking_ok_new_read_msg
  : core.

Lemma honest_labeled_step_honest_nonces_ok :
  forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
    step_user lbl suid bd bd'
    -> suid = Some u_id
    -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queue_ok honestk cs qmsgs gks
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
  induction 1; inversion 2; inversion 5; intros; subst; try discriminate
  ; eauto
  ; clean_context
  ; split_ex; subst
  ; unfold honest_nonces_ok in *
  ; split_ex; split; intros; subst
  ; autorewrite with find_user_keys in *
  ; eauto.

  - process_nonce_ok; trivial.

  - process_nonce_ok; eauto; simpl in *.
    eapply H4 in H18; eauto; simpl in *; eauto.
    eapply H4 in n; eauto; simpl in *; eauto.

  - process_nonce_ok; eauto.

    subst.
    unfold honest_user_nonces_ok in H3 |- *.
    process_nonce_ok.
    
    eapply H10 in H11; eauto; simpl in *; eauto.
    eapply H10 in H3; eauto; simpl in *; subst; eauto.

    subst; destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction; eauto.
    eapply H10 in n; eauto; simpl in *; subst.
    (* unfold honest_user_nonces_ok in H13; split_ex. *)
    unfold honest_user_nonces_ok in H4; split_ex.
    process_nonce_ok; eauto.

    unfold msg_nonce_not_same
    ; right
    ; intros.
    invert H35; clean_map_lookups.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; process_nonce_ok.
    
    eapply H10 in H3; eauto; simpl in *; subst; eauto.
    process_nonce_ok.
    unfold msg_nonce_not_same
    ; right
    ; intros.
    invert H24; clean_map_lookups.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; process_nonce_ok.
    
    subst; destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction; eauto.
    unfold honest_user_nonces_ok in H14; split_ex.
    eapply H10 in H3; eauto; simpl in *.
    process_nonce_ok.
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
    autorewrite with find_user_keys in *;
    process_nonce_ok; eauto.

  eapply H2 in H3; eauto; simpl in *; eauto.

  eapply H2 in n; eauto; simpl in *; eauto.

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

Hint Resolve nonce_not_in_msg_queue_addnl_cipher : core.

Ltac simply_specialize :=
  repeat
    match goal with
    | [ H : (_ = _) -> _ |- _ ] =>
      specialize (H eq_refl)
    end || specialize_simply1.

Ltac ss :=
  repeat
    match goal with
    | [ |- (?p1,?p2) <> cipher_nonce ?cn ] =>
      let H := fresh "H"
      in  unfold not
          ; intros H
          ; symmetry in H
          ; generalize H
          ; change (cipher_nonce cn <> (p1,p2))
    | [ OK : HNOK ?usrs ?cs
             , NE : ?uid <> ?recid
                    , U1 : ?usrs $? ?uid = Some _
                           , U2 : ?usrs $? ?recid = Some _
                                  , CS : ?cs $? _ = Some ?cn
        |- cipher_nonce ?cn <> (Some ?recid,_) ] =>

      let CN := fresh "CN" in
      let NE := fresh "NE" in
      let SUID := fresh "SUID" in
      let NON := fresh "NON" in
      let EQ := fresh "EQ"
      in idtac "destructing"
         ; destruct OK as [ OK ]
         ; assert (recid <> uid) as NE by congruence
         ; remember (cipher_nonce cn) as CN
         ; destruct CN as [ SUID NON ]
         ; specialize (OK _ _ _ _ NE U2 U1); simpl in OK
         ; unfold honest_nonce_tracking_ok in OK; split_ex
         ; simpl in *
         ; match goal with
           | [ H : forall _ _, ?cs $? _ = Some _ -> _ |- _ ] =>
             specialize (H _ _ CS)
           end

         ; match goal with
           | [ RW : (SUID,NON) = cipher_nonce cn |- _ ] =>
             rewrite <- RW in *
             ; simpl in *
             ; destruct SUID
             ; unfold not; intros EQ; simpl in *
             ; invert EQ
             ; simply_specialize
           end
    | [ OK : HNOK ?usrs ?cs
             , NE : ?recid <> ?uid
                    , U1 : ?usrs $? ?uid = Some _
                           , U2 : ?usrs $? ?recid = Some _
                                  , CS : ?cs $? _ = Some ?cn
        |- cipher_nonce ?cn <> (Some ?recid,_) ] =>

      let CN := fresh "CN" in
      (* let NE := fresh "NE" in *)
      let SUID := fresh "SUID" in
      let NON := fresh "NON" in
      let EQ := fresh "EQ"
      in idtac "destructing2"
         ; destruct OK as [ OK ]
         (* ; assert (recid <> uid) as NE by congruence *)
         ; remember (cipher_nonce cn) as CN
         ; destruct CN as [ SUID NON ]
         ; specialize (OK _ _ _ _ NE U2 U1); simpl in OK
         ; unfold honest_nonce_tracking_ok in OK; split_ex
         ; simpl in *
         ; match goal with
           | [ H : forall _ _, ?cs $? _ = Some _ -> _ |- _ ] =>
             specialize (H _ _ CS)
           end

         ; match goal with
           | [ RW : (SUID,NON) = cipher_nonce cn |- _ ] =>
             rewrite <- RW in *
             ; simpl in *
             ; destruct SUID
             ; unfold not; intros EQ; simpl in *
             ; invert EQ
             ; simply_specialize
           end
    | [ CS : ?cs $? _ = Some ?cn
        |- cipher_nonce ?cn <> (Some ?recid,_) ] =>

      let CN := fresh "CN" in
      let NE := fresh "NE" in
      let SUID := fresh "SUID" in
      let NON := fresh "NON" in
      let EQ := fresh "EQ"
      in  remember (cipher_nonce cn) as CN
          ; destruct CN as [ SUID NON ]
          ; simpl in *
          ; match goal with
            | [ H : forall _ _, ?cs $? _ = Some _ -> _ |- _ ] =>
              specialize (H _ _ CS)
            end

          ; match goal with
            | [ RW : (SUID,NON) = cipher_nonce cn |- _ ] =>
              rewrite <- RW in *
              ; simpl in *
              ; destruct SUID
              ; unfold not; intros EQ; simpl in *
              ; invert EQ
              ; simply_specialize
            end
    end.

Lemma honest_nonces_unique_new_key :
  forall cs honestk gks kid,
    honest_nonces_unique cs honestk
    -> gks $? kid = None
    -> encrypted_ciphers_ok honestk cs gks
    -> honest_nonces_unique cs (honestk $+ (kid,true))
.
Proof.
  unfold honest_nonces_unique; intros.
  process_nonce_ok; eauto.

  encrypted_ciphers_prop; simpl in *; clean_map_lookups.
  encrypted_ciphers_prop; simpl in *; clean_map_lookups.
  clear H4; encrypted_ciphers_prop; simpl in *; clean_map_lookups.
Qed.

Lemma honest_nonce_tracking_ok_new_key :
  forall honestk cs gks uid recuid sents cur_n froms qmsgs kid,
    honest_nonce_tracking_ok cs honestk (Some uid) sents cur_n recuid froms qmsgs
    -> gks $? kid = None
    -> uid <> recuid
    -> encrypted_ciphers_ok honestk cs gks
    -> honest_nonce_tracking_ok cs (honestk $+ (kid,true)) (Some uid) sents cur_n recuid froms qmsgs
.
Proof.
  intros.
  process_nonce_ok; eauto.

  Ltac xy :=
    match goal with
    | [ CS : ?cs $? ?cid = Some ?c, GKS : ?gks $? cipher_signing_key ?c = None,
                                          ECOK : encrypted_ciphers_ok _ ?cs ?gks  |- _ ] =>

      unfold encrypted_ciphers_ok in ECOK
      ; rewrite Forall_natmap_forall in ECOK
      ; specialize (ECOK _ _ CS)
      ; invert ECOK
      ; clean_map_lookups
    end.

  all: try solve [ xy; eauto ].

  - rewrite Forall_forall in H3 |- *; intros.
    specialize (H3 _ H5).
    destruct x; intros; subst.
    process_nonce_ok.
    xy.

  - rewrite Forall_forall in H10 |- *; intros.
    destruct x; intros.
    eapply H10 in H11; eauto.
    unfold msg_honestly_signed, msg_signing_key, honest_keyb in H11, H12
    ; destruct c0; try discriminate
    ; cases (cs $? c_id0); try discriminate.
    destruct (kid ==n cipher_signing_key c0); subst; clean_map_lookups.
    xy.
    cases (honestk $? cipher_signing_key c0); try discriminate
    ; destruct b; try discriminate.
    specialize_simply; eauto.
Qed.

Lemma honest_user_nonces_ok_new_key :
  forall honestk cs gks uid recuid sents cur_n kid,
    honest_user_nonces_ok cs honestk (Some uid) sents cur_n
    -> gks $? kid = None
    -> uid <> recuid
    -> encrypted_ciphers_ok honestk cs gks
    -> honest_user_nonces_ok cs (honestk $+ (kid,true)) (Some uid) sents cur_n
.
Proof.
  unfold honest_user_nonces_ok; intros.
  process_nonce_ok; eauto.
  xy.
Qed.


Hint Resolve
     honest_nonces_unique_new_key
     honest_nonce_tracking_ok_new_key
     honest_user_nonces_ok_new_key
  : core.

Lemma honest_nonces_ok_new_honest_key :
  forall {A} (usrs : honest_users A) k_id cs u_id ks cmd cmd' qmsgs mycs froms sents cur_n gks,
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
    -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
    -> gks $? k_id = None
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
    autorewrite with find_user_keys;
    process_nonce_ok; eauto.

  - generalize H5; intros; eapply H4 in H5; eauto; simpl in *; eauto.
  - generalize H5; intros; eapply H4 in H5; eauto; simpl in *; eauto.
Qed.

Hint Resolve
     honest_nonces_ok_newuser_nochange_froms_sents_msgs
     honest_nonces_ok_new_honest_key
  : core.

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

  Lemma honest_nonces_unique_new_cipher :
    forall cs honestk cid c uid sents cur_n,
      cs $? cid = None
      -> honestk $? cipher_signing_key c = Some true
      -> honest_user_nonces_ok cs honestk (Some uid) sents cur_n
      -> cipher_nonce c = (Some uid, cur_n)
      -> honest_nonces_unique cs honestk
      -> honest_nonces_unique (cs $+ (cid,c)) honestk.
  Proof.
    unfold honest_nonces_unique, honest_user_nonces_ok; intros.
    process_nonce_ok; eauto.
    - rewrite H2 in *.
      remember (cipher_nonce c1) as non
      ; destruct non
      ; simpl in *.
      destruct o; try congruence.
      destruct (u ==n uid); subst; try congruence; specialize_simply.
      unfold not; intros INV; invert INV; Nat.order.
      
    - rewrite H2 in *.
      remember (cipher_nonce c2) as non
      ; destruct non
      ; simpl in *.
      destruct o; try congruence.
      destruct (u ==n uid); subst; try congruence; specialize_simply.
      unfold not; intros INV; invert INV; Nat.order.

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
      -> Forall (fun '(existT _ _ msg) => 
                  forall c_id c,
                    msg = SignedCiphertext c_id
                    -> cs $? c_id = Some c
                    -> honestk $? (cipher_signing_key c) = Some true
                    -> cipher_to_user c = to_usr
                    -> fst (cipher_nonce c) = from_usr
                    -> snd (cipher_nonce c) < cur_n) qmsgs
      -> cur_n <= cur_n'
      -> Forall (fun '(existT _ _ msg) => 
                  forall c_id c,
                    msg = SignedCiphertext c_id
                    -> cs $+ (newcid, newc) $? c_id = Some c
                    -> honestk $? (cipher_signing_key c) = Some true
                    -> cipher_to_user c = to_usr
                    -> fst (cipher_nonce c) = from_usr
                    -> snd (cipher_nonce c) < cur_n') qmsgs.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    destruct x; intros.
    destruct (newcid ==n c_id); subst; clean_map_lookups;
      process_nonce_ok; eauto.

    specialize (H1 _ H3); simpl in H1.
    assert (snd (cipher_nonce c0) < cur_n) by eauto.
    lia.
  Qed.

  Lemma msg_queue_honest_no_dupes_new_cipher :
    forall honestk cs' cs cid c cid' c' (qmsgs : queued_messages) gks,
      Forall
        (fun '(existT _ _ msg) =>
           msg_honestly_signed honestk cs msg = true ->
           msg_to_this_user cs (Some (cipher_to_user c)) msg = false \/ msg_nonce_not_same c cs msg) qmsgs
      -> cs' = cs $+ (cid',c')
      -> cs $? cid = Some c
      -> ~ In cid' cs
      -> honestk $? (cipher_signing_key c) = Some true
      -> message_queue_ok honestk cs qmsgs gks
      -> Forall
          (fun '(existT _ _ msg) =>
             msg_honestly_signed honestk cs' msg = true ->
             msg_to_this_user cs' (Some (cipher_to_user c)) msg = false \/ msg_nonce_not_same c cs' msg) qmsgs.
  Proof.
    intros
    ; rewrite Forall_forall in *; intros
    ; subst
    ; destruct x; intros.

    unfold message_queue_ok in H4
    ; rewrite Forall_forall in H4
    ; specialize (H4 _ H5)
    ; simpl in H4; split_ex
    .

    unfold msg_honestly_signed, msg_signing_key in H0
    ; destruct c0
    ; try discriminate
    ; destruct (c_id ==n cid'); subst
    ; clean_map_lookups
    ; specialize (H6 _ eq_refl)
    ; try contradiction.

    cases (cs $? c_id); clean_map_lookups; eauto.

    assert (msg_honestly_signed honestk cs (@SignedCiphertext t0 c_id) = true) by
        (unfold msg_honestly_signed, msg_signing_key; context_map_rewrites; eauto).

    eapply H in H5; specialize_simply.
    
    unfold msg_to_this_user, msg_destination_user, msg_nonce_not_same in H5 |- *
    ; clean_map_lookups
    ; destruct (cipher_to_user c0 ==n cipher_to_user c)
    ; eauto
    .
    right; split_ors; try discriminate; intros.
    destruct (cid' ==n c_id0); subst; clean_map_lookups; eauto.
    invert H12; eauto.
  Qed.
  
  Hint Resolve
       msg_queue_nonces_good_new_cipher
       msg_queue_honest_no_dupes_new_cipher
       msg_queue_values_ok_new_cipher
       sents_ok_increase_nonce
       froms_ok_increase_nonce
    : core.

  Lemma honest_user_nonces_ok_my_new_cipher :
    forall cs honestk cid c uid sents cur_n,
      cipher_nonce c = (Some uid, cur_n)
      -> honest_user_nonces_ok cs honestk (Some uid) sents cur_n
      -> honest_user_nonces_ok (cs $+ (cid,c)) honestk (Some uid) sents (S cur_n).
  Proof.
    unfold honest_user_nonces_ok; intros.
    process_nonce_ok; eauto.
    rewrite H; eauto.
  Qed.

  Lemma honest_nonce_tracking_ok_my_new_cipher :
    forall cs honestk cid c uid sents cur_n recuid froms qmsgs gks,
      cs $? cid = None
      -> cipher_nonce c = (Some uid, cur_n)
      -> uid <> recuid
      -> message_queue_ok honestk cs qmsgs gks
      -> honest_user_nonces_ok cs honestk (Some uid) sents cur_n
      -> honest_nonce_tracking_ok cs honestk (Some uid) sents cur_n recuid froms qmsgs
      -> honest_nonce_tracking_ok (cs $+ (cid,c)) honestk (Some uid) sents (S cur_n) recuid froms qmsgs.
  Proof.
    unfold honest_nonce_tracking_ok, honest_user_nonces_ok; intros; split_ex.
    process_nonce_ok; eauto.

    - unfold not; intros LIN.
      rewrite H0 in LIN.
      rewrite Forall_forall in H4; eapply H4 in LIN; eauto.
      simpl in *; Nat.order.

    - rewrite Forall_forall; intros.
      destruct x; intros.

      unfold msg_honestly_signed, msg_signing_key in H10
      ; unfold msg_to_this_user, msg_destination_user, msg_nonce_not_same
      ; destruct c; try discriminate
      ; cases (c_id ==n c_id0); subst; clean_map_lookups; try discriminate.

      + right; intros.
        invert H13; clean_map_lookups.
        process_nonce_ok.

      + cases (cs $? c_id0); eauto.
        destruct ( cipher_to_user c ==n cipher_to_user c0 ); eauto.
        right; intros.
        invert H13; clean_map_lookups.

        rewrite H0.
        remember (cipher_nonce c1) as non
        ; destruct non
        ; destruct o; try congruence
        ; destruct (uid ==n u); subst; try congruence.

        pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ H11); split_ex.
        assert (c_id1 = x) by (invert H14; trivial); subst.
        assert (cs $+ (c_id, c0) $? x = Some c1) as CS by (clean_map_lookups; eauto).
        pose proof (msg_honestly_signed_cipher_honestly_signed _ _ _ H11 H14 CS).
        rewrite <- honest_key_honest_keyb in H15; invert H15.
        
        eapply H3 in Heq; eauto.
        unfold not; intros EQ; invert EQ.
        clean_map_lookups.
        rewrite <- Heqnon in Heq
        ; simpl in Heq
        ; Nat.order.
        rewrite <- Heqnon; trivial.
  Qed.

  Lemma honest_user_nonces_ok_new_cipher :
    forall cs honestk cid c sents cur_n cur_n' uid uid',
      cipher_nonce c = (Some uid', cur_n')
      -> uid <> uid'
      -> honest_user_nonces_ok cs honestk (Some uid) sents cur_n
      -> honest_user_nonces_ok (cs $+ (cid,c)) honestk (Some uid) sents cur_n.
  Proof.
    unfold honest_user_nonces_ok; intros.
    process_nonce_ok; eauto.
    rewrite H in H5; simpl in *; congruence.
  Qed.

  Lemma honest_nonce_tracking_ok_new_cipher :
    forall cs honestk cid c sents cur_n cur_n' uid uid' recuid froms qmsgs gks,
      cipher_nonce c = (Some uid', cur_n')
      -> uid <> uid'
      -> uid <> recuid
      -> honest_user_nonces_ok cs honestk (Some uid) sents cur_n
      -> message_queue_ok honestk cs qmsgs gks
      -> honest_nonce_tracking_ok cs honestk (Some uid) sents cur_n recuid froms qmsgs
      -> honest_nonce_tracking_ok (cs $+ (cid,c)) honestk (Some uid) sents cur_n recuid froms qmsgs.
  Proof.
    unfold honest_user_nonces_ok, honest_nonce_tracking_ok; intros; split_ex.
    process_nonce_ok; eauto.

    - rewrite Forall_forall in H5 |- *
      ; intros
      ; destruct x
      ; intros
      ; subst.

      destruct (cid ==n c_id); subst; clean_map_lookups; eauto.
      rewrite H in H13; simpl in *; congruence.

    - rewrite H; unfold not; intros.
      rewrite H in H10; simpl in H10; congruence.

    - rewrite H in H10; simpl in H10; congruence.

    - rewrite Forall_forall in H13 |- *; intros.
      destruct x; intros.
      eapply H13 in H15; eauto.

      unfold msg_honestly_signed, msg_signing_key in H15, H16
      ; unfold msg_to_this_user, msg_destination_user, msg_nonce_not_same
      ; destruct c1; try discriminate
      ; cases (cid ==n c_id0); subst; clean_map_lookups; try discriminate.

      + cases (cipher_to_user c ==n cipher_to_user c0); eauto.
        right; intros.
        invert H17; clean_map_lookups.
        unfold not; intros RW.
        rewrite RW in H10.
        rewrite H in H10; simpl in H10; congruence.

      + cases (cs $? c_id0); eauto.
        destruct ( cipher_to_user c1 ==n cipher_to_user c0 ); eauto.
        right; intros.
        invert H17; clean_map_lookups.
        specialize_simply.
        process_nonce_ok.
  Qed.


  Hint Resolve
       honest_nonces_unique_new_cipher
       honest_user_nonces_ok_my_new_cipher
       honest_nonce_tracking_ok_my_new_cipher
       honest_user_nonces_ok_new_cipher
       honest_nonce_tracking_ok_new_cipher
       findUserKeys_has_private_key_of_user
    : core.

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
        -> encrypted_ciphers_ok honestk cs gks
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
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto; (* clean_context; *)
      msg_queue_prop; process_nonce_ok; eauto.

    - unfold honest_nonces_ok in *; intros;
        simpl in *; subst;
          autorewrite with find_user_keys in *;
          clean_context;
          process_nonce_ok; subst; eauto; simpl in *.

      eapply honest_user_nonces_ok_new_cipher; simpl; eauto.

      generalize H9 ;intros; eapply H8 in H9; eauto; simpl in *; eauto.
      eapply honest_nonce_tracking_ok_new_cipher; simpl; eauto.

      generalize H9 ;intros; eapply H8 in H9; eauto; simpl in *; eauto.

      generalize H9 ;intros; eapply H8 in H9; eauto; simpl in *; eauto.
      eapply honest_nonce_tracking_ok_new_cipher; simpl; eauto.
      
    - user_cipher_queues_prop; encrypted_ciphers_prop.
      unfold honest_nonces_ok in *; intros;
        autorewrite with find_user_keys in *;
        rewrite honestk_merge_new_msgs_keys_dec_same in * by auto;
        process_nonce_ok; eauto.

      eapply H10 in H11; eauto; simpl in *; eauto.
      eapply H10 in H11; eauto; simpl in *; eauto.

    - unfold honest_nonces_ok in *; intros;
        simpl in *; subst;
          autorewrite with find_user_keys in *;
          clean_context;
          process_nonce_ok; subst; eauto; simpl in *.

      eapply honest_user_nonces_ok_new_cipher; simpl; eauto.

      generalize H7 ;intros; eapply H6 in H7; eauto; simpl in *; eauto.
      eapply honest_nonce_tracking_ok_new_cipher; simpl; eauto.

      generalize H7 ;intros; eapply H6 in H7; eauto; simpl in *; eauto.

      generalize H7 ;intros; eapply H6 in H7; eauto; simpl in *; eauto.
      eapply honest_nonce_tracking_ok_new_cipher; simpl; eauto.

      Unshelve.
      all: auto.
  Qed.

  Lemma honest_nonce_tracking_ok_new_adv_cipher :
    forall cs c_id c me my_sents my_n you your_froms your_msgs honestk gks,
      ~ In c_id cs
      -> message_queue_ok honestk cs your_msgs gks
      -> honestk $? cipher_signing_key c <> Some true
      -> honest_nonce_tracking_ok cs honestk (Some me) my_sents my_n you your_froms your_msgs
      -> honest_nonce_tracking_ok (cs $+ (c_id,c)) honestk (Some me) my_sents my_n you your_froms your_msgs.
  Proof.
    unfold honest_nonce_tracking_ok; intros; split_ands;
      repeat (apply conj); eauto
      ; intros
      ; split
      ; process_nonce_ok.

    rewrite Forall_forall in H10 |- *; intros * LIN.
    destruct x; eapply H10 in LIN
    ; intros.
        
    unfold msg_honestly_signed, msg_to_this_user, msg_destination_user, msg_signing_key,
           msg_nonce_not_same in LIN , H11 |- *
    ; destruct c1; eauto.

    destruct (c_id ==n c_id1); subst; clean_map_lookups.

    - destruct (cipher_to_user c ==n cipher_to_user c0); eauto.
      right; intros.
      invert H12.
      rewrite <- honest_key_honest_keyb in H11
      ; invert H11
      ; clean_map_lookups.

    - cases (cs $? c_id1); try discriminate.
      specialize_simply.

      destruct (cipher_to_user c1 ==n cipher_to_user c0); eauto.
      right; intros.
      invert H12; clean_map_lookups.
      process_nonce_ok.

  Qed.

  Hint Resolve
       honest_nonce_tracking_ok_new_adv_cipher
       : core.

  Lemma honest_nonces_ok_adv_new_cipher :
    forall {A} (usrs : honest_users A) cs c_id c gks,
      ~ In c_id cs
      -> message_queues_ok cs usrs gks
      -> (findUserKeys usrs) $? cipher_signing_key c <> Some true
      -> honest_nonces_ok cs usrs
      -> honest_nonces_ok (cs $+ (c_id,c)) usrs.
  Proof.
    unfold honest_nonces_ok; intros; split_ex
    ; repeat simple apply conj; intros; eauto.

    - unfold honest_nonces_unique in *; intros.
      process_nonce_ok; eauto.

    - eapply H3 in H5; eauto.
      unfold honest_user_nonces_ok in *; split_ex; split; eauto.
      intros; process_nonce_ok.
  Qed.

  Hint Resolve honest_nonces_ok_adv_new_cipher : core.

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
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> honest_nonces_ok cs' usrs'.
  Proof.
    induction 1; inversion 1; inversion 13; intros
    ; subst ; eauto
    ; clean_context.

    (* send *)
    - unfold honest_nonces_ok in *
      ; intros; clean_map_lookups
      ; autorewrite with find_user_keys
      ; repeat simple apply conj
      ; eauto
      ; intros.

      + process_nonce_ok.
      + process_nonce_ok; eauto.

        eapply H5 in H6; eauto.
        generalize (H4 _ _ H7); intros.
        unfold honest_user_nonces_ok in H9; split_ex; subst.
        process_nonce_ok; subst; eauto.

        * simpl in *.
          assert (List.In c_id adv.(c_heap)) as LIN by eauto.
          unfold adv_cipher_queue_ok in H29
          ; rewrite Forall_forall in H29
          ; eapply H29 in LIN
          ; split_ex.

          split_ors; split_ex; clean_map_lookups.
          rewrite cipher_honestly_signed_honest_keyb_iff in H17
          ; unfold honest_keyb in H17
          ; context_map_rewrites
          ; discriminate.

          process_nonce_ok; eauto.
          rewrite H22 in H18; invert H18; clean_map_lookups.
          rewrite Forall_forall in H6
          ; eapply H6 in H14
          ; eauto.

          rewrite Exists_exists in H14; split_ex; destruct x3; process_nonce_ok.
          unfold msg_nonce_same in H31.
          unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key
          , msg_to_this_user, msg_destination_user in H27
          ; rewrite andb_true_iff in H27; split_ex
          ; destruct c; try discriminate
          ; cases (cs' $? c_id0); try discriminate
          ; destruct (cipher_to_user c ==n cipher_to_user x); try discriminate.
          specialize (H31 _ _ eq_refl Heq).
          specialize (H4 _ _ H23)
          ; unfold honest_user_nonces_ok in H4
          ; split_ex.
          process_nonce_ok.

        * unfold msg_to_this_user, msg_destination_user, msg_nonce_not_same
          ; destruct msg; eauto
          ; cases (cs' $? c_id0); eauto
          ; destruct (cipher_to_user c0 ==n cipher_to_user c); eauto.

          right; intros.
          invert H17; clean_map_lookups.
          destruct (c_id ==n c_id1); subst; clean_map_lookups; process_nonce_ok.
          ** assert (List.In c_id1 adv.(c_heap)) as LIN by eauto.
             unfold adv_cipher_queue_ok in H29
             ; rewrite Forall_forall in H29
             ; eapply H29 in LIN
             ; split_ex.
             split_ors; split_ex; clean_map_lookups; eauto; exfalso; process_nonce_ok.

             unfold msg_honestly_signed, msg_signing_key in H19
             ; rewrite cipher_honestly_signed_honest_keyb_iff in H24
             ; context_map_rewrites
             ; clean_map_lookups.
             
          ** eapply H; eauto.

    (* encrypt *)
    - eapply honest_nonces_ok_adv_new_cipher; eauto.
      simpl.
      specialize (H33 k__signid); split_ors; context_map_rewrites; congruence.

    (* sign *)
    - eapply honest_nonces_ok_adv_new_cipher; eauto.
      simpl.
      specialize (H31 k_id); split_ors; context_map_rewrites; congruence.
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

      Lemma clean_messages_keeps_hon_signed :
    forall {t} qmsgs (msg : crypto t) honestk cs rec_u_id froms u_id sents n,
      honest_nonce_tracking_ok cs honestk u_id sents n rec_u_id froms qmsgs
      -> honest_user_nonces_ok cs honestk u_id sents n
      -> honest_nonces_unique cs honestk
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

    - unfold clean_messages'; simpl; rewrite H2;
        context_map_rewrites; process_nonce_ok; eauto.
      unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H2; rewrite andb_true_iff in H2;
        context_map_rewrites;
        split_ex.
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

          unfold msg_signed_addressed in Heq
          ; rewrite andb_true_iff in Heq
          ; split_ex.

          generalize (msg_signed_addressed_has_signing_key _ _ _ H3); intros; split_ex.
          unfold msg_signing_key in H8; context_map_rewrites; invert H8.
          invert H11.
          econstructor; process_nonce_ok; eauto.
          
          repeat simple apply conj; eauto.
          intros; split.
          2: process_nonce_ok.

          specialize (H5 _ _ H3); specialize_simply; eauto
          ; invert H13; specialize_simply
          ; eauto.

          unfold msg_to_this_user, msg_destination_user, msg_nonce_not_same in H16
          ; context_map_rewrites.

          unfold not; intros LIN; simpl in LIN; destruct LIN; try contradiction.

          unfold msg_signed_addressed in Heq
          ; rewrite andb_true_iff in Heq
          ; split_ex
          ; specialize_simply.
          
          generalize H11
          ; destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.

          exfalso.
          destruct (cipher_to_user c0 ==n cipher_to_user c0); try contradiction.
          split_ors; try discriminate.
          eapply H3 in Heq1; eauto.

          eapply H1; eauto.
          unfold msg_honestly_signed, msg_signing_key in H13
          ; context_map_rewrites
          ; rewrite <- honest_key_honest_keyb in H13
          ; invert H13
          ; trivial.
          
        * eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.
          
      + eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.
  Qed.
  
