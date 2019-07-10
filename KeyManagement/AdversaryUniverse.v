From Coq Require Import
     List
     Morphisms
     Eqdep
     (* Program.Equality (* for dependent induction *) *)
.

Require Import
        MyPrelude
        Maps
        Common
        MapLtac
        Keys
        Tactics.

Require IdealWorld
        RealWorld.

Set Implicit Arguments.

Lemma accepted_safe_msg_pattern_honestly_signed :
  forall {t} (msg : RealWorld.message t) honestk pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern pat msg
    -> RealWorld.msg_honestly_signed honestk msg = true.
Proof.
  intros.
  destruct msg;
    repeat match goal with
           | [ H : RealWorld.msg_pattern_safe _ _ |- _] => invert H
           | [ H : RealWorld.msg_accepted_by_pattern _ _ |- _] => invert H
           end; simpl; rewrite <- RealWorld.honest_key_honest_keyb; auto.
Qed.

Hint Resolve accepted_safe_msg_pattern_honestly_signed.

(******************** CIPHER CLEANING *********************
 **********************************************************
 *
 * Function to clean ciphehrs and lemmas about it.
 *)

Section CleanCiphers.
  Import RealWorld.

  Variable honestk : key_perms.

  Definition honest_cipher_filter_fn (c_id : cipher_id) (c : cipher) :=
    cipher_honestly_signed honestk c.

  Lemma honest_cipher_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) honest_cipher_filter_fn.
  Proof.
    solve_proper.
  Qed.

  Lemma honest_cipher_filter_fn_filter_proper :
    Proper
      ( eq  ==>  eq  ==>  Equal  ==>  Equal)
      (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn k e then m $+ (k, e) else m).
  Proof.
    unfold Proper, respectful;
      unfold Equal; intros; apply map_eq_Equal in H1; subst; auto.
  Qed.

  Lemma honest_cipher_filter_fn_filter_transpose :
    transpose_neqkey Equal
       (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn k e then m $+ (k, e) else m).
  Proof.
    unfold transpose_neqkey, Equal, honest_cipher_filter_fn, cipher_honestly_signed; intros.
    cases e; cases e'; simpl;
      repeat match goal with
             | [ |- context[if ?cond then _ else _] ] => cases cond
             | [ |- context[_ $+ (?k1,_) $? ?k2] ] => cases (k1 ==n k2); subst; clean_map_lookups
             end; eauto.
  Qed.

  Lemma honest_cipher_filter_fn_filter_proper_eq :
    Proper
      ( eq  ==>  eq  ==>  eq  ==>  eq)
      (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn k e then m $+ (k, e) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_cipher_filter_fn_filter_transpose_eq :
    transpose_neqkey eq
       (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn k e then m $+ (k, e) else m).
  Proof.
    unfold transpose_neqkey, honest_cipher_filter_fn, cipher_honestly_signed; intros.
    cases e; cases e'; subst; simpl;
      repeat match goal with
             | [ |- context[if ?cond then _ else _] ] => cases cond
             | [ |- context[_ $+ (?k1,_) $? ?k2] ] => cases (k1 ==n k2); subst; clean_map_lookups
             end; eauto;
        rewrite map_ne_swap; eauto.
  Qed.

  Definition clean_ciphers (cs : ciphers) :=
    filter honest_cipher_filter_fn cs.

  Hint Resolve
       honest_cipher_filter_fn_proper
       honest_cipher_filter_fn_filter_proper
       honest_cipher_filter_fn_filter_transpose
       honest_cipher_filter_fn_filter_proper_eq
       honest_cipher_filter_fn_filter_transpose_eq.

  Hint Rewrite @findUserKeys_readd_user_same_keys_idempotent'
       using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.
  Hint Rewrite @findUserKeys_readd_user_addnl_keys
       using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.

  Lemma findUserKeys_multi_add_same_keys_idempotent :
    forall {A} (usrs : honest_users A) u_id1 u_id2 ks1 ks2 cmd1 cmd2 qmsgs1 qmsgs2 mycs1 mycs2,
      user_keys usrs u_id1 = Some ks1
      -> user_keys usrs u_id2 = Some ks2
      -> findUserKeys (usrs $+ (u_id1, {| key_heap := ks1; protocol := cmd1; msg_heap := qmsgs1; c_heap := mycs1 |})
                           $+ (u_id2, {| key_heap := ks2; protocol := cmd2; msg_heap := qmsgs2; c_heap := mycs2 |})) = findUserKeys usrs.
  Proof.
    intros.

    cases (u_id1 ==n u_id2); subst; clean_map_lookups.
    - rewrite map_add_eq; eauto.
      autorewrite with find_user_keys; trivial.

    - remember (usrs $+ (u_id1,{| key_heap := ks1; protocol := cmd1; msg_heap := qmsgs1; c_heap := mycs1 |})) as usrs'.
      (* unfold user_keys in H0. *)
      (* destruct (usrs $? u_id2); try discriminate. *)
      (* destruct H0. *)
      autorewrite with find_user_keys; subst; autorewrite with find_user_keys; trivial.
      rewrite add_neq_o; unfold user_keys in *; auto.
  Qed.

  Hint Rewrite @findUserKeys_multi_add_same_keys_idempotent
       using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.

  Lemma clean_ciphers_mapsto_iff : forall cs c_id c,
      MapsTo c_id c (clean_ciphers cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn c_id c = true.
  Proof.
    intros.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_ciphers_keeps_honest_cipher :
    forall c_id c cs,
      cs $? c_id = Some c
      -> honest_cipher_filter_fn c_id c = true
      -> clean_ciphers cs $? c_id = Some c.
  Proof.
    intros.
    rewrite <- find_mapsto_iff.
    rewrite <- find_mapsto_iff in H.
    apply clean_ciphers_mapsto_iff; intuition idtac.
  Qed.

  Lemma honest_key_not_cleaned :
    forall cs c_id c k,
      cs $? c_id = Some c
      -> k = cipher_signing_key c
      -> honest_key honestk k
      -> clean_ciphers cs $? c_id = Some c.
  Proof.
    intros.
    eapply clean_ciphers_keeps_honest_cipher; auto.
    unfold honest_cipher_filter_fn, cipher_honestly_signed.
    cases c; subst; rewrite <- honest_key_honest_keyb; eauto.
  Qed.

  Hint Constructors
       msg_accepted_by_pattern
       msg_contains_only_honest_public_keys.

  Hint Extern 1 (_ $+ (?k, _) $? ?k = Some _) => rewrite add_eq_o.
  Hint Extern 1 (_ $+ (?k, _) $? ?v = _) => rewrite add_neq_o.

  Lemma clean_ciphers_eliminates_dishonest_cipher :
    forall c_id c cs k,
      cs $? c_id = Some c
      -> honest_keyb honestk k = false
      -> k = cipher_signing_key c
      -> clean_ciphers cs $? c_id = None.
  Proof.
    intros; unfold clean_ciphers, filter.
    apply P.fold_rec_bis; intros; eauto.
    cases (honest_cipher_filter_fn k0 e); eauto.
    cases (c_id ==n k0); subst; eauto.
    exfalso.
    rewrite find_mapsto_iff in H2; rewrite H2 in H; invert H.
    unfold honest_cipher_filter_fn, cipher_honestly_signed, cipher_signing_key in *.
    cases c;
      rewrite Heq in H0; invert H0.
  Qed.

  Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher.

  Lemma clean_ciphers_keeps_added_honest_cipher :
    forall c_id c cs,
      honest_cipher_filter_fn c_id c = true
      -> ~ In c_id cs
      -> clean_ciphers (cs $+ (c_id,c)) = clean_ciphers cs $+ (c_id,c).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (c_id ==n y); subst; clean_map_lookups; eauto.
    unfold clean_ciphers, filter; rewrite fold_add; eauto.
    rewrite H; auto.
  Qed.

  Lemma clean_ciphers_reduces_or_keeps_same_ciphers :
    forall c_id c cs,
      cs $? c_id = Some c
      -> ( clean_ciphers  cs $? c_id = Some c
        /\ honest_keyb honestk (cipher_signing_key c) = true)
      \/ ( clean_ciphers cs $? c_id = None
        /\ honest_keyb honestk (cipher_signing_key c) = false).
  Proof.
    intros.
    case_eq (honest_keyb honestk (cipher_signing_key c)); intros; eauto.
    left; intuition idtac.
    eapply clean_ciphers_keeps_honest_cipher; eauto.
    unfold honest_cipher_filter_fn, cipher_signing_key in *.
    cases c; eauto.
  Qed.

  Lemma clean_ciphers_no_new_ciphers :
    forall c_id cs,
      cs $? c_id = None
      -> clean_ciphers cs $? c_id = None.
  Proof.
    intros.
    unfold clean_ciphers, filter.
    apply P.fold_rec_bis; intros; eauto.
    cases (honest_cipher_filter_fn k e); eauto.
    - case (c_id ==n k); intro; subst; unfold honest_cipher_filter_fn.
      + rewrite find_mapsto_iff in H0; rewrite H0 in H; invert H.
      + rewrite add_neq_o; eauto.
  Qed.

  Hint Resolve clean_ciphers_no_new_ciphers.

  Lemma clean_ciphers_eliminates_added_dishonest_cipher :
    forall c_id c cs k,
      cs $? c_id = None
      -> honest_keyb honestk k = false
      -> k = cipher_signing_key c
      -> clean_ciphers cs = clean_ciphers (cs $+ (c_id,c)).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n c_id); subst.
    - rewrite clean_ciphers_no_new_ciphers; auto.
      symmetry.
      eapply clean_ciphers_eliminates_dishonest_cipher; eauto.
    - unfold clean_ciphers at 2, filter.
      rewrite fold_add; auto. simpl.
      unfold honest_cipher_filter_fn at 1.
      cases c; simpl in *; rewrite H0; trivial.
  Qed.

  Lemma not_in_ciphers_not_in_cleaned_ciphers :
    forall c_id cs,
      ~ In c_id cs
      -> ~ In c_id (clean_ciphers cs).
  Proof.
    intros.
    rewrite not_find_in_iff in H.
    apply not_find_in_iff; eauto.
  Qed.

  Hint Resolve not_in_ciphers_not_in_cleaned_ciphers.

  Lemma dishonest_cipher_cleaned :
    forall cs c_id cipherMsg,
      honest_keyb honestk (cipher_signing_key cipherMsg) = false
      -> ~ In c_id cs
      -> clean_ciphers cs = clean_ciphers (cs $+ (c_id, cipherMsg)).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.

    case_eq (cs $? y); intros.

    - eapply clean_ciphers_reduces_or_keeps_same_ciphers in H1.
      destruct H1; destruct H1;
        rewrite H1;
        unfold clean_ciphers, filter;
        rewrite fold_add by auto;
        symmetry;
        unfold honest_cipher_filter_fn; cases cipherMsg; simpl in *;
          rewrite H; simpl; auto.

    - rewrite clean_ciphers_no_new_ciphers; auto.
      eapply clean_ciphers_no_new_ciphers in H1.
      unfold clean_ciphers, filter. rewrite fold_add by auto.
      unfold honest_cipher_filter_fn; cases cipherMsg; simpl in *; rewrite H; eauto.
  Qed.

  Hint Resolve dishonest_cipher_cleaned.

  Hint Extern 1 (honest_cipher_filter_fn _ _ ?c = _) => unfold honest_cipher_filter_fn; cases c.

  Lemma clean_ciphers_added_honest_cipher_not_cleaned :
    forall cs c_id c k,
      honest_key honestk k
      -> k = cipher_signing_key c
      -> clean_ciphers (cs $+ (c_id,c)) = clean_ciphers cs $+ (c_id,c).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.

    case (y ==n c_id); intros; subst; clean_map_lookups.
    - erewrite clean_ciphers_keeps_honest_cipher; auto.
      invert H; unfold honest_cipher_filter_fn; eauto.
      unfold cipher_honestly_signed, honest_keyb;
        cases c; simpl in *; context_map_rewrites; auto.
    - case_eq (clean_ciphers cs $? y); intros; subst.
      + cases (cs $? y); subst; eauto.
        * assert (cs $? y = Some c1) by assumption;
            eapply clean_ciphers_reduces_or_keeps_same_ciphers in Heq; split_ors;
              split_ands; subst; contra_map_lookup.
          eapply clean_ciphers_keeps_honest_cipher; auto.
          unfold honest_cipher_filter_fn, cipher_honestly_signed;
            cases c1; simpl in *; auto.
        * exfalso; eapply clean_ciphers_no_new_ciphers in Heq; contra_map_lookup.
      + case_eq (cs $? y); intros; subst; eauto.
        eapply clean_ciphers_eliminates_dishonest_cipher; eauto.
        case_eq (honest_keyb honestk (cipher_signing_key c0)); intros; subst; auto.
        exfalso; eapply clean_ciphers_keeps_honest_cipher in H1; contra_map_lookup; auto.
        unfold honest_cipher_filter_fn, cipher_honestly_signed;
          cases c0; simpl in *; auto.
  Qed.

  Lemma clean_ciphers_idempotent :
    forall cs,
      ciphers_honestly_signed honestk cs
      -> clean_ciphers cs = cs.
  Proof.
    unfold clean_ciphers, filter, ciphers_honestly_signed; intros.
    apply P.fold_rec_bis; intros; Equal_eq; subst; eauto.
    unfold honest_cipher_filter_fn.
    rewrite find_mapsto_iff in H0.
    assert (cipher_honestly_signed honestk e = true).
    eapply Forall_natmap_in_prop with (P := fun c => cipher_honestly_signed honestk c = true); eauto.
    rewrite H2; trivial.
  Qed.

  Lemma clean_ciphers_honestly_signed :
    forall cs,
      ciphers_honestly_signed honestk (clean_ciphers cs).
  Proof.
    unfold ciphers_honestly_signed; intros.
    rewrite Forall_natmap_forall; intros.
    rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff in H; split_ands.
    unfold honest_cipher_filter_fn in *; assumption.
  Qed.

End CleanCiphers.

(******************** MESSAGE CLEANING ********************
 **********************************************************
 *
 * Function to clean messages and lemmas about it.
 *)

Section CleanMessages.
  Import RealWorld.

  Section CleanMessagesImpl.
    Variable honestk : key_perms.
    Variable msgs : queued_messages.

    Definition msg_filter (sigM : { t & message t } ) : bool :=
      match sigM with
      | existT _ _ msg => msg_honestly_signed honestk msg
      end.

    Definition clean_messages :=
      List.filter msg_filter.

  End CleanMessagesImpl.

  Lemma clean_messages_keeps_honestly_signed :
    forall {t} (msg : message t) honestk msgs,
      msg_honestly_signed honestk msg = true
      -> clean_messages honestk (msgs ++ [existT _ _ msg])
        = clean_messages honestk msgs ++ [existT _ _ msg].
  Proof.
    intros; unfold clean_messages.
    induction msgs; simpl; eauto.
    - rewrite H; trivial.
    - cases (msg_filter honestk a); subst; eauto.
      rewrite IHmsgs; trivial.
  Qed.

  Lemma clean_messages_drops_not_honestly_signed :
    forall {t} (msg : message t) msgs honestk,
      msg_honestly_signed honestk msg = false
      -> clean_messages honestk (msgs ++ [existT _ _ msg])
        = clean_messages honestk msgs.
  Proof.
    intros; unfold clean_messages.
    induction msgs; simpl; eauto.
    - rewrite H; trivial.
    - cases (msg_filter honestk a); subst; eauto.
      rewrite IHmsgs; trivial.
  Qed.

  Lemma clean_message_keeps_safely_patterned_message :
    forall {t} (msg : message t) honestk msgs pat,
      msg_pattern_safe honestk pat
      -> msg_accepted_by_pattern pat msg
      -> clean_messages honestk (existT _ _ msg :: msgs)
        = (existT _ _ msg) :: clean_messages honestk msgs.
  Proof.
    intros.
    assert (msg_honestly_signed honestk msg = true) by eauto.
    unfold clean_messages; simpl;
      match goal with
      | [ H : msg_honestly_signed _ _ = _ |- _ ] => rewrite H
      end; trivial.
  Qed.

  Lemma clean_messages_idempotent :
    forall msgs honestk,
      clean_messages honestk (clean_messages honestk msgs) = clean_messages honestk msgs.
  Proof.
    induction msgs; intros; eauto.
    simpl.
    case_eq (msg_filter honestk a); intros; eauto.
    simpl; rewrite H; auto.
    rewrite IHmsgs; trivial.
  Qed.

End CleanMessages.

(******************** USER CLEANING ***********************
 **********************************************************
 *
 * Function to clean users and lemmas about it.
 *)

Section CleanUsers.
  Import RealWorld.

  Variable honestk : key_perms.

  Definition clean_users {A} (usrs : honest_users A) :=
    map (fun u_d => {| key_heap := u_d.(key_heap)
                  ; protocol := u_d.(protocol)
                  ; msg_heap := clean_messages honestk u_d.(msg_heap)
                  ; c_heap   := u_d.(c_heap) |}) usrs.

  Lemma clean_users_cleans_user :
    forall {A} (usrs : honest_users A) u_id u_d u_d',
      usrs $? u_id = Some u_d
      -> u_d' = {| key_heap := u_d.(key_heap)
                ; protocol := u_d.(protocol)
                ; msg_heap :=  clean_messages honestk u_d.(msg_heap)
                ; c_heap   := u_d.(c_heap) |}
      -> clean_users usrs $? u_id = Some u_d'.
  Proof.
    intros.
    unfold clean_users; rewrite map_o; unfold option_map;
      context_map_rewrites; subst; auto.
  Qed.

  Lemma clean_users_cleans_user_inv :
    forall {A} (usrs : honest_users A) u_id u_d,
      clean_users usrs $? u_id = Some u_d
      -> exists msgs, usrs $? u_id = Some {| key_heap := u_d.(key_heap)
                                     ; protocol := u_d.(protocol)
                                     ; msg_heap := msgs
                                     ; c_heap   := u_d.(c_heap) |}
                /\ u_d.(msg_heap) = clean_messages honestk msgs.
  Proof.
    intros.
    unfold clean_users in *. rewrite map_o in H. unfold option_map in *.
    cases (usrs $? u_id); try discriminate; eauto.
    destruct u; destruct u_d; simpl in *.
    invert H.
    eexists; eauto.
  Qed.

  Lemma clean_users_add_pull :
    forall {A} (usrs : honest_users A) u_id u,
      clean_users (usrs $+ (u_id,u))
      = clean_users usrs $+ (u_id, {| key_heap := u.(key_heap)
                                    ; protocol := u.(protocol)
                                    ; msg_heap :=  clean_messages honestk u.(msg_heap)
                                    ; c_heap   := u.(c_heap) |}).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n u_id); subst; clean_map_lookups; eauto;
      unfold clean_users; rewrite !map_o; unfold option_map; clean_map_lookups; auto.
  Qed.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

  Lemma clean_users_no_change_findUserKeys :
    forall {A} (usrs : honest_users A),
      findUserKeys (clean_users usrs) = findUserKeys usrs.
  Proof.
    induction usrs using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; auto.
    unfold findUserKeys.
    rewrite fold_add; auto.
    rewrite clean_users_add_pull; auto. simpl.
    apply map_eq_Equal; unfold Equal; intros.
    rewrite !fold_add; auto. simpl.
    rewrite !findUserKeys_notation, IHusrs; trivial.

    unfold not; intros.
    apply map_in_iff in H0; contradiction.
  Qed.

  Lemma clean_users_idempotent :
    forall {A} (usrs : honest_users A),
      clean_users (clean_users usrs) = clean_users usrs.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    case_eq (clean_users usrs $? y); intros.
    - destruct u; simpl in *; eapply clean_users_cleans_user; eauto; simpl.
      apply clean_users_cleans_user_inv in H.
      destruct H; split_ands; simpl in *; eauto.
      f_equal; subst; eauto using clean_messages_idempotent.
    - unfold clean_users in *.
      rewrite map_o in H; unfold option_map in H; cases (usrs $? y); try discriminate.

      rewrite !map_o, Heq; trivial.
  Qed.

End CleanUsers.

(******************** KEYS CLEANING ***********************
 **********************************************************
 *
 * Function to clean keys and lemmas about it.
 *)

Section CleanKeys.
  Import RealWorld.

  Variable honestk : key_perms.

  Definition honest_key_filter_fn (k_id : key_identifier) (k : key) :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Definition clean_keys :=
    filter honest_key_filter_fn.

  Lemma honest_key_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) honest_key_filter_fn.
  Proof.
    solve_proper.
  Qed.

  Hint Resolve honest_key_filter_fn_proper.

  Lemma honest_key_filter_fn_filter_proper :
    Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_key_filter_fn k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_key_filter_fn_filter_transpose :
    transpose_neqkey eq (fun k v m => if honest_key_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey; intros.
    unfold honest_key_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Lemma honest_key_filter_fn_filter_proper_Equal :
    Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_key_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    destruct (honest_key_filter_fn y y0); eauto.
    destruct (y ==n y2); subst; clean_map_lookups; auto.
  Qed.

  Lemma honest_key_filter_fn_filter_transpose_Equal :
    transpose_neqkey Equal (fun k v m => if honest_key_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal; intros.
    unfold honest_key_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Hint Resolve honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal.

  Lemma clean_keys_inv :
    forall k_id k ks,
      clean_keys ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_key_filter_fn k_id k = true.
  Proof.
    unfold clean_keys; intros until ks.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_keys_keeps_honest_key :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn k_id k = true
      -> clean_keys ks $? k_id = Some k.
  Proof.
    unfold clean_keys; intros.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
    rewrite find_mapsto_iff; eauto.
  Qed.

  Lemma clean_keys_adds_no_keys :
    forall k_id ks,
        ks $? k_id = None
      -> clean_keys ks $? k_id = None.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
    unfold clean_keys, filter; rewrite fold_add; eauto.
    destruct (x ==n k_id); subst; clean_map_lookups.
    destruct (honest_key_filter_fn x e); eauto.
    clean_map_lookups; eauto.
  Qed.

  Lemma clean_keys_idempotent :
    forall ks,
      clean_keys (clean_keys ks) = clean_keys ks.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (clean_keys ks $? y); eauto using clean_keys_adds_no_keys.
    eapply clean_keys_keeps_honest_key; auto.
    apply clean_keys_inv in Heq; split_ands; auto.
  Qed.

End CleanKeys.


Section StripAdv.
  Import RealWorld.

  Definition strip_adversary_univ {A B} (U__r : universe A B) (b : B) : universe A B :=
    let honestk := findUserKeys U__r.(users)
    in {| users       := clean_users honestk U__r.(users)
          ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                            ; protocol := Return b
                            ; msg_heap := U__r.(adversary).(msg_heap)
                            ; c_heap   := U__r.(adversary).(c_heap) |}
        ; all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
        ; all_keys    := clean_keys honestk U__r.(all_keys)
       |}.

  Definition strip_adversary {A B} (U__r : universe A B) : simpl_universe A :=
    let honestk := findUserKeys U__r.(users)
    in {| s_users       := clean_users honestk U__r.(users)
        ; s_all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
        ; s_all_keys    := clean_keys honestk U__r.(all_keys)
       |}.

  Definition strip_adversary_simpl {A} (U__r : simpl_universe A) : simpl_universe A :=
    let honestk := findUserKeys U__r.(s_users)
    in {| s_users       := clean_users honestk U__r.(s_users)
        ; s_all_ciphers := clean_ciphers honestk U__r.(s_all_ciphers)
        ; s_all_keys    := clean_keys honestk U__r.(s_all_keys)
       |}.


  Lemma peel_strip_univ_eq_strip_adv :
    forall A B (U : universe A B) b,
      peel_adv (strip_adversary_univ U b) = strip_adversary U.
  Proof.
    unfold peel_adv, strip_adversary, strip_adversary_univ; trivial.
  Qed.

End StripAdv.
