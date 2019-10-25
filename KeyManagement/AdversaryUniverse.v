
From Coq Require Import
     List
     Morphisms
     Eqdep
     (* Program.Equality (* for dependent induction *) *)
.

Require Import
        MyPrelude
        Maps
        Messages
        Common
        MapLtac
        Keys
        Automation
        Tactics.

Require IdealWorld
        RealWorld.

Set Implicit Arguments.

Lemma accepted_safe_msg_pattern_msg_filter_true :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true
    /\ RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros.
  destruct msg;
    repeat match goal with
           | [ H : RealWorld.msg_pattern_safe _ _ |- _] => invert H
           | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ |- _] => invert H
           end;
    unfold RealWorld.msg_honestly_signed, RealWorld.msg_to_this_user;
    simpl; context_map_rewrites; unfold RealWorld.cipher_to_user;
      destruct (msg_to0 ==n msg_to0); subst; try contradiction;
      rewrite <- RealWorld.honest_key_honest_keyb; auto.
Qed.

Lemma accepted_safe_msg_pattern_honestly_signed :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Lemma accepted_safe_msg_pattern_to_this_user :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Hint Resolve
     accepted_safe_msg_pattern_honestly_signed
     accepted_safe_msg_pattern_to_this_user.

(******************** CIPHER CLEANING *********************
vvv **********************************************************
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

  Lemma honest_key_not_cleaned : forall cs c_id c k,
      cs $? c_id = Some c
      -> k = cipher_signing_key c
      -> honest_key honestk k
      -> clean_ciphers cs $? c_id = Some c.
  Proof.
    intros.
    eapply clean_ciphers_keeps_honest_cipher; auto.
    unfold honest_cipher_filter_fn, cipher_honestly_signed.
    destruct c; subst.
    + invert H. rewrite <- honest_key_honest_keyb; eauto.
    + invert H. rewrite <- honest_key_honest_keyb; eauto.
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
    cases c; rewrite H0 in Heq; invert Heq. 
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
    forall c_id c cs k,
      cs $? c_id = Some c
      -> cipher_signing_key c = k
      -> ( clean_ciphers  cs $? c_id = Some c
        /\ honest_keyb honestk k = true)
      \/ ( clean_ciphers cs $? c_id = None
        /\ honest_keyb honestk k = false).
  Proof.
    intros.
    case_eq (honest_keyb honestk k); intros; eauto.
    left; intuition idtac.
    eapply clean_ciphers_keeps_honest_cipher; eauto.
    unfold honest_cipher_filter_fn, cipher_signing_key in *.
    cases c; try invert H0; eauto.
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
      cases c; simpl in *; try invert H1; rewrite H0; trivial.
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
    forall cs c_id cipherMsg k,
      cipher_signing_key cipherMsg = k
      -> honest_keyb honestk k = false
      -> ~ In c_id cs
      -> clean_ciphers cs = clean_ciphers (cs $+ (c_id, cipherMsg)).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    case_eq (cs $? y); intros; simpl in *.
    - eapply clean_ciphers_reduces_or_keeps_same_ciphers in H2; eauto.
      split_ors; split_ands;
        unfold clean_ciphers, filter; rewrite fold_add by auto;
          unfold honest_cipher_filter_fn; cases cipherMsg; invert H; simpl in *; rewrite H0; reflexivity.
    - rewrite clean_ciphers_no_new_ciphers; auto. eapply clean_ciphers_no_new_ciphers in H2.
      unfold clean_ciphers, filter. rewrite fold_add by auto.
      unfold honest_cipher_filter_fn; cases cipherMsg; invert H; simpl in *; rewrite H0; eauto. 
  Qed.

  Hint Resolve dishonest_cipher_cleaned.

  Hint Extern 1 (honest_cipher_filter_fn _ ?c = _) => unfold honest_cipher_filter_fn; cases c.

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
        cases c; simpl in *; context_map_rewrites; auto; invert H0; rewrite H1; trivial.
    - case_eq (clean_ciphers cs $? y); intros; subst;
        cases (cs $? y); subst; eauto.
        * assert (cs $? y = Some c1) as CSY by assumption;
            eapply clean_ciphers_reduces_or_keeps_same_ciphers in CSY; eauto;
              split_ors; split_ands;
                clean_map_lookups.
          eapply clean_ciphers_keeps_honest_cipher; eauto.
        * exfalso; eapply clean_ciphers_no_new_ciphers in Heq; contra_map_lookup.
        * assert (cs $? y = Some c0) as CSY by assumption;
            eapply clean_ciphers_reduces_or_keeps_same_ciphers in CSY; eauto;
              split_ors; split_ands; contra_map_lookup; eauto.
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
    Variable cs : ciphers.
    (* Variable msgs : queued_messages. *)

    (* Definition msg_nonce_ok {t} (froms : recv_nonces) (msg : crypto t) : bool * recv_nonces := *)
    (*   match msg with *)
    (*   | Content _ => (true, froms) *)
    (*   | SignedCiphertext c_id => *)
    (*     match cs $? c_id with *)
    (*     | None => (false, froms) *)
    (*     | Some c => *)
    (*       let nonce := cipher_nonce c in *)
    (*       let kid   := cipher_signing_key c *)
    (*       in  match froms $? kid with *)
    (*           | None => (true, froms $+ (kid, nonce)) *)
    (*           | Some nonce' => *)
    (*             match nonce ?= nonce' with *)
    (*             | Eq => (false, froms) *)
    (*             | Lt => (false, froms) *)
    (*             | Gt => (true, froms $+ (kid,nonce)) *)
    (*             end *)
    (*           end *)
    (*     end *)
    (*   end. *)
    Definition msg_nonce_ok {t} (froms : recv_nonces) (msg : crypto t) : option recv_nonces :=
      match msg with
      | Content _ => Some froms
      | SignedCiphertext c_id =>
        match cs $? c_id with
        | None => None
        | Some c =>
          let msg_nonce := cipher_nonce c in
          let msg_kid   := cipher_signing_key c
          in  match froms $? msg_kid with
              | None => Some (froms $+ (msg_kid, msg_nonce))
              | Some froms_nonce => if msg_nonce <=? froms_nonce then None else Some (froms $+ (msg_kid,msg_nonce))
                (* match nonce ?= nonce' with *)
                (* | Eq => None *)
                (* | Lt => None *)
                (* | Gt => Some (froms $+ (kid,nonce)) *)
                (* end *)
              end
        end
      end.

    Definition msg_signed_addressed (to_user_id : option user_id) {t} (msg : crypto t) :=
      msg_honestly_signed honestk cs msg && msg_to_this_user cs to_user_id msg.

    Definition msg_filter
               (to_user_id : option user_id) 
               (fld_param : queued_messages * recv_nonces)
               (sigM : { t & crypto t } ) : queued_messages * recv_nonces :=
      match sigM with
      | existT _ _ msg =>
        if msg_signed_addressed to_user_id msg
        then match msg_nonce_ok (snd fld_param) msg with
             | None => fld_param
             | Some froms => (fst fld_param ++ [sigM], froms)
             end
        else fld_param
      end.

    Definition clean_messages' (to_usr_id : option user_id) (froms : recv_nonces) (acc msgs : queued_messages) :=
      List.fold_left (msg_filter to_usr_id) msgs (acc, froms).

    Definition clean_messages (to_usr_id : option user_id) (froms : recv_nonces) (msgs : queued_messages) :=
      fst (clean_messages' to_usr_id froms [] msgs).

    Definition nonce_absent_or_gt (froms : recv_nonces) (k_id : key_identifier) (nonce : nat) := 
      froms $? k_id = None
      \/ (exists n, froms $? k_id = Some n /\ n < nonce).
            (* match nonce ?= n with *)
            (* | Gt => True *)
            (* | _  => False *)
            (* end ). *)

    (* Definition msg_not_replayed' {t} (msg : crypto t) (froms : recv_nonces) := *)
    (*   forall c_id c nonce k_id, *)
    (*       msg = SignedCiphertext c_id *)
    (*     -> cs $? c_id = Some c *)
    (*     -> cipher_nonce c = nonce *)
    (*     -> cipher_signing_key c = k_id *)
    (*     -> nonce_absent_or_gt froms k_id nonce. *)

    Definition overlapping_msg_nonce_smaller (new_cipher : cipher) (cs : ciphers) {t} (msg : crypto t) : Prop :=
      forall c_id c,
        msg = SignedCiphertext c_id
        -> cs $? c_id = Some c
        -> cipher_signing_key c = cipher_signing_key new_cipher
        -> cipher_nonce c < cipher_nonce new_cipher.


    Definition msg_not_replayed {t} (froms : recv_nonces) (msg : crypto t) (msgs : queued_messages) : Prop :=
      exists c_id c,
        msg = SignedCiphertext c_id
      /\ cs $? c_id = Some c
      /\ nonce_absent_or_gt froms (cipher_signing_key c) (cipher_nonce c)
      /\ Forall (fun sigM => match sigM with existT _ _ m => overlapping_msg_nonce_smaller c cs m end) msgs.
      (* /\ Forall (fun sigM => match sigM with existT _ _ m => msg_not_replayed' m froms end) msgs. *)

    (* Definition list_contains (mycs : my_ciphers) (c_id : cipher_id) : bool := *)
    (*   match count_occ eq_nat_dec mycs c_id with *)
    (*   | 0 => false *)
    (*   | _ => true *)
    (*   end. *)

    (* Definition msg_cipher_has_been_seen {t} (mycs : my_ciphers) (msg : crypto t) : bool := *)
    (*   match msg_cipher_id msg with *)
    (*   | Some c_id => list_contains mycs c_id *)
    (*   | None      => false (* not filtering non-cipher messages *) *)
    (*   end. *)

    (* Definition msg_filter (to_usr_id : option user_id) (mycs : my_ciphers) (sigM : { t & crypto t } ) : bool := *)
    (*   match sigM with *)
    (*   | existT _ _ msg => msg_honestly_signed honestk cs msg *)
    (*                   && msg_to_this_user cs to_usr_id msg *)
    (*                   && msg_cipher_has_been_seen mycs msg *)
    (*   end. *)

    (* Definition clean_messages (to_usr_id : option user_id) (mycs : my_ciphers) := *)
    (*   List.filter (msg_filter to_usr_id mycs). *)

  End CleanMessagesImpl.

  Lemma msg_honestly_signed_after_without_cleaning :
    forall {t} (msg : crypto t) honestk cs,
      msg_honestly_signed honestk (clean_ciphers honestk cs) msg = true
      -> msg_honestly_signed honestk cs msg = true.
  Proof.
    intros.
    unfold msg_honestly_signed in *.
    cases (msg_signing_key (clean_ciphers honestk cs) msg); try discriminate.
    unfold msg_signing_key in *; destruct msg; try discriminate.
    - cases (clean_ciphers honestk cs $? c_id); try discriminate.
      rewrite <- find_mapsto_iff in Heq0; rewrite clean_ciphers_mapsto_iff in Heq0; rewrite find_mapsto_iff in Heq0; split_ands.
      rewrite H0; destruct c; try discriminate; eauto.
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

  Hint Resolve
       msg_to_this_user_before_after_cleaning
       msg_honestly_signed_after_without_cleaning
       msg_honestly_signed_before_after_cleaning
       msg_honestly_signed_before_after_cleaning'.

  Lemma message_not_replayed_addnl_destruct :
    forall {t1 t2} (msg1 : crypto t1) (msg2 : crypto t2) cs froms msgs,
      msg_not_replayed cs froms msg1 (existT _ _ msg2 :: msgs)
      -> msg_not_replayed cs froms msg1 msgs.
  Proof.
    intros.
    unfold msg_not_replayed in *; intros; split_ex; split_ands; subst; eauto.
    invert H2; eauto 8.
  Qed.

  Hint Resolve message_not_replayed_addnl_destruct.

  Lemma message_nonce_ok_no_replay :
    forall {t} (msg : crypto t) cs c_id c honestk nonce froms,
      nonce_absent_or_gt froms (cipher_signing_key c) nonce
      -> cipher_nonce c = nonce
      -> msg_cipher_id msg = Some c_id
      -> msg_honestly_signed honestk cs msg = true
      -> cs $? c_id = Some c
      -> msg_nonce_ok cs froms msg = Some (froms $+ (cipher_signing_key c, cipher_nonce c)).
  Proof.
    unfold msg_nonce_ok; intros.
    unfold msg_cipher_id, msg_honestly_signed in *; destruct msg; try discriminate.
    invert H1; context_map_rewrites.
    unfold nonce_absent_or_gt in *; split_ors; split_ex; split_ands; context_map_rewrites; auto.
    cases (cipher_nonce c <=? x); eauto.
    Nat.order.
  Qed.

  Lemma message_not_replayed_cons_split :
    forall {t} (msg : crypto t) cs froms m msgs,
      msg_not_replayed cs froms msg (m :: msgs)
      -> msg_not_replayed cs froms msg msgs.
  Proof.
    unfold msg_not_replayed; intros; split_ex; split_ands; eauto.
    invert H2; eauto 8.
  Qed.

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

  Hint Resolve message_not_replayed_cons_split.

  Ltac message_cleaning :=
    repeat
      match goal with
      | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] => apply andb_prop in H; split_ands
      | [ MHS : msg_honestly_signed _ _ _ = true, MNOK : msg_nonce_ok _ _ _ = _ |- _ ] =>
        unfold msg_nonce_ok, msg_honestly_signed in MHS, MNOK
      | [ H : match ?c with | Content _ => _ | _ => _ end = _ |- _ ] => destruct c; try discriminate
      | [ H : match ?cs $? ?cid with _ => _ end = _ |- _ ] => cases (cs $? cid); try discriminate
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


  Lemma clean_messages_adds_no_nonces :
    forall honestk cs to_usr k_id msgs froms acc,
      snd (clean_messages' honestk cs to_usr froms acc msgs) $? k_id = None
      -> froms $? k_id = None
      /\ Forall (fun sigM => match sigM with
                         | existT _ _ msg =>
                           msg_signed_addressed honestk cs to_usr msg = true -> msg_signing_key cs msg <> Some k_id
                         end) msgs.
  Proof.
    unfold clean_messages'; induction msgs; intros; eauto.
    destruct a; simpl in *; message_cleaning.
  Qed.

  Lemma clean_messages_froms_nonce_in_folds_correct :
    forall honestk cs to_usr msgs k_id froms acc froms_non final_non,
      froms $? k_id = Some froms_non
      -> snd (clean_messages' honestk cs to_usr froms acc msgs) $? k_id = Some final_non
      -> ( froms_non = final_non
        /\ Forall (fun sigM => match sigM with
                           | existT _ _ msg => msg_signed_addressed honestk cs to_usr msg = true
                                            -> msg_signing_key cs msg = Some k_id
                                            -> exists c_id c, msg_cipher_id msg = Some c_id
                                                      /\ cs $? c_id = Some c
                                                      /\ cipher_nonce c <= final_non
                           end) msgs)
      \/ ( froms_non < final_non 
        /\ Exists (fun sigM => match sigM with
                           | existT _ _ msg => msg_signed_addressed honestk cs to_usr msg = true
                                            /\ msg_signing_key cs msg = Some k_id
                                            /\ exists c_id c, msg_cipher_id msg = Some c_id
                                                      /\ cs $? c_id = Some c
                                                      /\ cipher_nonce c = final_non
                           end)
                 msgs).
  Proof.
    unfold clean_messages'; induction msgs; intros; simpl in *; clean_map_lookups; eauto.

    destruct a.
    unfold msg_filter at 2 in H0.
    cases (msg_signed_addressed honestk cs to_usr c); simpl in *.
    - cases (msg_nonce_ok cs froms c).
      + message_cleaning;
          destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups.
        * assert (froms $+ (cipher_signing_key c, cipher_nonce c) $? cipher_signing_key c = Some (cipher_nonce c))
            as FROMS by (clean_map_lookups; trivial).
          specialize (IHmsgs _ _ _ _ _ FROMS H0); split_ors; split_ands; eauto.
          ** cases (@msg_signing_key t0 cs (SignedCiphertext c_id)); try discriminate; subst.
             right; intuition eauto.
             econstructor; intros; simpl; context_map_rewrites; unfold msg_signed_addressed; intuition eauto.
             rewrite andb_true_iff; split; auto.
             unfold msg_honestly_signed.
             rewrite Heq0; auto.
             
          ** right; intuition eauto.
             apply Exists_exists in H4; split_ex; split_ands; destruct x; split_ands; split_ex; split_ands; subst.
             Nat.order.

        * assert (froms $+ (cipher_signing_key c, cipher_nonce c) $? k_id = Some froms_non)
            as FROMS by (clean_map_lookups; trivial).
          specialize (IHmsgs _ _ _ _ _ FROMS H0); split_ors; split_ands; subst; eauto.
          left; intuition idtac; econstructor; eauto; intros; simpl.
          repeat eexists; eauto.
          unfold msg_signing_key in H5; context_map_rewrites; clean_context.
          Nat.order.
          
        * assert (froms $+ (cipher_signing_key c, cipher_nonce c) $? k_id = Some froms_non)
            as FROMS by (clean_map_lookups; trivial).
          specialize (IHmsgs _ _ _ _ _ FROMS H0); split_ors; split_ands; subst; eauto.
          left; intuition idtac; econstructor; eauto; intros; simpl.
          repeat eexists; eauto.
          unfold msg_signing_key in H5; context_map_rewrites; clean_context.
          Nat.order.
        
      + message_cleaning;
          cases (@msg_signing_key t0 cs (SignedCiphertext c_id)); try discriminate;
            message_cleaning.
        specialize (IHmsgs _ _ _ _ _ H H0); split_ors; split_ands; eauto.
        destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups;
          left; intuition idtac;
            econstructor; eauto; intros; message_cleaning; eauto.

    - specialize (IHmsgs _ _ _ _ _ H H0); split_ors; split_ands; subst; eauto.
      left; intuition eauto.
      econstructor; eauto; intros; message_cleaning.
  Qed.

  Lemma clean_messages_froms_nonce_not_in_folds_correct :
    forall honestk cs to_usr msgs k_id froms acc non,
      froms $? k_id = None
      -> snd (clean_messages' honestk cs to_usr froms acc msgs) $? k_id = Some non
      -> Exists (fun sigM => match sigM with
                         | existT _ _ msg => msg_signed_addressed honestk cs to_usr msg = true
                                          /\ msg_signing_key cs msg = Some k_id
                                          /\ exists c_id c, msg_cipher_id msg = Some c_id
                                                    /\ cs $? c_id = Some c
                                                    /\ cipher_nonce c = non
                         end)
               msgs.
  Proof.
    unfold clean_messages'; induction msgs; intros; simpl in *; clean_map_lookups; eauto.

    destruct a.
    unfold msg_filter at 2 in H0.
    cases (msg_signed_addressed honestk cs to_usr c); simpl in *; eauto.
    cases (msg_nonce_ok cs froms c); message_cleaning.
    - destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups.
      eapply Exists_cons_tl; eapply IHmsgs with (froms := froms $+ (cipher_signing_key c, cipher_nonce c)); clean_map_lookups; eauto.
    - destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups.
      + assert (froms $+ (cipher_signing_key c, cipher_nonce c) $? cipher_signing_key c = Some (cipher_nonce c))
          as FROMS by (clean_map_lookups; trivial).
 
        generalize (clean_messages_froms_nonce_in_folds_correct _ _ _ _ _ _ _ FROMS H0); intros;
          split_ors; split_ands; subst; eauto.

        cases (@msg_signing_key t0 cs (SignedCiphertext c_id)); try discriminate.
        econstructor; intros; simpl; context_map_rewrites; unfold msg_signed_addressed; intuition eauto.
        rewrite andb_true_iff; split; auto.
        unfold msg_honestly_signed.
        rewrite Heq0; auto.
      + eapply Exists_cons_tl; eapply IHmsgs with (froms := froms $+ (cipher_signing_key c, cipher_nonce c));
          clean_map_lookups; eauto.
  Qed.

  
  Lemma msg_nonce_ok_eq :
    forall {t} (msg : crypto t) cs froms froms',
      msg_nonce_ok cs froms msg = froms'
      -> froms' = Some froms
      \/ froms' = None
      \/ exists c_id c,
          msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ froms' = Some (froms $+ (cipher_signing_key c,cipher_nonce c)).
  Proof.
    intros.
    destruct msg; unfold msg_nonce_ok in *; eauto.
    cases (cs $? c_id); eauto.
    cases (froms $? cipher_signing_key c); eauto 7.
    destruct (cipher_nonce c <=? n); eauto 7.
  Qed.

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

  Ltac process_message_cleaning :=
    repeat
      match goal with
      | [ H : snd (clean_messages' _ _ _ ?froms _ _) $? ?sgnKey = Some _
        , FROMS : ?froms $? ?sgnKey = None |- _ ] => idtac 1;
        eapply (clean_messages_froms_nonce_not_in_folds_correct _ _ _ _ _ _ _ FROMS) in H
      | [ H : snd (clean_messages' _ _ _ ?froms _ _) $? ?sgnKey = Some _
        , FROMS : ?froms $? ?sgnKey = Some _ |- _ ] => idtac 2;
        eapply (clean_messages_froms_nonce_in_folds_correct _ _ _ _ _ _ _ FROMS) in H;
        split_ors; split_ands; subst; try Nat.order
      | [ H : snd (clean_messages' _ _ _ ?froms _ _) $? ?sgnKey = Some _ |- _ ] => 
        match froms with
        | ?base $+ (sgnKey,?v) =>
          assert (base $+ (sgnKey,v) $? sgnKey = Some v) by map_lkup_ok
        | ?base $+ (?k,?v) =>
          match goal with
          | [ H : base $? sgnKey = ?ans |- _ ] =>
            assert (base $+ (k,v) $? sgnKey = ans) by map_lkup_ok
          | [ H1 : base $? sgnKey = _, H2 : base $? ?sgnKey2 = _ |- _ ] =>
            destruct (sgnKey ==n sgnKey2);
            try
              match goal with
              | [ H : sgnKey = sgnKey2 |- _ ] => rewrite H in *
              end; clean_map_lookups
          end
        end
          
      | [ H : Exists _ _ |- _ ] => rewrite Exists_exists in H
      | [ H : let (_,_) := ?x in _ |- _ ] => destruct x; simpl in H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : exists _, _ |- _ ] => destruct H
      | [ IN : List.In _ ?lst
        , H : Forall (fun _ => let (_,_) := _ in overlapping_msg_nonce_smaller _ _ _) ?lst |- _ ] =>
        rewrite Forall_forall in H; specialize (H _ IN); simpl in H; subst
      | [ SK : msg_signing_key _ ?c = Some _, MC : msg_cipher_id ?c = Some _ |- _ ] =>
        unfold msg_signing_key in SK; unfold msg_cipher_id in MC;
        destruct c; try discriminate; clean_context; context_map_rewrites; clean_context
      | [ MSGN : overlapping_msg_nonce_smaller ?non ?cs (SignedCiphertext ?cid)
        , CS : ?cs $? ?cid = Some ?c |- _ ] =>
        unfold overlapping_msg_nonce_smaller in MSGN;
        assert (cipher_nonce c < cipher_nonce non) by eauto;
        Nat.order
      (* This rule should probably go *)
      | [ MSGN : overlapping_msg_nonce_smaller ?c__cmp ?cs (SignedCiphertext ?cid)
        , CS : ?cs $? ?cid = Some ?c__end
        , SK1 : cipher_signing_key ?c__cmp = cipher_signing_key ?c
        , SK2 : cipher_signing_key ?c__end = cipher_signing_key ?c  |- _ ] =>
        unfold overlapping_msg_nonce_smaller in MSGN;
        assert (cipher_nonce c__end < cipher_nonce c__cmp) by (eapply MSGN; (Nat.order || eauto));
        Nat.order
      end.

  Lemma clean_messages_keeps_honestly_signed :
    forall {t} (msg : crypto t) honestk cs to_usr msgs froms,
      msg_signed_addressed honestk cs to_usr msg = true
      -> msg_not_replayed cs froms msg msgs
      -> clean_messages honestk cs to_usr froms (msgs ++ [existT _ _ msg])
        = clean_messages honestk cs to_usr froms msgs ++ [existT _ _ msg].
  Proof.
    intros; unfold clean_messages; induction msgs; simpl; eauto.
    - unfold clean_messages'; simpl; rewrite H.
      unfold msg_nonce_ok, msg_not_replayed in *; simpl;
        split_ex; split_ands; subst; context_map_rewrites.

      unfold nonce_absent_or_gt in H2; split_ors; context_map_rewrites; eauto.
      split_ex; split_ands; context_map_rewrites.

      cases (cipher_nonce x0 <=? x1); eauto; Nat.order.

    - unfold msg_filter, clean_messages'.
      destruct a; simpl.
      rewrite fold_left_app; simpl.
      rewrite H.
      assert (msg_signed_addressed honestk cs to_usr msg = true) as MSA by assumption;
        unfold msg_signed_addressed in MSA; apply andb_prop in MSA;
          unfold msg_honestly_signed, msg_signing_key in MSA; split_ands.
      unfold msg_nonce_ok; destruct msg; try discriminate.
      cases (cs $? c_id); try discriminate.
      cases (msg_signed_addressed honestk cs to_usr c).
      + destruct c; simpl; message_cleaning.
        unfold msg_honestly_signed in H3; simpl in *.
        cases (cs $? c_id0); try discriminate.
        cases (froms $? cipher_signing_key c); simpl in *.
        * cases (cipher_nonce c <=? n);
            rewrite !fold_clean_messages2';
            invert H0; split_ex; split_ands;
              invert H7; clean_map_lookups.

          ** unfold nonce_absent_or_gt in H6.
             unfold overlapping_msg_nonce_smaller in H10.
             
             cases (snd (clean_messages' honestk cs to_usr froms [] msgs) $? cipher_signing_key c0); eauto.
             cases (cipher_nonce c0 <=? n0); eauto.

             exfalso; split_ors; split_ex; split_ands; subst; invert H0; clean_map_lookups;
               process_message_cleaning.

          ** cases (snd
                      (clean_messages' honestk cs to_usr
                                       (froms $+ (cipher_signing_key c, cipher_nonce c))
                                       [existT crypto t1 (SignedCiphertext c_id0)]
                                       msgs) $? cipher_signing_key c0); eauto.
             cases (cipher_nonce c0 <=? n0); eauto.
             exfalso.
             invert H0; clean_map_lookups.
             unfold nonce_absent_or_gt in H6; split_ors; split_ex; split_ands; subst.

             *** process_message_cleaning.
             *** process_message_cleaning.
             
        * rewrite !fold_clean_messages2'.

          cases (  snd
          (clean_messages' honestk cs to_usr (froms $+ (cipher_signing_key c, cipher_nonce c)) [existT crypto t1 (SignedCiphertext c_id0)]
                           msgs) $? cipher_signing_key c0); eauto.
          cases (cipher_nonce c0 <=? n); eauto.
          exfalso.

          unfold msg_not_replayed in H0; split_ex; split_ands; split_ex; split_ands.
          invert H0.
          invert H7.
          unfold nonce_absent_or_gt in H6.
          split_ors; split_ex; split_ands; subst; clean_map_lookups; process_message_cleaning.
        
      + rewrite !fold_clean_messages2'.
        invert H0; split_ex; split_ands; invert H0; clean_map_lookups.
        cases (snd (clean_messages' honestk cs to_usr froms [] msgs) $? cipher_signing_key x1); simpl; eauto.
        cases (cipher_nonce x1 <=? n); eauto.
        exfalso.
        
        unfold nonce_absent_or_gt in *; split_ors; split_ex; split_ands; subst.
        * generalize (clean_messages_froms_nonce_not_in_folds_correct _ _ _ _ _ _ _ H0 Heq1); intros.
          apply Exists_exists in H3; split_ex; split_ands; destruct x2; split_ands; split_ex; split_ands; subst.
          invert H5.
          rewrite Forall_forall in H12.
          specialize (H12 _ H3).
          simpl in *.
          unfold overlapping_msg_nonce_smaller in H12.
          unfold msg_cipher_id in H7; destruct c0; try discriminate; clean_context.
          simpl in *; context_map_rewrites; clean_context.
          assert (cipher_nonce x4 < cipher_nonce x1) by eauto.
          Nat.order.

        * generalize (clean_messages_froms_nonce_in_folds_correct _ _ _ _ _ _ _ H0 Heq1); intros; split_ors; split_ands; subst;
            try Nat.order.
          apply Exists_exists in H6; split_ex; split_ands; destruct x3; split_ands; split_ex; split_ands; subst.
          invert H5.
          rewrite Forall_forall in H14.
          specialize (H14 _ H6); simpl in *.
          unfold overlapping_msg_nonce_smaller in H14.
          unfold msg_cipher_id in H9; destruct c0; try discriminate; clean_context.
          simpl in *; context_map_rewrites; clean_context.
          assert (cipher_nonce x5 < cipher_nonce x1) by eauto.
          Nat.order.
  Qed.

  
        

  Lemma clean_messages_drops_msg_filter_false :
    forall (msg : { type & crypto type }) msgs honestk to_usr mycs cs,
      msg_filter honestk cs to_usr mycs msg = false
      -> clean_messages honestk cs to_usr mycs (msgs ++ [msg])
        = clean_messages honestk cs to_usr mycs msgs.
  Proof.
    intros; unfold clean_messages. (*  *)
    induction msgs; simpl; eauto.
    - rewrite H; trivial.
    - cases (msg_filter honestk cs to_usr mycs a); subst; eauto.
      rewrite IHmsgs; trivial.
  Qed.
  
  (* Lemma clean_messages_drops_not_honestly_signed : *)
  (*   forall {t} (msg : crypto t) msgs honestk to_usr cs, *)
  (*     msg_honestly_signed honestk cs msg = false *)
  (*     -> clean_messages honestk cs to_usr (msgs ++ [existT _ _ msg]) *)
  (*       = clean_messages honestk cs to_usr msgs. *)
  (* Proof. *)
  (*   intros; unfold clean_messages. (*  *) *)
  (*   induction msgs; simpl; eauto. *)
  (*   - rewrite H; trivial. *)
  (*   - cases (msg_filter honestk cs to_usr a); subst; eauto. *)
  (*     rewrite IHmsgs; trivial. *)
  (* Qed. *)

  (* Lemma clean_message_keeps_safely_patterned_message : *)
  (*   forall {t} (msg : crypto t) honestk cs msg_to msgs pat, *)
  (*     msg_pattern_safe honestk pat *)
  (*     -> msg_accepted_by_pattern cs (Some msg_to) pat msg *)
  (*     -> clean_messages honestk cs msg_to  (existT _ _ msg :: msgs) *)
  (*       = (existT _ _ msg) :: clean_messages honestk cs msg_to msgs. *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (msg_honestly_signed honestk cs msg = true) by eauto. *)
  (*   unfold clean_messages; simpl; *)
  (*     match goal with *)
  (*     | [ H : msg_honestly_signed _ _ _ = _ |- _ ] => rewrite H *)
  (*     end; trivial. *)

  (*   unfold msg_honestly_signed in *; cases (msg_signing_key cs msg); try discriminate. *)
  (*   unfold msg_to_this_user. *)
  (*   cases (msg_destination_user cs msg). *)
  (*   - invert H0. *)
  (*   - exfalso. *)
  (*     unfold msg_destination_user, msg_signing_key in *; destruct msg; try discriminate. *)
  (*     destruct (cs $? c_id ); try discriminate. *)
  (* Qed. *)

  Lemma clean_messages_idempotent :
    forall msgs honestk honestk' cs msg_to mycs,
      (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
      -> clean_messages honestk' (clean_ciphers honestk cs) msg_to mycs (clean_messages honestk cs msg_to mycs msgs)
        = clean_messages honestk cs msg_to mycs msgs.
  Proof.
    induction msgs; intros; eauto.
    simpl.
    case_eq (msg_filter honestk cs msg_to mycs a); intros; eauto.
    assert (msg_filter honestk' (clean_ciphers honestk cs) msg_to mycs a = true)
      as MSG_FLTR.
    (* by (unfold msg_filter in *; destruct a; eauto). *)
    unfold msg_filter in *; destruct a; rewrite !andb_true_iff in H0; split_ands.
    rewrite !andb_true_iff; eauto.
    simpl.
    rewrite MSG_FLTR, IHmsgs; eauto.
  Qed.

End CleanMessages.

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

  Hint Resolve
       honest_key_filter_fn_proper
       honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
       honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal.

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

  Lemma clean_keys_inv' :
    forall k_id k ks,
      clean_keys ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_key_filter_fn k_id k = false.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; clean_map_lookups; eauto.

    destruct (x ==n k_id); subst; clean_map_lookups; eauto.
    - unfold clean_keys,filter in H0; rewrite fold_add in H0; eauto.
      cases (honest_key_filter_fn k_id k); clean_map_lookups; try discriminate; trivial.
    - eapply IHks; eauto.
      unfold clean_keys, filter in H0.
      rewrite fold_add in H0; eauto.
      cases (honest_key_filter_fn x e); eauto.
      clean_map_lookups; eauto.
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

  Lemma clean_keys_drops_dishonest_key :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_key_filter_fn k_id k = false
      -> clean_keys ks $? k_id = None.
  Proof.
    unfold clean_keys; intros.
    rewrite <- not_find_in_iff.
    unfold not; intros.
    rewrite in_find_iff in H1.
    cases (filter honest_key_filter_fn ks $? k_id); try contradiction.
    rewrite <- find_mapsto_iff in Heq.
    rewrite filter_iff in Heq; eauto.
    split_ands.
    rewrite find_mapsto_iff in H2.
    clean_map_lookups.
    rewrite H0 in H3; discriminate.
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

  Definition honest_perm_filter_fn (k_id : key_identifier) (kp : bool) :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Definition clean_key_permissions :=
    filter honest_perm_filter_fn.

  Lemma honest_perm_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) honest_perm_filter_fn.
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper :
    Proper (eq  ==>  eq  ==>  eq  ==>  eq) (fun k v m => if honest_perm_filter_fn k v then m $+ (k,v) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose :
    transpose_neqkey eq (fun k v m => if honest_perm_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey; intros.
    unfold honest_perm_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Lemma honest_perm_filter_fn_filter_proper_Equal :
    Proper (eq  ==>  eq  ==>  Equal  ==>  Equal) (fun k v m => if honest_perm_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold Equal, Proper, respectful; intros; subst.
    destruct (honest_perm_filter_fn y y0); eauto.
    destruct (y ==n y2); subst; clean_map_lookups; auto.
  Qed.

  Lemma honest_perm_filter_fn_filter_transpose_Equal :
    transpose_neqkey Equal (fun k v m => if honest_perm_filter_fn k v then m $+ (k,v) else m).
  Proof.
    unfold transpose_neqkey, Equal; intros.
    unfold honest_perm_filter_fn.
    cases (honestk $? k); cases (honestk $? k'); eauto.
    destruct b; destruct b0; eauto.
    rewrite map_ne_swap; auto.
  Qed.

  Hint Resolve
       honest_perm_filter_fn_proper
       honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
       honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal.

  Lemma clean_key_permissions_inv :
    forall k_id k ks,
      clean_key_permissions ks $? k_id = Some k
      -> ks $? k_id = Some k
      /\ honest_perm_filter_fn k_id k = true.
  Proof.
    unfold clean_key_permissions; intros until ks.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_key_permissions_inv' :
    forall k_id k ks,
      clean_key_permissions ks $? k_id = None
      -> ks $? k_id = Some k
      -> honest_perm_filter_fn k_id k = false.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; clean_map_lookups; eauto.

    destruct (x ==n k_id); subst; clean_map_lookups; eauto.
    - unfold clean_key_permissions,filter in H0; rewrite fold_add in H0; eauto.
      cases (honest_perm_filter_fn k_id k); clean_map_lookups; try discriminate; trivial.
    - eapply IHks; eauto.
      unfold clean_key_permissions, filter in H0.
      rewrite fold_add in H0; eauto.
      cases (honest_perm_filter_fn x e); eauto.
      clean_map_lookups; eauto.
  Qed.

  Lemma clean_key_permissions_adds_no_permissions :
    forall k_id ks,
        ks $? k_id = None
      -> clean_key_permissions ks $? k_id = None.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
    unfold clean_key_permissions, filter; rewrite fold_add; eauto.
    destruct (x ==n k_id); subst; clean_map_lookups.
    destruct (honest_perm_filter_fn x e); eauto.
    clean_map_lookups; eauto.
  Qed.

  Lemma clean_key_permissions_keeps_honest_permission :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn k_id k = true
      -> clean_key_permissions ks $? k_id = Some k.
  Proof.
    unfold clean_key_permissions; intros.
    rewrite <- !find_mapsto_iff.
    apply filter_iff; eauto.
    rewrite find_mapsto_iff; eauto.
  Qed.

  Lemma clean_key_permissions_drops_dishonest_permission :
    forall k_id k ks,
        ks $? k_id = Some k
      -> honest_perm_filter_fn k_id k = false
      -> clean_key_permissions ks $? k_id = None.
  Proof.
    unfold clean_key_permissions; intros.
    rewrite <- not_find_in_iff.
    unfold not; intros.
    rewrite in_find_iff in H1.
    cases (filter honest_perm_filter_fn ks $? k_id); try contradiction.
    rewrite <- find_mapsto_iff in Heq.
    rewrite filter_iff in Heq; eauto.
    split_ands.
    rewrite find_mapsto_iff in H2.
    clean_map_lookups.
    rewrite H0 in H3; discriminate.
  Qed.

  Lemma clean_key_permissions_idempotent :
    forall ks,
      clean_key_permissions ks = clean_key_permissions (clean_key_permissions ks).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    symmetry; cases (clean_key_permissions ks $? y).
    - generalize (clean_key_permissions_inv _ _ Heq); intros;
        split_ands; apply clean_key_permissions_keeps_honest_permission; eauto.
    - eapply clean_key_permissions_adds_no_permissions; eauto.
  Qed.

  Lemma clean_key_permissions_distributes_merge_key_permissions :
    forall perms1 perms2,
      clean_key_permissions (perms1 $k++ perms2) = clean_key_permissions perms1 $k++ clean_key_permissions perms2.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (clean_key_permissions perms1 $? y);
      cases (clean_key_permissions perms2 $? y);
      cases (clean_key_permissions (perms1 $k++ perms2) $? y); simplify_key_merges1; eauto;
        repeat (
            match goal with
            | [ H1 : honest_perm_filter_fn ?y _ = true, H2 : honest_perm_filter_fn ?y _ = false |- _ ] =>
              unfold honest_perm_filter_fn in *; cases (honestk $? y); try discriminate
            | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b; try discriminate
            | [ H : clean_key_permissions _ $? _ = Some _ |- _ ] => apply clean_key_permissions_inv in H
            | [ H0 : ?perms $? ?y = Some _ , H : clean_key_permissions ?perms $? ?y = None |- _ ] =>
              apply (clean_key_permissions_inv' _ _ H) in H0; clear H
            | [ H1 : _ $? ?y = Some _, H2 : perms1 $k++ perms2 $? ?y = None |- _ ] =>
              apply merge_perms_no_disappear_perms in H2; split_ands; contra_map_lookup
            | [ H0 : ?perms $? ?y = None , H : clean_key_permissions ?perms $? ?y = None |- _ ] =>
              simplify_key_merges1; eauto 2
            | [ H : clean_key_permissions ?perms $? ?y = None |- _ ] =>
              match goal with
                | [ H : perms $? y = _ |- _ ] => fail 1
                | _ => cases (perms $? y)
              end
            | [ H1 : perms1 $? ?y = _, H2 : perms2 $? ?y = _ |- _ ] => simplify_key_merges1
            end; split_ands; auto 2).
  Qed.

  Lemma clean_honest_key_permissions_distributes :
    forall perms pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> clean_key_permissions (perms $k++ pubk) = clean_key_permissions perms $k++ pubk.
  Proof.
    intros.

    rewrite clean_key_permissions_distributes_merge_key_permissions.
    apply map_eq_Equal; unfold Equal; intros.
    cases (pubk $? y).
    - specialize (H _ _ Heq); split_ands; subst.
      assert (clean_key_permissions pubk $? y = Some false)
        by (eapply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial).
      cases (clean_key_permissions perms $? y);
        simplify_key_merges; eauto.
    - assert (clean_key_permissions pubk $? y = None) 
        by (apply clean_key_permissions_adds_no_permissions; eauto).
      cases (clean_key_permissions perms $? y);
        simplify_key_merges; eauto.
  Qed.

  Lemma adv_no_honest_key_honest_key :
    forall pubk,
      (forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> forall k_id kp, pubk $? k_id = Some kp -> honestk $? k_id = Some true.
  Proof.
    intros.
    specialize (H _ _ H0); intuition idtac.
  Qed.

End CleanKeys.

(******************** USER CLEANING ***********************
 **********************************************************
 *
 * Function to clean users and lemmas about it.
 *)

Section CleanUsers.
  Import RealWorld.

  Variable honestk : key_perms.

  Definition clean_users {A} (cs : ciphers) (usrs : honest_users A) :=
    mapi (fun u_id u_d => {| key_heap := clean_key_permissions honestk u_d.(key_heap)
                        ; protocol := u_d.(protocol)
                        ; msg_heap := clean_messages honestk cs (Some u_id) u_d.(c_heap) u_d.(msg_heap)
                        ; c_heap   := u_d.(c_heap)
                        ; from_ids := u_d.(from_ids)
                        ; to_ids   := u_d.(to_ids) |}) usrs.

  Lemma clean_users_notation :
    forall {A} (cs : ciphers) (usrs : honest_users A),
      mapi (fun u_id u_d => {| key_heap := clean_key_permissions honestk u_d.(key_heap)
                          ; protocol := u_d.(protocol)
                          ; msg_heap := clean_messages honestk cs (Some u_id) u_d.(c_heap) u_d.(msg_heap)
                          ; c_heap   := u_d.(c_heap)
                          ; from_ids := u_d.(from_ids)
                          ; to_ids   := u_d.(to_ids) |}) usrs = clean_users cs usrs.
  Proof. unfold clean_users; trivial. Qed.

  Lemma clean_users_cleans_user :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id u_d u_d',
      usrs $? u_id = Some u_d
      -> u_d' = {| key_heap := clean_key_permissions honestk u_d.(key_heap)
                ; protocol := u_d.(protocol)
                ; msg_heap :=  clean_messages honestk cs (Some u_id) u_d.(c_heap) u_d.(msg_heap)
                ; c_heap   := u_d.(c_heap)
                ; from_ids := u_d.(from_ids)
                ; to_ids   := u_d.(to_ids) |}
      -> clean_users cs usrs $? u_id = Some u_d'.
  Proof.
    intros.
    unfold clean_users; rewrite mapi_o; intros; subst; unfold option_map;
      context_map_rewrites; subst; auto.
  Qed.

  Lemma clean_users_cleans_user_inv :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id u_d,
      clean_users cs usrs $? u_id = Some u_d
      -> exists msgs perms,
        usrs $? u_id = Some {| key_heap := perms
                             ; protocol := u_d.(protocol)
                             ; msg_heap := msgs
                             ; c_heap   := u_d.(c_heap)
                             ; from_ids := u_d.(from_ids)
                             ; to_ids   := u_d.(to_ids) |}
        /\ u_d.(key_heap) = clean_key_permissions honestk perms
        /\ u_d.(msg_heap) = clean_messages honestk cs (Some u_id) u_d.(c_heap) msgs.
  Proof.
    intros.
    unfold clean_users in *. rewrite mapi_o in H; intros; subst; auto; unfold option_map in *.
    cases (usrs $? u_id); try discriminate; eauto.
    destruct u; destruct u_d; simpl in *.
    invert H.
    eexists; eauto.
  Qed.

  Lemma clean_users_add_pull :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id u,
      clean_users cs (usrs $+ (u_id,u))
      = clean_users cs usrs $+ (u_id, {| key_heap := clean_key_permissions honestk u.(key_heap)
                                       ; protocol := u.(protocol)
                                       ; msg_heap := clean_messages honestk cs (Some u_id) u.(c_heap) u.(msg_heap)
                                       ; c_heap   := u.(c_heap)
                                       ; from_ids := u.(from_ids)
                                       ; to_ids   := u.(to_ids) |}).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n u_id); subst; clean_map_lookups; eauto;
      unfold clean_users; rewrite !mapi_o; intros; subst; unfold option_map; clean_map_lookups; auto.
  Qed.

  Lemma clean_users_adds_no_users :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id,
      usrs $? u_id = None
      -> clean_users cs usrs $? u_id = None.
  Proof.
    unfold clean_users; intros.
    rewrite mapi_o; intros; subst; eauto.
    unfold option_map; context_map_rewrites; trivial.
  Qed.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

End CleanUsers.

Section FindUserKeysCleanUsers.
  Import RealWorld.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

  Hint Resolve clean_users_adds_no_users.

  Lemma findUserKeys_add_user :
    forall {A} (usrs : honest_users A) u_id u_d,
      ~ In u_id usrs
      -> findUserKeys (usrs $+ (u_id, u_d)) =
        findUserKeys usrs $k++ key_heap u_d.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    unfold findUserKeys at 1.
    rewrite fold_add; eauto.
  Qed.

  Lemma findUserKeys_clean_users_addnl_keys :
    forall {A} (usrs : honest_users A) honestk cs ukeys k_id,
      findUserKeys (clean_users honestk cs usrs) $? k_id = Some true
      -> findUserKeys (clean_users (honestk $k++ ukeys) cs usrs) $? k_id = Some true.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; contra_map_lookup; auto.
    rewrite clean_users_add_pull; simpl.
    unfold findUserKeys at 1.
    rewrite fold_add; clean_map_lookups; eauto.
    simpl; rewrite findUserKeys_notation.
    rewrite clean_users_add_pull in H;
      unfold findUserKeys in H; rewrite fold_add in H; clean_map_lookups; eauto.
    simpl in *; rewrite findUserKeys_notation in H.
    apply merge_perms_split in H; split_ors.
    - specialize (IHusrs H);
        cases (clean_key_permissions (honestk $k++ ukeys) (key_heap e) $? k_id);
        simplify_key_merges; eauto.
    - assert (clean_key_permissions (honestk $k++ ukeys) (key_heap e) $? k_id = Some true).
      eapply clean_key_permissions_inv in H; split_ands.
      eapply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn; context_map_rewrites; trivial.
      unfold honest_perm_filter_fn in H1.
      cases (honestk $? k_id); cases (ukeys $? k_id);
        try discriminate;
        simplify_key_merges1;
        eauto.
      destruct b; try discriminate; eauto.
      cases (findUserKeys (clean_users (honestk $k++ ukeys) cs usrs) $? k_id); simplify_key_merges; eauto.
  Qed.

  Hint Resolve findUserKeys_clean_users_addnl_keys.

  Lemma clean_users_no_change_honestk :
    forall {A} (usrs : honest_users A) cs k_id,
      findUserKeys usrs $? k_id = Some true
      -> findUserKeys (clean_users (findUserKeys usrs) cs usrs) $? k_id = Some true.
  Proof.
    intros.
    unfold clean_users.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; eauto.
    rewrite clean_users_notation in *.
    unfold findUserKeys in H; rewrite fold_add in H; eauto;
      rewrite findUserKeys_notation in H.
    remember (findUserKeys (usrs $+ (x,e))) as honestk.
    rewrite clean_users_add_pull.
    unfold findUserKeys at 1.
    rewrite fold_add; clean_map_lookups; eauto using clean_users_adds_no_users;
      simpl; rewrite findUserKeys_notation.

    apply merge_perms_split in H; split_ors.
    - specialize (IHusrs H).
      assert (findUserKeys (clean_users honestk cs usrs) $? k_id = Some true).
      subst.
      rewrite findUserKeys_add_user; eauto.
      cases (clean_key_permissions honestk (key_heap e) $? k_id); simplify_key_merges; eauto.

    - assert ( honestk $? k_id = Some true )
        by (subst; eapply findUserKeys_has_private_key_of_user with (u_id := x); clean_map_lookups; eauto).
      assert (clean_key_permissions honestk (key_heap e) $? k_id = Some true).
      eapply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn; context_map_rewrites; trivial.
      cases (findUserKeys (clean_users honestk cs usrs) $? k_id); simplify_key_merges; eauto.
  Qed.

  Lemma clean_users_removes_non_honest_keys :
    forall {A} (usrs : honest_users A) cs k_id u_id u_d,
      findUserKeys usrs $? k_id = Some false
      -> clean_users (findUserKeys usrs) cs usrs $? u_id = Some u_d
      -> key_heap u_d $? k_id = None.
  Proof.
    intros.
    eapply clean_users_cleans_user_inv in H0; eauto; split_ex; split_ands.
    rewrite H1.
    cases (x0 $? k_id).
    - eapply clean_key_permissions_drops_dishonest_permission; eauto.
      unfold honest_perm_filter_fn; rewrite H; trivial.
    - eapply clean_key_permissions_adds_no_permissions; auto.
  Qed.

  Lemma findUserKeys_clean_users_removes_non_honest_keys :
    forall {A} (usrs : honest_users A) honestk cs k_id,
      honestk $? k_id = Some false
      -> findUserKeys (clean_users honestk cs usrs) $? k_id = None.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; eauto.
    rewrite clean_users_add_pull.
    unfold findUserKeys; rewrite fold_add; clean_map_lookups; eauto.
    rewrite findUserKeys_notation; simpl.
    assert (clean_key_permissions honestk (key_heap e) $? k_id = None).
    cases (key_heap e $? k_id).
    eapply clean_key_permissions_drops_dishonest_permission; eauto.
    unfold honest_perm_filter_fn; context_map_rewrites; trivial.
    eapply clean_key_permissions_adds_no_permissions; auto.
    simplify_key_merges; eauto.
  Qed.

  Lemma findUserKeys_clean_users_removes_non_honest_keys' :
    forall {A} (usrs : honest_users A) honestk cs k_id,
      honestk $? k_id = None
      -> findUserKeys (clean_users honestk cs usrs) $? k_id = None.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; eauto.
    rewrite clean_users_add_pull.
    unfold findUserKeys; rewrite fold_add; clean_map_lookups; eauto.
    rewrite findUserKeys_notation; simpl.
    assert (clean_key_permissions honestk (key_heap e) $? k_id = None).
    cases (key_heap e $? k_id).
    eapply clean_key_permissions_drops_dishonest_permission; eauto.
    unfold honest_perm_filter_fn; context_map_rewrites; trivial.
    eapply clean_key_permissions_adds_no_permissions; auto.
    simplify_key_merges; eauto.
  Qed.

  Lemma findUserKeys_clean_users_correct :
    forall {A} (usrs : honest_users A) cs k_id,
      match findUserKeys usrs $? k_id with
      | Some true => findUserKeys (clean_users (findUserKeys usrs) cs usrs) $? k_id = Some true
      | _ => findUserKeys (clean_users (findUserKeys usrs) cs usrs) $? k_id = None
      end.
  Proof.
    intros.
    cases (findUserKeys usrs $? k_id); try destruct b;
      eauto using
            findUserKeys_clean_users_removes_non_honest_keys
          , findUserKeys_clean_users_removes_non_honest_keys'
          , clean_users_no_change_honestk.
  Qed.

  Lemma clean_key_permissions_ok_extra_user_cleaning :
    forall {A} (usrs : honest_users A) cs perms,
      clean_key_permissions (findUserKeys usrs) perms =
      clean_key_permissions (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_key_permissions (findUserKeys usrs) perms).
  Proof.
    intros; symmetry.
    apply map_eq_Equal; unfold Equal; intros.
    case_eq (clean_key_permissions (findUserKeys usrs) perms $? y); intros.
    - apply clean_key_permissions_inv in H; split_ands.
      apply clean_key_permissions_keeps_honest_permission; eauto.
      apply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn in *.
      cases (findUserKeys usrs $? y); try discriminate; destruct b0; try discriminate.
      pose proof (findUserKeys_clean_users_correct usrs cs y) as CORRECT.
      rewrite Heq in CORRECT.
      rewrite CORRECT; trivial.
    - apply clean_key_permissions_adds_no_permissions; eauto.
  Qed.

  Lemma clean_messages_ok_extra_user_cleaning :
    forall {A} (usrs : honest_users A) cs msgs mycs u_id,
      clean_messages (findUserKeys usrs) cs u_id mycs msgs =
      clean_messages (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) cs u_id mycs (clean_messages (findUserKeys usrs) cs u_id mycs msgs).
  Proof.
    induction msgs; eauto; intros; simpl;
      rewrite IHmsgs.
    case_eq ( msg_filter (findUserKeys usrs) cs u_id mycs a ); intros.
    - assert (msg_filter (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) cs u_id mycs a = true).
      unfold msg_filter, msg_honestly_signed, msg_to_this_user, honest_keyb in *; destruct a;
        destruct c; try discriminate.
          repeat match goal with
                 | [ H : context [_ && _ = true] |- _ ] => rewrite andb_true_iff in H; split_ands
                 | [ |- context [msg_signing_key ?cs ?c]] => cases (msg_signing_key cs c); try discriminate
                 | [ |- context [msg_destination_user ?cs ?c]] => cases (msg_destination_user cs c); try discriminate
                 | [ |- context [ if ?uid1 ==n ?uid2 then _ else _] ] => destruct (uid1 ==n uid2); subst; try discriminate
                 | [ H : ?stuff = true |- context [?stuff] ] => rewrite H; simpl
                 | [ H : match findUserKeys ?usrs $? ?k with _ => _ end = true |- _ ] => cases (findUserKeys usrs $? k); try discriminate
                 | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b; subst; try discriminate
                 | [ H : findUserKeys ?usrs $? ?k = Some true |- context [ findUserKeys (clean_users (findUserKeys ?usrs) ?cs ?usrs) $? ?k ] ] =>
                   assert (findUserKeys (clean_users (findUserKeys usrs) cs usrs) $? k = Some true)
                     by (pose proof (findUserKeys_clean_users_correct usrs cs k) as FNDKSCLN; rewrite H in FNDKSCLN; assumption);
                     context_map_rewrites
                 end; eauto.

      simpl; rewrite H0. rewrite <- !IHmsgs; trivial.

    - rewrite <- !IHmsgs; trivial.
  Qed.

  Hint Resolve
       clean_key_permissions_ok_extra_user_cleaning
       clean_messages_idempotent
       clean_messages_ok_extra_user_cleaning.

  Lemma clean_users_idempotent' :
    forall {A} (usrs : honest_users A) cs,
      clean_users (findUserKeys (clean_users (findUserKeys usrs) cs usrs))
                  (clean_ciphers (findUserKeys usrs) cs)
                  (clean_users (findUserKeys usrs) cs usrs) =
      clean_users (findUserKeys usrs) cs usrs.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    case_eq (clean_users (findUserKeys usrs) cs usrs $? y); intros.
    - apply clean_users_cleans_user_inv in H; split_ex; split_ands.
      destruct u; simpl in *.
      eapply clean_users_cleans_user; eauto.
      eapply clean_users_cleans_user; eauto.
      f_equal; simpl; subst; eauto.
      rewrite clean_messages_idempotent; eauto.
      intros.
      pose proof (findUserKeys_clean_users_correct usrs cs k); context_map_rewrites; eauto.

    - unfold clean_users in H; rewrite mapi_o in H; intros; subst; auto; unfold option_map in H.
      cases (usrs $? y); try discriminate.
      apply clean_users_adds_no_users; eauto.
  Qed.

  Lemma clean_keys_ok_extra_user_cleaning :
    forall {A} (usrs : honest_users A) cs gks,
      clean_keys (findUserKeys usrs) gks =
      clean_keys (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_keys (findUserKeys usrs) gks).
  Proof.
    intros; symmetry.
    apply map_eq_Equal; unfold Equal; intros.
    case_eq (clean_keys (findUserKeys usrs) gks $? y); intros.
    - generalize (clean_keys_inv _ _ _ H); intros; split_ands.
      apply clean_keys_keeps_honest_key; eauto.
      unfold honest_key_filter_fn in *.
      cases (findUserKeys usrs $? y); try discriminate; destruct b; try discriminate.
      pose proof (findUserKeys_clean_users_correct usrs cs y) as CORRECT.
      rewrite Heq in CORRECT.
      rewrite CORRECT; trivial.
    - apply clean_keys_adds_no_keys; eauto.
  Qed.

  Lemma clean_ciphers_ok_extra_user_cleaning :
    forall {A} (usrs : honest_users A) cs,
      clean_ciphers (findUserKeys usrs) cs =
      clean_ciphers (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_ciphers (findUserKeys usrs) cs).
  Proof.
    intros; symmetry.
    apply map_eq_Equal; unfold Equal; intros.
    case_eq (clean_ciphers (findUserKeys usrs) cs $? y); intros.
    - apply clean_ciphers_keeps_honest_cipher; eauto.
      rewrite <- find_mapsto_iff in H; apply clean_ciphers_mapsto_iff in H; split_ands.
      rewrite find_mapsto_iff in H.
      unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb in *.
      destruct c.
      + cases (findUserKeys usrs $? k__sign); try discriminate; destruct b; try discriminate.
        pose proof (findUserKeys_clean_users_correct usrs cs k__sign) as CORRECT.
        rewrite Heq in CORRECT.
        rewrite CORRECT; trivial.
      + cases (findUserKeys usrs $? k__sign); try discriminate; destruct b; try discriminate.
        pose proof (findUserKeys_clean_users_correct usrs cs k__sign) as CORRECT.
        rewrite Heq in CORRECT.
        rewrite CORRECT; trivial.
    - apply clean_ciphers_no_new_ciphers; eauto.
  Qed.

End FindUserKeysCleanUsers.

Section StripAdv.
  Import RealWorld.

  Definition clean_adv {B} (adv : user_data B) (honestk : key_perms) (cs : ciphers) (b : B) :=
    {| key_heap := clean_key_permissions honestk adv.(key_heap)
     ; protocol := Return b
     ; msg_heap := clean_messages honestk cs None adv.(c_heap) adv.(msg_heap)
     ; c_heap   := []
     ; from_ids := $0
     ; to_ids   := $0 |}.

  Definition strip_adversary_univ {A B} (U__r : universe A B) (b : B) : universe A B :=
    let honestk := findUserKeys U__r.(users)
    in {| users       := clean_users honestk U__r.(all_ciphers) U__r.(users)
        ; adversary   := clean_adv U__r.(adversary) honestk U__r.(all_ciphers) b
        ; all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
        ; all_keys    := clean_keys honestk U__r.(all_keys)
       |}.

  Definition strip_adversary {A B} (U__r : universe A B) : simpl_universe A :=
    let honestk := findUserKeys U__r.(users)
    in {| s_users       := clean_users honestk U__r.(all_ciphers) U__r.(users)
        ; s_all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
        ; s_all_keys    := clean_keys honestk U__r.(all_keys)
       |}.

  Definition strip_adversary_simpl {A} (U__r : simpl_universe A) : simpl_universe A :=
    let honestk := findUserKeys U__r.(s_users)
    in {| s_users       := clean_users honestk U__r.(s_all_ciphers) U__r.(s_users)
        ; s_all_ciphers := clean_ciphers honestk U__r.(s_all_ciphers)
        ; s_all_keys    := clean_keys honestk U__r.(s_all_keys)
       |}.

  Definition strip_action (honestk : key_perms) (act : action) :=
    act.
    (* match act with *)
    (* | Input msg pat msg_to => Input msg pat msg_to *)
    (* | output              => output *)
    (* end. *)

  Definition strip_label (honestk : key_perms) (lbl : label) :=
    match lbl with
    | Silent => Silent
    | Action a => Action (strip_action honestk a)
    end.

  Lemma peel_strip_univ_eq_strip_adv :
    forall A B (U : universe A B) b,
      peel_adv (strip_adversary_univ U b) = strip_adversary U.
  Proof.
    unfold peel_adv, strip_adversary, strip_adversary_univ; trivial.
  Qed.

End StripAdv.
