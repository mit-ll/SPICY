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
     Automation
     AdversaryUniverse
     RealWorld

     Theory.KeysTheory
.

Set Implicit Arguments.

Lemma cipher_honestly_signed_honest_keyb_iff :
  forall honestk c tf,
    cipher_honestly_signed honestk c = tf <-> honest_keyb honestk (cipher_signing_key c) = tf.
Proof.
  intros.
  unfold cipher_honestly_signed, cipher_signing_key; split; destruct c; trivial.
Qed.

(******************** CIPHER CLEANING *********************
 **********************************************************
 *
 * Function to clean ciphehrs and lemmas about it.
 *)

Section CleanCiphers.
  Import RealWorld.

  Variable honestk : key_perms.

  Lemma honest_cipher_filter_fn_proper :
    Proper (eq  ==>  eq  ==>  eq) (honest_cipher_filter_fn honestk).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_cipher_filter_fn_filter_proper :
    Proper
      ( eq  ==>  eq  ==>  Equal  ==>  Equal)
      (fun (k : NatMap.Map.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk k e then m $+ (k, e) else m).
  Proof.
    unfold Proper, respectful;
      unfold Equal; intros; apply map_eq_Equal in H1; subst; auto.
  Qed.

  Lemma honest_cipher_filter_fn_filter_transpose :
    transpose_neqkey Equal
       (fun (k : NatMap.Map.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk k e then m $+ (k, e) else m).
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
      (fun (k : NatMap.Map.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk k e then m $+ (k, e) else m).
  Proof.
    solve_proper.
  Qed.

  Lemma honest_cipher_filter_fn_filter_transpose_eq :
    transpose_neqkey eq
       (fun (k : NatMap.Map.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk k e then m $+ (k, e) else m).
  Proof.
    unfold transpose_neqkey, honest_cipher_filter_fn, cipher_honestly_signed; intros.
    cases e; cases e'; subst; simpl;
      repeat match goal with
             | [ |- context[if ?cond then _ else _] ] => cases cond
             | [ |- context[_ $+ (?k1,_) $? ?k2] ] => cases (k1 ==n k2); subst; clean_map_lookups
             end; eauto;
        rewrite map_ne_swap; eauto.
  Qed.

  Hint Resolve
       honest_cipher_filter_fn_proper
       honest_cipher_filter_fn_filter_proper
       honest_cipher_filter_fn_filter_transpose
       honest_cipher_filter_fn_filter_proper_eq
       honest_cipher_filter_fn_filter_transpose_eq
  : core.

  Lemma clean_ciphers_mapsto_iff : forall cs c_id c,
      MapsTo c_id c (clean_ciphers honestk cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn honestk c_id c = true.
  Proof.
    intros.
    apply filter_iff; eauto.
  Qed.

  Lemma clean_ciphers_inv :
    forall c_id c cs,
      (clean_ciphers honestk cs) $? c_id = Some c
      -> cs $? c_id = Some c.
  Proof.
    intros.
    rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H;
      split_ands; assumption.
  Qed.

  Lemma clean_ciphers_keeps_honest_cipher :
    forall c_id c cs,
      cs $? c_id = Some c
      -> honest_cipher_filter_fn honestk c_id c = true
      -> clean_ciphers honestk cs $? c_id = Some c.
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
      -> clean_ciphers honestk cs $? c_id = Some c.
  Proof.
    intros.
    eapply clean_ciphers_keeps_honest_cipher; auto.
    unfold honest_cipher_filter_fn, cipher_honestly_signed.
    destruct c; subst.
    + invert H. rewrite <- honest_key_honest_keyb; eauto.
    + invert H. rewrite <- honest_key_honest_keyb; eauto.
  Qed.

  Hint Constructors
       msg_accepted_by_pattern : core.

  Hint Extern 1 (_ $+ (_,_) $? _ = _) => progress clean_map_lookups : core.

  Lemma clean_ciphers_eliminates_dishonest_cipher :
    forall c_id c cs k,
      cs $? c_id = Some c
      -> honest_keyb honestk k = false
      -> k = cipher_signing_key c
      -> clean_ciphers honestk cs $? c_id = None.
  Proof.
    intros; unfold clean_ciphers, filter.
    apply P.fold_rec_bis; intros; eauto.
    cases (honest_cipher_filter_fn honestk k0 e); eauto.
    cases (c_id ==n k0); subst; eauto.
    exfalso.
    rewrite find_mapsto_iff in H2; rewrite H2 in H; invert H.
    unfold honest_cipher_filter_fn, cipher_honestly_signed, cipher_signing_key in *.
    cases c; rewrite H0 in Heq; invert Heq.
  Qed.

  Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher : core.

  Lemma clean_ciphers_keeps_added_honest_cipher :
    forall c_id c cs,
      honest_cipher_filter_fn honestk c_id c = true
      -> ~ In c_id cs
      -> clean_ciphers honestk (cs $+ (c_id,c)) = clean_ciphers honestk cs $+ (c_id,c).
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
      -> ( clean_ciphers  honestk cs $? c_id = Some c
        /\ honest_keyb honestk k = true)
      \/ ( clean_ciphers honestk cs $? c_id = None
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
      -> clean_ciphers honestk cs $? c_id = None.
  Proof.
    intros.
    unfold clean_ciphers, filter.
    apply P.fold_rec_bis; intros; eauto.
    cases (honest_cipher_filter_fn honestk k e); eauto.
    - case (c_id ==n k); intro; subst; unfold honest_cipher_filter_fn.
      + rewrite find_mapsto_iff in H0; rewrite H0 in H; invert H.
      + rewrite add_neq_o; eauto.
  Qed.

  Hint Resolve clean_ciphers_no_new_ciphers : core.

  Lemma clean_ciphers_eliminates_added_dishonest_cipher :
    forall c_id c cs k,
      cs $? c_id = None
      -> honest_keyb honestk k = false
      -> k = cipher_signing_key c
      -> clean_ciphers honestk cs = clean_ciphers honestk (cs $+ (c_id,c)).
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
      -> ~ In c_id (clean_ciphers honestk cs).
  Proof.
    intros.
    rewrite not_find_in_iff in H.
    apply not_find_in_iff; eauto.
  Qed.

  Hint Resolve not_in_ciphers_not_in_cleaned_ciphers : core.

  Lemma dishonest_cipher_cleaned :
    forall cs c_id cipherMsg k,
      cipher_signing_key cipherMsg = k
      -> honest_keyb honestk k = false
      -> ~ In c_id cs
      -> clean_ciphers honestk cs = clean_ciphers honestk (cs $+ (c_id, cipherMsg)).
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

  Hint Resolve dishonest_cipher_cleaned : core.

  Hint Extern 1 (honest_cipher_filter_fn _ _ ?c = _) => unfold honest_cipher_filter_fn; cases c : core.

  Lemma clean_ciphers_added_honest_cipher_not_cleaned :
    forall cs c_id c k,
        honest_key honestk k
      -> k = cipher_signing_key c
      -> clean_ciphers honestk (cs $+ (c_id,c)) = clean_ciphers honestk cs $+ (c_id,c).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.

    case (y ==n c_id); intros; subst; clean_map_lookups.
    - erewrite clean_ciphers_keeps_honest_cipher; auto.
      invert H; unfold honest_cipher_filter_fn; eauto.
      unfold cipher_honestly_signed, honest_keyb;
        cases c; simpl in *; context_map_rewrites; auto; invert H0; rewrite H1; trivial.
    - case_eq (clean_ciphers honestk cs $? y); intros; subst;
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
      -> clean_ciphers honestk cs = cs.
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
      ciphers_honestly_signed honestk (clean_ciphers honestk cs).
  Proof.
    unfold ciphers_honestly_signed; intros.
    rewrite Forall_natmap_forall; intros.
    rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff in H; split_ands.
    unfold honest_cipher_filter_fn in *; assumption.
  Qed.

End CleanCiphers.
