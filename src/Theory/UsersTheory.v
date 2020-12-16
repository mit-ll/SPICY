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
     Automation
     Tactics
     RealWorld
     AdversaryUniverse

     Theory.KeysTheory
     Theory.MessagesTheory
     Theory.CipherTheory
.

Set Implicit Arguments.

(******************** USER CLEANING ***********************
 **********************************************************
 *
 * Function to clean users and lemmas about it.
 *)

Section CleanUsers.

  Variable honestk : key_perms.

  Lemma clean_users_notation :
    forall {A} (cs : ciphers) (usrs : honest_users A),
      mapi (fun u_id u_d => {| key_heap := clean_key_permissions honestk u_d.(key_heap)
                          ; protocol := u_d.(protocol)
                          ; msg_heap := clean_messages honestk cs (Some u_id) u_d.(from_nons) u_d.(msg_heap)
                          ; c_heap   := u_d.(c_heap)
                          ; from_nons := u_d.(from_nons)
                          ; sent_nons := u_d.(sent_nons)
                          ; cur_nonce := u_d.(cur_nonce) |}) usrs = clean_users honestk cs usrs.
  Proof. unfold clean_users; trivial. Qed.

  Lemma clean_users_cleans_user :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id u_d u_d',
      usrs $? u_id = Some u_d
      -> u_d' = {| key_heap  := clean_key_permissions honestk u_d.(key_heap)
                ; protocol  := u_d.(protocol)
                ; msg_heap  :=  clean_messages honestk cs (Some u_id) u_d.(from_nons) u_d.(msg_heap)
                ; c_heap    := u_d.(c_heap)
                ; from_nons := u_d.(from_nons)
                ; sent_nons := u_d.(sent_nons)
                ; cur_nonce := u_d.(cur_nonce) |}
      -> clean_users honestk cs usrs $? u_id = Some u_d'.
  Proof.
    intros.
    unfold clean_users; rewrite mapi_o; intros; subst; unfold option_map;
      context_map_rewrites; subst; auto.
  Qed.

  Lemma clean_users_cleans_user_inv :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id u_d,
      clean_users honestk cs usrs $? u_id = Some u_d
      -> exists msgs perms,
        usrs $? u_id = Some {| key_heap := perms
                             ; protocol := u_d.(protocol)
                             ; msg_heap := msgs
                             ; c_heap   := u_d.(c_heap)
                             ; from_nons := u_d.(from_nons)
                             ; sent_nons := u_d.(sent_nons)
                             ; cur_nonce := u_d.(cur_nonce) |}
        /\ u_d.(key_heap) = clean_key_permissions honestk perms
        /\ u_d.(msg_heap) = clean_messages honestk cs (Some u_id) u_d.(from_nons) msgs.
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
      clean_users honestk cs (usrs $+ (u_id,u))
      = clean_users honestk cs usrs $+ (u_id, {| key_heap := clean_key_permissions honestk u.(key_heap)
                                       ; protocol := u.(protocol)
                                       ; msg_heap := clean_messages honestk cs (Some u_id) u.(from_nons) u.(msg_heap)
                                       ; c_heap   := u.(c_heap)
                                       ; from_nons := u.(from_nons)
                                       ; sent_nons := u.(sent_nons)
                                       ; cur_nonce := u.(cur_nonce) |} ).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n u_id); subst; clean_map_lookups; eauto;
      unfold clean_users; rewrite !mapi_o; intros; subst; unfold option_map; clean_map_lookups; auto.
  Qed.

  Lemma clean_users_adds_no_users :
    forall {A} (cs : ciphers) (usrs : honest_users A) u_id,
      usrs $? u_id = None
      -> clean_users honestk cs usrs $? u_id = None.
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
        solve_perm_merges; eauto.
    - assert (clean_key_permissions (honestk $k++ ukeys) (key_heap e) $? k_id = Some true).
      eapply clean_key_permissions_inv in H; split_ands.
      eapply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn; context_map_rewrites; trivial.
      unfold honest_perm_filter_fn in H1.
      cases (honestk $? k_id); cases (ukeys $? k_id);
        try discriminate;
        solve_perm_merges;
        eauto.

      cases (findUserKeys (clean_users (honestk $k++ ukeys) cs usrs) $? k_id); solve_perm_merges; eauto.
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
      cases (clean_key_permissions honestk (key_heap e) $? k_id); solve_perm_merges; eauto.

    - assert ( honestk $? k_id = Some true )
        by (subst; eapply findUserKeys_has_private_key_of_user with (u_id := x); clean_map_lookups; eauto).
      assert (clean_key_permissions honestk (key_heap e) $? k_id = Some true).
      eapply clean_key_permissions_keeps_honest_permission; eauto.
      unfold honest_perm_filter_fn; context_map_rewrites; trivial.
      cases (findUserKeys (clean_users honestk cs usrs) $? k_id); solve_perm_merges; eauto.
  Qed.

  Lemma clean_users_no_change_honestk'' :
    forall {A} (usrs : honest_users A) honestk cs k_id,
        findUserKeys (clean_users honestk cs usrs) $? k_id = Some true
      -> findUserKeys usrs $? k_id = Some true.
  Proof.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; eauto.

    unfold findUserKeys; rewrite fold_add; eauto;
      rewrite findUserKeys_notation.

    rewrite clean_users_add_pull in H0; simpl in H.
    unfold findUserKeys in H0; rewrite fold_add in H0; eauto;
      simpl in H0;
      rewrite !findUserKeys_notation in H0;
      clean_map_lookups;
      eauto.

    apply merge_perms_split in H0.
    split_ors.

    - specialize (IHusrs _ _ _ H0); solve_perm_merges; eauto.
    - apply clean_key_permissions_inv in H0; split_ands; solve_perm_merges; eauto.
  Qed.

  Lemma clean_users_no_change_honestk' :
    forall {A} (usrs : honest_users A) cs k_id,
      findUserKeys (clean_users (findUserKeys usrs) cs usrs) $? k_id = Some true
      -> findUserKeys usrs $? k_id = Some true.
  Proof.
    intros.
    eapply clean_users_no_change_honestk''; eauto.
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
    solve_perm_merges; eauto.
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
    solve_perm_merges; eauto.
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
 
  Hint Resolve
       clean_key_permissions_ok_extra_user_cleaning
       clean_messages_idempotent
       .

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
      eapply clean_messages_idempotent; intros; eauto.
      pose proof (findUserKeys_clean_users_correct usrs cs k); context_map_rewrites; trivial.

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
