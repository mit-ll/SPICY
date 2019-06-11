From Coq Require Import
     List
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

Require Import
        MyPrelude
        Maps
        Common
        MapLtac
        Keys
        Tactics
        Simulation.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Ltac clean_context :=
  try discriminate;
  repeat
    match goal with
    | [ H : ?X = ?X |- _ ] => clear H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : Action _ = Action _ |- _ ] => invert H; simpl in *; split_ands
    end.

Ltac simplify_key_merges1 :=
  match goal with
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
      => rewrite (merge_perms_chooses_greatest _ _ H1 H2) by trivial; unfold greatest_permission; simpl
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
      => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _ |- context [?ks1 $k++ ?ks2 $? ?kid]]
      => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None |- context [?ks1 $k++ ?ks2 $? ?kid]]
      => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) by trivial
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
      => rewrite (merge_perms_chooses_greatest _ _ H1 H2) in H3 by trivial; unfold greatest_permission in H3; simpl in *
  | [ H1 : ?ks1 $? ?kid = Some _
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
      => rewrite (merge_perms_adds_ks1 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = Some _
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
      => rewrite (merge_perms_adds_ks2 _ _ _ H1 H2) in H3 by trivial
  | [ H1 : ?ks1 $? ?kid = None
    , H2 : ?ks2 $? ?kid = None
    , H3 : ?ks1 $k++ ?ks2 $? ?kid = _ |- _ ]
      => rewrite (merge_perms_adds_no_new_perms _ _ _ H1 H2) in H3 by trivial
  end.

Section UniverseLemmas.
  Import RealWorld.

  Lemma adv_no_honest_keys_after_honestk_no_private_key_msg :
    forall {t} (msg : message t) honestk advk,
      adv_no_honest_keys honestk advk
      -> (forall (k_id : NatMap.key) (kp : bool), findKeys msg $? k_id = Some kp -> kp = false)
      -> adv_no_honest_keys (honestk $k++ findKeys msg) advk.
  Proof.
    unfold adv_no_honest_keys; intros; eauto;
      match goal with
      | [ kid : ?T, H : forall _ : ?T, _ \/ _ |- _ ] => specialize (H kid)
      end;
        split_ors; intuition idtac;
        cases (findKeys msg $? k_id);
        try match goal with
            | [ H1 : findKeys _ $? ?k_id = Some ?kp
              , H2 : forall k p, _ |- _ ] => specialize (H2 _ _ H1)
            end;
        subst; simplify_key_merges1; auto.
  Qed.

  Lemma msgCiphersSigned_after_msg_keys :
    forall {t} (msg : message t) cs honestk msgk,
      msgCiphersSigned honestk cs msg
      -> msgCiphersSigned (honestk $k++ msgk) cs msg.
  Proof.
    unfold msgCiphersSigned, msgCipherOk.
    induction 1; eauto.
    econstructor; eauto.
    destruct x; eauto.
    intuition idtac.
    apply message_honestly_signed_after_add_keys; auto.
  Qed.

  Hint Resolve msgCiphersSigned_after_msg_keys.

  (* Step keys good *)

  Lemma honest_labeled_step_keys_good :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
      step_user lbl u_id bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> keys_good gks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> keys_good gks'.
  Proof.
    induction 1; inversion 1; inversion 2; intros; subst; try discriminate; eauto.
  Qed.

  Lemma honest_silent_step_keys_good :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl u_id bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> keys_good gks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> keys_good gks'.
  Proof.
    induction 1; inversion 1; inversion 2; intros; subst; try discriminate; eauto.
  Qed.

  Lemma adv_step_keys_good :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> ks = adv.(key_heap)
        -> keys_good gks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> keys_good gks'.
  Proof.
    induction 1; inversion 1; inversion 3; intros; subst; try discriminate; eauto.
  Qed.

  Hint Rewrite @findUserKeys_readd_user_same_keys_idempotent'
       using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.
  Hint Rewrite @findUserKeys_readd_user_addnl_keys
       using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.

  (* Step user cipher queues ok *)

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

  Lemma user_cipher_queues_ok_readd_user :
    forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs,
      usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok cs
          (findUserKeys usrs)
          (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs |})).
  Proof.
    unfold user_cipher_queues_ok; intros.

    rewrite Forall_natmap_forall in *; intros.
    cases (k ==n u_id); subst; clean_map_lookups; eauto.
    rewrite <- Forall_natmap_forall in H0.
    simpl.
    eapply Forall_natmap_in_prop in H0; eauto.
    simpl in *; auto.
  Qed.

  Lemma user_cipher_queue_ok_addnl_global_cipher :
    forall honestk cs c_id c mycs,
      Forall (fun cid => exists c, cs $? cid = Some c /\ cipher_honestly_signed honestk c = true) mycs
      -> ~ In (elt:=cipher) c_id cs
      -> Forall (fun cid => exists c0, cs $+ (c_id,c) $? cid = Some c0 /\ cipher_honestly_signed honestk c0 = true) mycs.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    specialize (H _ H1); invert H.
    eexists; cases (c_id ==n x); subst; split_ands; clean_map_lookups; eauto.
  Qed.

  Hint Resolve user_cipher_queue_ok_addnl_global_cipher.

  Lemma user_cipher_queues_ok_addnl_global_cipher :
    forall {A} (usrs : honest_users A) honestk cs c_id c,
      user_cipher_queues_ok cs honestk usrs
      -> ~ In (elt:=cipher) c_id cs
      -> user_cipher_queues_ok (cs $+ (c_id,c)) honestk usrs.
  Proof.
    unfold user_cipher_queues_ok; intros.
    rewrite Forall_natmap_forall in *; intros; eauto.
    eapply user_cipher_queue_ok_addnl_global_cipher; eauto.
    eapply H; eauto.
  Qed.

  Lemma user_cipher_queue_ok_addnl_pubk :
    forall honestk pubk cs mycs,
      user_cipher_queue_ok cs honestk mycs
      -> user_cipher_queue_ok cs (honestk $k++ pubk) mycs.
  Proof.
    induction 1; intros; econstructor; eauto.
    invert H; eexists; intuition eauto.
    eapply cipher_honestly_signed_after_msg_keys; auto.
  Qed.

  Lemma user_cipher_queues_ok_addnl_pubk :
    forall {A} (usrs : honest_users A) honestk pubk cs,
      user_cipher_queues_ok cs honestk usrs
      -> user_cipher_queues_ok cs (honestk $k++ pubk) usrs.
  Proof.
    induction 1; intros; econstructor; eauto using user_cipher_queue_ok_addnl_pubk.
  Qed.

  Lemma msgCiphersSigned_user_cipher_queue_ok_findCiphers :
    forall {t} (msg : message t) honestk cs,
      msgCiphersSigned honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeys msg) (findCiphers msg).
  Proof.
    induction msg; intros; simpl in *; try solve [econstructor].
    - invert H; simpl in *; split_ands.
      destruct H0; destruct H0.
      econstructor; eauto.

    - invert H; simpl in *; split_ands; econstructor.
      + eexists; intuition eauto.
        simpl.
        eapply honest_keyb_true_findKeys in H.
        unfold honest_keyb; cases (findKeys msg $? k); simplify_key_merges1; trivial.
      + eapply IHmsg; eauto.

  Qed.

  Lemma user_cipher_queue_ok_add_user :
    forall {t} (msg : message t) cs honestk mycs,
      user_cipher_queue_ok cs honestk mycs
      -> msgCiphersSigned honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeys msg) (findCiphers msg ++ mycs).
  Proof.
    induction 1; intros.
    - rewrite app_nil_r;
        eapply msgCiphersSigned_user_cipher_queue_ok_findCiphers; auto.
    - unfold user_cipher_queue_ok; rewrite Forall_app_sym.
      rewrite <- app_comm_cons.
      econstructor.
      + invert H; eexists; intuition eauto.
        apply cipher_honestly_signed_after_msg_keys; auto.
      + rewrite Forall_app_sym.
        eapply IHForall; auto.
  Qed.

  Lemma user_cipher_queues_ok_add_user :
    forall {A t} (usrs usrs' : honest_users A) (msg : message t) honestk u_id ks cmd cmd' qmsgs qmsgs' mycs cs,
      user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> msgCiphersSigned (findUserKeys usrs) cs msg
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ findKeys msg; protocol := cmd'; msg_heap := qmsgs'; c_heap := findCiphers msg ++ mycs |})
      -> honestk = findUserKeys usrs'
      -> user_cipher_queues_ok cs honestk usrs'.
  Proof.
    unfold user_cipher_queues_ok; intros.
    rewrite Forall_natmap_forall in *; subst; intros.
    autorewrite with find_user_keys.
    cases (u_id ==n k); subst; clean_map_lookups.
    - specialize (H _ _ H0); simpl in *.
      eapply user_cipher_queue_ok_add_user; eauto.
    - eapply user_cipher_queue_ok_addnl_pubk; eauto.

  Qed.

  Hint Resolve
       user_cipher_queues_ok_addnl_global_cipher
       user_cipher_queues_ok_add_user
       user_cipher_queues_ok_readd_user
       user_cipher_queues_ok_addnl_pubk
  .

  Lemma findUserKeys_keys_mine_user :
    forall {A} (usrs : honest_users A) msgk u_id ks qmsgs cmd mycs ,
      keys_mine ks msgk
      -> usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs |}
      -> keys_mine (findUserKeys usrs) msgk.
  Proof.
    unfold keys_mine; intros.
    specialize (H _ _ H1); split_ors; split_ands; subst; eauto.
    - cases kp; subst; eauto.
      + erewrite findUserKeys_has_private_key_of_user; eauto.
      + assert (findUserKeys usrs $? k_id <> None).  eapply findUserKeys_has_key_of_user; eauto.
        cases (findUserKeys usrs $? k_id); clean_map_lookups; try contradiction.
        cases b; eauto.
    - erewrite findUserKeys_has_private_key_of_user; eauto.
  Qed.

  Hint Resolve findUserKeys_keys_mine_user.

  Lemma merge_keys_mine :
    forall ks1 ks2,
      keys_mine ks1 ks2
      -> ks1 $k++ ks2 = ks1.
  Proof.
    unfold keys_mine; intros.
    apply map_eq_Equal; unfold Equal; intros.
    specialize (H y).
    cases (ks1 $? y); cases (ks2 $? y); subst;
      try match goal with
          | [ H1 : ks2 $? _ = Some ?b
            , H2 : forall _ : bool, _ |- _ ]  =>   generalize  (H2 b); intro
          end;
      simplify_key_merges1; intuition (clean_context; eauto).
    rewrite orb_diag; trivial.
  Qed.

  Lemma accepted_safe_msg_pattern_honestly_signed :
    forall {t} (msg : message t) honestk pat,
      msg_pattern_safe honestk pat
      -> msg_accepted_by_pattern pat msg
      -> msg_honestly_signed honestk msg = true.
  Proof.
    intros.
    destruct msg;
      repeat match goal with
             | [ H : msg_pattern_safe _ _ |- _] => invert H
             | [ H : msg_accepted_by_pattern _ _ |- _] => invert H
             end; simpl; rewrite <- honest_key_honest_keyb; auto.
  Qed.

  Hint Resolve accepted_safe_msg_pattern_honestly_signed.

  Lemma honest_labeled_step_user_cipher_queues_ok :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a suid,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok honestk cs usrs
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate; eauto;
      autorewrite with find_user_keys;
      clean_context.

    - assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
      eapply Forall_natmap_in_prop in H17; eauto; simpl in *.
      invert H17. specialize (H2 H); split_ands.

      eapply user_cipher_queues_ok_add_user; eauto.
      autorewrite with find_user_keys; trivial.

    - remember ((usrs $+ (rec_u_id,
                          {| key_heap := key_heap rec_u;
                             protocol := protocol rec_u;
                             msg_heap := msg_heap rec_u ++ [existT message t0 msg];
                             c_heap := c_heap rec_u |}))) as usrs'.

      assert (findUserKeys usrs = findUserKeys usrs') as RW
        by (subst; autorewrite with find_user_keys; eauto).

      rewrite RW; clear RW.

      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
      destruct rec_u; simpl in *.
      autorewrite with find_user_keys.

      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.

  Qed.

  Lemma honest_silent_step_user_cipher_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; simpl; eauto.
      eapply Forall_natmap_in_prop in H21; eauto; simpl in *.
      + econstructor; eauto.

        eexists; clean_map_lookups; eauto.
        intuition eauto.
        assert (findUserKeys usrs' $? k__signid = Some true)
          by (eauto using findUserKeys_has_private_key_of_user).
        simpl; unfold honest_keyb; context_map_rewrites; auto.

      + eapply user_cipher_queues_ok_addnl_global_cipher; eauto.

    - eapply Forall_natmap_in_prop in H20; eauto.
      assert (findUserKeys usrs' $? k__encid = Some true) by eauto using findUserKeys_has_private_key_of_user.
      assert ( user_cipher_queues_ok cs' (findUserKeys usrs') usrs') as UCQOK by assumption.
      eapply Forall_natmap_in_prop in H21; eauto; simpl in *.
      eapply Forall_forall in H21; eauto; invert H21; split_ands; clean_map_lookups.
      simpl in *. unfold honest_keyb in H6.
      cases (findUserKeys usrs' $? k__signid); try discriminate.
      cases b; try discriminate.
      invert H20; try contradiction.

      eapply user_cipher_queues_ok_add_user; eauto.
      autorewrite with find_user_keys; trivial.

    - assert (user_cipher_queues_ok cs (findUserKeys usrs') usrs') as UCQOK by assumption.
      eapply Forall_natmap_in_prop in H17; eauto.
      assert (findUserKeys usrs' $? k_id = Some true) by eauto using findUserKeys_has_private_key_of_user.
      simpl in *.
      econstructor; simpl.
      + econstructor; eauto.
        eexists; clean_map_lookups; intuition eauto.
        simpl; unfold honest_keyb; context_map_rewrites; trivial.
      + eapply user_cipher_queues_ok_addnl_global_cipher; eauto.
  Qed.

  Lemma adv_step_user_cipher_queues_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> user_cipher_queues_ok cs' honestk' usrs'.
  Proof.
    induction 1; inversion 1; inversion 4; intros; subst; eauto.

    destruct rec_u; simpl in *;
      autorewrite with find_user_keys; eauto.
  Qed.

  (* Message queues ok step *)

  Lemma message_queue_ok_adding_public_keys :
    forall msgs cs honestk pubk,
      message_queue_ok honestk cs msgs
      -> (forall k kp, pubk $? k = Some kp -> kp = false)
      -> message_queue_ok (honestk $k++ pubk) cs msgs.
  Proof.
    unfold message_queue_ok; induction 1; eauto; intros;
      econstructor; eauto.

    destruct x; simpl in *; intros.
    assert (message_no_adv_private m /\ msgCiphersSigned honestk cs m)
      by (eauto using message_honestly_signed_after_remove_pub_keys).
    intuition idtac.
    eapply msgCiphersSigned_after_msg_keys; auto.
  Qed.

  Hint Resolve message_queue_ok_adding_public_keys.

  (* Lemma honest_keyb_msgk : *)
  (*   forall honestk msgk k, *)
  (*     honest_keyb (honestk $k++ msgk) k = true *)
  (*     -> (forall k : NatMap.key, msgk $? k = Some true -> honestk $? k <> Some true) *)
  (*     -> honest_keyb honestk k = true. *)
  (* Proof. *)
  (*   intros; rewrite <- honest_key_honest_keyb in *. *)
  (*   invert H. *)
  (*   apply merge_perms_split in H1; split_ors; constructor; auto. *)


  (* Lemma message_queue_ok_adding_msg_keys : *)
  (*   forall msgs cs honestk msgk, *)
  (*     message_queue_ok honestk cs msgs *)
  (*     -> (forall k, msgk $? k = Some true -> honestk $? k <> Some true) *)
  (*     -> message_queue_ok (honestk $k++ msgk) cs msgs. *)
  (* Proof. *)
  (*   unfold message_queue_ok; induction 1; eauto; intros; *)
  (*     econstructor; eauto. *)

  (*   destruct x; simpl in *; intros. *)
  (*   clear IHForall. *)



  (*   assert (message_no_adv_private m /\ msgCiphersSigned honestk cs m). *)
  (*   apply H; clear H. *)
  (*   unfold msg_honestly_signed in H2. *)
  (*   unfold msg_honestly_signed. *)
  (*   destruct m; eauto. *)
  (*    unfold honest_keyb in H2; unfold honest_keyb. *)
  (*   cases (honestk $? k__sign); cases (msgk $? k__sign); try simplify_key_merges1. *)


  (*     by (eauto using message_honestly_signed_after_remove_pub_keys). *)
  (*   intuition idtac. *)
  (*   eapply msgCiphersSigned_after_msg_keys; auto. *)
  (* Qed. *)




  Lemma message_queues_ok_adding_public_keys :
    forall {A} (usrs : honest_users A) cs honestk pubk,
      message_queues_ok honestk cs usrs
      -> (forall k kp, pubk $? k = Some kp -> kp = false)
      -> message_queues_ok (honestk $k++ pubk) cs usrs.
  Proof.
    induction 1; intros; econstructor; eauto.
    eapply IHForall_natmap; intros; eauto.
  Qed.

  Hint Resolve message_queues_ok_adding_public_keys.

  Lemma message_queues_ok_readd_user_same_queue :
    forall {A} (usrs : honest_users A) cs honestk u_id ks ks' cmd cmd' qmsgs mycs mycs',
      message_queues_ok honestk cs usrs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> message_queues_ok honestk cs (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' |})).
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; eauto; simpl.
    eapply Forall_natmap_in_prop in H; eauto; simpl in *; auto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_same_queue.

  Lemma msgCiphersSigned_addnl_cipher :
    forall cs msgs honestk c_id c,
      Forall (msgCipherOk honestk cs) msgs
      -> ~ In c_id cs
      -> Forall (msgCipherOk honestk (cs $+ (c_id,c))) msgs.
  Proof.
    induction msgs; intros; econstructor; invert H; eauto; clean_map_lookups.
    unfold msgCipherOk in H3. unfold msgCipherOk.
    destruct a; intuition idtac.
    destruct m; eauto.
    - invert H1; invert H2; repeat eexists.
      destruct (c_id ==n msg_id); subst; clean_map_lookups; eauto.
    - destruct (c_id ==n sig); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve msgCiphersSigned_addnl_cipher.

  Lemma message_queue_ok_addnl_cipher :
    forall msgs cs honestk c_id c,
      message_queue_ok honestk cs msgs
      -> ~ In c_id cs
      -> message_queue_ok honestk (cs $+ (c_id, c)) msgs.
  Proof.
    induction 1; intros; econstructor; eauto.
    - destruct x; simpl in *; intros.
      intuition idtac.
      apply msgCiphersSigned_addnl_cipher; auto.
    - apply IHForall; auto.
  Qed.

  Hint Resolve message_queue_ok_addnl_cipher.

  Lemma message_queues_ok_addnl_cipher :
    forall {A} (usrs : honest_users A) cs honestk c_id c,
      message_queues_ok honestk cs usrs
      -> ~ In c_id cs
      -> message_queues_ok honestk (cs $+ (c_id,c)) usrs.
  Proof.
    induction 1; intros; econstructor; eauto.
    eapply IHForall_natmap; auto.
  Qed.

  Hint Resolve message_queues_ok_addnl_cipher.

  Lemma message_contains_only_honest_public_keys_findkeys_no_priv :
    forall {t} (msg : message t) k honestk,
      msg_contains_only_honest_public_keys honestk msg
      -> findKeys msg $? k <> Some true.
  Proof.
    induction 1; simpl; unfold not; intros; auto.
    - invert H.
    - destruct kp; simpl in *; subst.
      cases (k ==n k0); subst; clean_map_lookups.
    - cases (findKeys msg1 $? k); cases (findKeys msg2 $? k); simplify_key_merges1; clean_context; try contradiction.
      cases b; cases b0; simpl in *; try contradiction; try discriminate.
    - invert H0.
  Qed.

  Hint Resolve message_contains_only_honest_public_keys_findkeys_no_priv.

  Lemma honest_labeled_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok honestk cs usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok honestk' cs' usrs''.
  Proof.
    induction 1; inversion 2; inversion 3; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    - assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
      assert (message_queues_ok (findUserKeys usrs') cs' usrs') as MQOK by assumption.
      eapply Forall_natmap_in_prop in MQOK; eauto; invert MQOK.
      specialize (H2 H); split_ands.
      econstructor; eauto.
      + simpl.
        eapply message_queue_ok_adding_public_keys; eauto.
        intros; unfold message_no_adv_private in *; specialize (H0 k).
        cases kp; try contradiction; trivial.

      + eapply message_queues_ok_adding_public_keys; eauto.
        intros; unfold message_no_adv_private in *; specialize (H0 k).
        cases kp; try contradiction; trivial.

    - assert (message_queues_ok (findUserKeys usrs) cs' usrs) as MQOK by assumption.
      eapply message_queues_ok_readd_user_same_queue; clean_map_lookups; eauto.
      destruct rec_u; simpl in *.
      eapply Forall_natmap_in_prop with (k:=rec_u_id) in MQOK; eauto; simpl in *.
      econstructor; eauto; simpl.
      eapply Forall_app; econstructor; eauto.
      intros; intuition idtac.
      unfold message_no_adv_private; intros.
      invert H; simpl in *; try discriminate.
      assert (findKeys msg0 $? k <> Some true) by eauto; contradiction.

  Qed.

  Lemma honest_silent_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs
        -> user_cipher_queues_ok cs honestk usrs
        -> message_queues_ok honestk cs usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok honestk' cs' usrs''.
  Proof.
    induction 1; inversion 2; inversion 5; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; eauto.
      eapply Forall_natmap_in_prop with (k:=u_id) in H15.
      2:exact H26.
      simpl in *; eauto.
      invert H15; eauto.

    - eapply message_queues_ok_readd_user_same_queue; eauto.
      eapply Forall_natmap_in_prop in H20; eauto.
      eapply Forall_natmap_in_prop in H21; eauto.
      simpl in *.
      unfold user_cipher_queue_ok in H21; rewrite Forall_forall in H21.
      specialize (H21 _ H8); invert H21; split_ands; clean_map_lookups.
      simpl in H5.
      apply honest_keyb_true_findKeys in H5.
      invert H20; try contradiction.
      rewrite merge_keys_mine; auto.
  Qed.

  Lemma adv_step_message_queues_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs
        -> message_queues_ok honestk cs usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> message_queues_ok honestk' cs' usrs'.
  Proof.
    induction 1; inversion 1; inversion 5; intros; subst;
      eauto 2; try discriminate; eauto;
        autorewrite with find_user_keys.

    destruct rec_u; simpl in *.
    econstructor; eauto; simpl.
    eapply Forall_natmap_in_prop in H17; eauto.
    simpl in *; eapply Forall_app; econstructor; eauto.

    destruct msg; simpl; intro; try discriminate; simpl in *.
    - unfold message_no_adv_private, msgCiphersSigned, msgCipherOk; simpl.
      intuition clean_map_lookups.

      econstructor; auto.
      intuition idtac.
      assert (exists t (m':message t), cs' $? msg_id = Some (SigEncCipher k__sign k__enc m')) by admit.
      simpl; auto.

    - assert (cs' $? sig = Some (SigCipher k msg)) by admit.
      eapply Forall_natmap_in_prop in H16; eauto.
      apply honest_keyb_true_findKeys in H.
      invert H16; try contradiction.
      intuition eauto.
      unfold msgCiphersSigned; simpl.
      econstructor; eauto.
      simpl.
      unfold honest_keyb; context_map_rewrites; intuition idtac.

  Admitted.


  (* Step adv no honest keys *)

  Lemma honest_labeled_step_adv_no_honest_keys :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok honestk cs usrs
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst;
      try discriminate; eauto 2;
        autorewrite with find_user_keys; eauto;
          clean_context.

    - assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
      eapply Forall_natmap_in_prop in H17; eauto; invert H17.
      assert ( message_no_adv_private msg /\ msgCiphersSigned (findUserKeys usrs') cs' msg ) by auto; split_ands.
      unfold adv_no_honest_keys, message_no_adv_private in *.
      intros.
      specialize (H18 k_id); specialize (H0 k_id); subst;
        intuition idtac; cases (findKeys msg $? k_id); simplify_key_merges1; auto;
          cases b; auto.

    - unfold adv_no_honest_keys in *; intros.
      specialize (H17 k_id).
      assert (findKeys msg $? k_id <> Some true) by eauto.
      intuition idtac.
      right; right.
      split; eauto.
      intros.
      eapply merge_perms_split in H7; split_ors; eauto.
  Qed.

  Lemma honest_silent_step_adv_no_honest_keys :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 5; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto.

    assert (findUserKeys usrs' $? k__encid = Some true) by eauto using findUserKeys_has_private_key_of_user.
    eapply Forall_natmap_in_prop in H21; eauto.
    simpl in H21; unfold user_cipher_queue_ok in H21; rewrite Forall_forall in H21.
    specialize (H21 _ H8).
    invert H21; split_ands; clean_map_lookups.

    eapply Forall_natmap_in_prop in H20; eauto.
    simpl in H6; unfold honest_keyb in H6.
    cases (findUserKeys usrs' $? k__signid); try discriminate; cases b; subst; try discriminate.
    invert H20; try contradiction.
    rewrite merge_keys_mine; eauto.
  Qed.

  Lemma adv_step_adv_no_honest_keys :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs
        -> adv_no_honest_keys honestk ks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 5; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - (* need property on adv message queue which enforces something about keys leaking *)
      admit.

    - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (ADV k__encid); split_ors; split_ands; try contradiction.
      + eapply Forall_natmap_in_prop in H20; eauto; invert H20;
          unfold adv_no_honest_keys; intros;
            specialize (H21 k_id); clean_map_lookups; intuition idtac.

        right; right; split; eauto; intros.
        eapply merge_perms_split in H6; split_ors; eauto.

      + eapply Forall_natmap_in_prop in H20; eauto; invert H20; 
          unfold adv_no_honest_keys; intros;
            specialize (H21 k_id); clean_map_lookups; intuition idtac.

        right; right; split; eauto; intros.
        eapply merge_perms_split in H6; split_ors; eauto.

  Admitted.

  (* Encrypted ciphers ok adv step *)

  Lemma encrypted_cipher_ok_addnl_cipher :
    forall honestk cs c_id c1 c2,
      encrypted_cipher_ok honestk cs c1
      -> ~ In c_id cs
      -> encrypted_cipher_ok honestk (cs $+ (c_id,c2)) c1.
  Proof.
    inversion 1; intros; try solve [ econstructor; eauto ].
    - econstructor; eauto.
      eapply msgCiphersSigned_addnl_cipher; auto.
    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      eapply msgCiphersSigned_addnl_cipher; auto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_cipher :
    forall honestk cs c_id c,
      Forall_natmap (encrypted_cipher_ok honestk cs) cs
      -> ~ In c_id cs
      -> Forall_natmap (encrypted_cipher_ok honestk (cs $+ (c_id, c))) cs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in *.
    intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_cipher.
  Qed.

  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Lemma adv_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> adv_no_honest_keys honestk ks
        -> encrypted_ciphers_ok honestk cs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs'.
  Proof.
    induction 1; inversion 1; inversion 5; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; eauto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H20 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros.
        specialize (H4 _ _ H6).
        specialize (ADV k); unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
    - econstructor; eauto.
      specialize (H16 k_id).
      eapply SigCipherNotHonestOk; unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
  Qed.

End UniverseLemmas.


(* Inductive couldGenerate : forall {A B}, RealWorld.universe A B -> list RealWorld.action -> Prop := *)
(* | CgNothing : forall {A B} (u : RealWorld.universe A), *)
(*     couldGenerate u [] *)
(* | CgSilent : forall {A} {u u' : RealWorld.universe A} tr, *)
(*     RealWorld.lstep_universe u Silent u' *)
(*     -> couldGenerate u' tr *)
(*     -> couldGenerate u tr *)
(* | CgAction : forall {A} a (u u' : RealWorld.universe A) tr, *)
(*     RealWorld.lstep_universe u (Action a) u' *)
(*     -> couldGenerate u' tr *)
(*     -> couldGenerate u (a :: tr). *)

Section SingleAdversarySimulates.

  (* If we have a simulation proof, we know that:
   *   1) No receives could have accepted spoofable messages
   *   2) Sends we either of un-spoofable, or were 'public' and are safely ignored
   *
   * This should mean we can write some lemmas that say we can:
   *   safely ignore all adversary messages (wipe them from the universe) -- Adam's suggestion, I am not exactly sure how...
   *   or, prove an appended simulation relation, but I am not sure how to generically express this
   *)
  Hint Resolve accepted_safe_msg_pattern_honestly_signed.

  Section AdversaryHelpers.
    Import RealWorld.

    Variable global_keys : keys.
    Variable honestk advk : key_perms.

    Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
      {| users       := U__r.(users)
       ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                         ; msg_heap := U__r.(adversary).(msg_heap)
                         ; protocol := advcode
                         ; c_heap   := U__r.(adversary).(c_heap) |}
       ; all_ciphers := U__r.(all_ciphers)
       ; all_keys    := U__r.(all_keys)
      |}.

    Definition msg_filter (sigM : { t & message t } ) : bool :=
      match sigM with
      | existT _ _ msg => msg_honestly_signed honestk msg
      end.

    Definition clean_messages (msgs : queued_messages) :=
      List.filter msg_filter msgs.

    Definition clean_users {A} (usrs : honest_users A) :=
      (* usrs. *)
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages u_d.(msg_heap)
                    ; c_heap   := u_d.(c_heap) |}) usrs.

    Definition honest_cipher_filter_fn (c_id : cipher_id) (c : cipher) :=
      cipher_honestly_signed honestk c.

    Lemma honest_cipher_filter_fn_proper :
      Proper (eq  ==>  eq  ==>  eq) honest_cipher_filter_fn.
    Proof.
      unfold Proper, Morphisms.respectful; intros; subst; reflexivity.
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
      unfold Proper, respectful; intros; subst; trivial.
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

  End AdversaryHelpers.

  Section RealWorldLemmas.
    Import RealWorld.

    Definition strip_adversary {A B} (U__r : universe A B) (b : B) : universe A B :=
      let honestk := findUserKeys U__r.(users)
      in {| users       := clean_users (findUserKeys U__r.(users)) U__r.(users)
          ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                            ; msg_heap := U__r.(adversary).(msg_heap)
                            ; protocol := Return b
                            ; c_heap   := U__r.(adversary).(c_heap) |}
          ; all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
          ; all_keys    := U__r.(all_keys)
         |}.

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
    Hint Rewrite @findUserKeys_multi_add_same_keys_idempotent
         using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys.

    Lemma univ_components :
      forall {A B} (U__r : universe A B),
        {| users       := users U__r
         ; adversary   := adversary U__r
         ; all_ciphers := all_ciphers U__r
         ; all_keys    := all_keys U__r
        |} = U__r.
      intros. destruct U__r; simpl; trivial.
    Qed.

    Lemma adduserkeys_keys_idempotent :
      forall {A} (us : user_list (user_data A)) ks uid ud,
        us $? uid = Some ud
        -> exists ud', addUsersKeys us ks $? uid = Some ud'.
    Proof.
      intros.
      (* eexists. *)
      unfold addUsersKeys, addUserKeys.
      apply find_mapsto_iff in H.
      eexists.
      rewrite <- find_mapsto_iff.
      rewrite map_mapsto_iff.
      eexists; intuition. eassumption.
    Qed.

    Lemma clean_ciphers_mapsto_iff : forall honestk cs c_id c,
        MapsTo c_id c (clean_ciphers honestk cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn honestk c_id c = true.
    Proof.
      intros.
      apply filter_iff; eauto.
    Qed.

    Lemma clean_ciphers_keeps_honest_cipher :
      forall c_id c honestk cs,
        cs $? c_id = Some c
        -> honest_cipher_filter_fn honestk c_id c = true
        -> clean_ciphers honestk cs $? c_id = Some c.
    Proof.
      intros.
      rewrite <- find_mapsto_iff.
      rewrite <- find_mapsto_iff in H.
      apply clean_ciphers_mapsto_iff; intuition idtac.
    Qed.

    Lemma honest_key_not_cleaned :
      forall cs c_id c honestk k,
        cs $? c_id = Some c
        -> k = cipher_signing_key c
        -> honest_key honestk k
        -> clean_ciphers honestk cs $? c_id = Some c.
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
      forall c_id c honestk cs k,
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
      cases c;
        rewrite Heq in H0; invert H0.
    Qed.

    Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher.

    Lemma clean_ciphers_reduces_or_keeps_same_ciphers :
      forall c_id c honestk cs,
        cs $? c_id = Some c
        -> ( clean_ciphers honestk  cs $? c_id = Some c
          /\ honest_keyb honestk (cipher_signing_key c) = true)
        \/ ( clean_ciphers honestk cs $? c_id = None
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
      forall c_id cs honestk,
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

    Hint Resolve clean_ciphers_no_new_ciphers.

    Lemma clean_ciphers_eliminates_added_dishonest_cipher :
      forall c_id c honestk cs k,
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
        cases c; simpl in *; rewrite H0; trivial.
    Qed.

    Lemma not_in_ciphers_not_in_cleaned_ciphers :
      forall c_id cs honestk,
          ~ In c_id cs
        -> ~ In c_id (clean_ciphers honestk cs).
    Proof.
      intros.
      rewrite not_find_in_iff in H.
      apply not_find_in_iff; eauto.
    Qed.

    Hint Resolve not_in_ciphers_not_in_cleaned_ciphers.

    Lemma honest_heap_private_honestk :
      forall {A} k_id ks u_id (usrs : honest_users A),
        ks $? k_id = Some true
        -> user_keys usrs u_id = Some ks
        -> honest_key (findUserKeys usrs) k_id.
    Proof.
      intros.
      constructor.
      unfold user_keys in *; cases (usrs $? u_id); subst; clean_map_lookups.
      eapply findUserKeys_has_private_key_of_user; eauto.
    Qed.

    Lemma adv_key_not_honestk :
      forall k_id honestk advk,
        advk $? k_id = Some true
        -> adv_no_honest_keys honestk advk
        -> honest_keyb honestk k_id = false.
    Proof.
      unfold adv_no_honest_keys, honest_keyb; intros.
      specialize (H0 k_id); split_ors; split_ands;
        context_map_rewrites; auto;
          contradiction.
    Qed.

    Hint Resolve
         honest_heap_private_honestk
         honest_key_not_cleaned
         adv_key_not_honestk.

    Lemma dishonest_cipher_cleaned :
      forall cs  honestk c_id cipherMsg,
          honest_keyb honestk (cipher_signing_key cipherMsg) = false
        -> ~ In c_id cs
        -> clean_ciphers honestk cs = clean_ciphers honestk (cs $+ (c_id, cipherMsg)).
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

    Hint Extern 1 (honest_cipher_filter_fn _ _ _ ?c = _) => unfold honest_cipher_filter_fn; cases c.

    Lemma clean_ciphers_added_honest_cipher_not_cleaned :
      forall honestk cs c_id c k,
          honest_key honestk k
        -> k = cipher_signing_key c
        -> clean_ciphers honestk (cs $+ (c_id,c)) = clean_ciphers honestk cs $+ (c_id,c).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      (* unfold honest_signing_key,honest_key in H. *)

      case (y ==n c_id); intros; subst; clean_map_lookups.
      - erewrite clean_ciphers_keeps_honest_cipher; auto.
        invert H; unfold honest_cipher_filter_fn; eauto.
        unfold cipher_honestly_signed, honest_keyb;
          cases c; simpl in *; context_map_rewrites; auto.
      - case_eq (clean_ciphers honestk cs $? y); intros; subst.
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
      forall uks cs,
        ciphers_honestly_signed uks cs
      -> clean_ciphers uks cs = cs.
    Proof.
      unfold clean_ciphers, filter, ciphers_honestly_signed; intros.
      apply P.fold_rec_bis; intros; Equal_eq; subst; eauto.
      unfold honest_cipher_filter_fn.
      rewrite find_mapsto_iff in H0.
      assert (cipher_honestly_signed uks e = true).
        eapply Forall_natmap_in_prop with (P := fun c => cipher_honestly_signed uks c = true); eauto.
      rewrite H2; trivial.
    Qed.

    Lemma clean_messages_keeps_honestly_signed :
      forall {t} (msg : message t) msgs honestk,
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

    Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
    Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

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

    Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
         findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

    Lemma clean_users_cleans_user :
      forall {A} (usrs : honest_users A) honestk u_id u_d u_d',
        usrs $? u_id = Some u_d
        -> u_d' = {| key_heap := u_d.(key_heap)
                  ; protocol := u_d.(protocol)
                  ; msg_heap :=  clean_messages honestk u_d.(msg_heap)
                  ; c_heap   := u_d.(c_heap) |}
        -> clean_users honestk usrs $? u_id = Some u_d'.
    Proof.
      intros.
      unfold clean_users; rewrite map_o; unfold option_map;
        context_map_rewrites; subst; auto.
    Qed.

    Lemma clean_users_cleans_user_inv :
      forall {A} (usrs : honest_users A) honestk u_id u_d,
        clean_users honestk usrs $? u_id = Some u_d
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
      forall {A} (usrs : honest_users A) honestk u_id u,
        clean_users honestk (usrs $+ (u_id,u))
          = clean_users honestk usrs $+ (u_id, {| key_heap := u.(key_heap)
                                                ; protocol := u.(protocol)
                                                ; msg_heap :=  clean_messages honestk u.(msg_heap)
                                                ; c_heap   := u.(c_heap) |}).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n u_id); subst; clean_map_lookups; eauto;
        unfold clean_users; rewrite !map_o; unfold option_map; clean_map_lookups; auto.
    Qed.

    Lemma clean_users_no_change_findUserKeys :
      forall {A} (usrs : honest_users A) honestk,
        findUserKeys (clean_users honestk usrs) = findUserKeys usrs.
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

    Lemma user_cipher_queue_cleaned_users_nochange :
      forall {A} (usrs : honest_users A) honestk u_id,
        user_cipher_queue (clean_users honestk usrs) u_id
        = user_cipher_queue usrs u_id.
    Proof.
      unfold user_cipher_queue, clean_users; simpl; intros.
      rewrite map_o; unfold option_map; simpl.
      cases (usrs $? u_id); auto.
    Qed.

    Lemma findUserKeys_same_stripped_univ :
      forall {A B} (U : universe A B) b,
        findUserKeys U.(users) = findUserKeys (strip_adversary U b).(users).
    Proof.
      intros; unfold strip_adversary; simpl.
      rewrite clean_users_no_change_findUserKeys; trivial.
    Qed.

    Lemma user_in_univ_user_in_stripped_univ :
      forall {A B} (U : universe A B) u_id user_data user_data' b,
        U.(users) $? u_id = Some user_data
        -> user_data' =
            {| key_heap := user_data.(key_heap)
             ; protocol := user_data.(protocol)
             ; msg_heap := clean_messages (findUserKeys U.(users)) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap) |}
        -> (strip_adversary U b).(users) $? u_id = Some user_data'.
    Proof.
      unfold strip_adversary, clean_users; destruct user_data; simpl; intros.
      rewrite <- find_mapsto_iff in H.
      rewrite <- find_mapsto_iff, map_mapsto_iff; eexists; subst; simpl; intuition eauto.
      simpl; trivial.
    Qed.

    Hint Resolve user_in_univ_user_in_stripped_univ.

    Lemma prop_in_adv_message_queues_still_good_after_cleaning :
      forall msgs honestk P,
        Forall P msgs
        -> Forall P (clean_messages honestk msgs).
    Proof.
      induction msgs; intros; eauto.
      invert H.
      unfold clean_messages; simpl.
      cases (msg_filter honestk a); eauto.
    Qed.

    Hint Resolve prop_in_adv_message_queues_still_good_after_cleaning.

    Lemma msgCiphersSigned_after_clean_ciphers' :
      forall msgs honestk cs,
        Forall (msgCipherOk honestk cs) msgs
        -> Forall (msgCipherOk honestk (clean_ciphers honestk cs)) msgs.
    Proof.
      induction 1; econstructor; eauto.
      unfold msgCipherOk in *.
      destruct x; intuition idtac.
      destruct m; eauto.
      repeat match goal with [H : exists _, _ |- _] => destruct H end.
      repeat eexists.
      eapply clean_ciphers_keeps_honest_cipher; eauto.
    Qed.

    Lemma msgCiphersSigned_after_clean_ciphers :
      forall {t} (msg : message t) honestk cs,
        msgCiphersSigned honestk cs msg
        -> msgCiphersSigned honestk (clean_ciphers honestk cs) msg.
    Proof.
      intros; eapply msgCiphersSigned_after_clean_ciphers'; eauto.
    Qed.

    Hint Resolve msgCiphersSigned_after_clean_ciphers.

    Lemma clean_ciphers_encrypted_ciphers_ok :
      forall honestk cs,
        encrypted_ciphers_ok honestk cs
        -> encrypted_ciphers_ok honestk (clean_ciphers honestk cs).
    Proof.
      unfold encrypted_ciphers_ok; intros; rewrite Forall_natmap_forall in *.
      intros.

      assert (clean_ciphers honestk cs $? k = Some v) as CSOK by assumption.
      rewrite <- find_mapsto_iff in CSOK.
      rewrite clean_ciphers_mapsto_iff in CSOK; split_ands.
      rewrite find_mapsto_iff in H1.
      specialize (H _ _ H1).
      unfold honest_cipher_filter_fn, cipher_honestly_signed in H2.

      destruct v.
      - eapply honest_keyb_true_findKeys in H2.
        invert H; try contradiction.
        econstructor; eauto.
      - eapply honest_keyb_true_findKeys in H2.
        invert H; try contradiction.
        eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
    Qed.

    Hint Resolve clean_ciphers_encrypted_ciphers_ok.

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      unfold universe_ok.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        rewrite clean_users_no_change_findUserKeys; subst; simpl in *; eauto.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user.

    Lemma cipher_message_keys_already_in_honest :
      forall {A t} (msg : message t) (usrs : honest_users A) honestk cs c_id k__s k__e,
        honestk = findUserKeys usrs
        -> cs $? c_id = Some (SigEncCipher k__s k__e msg)
        -> honest_key honestk k__s
        -> honest_key honestk k__e
        -> encrypted_ciphers_ok honestk cs
        -> honestk $k++ findKeys msg = honestk.
    Proof.
      intros.
      invert H1; invert H2.
      eapply Forall_natmap_in_prop in H3; eauto; invert H3; try contradiction.
      rewrite merge_keys_mine; eauto.
    Qed.

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl,
        step_universe U lbl U'
        -> lbl = Silent
        -> adv_no_honest_keys (findUserKeys U.(users)) U.(adversary).(key_heap)
        -> universe_ok U
        -> universe_ok U'.
    Proof.
      intros.
      invert H; auto; try discriminate.

      (* Honest step *)
      - destruct U; unfold build_data_step in *; simpl in *.
        unfold universe_ok in *; simpl in *.
        admit.

      (* adv step *)
      - destruct U; unfold build_data_step in *; simpl in *.
        unfold universe_ok in *; simpl in *; split_ands;
          eauto using adv_step_encrypted_ciphers_ok.

    Admitted.


    Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' (b: B),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok honestk cs
          (* -> user_keys usrs u_id = Some ks *)
          (* -> user_cipher_queue usrs u_id = Some mycs *)
          -> user_cipher_queues_ok cs honestk usrs
          -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv' honestk',
                 bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> pwless_adv = {| key_heap := key_heap adv
                              ; protocol := Return b
                              ; msg_heap := adv.(msg_heap)
                              ; c_heap   := adv.(c_heap) |}
              -> pwless_adv' = {| key_heap := key_heap adv'
                               ; protocol := Return b
                               ; msg_heap := adv'.(msg_heap)
                               ; c_heap   := adv'.(c_heap) |}

              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' usrs'
                  -> step_user lbl suid
                              (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                              (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd')
                  \/ (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                    = (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 5; inversion 3; intros; subst; clean_context;
        try (erewrite findUserKeys_readd_user_same_keys_idempotent' by (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial));
        (* autorewrite with find_user_keys in *; *)
        try solve [ left; econstructor; eauto ].

      - remember (findUserKeys usrs) as honestk.
        remember (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs'; c_heap := mycs' |})) as usrs''.
        remember (findUserKeys usrs'') as honestk'.
        remember (clean_ciphers honestk cs) as cs__s.
        remember (clean_ciphers honestk' cs') as cs__s'.
        remember (clean_users honestk usrs) as usrs__s.
        remember (clean_users honestk' usrs') as usrs__s'.
        remember ({| key_heap := key_heap adv; protocol := Return b; msg_heap := msg_heap adv |})
          as pwless_adv.
        remember ({| key_heap := key_heap adv'; protocol := Return b; msg_heap := msg_heap adv' |})
          as pwless_adv'.
        assert (@Silent action = Silent) as SIL by trivial.
        assert ((usrs,adv,cs,gks,ks,qmsgs,mycs,cmd1)=(usrs,adv,cs,gks,ks,qmsgs,mycs,cmd1)) as bd1 by trivial.
        assert ((usrs',adv',cs',gks',ks',qmsgs',mycs',cmd1')=(usrs',adv',cs',gks',ks',qmsgs',mycs',cmd1')) as bd1' by trivial.
        assert (Some u_id = Some u_id) by trivial. 

        specialize (IHstep_user _ _ _ _ _ H0 _ _ _ _
                                Heqhonestk
                                Heqcs__s
                                Hequsrs__s
                                bd1
                                H5
                                H14
                                _ _ _ _ _ _
                                bd1'
                                SIL
                                Heqpwless_adv
                                Heqpwless_adv'
                                _ _ _
                                H27
                                Hequsrs''
                                Heqhonestk'
                                Heqcs__s'
                                Hequsrs__s'
                   ); split_ors.
        + clean_context.
          left; econstructor; eauto.

        + clean_context.
          right; invert H1; eauto.

      - cases (msg_honestly_signed (findUserKeys usrs') msg).
        + left. econstructor; eauto.
          unfold clean_messages, msg_filter; simpl; rewrite Heq; eauto.
        + right. simpl. rewrite Heq. trivial.

      - left.
        autorewrite with find_user_keys.
        (* erewrite findUserKeys_readd_user_addnl_keys; eauto. *)
        eapply Forall_natmap_in_prop in H14; eauto.
        assert (findUserKeys usrs' $? k__encid = Some true) by eauto.
        invert H14; try contradiction.
        + exfalso; unfold not in *.
          eapply Forall_natmap_in_prop in H23; eauto.
          simpl in H23; unfold user_cipher_queue_ok in H23; rewrite Forall_forall in H23; specialize (H23 _ H8).
          invert H23; split_ands; clean_map_lookups.
          simpl in *.
          eapply honest_keyb_true_findKeys in H6; auto.

        + rewrite merge_keys_mine; eauto; econstructor; eauto.

      - left; econstructor; eauto.
        eapply Forall_natmap_in_prop in H17; eauto.
        simpl in H17; unfold user_cipher_queue_ok in H17; rewrite Forall_forall in H17; specialize (H17 _ H2).
        invert H17; split_ands; clean_map_lookups; eauto.

    Qed.

    Lemma honest_cipher_filter_fn_nochange_pubk :
      forall honestk pubk k v,
        (forall k, pubk $? k = Some true -> False)
        -> honest_cipher_filter_fn honestk k v =
          honest_cipher_filter_fn (honestk $k++ pubk) k v.
    Proof.
      unfold honest_cipher_filter_fn; intros;
        unfold cipher_honestly_signed;
        cases v; unfold honest_keyb; simpl.

      - cases (honestk $? k_id); cases (pubk $? k_id); simplify_key_merges1; auto;
          cases b; auto.
        destruct b0; simpl; eauto; exfalso; eauto.
        exfalso; eauto.

      - cases (honestk $? k__sign); cases (pubk $? k__sign); simplify_key_merges1; auto;
          cases b; auto.
        destruct b0; simpl; eauto; exfalso; eauto.
        exfalso; eauto.
    Qed.

    Lemma clean_ciphers_nochange_pubk :
      forall honestk pubk cs,
        (forall k, pubk $? k = Some true -> False)
        -> clean_ciphers (honestk $k++ pubk) cs = clean_ciphers honestk cs.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      rewrite fold_add; eauto; simpl.
      erewrite <- honest_cipher_filter_fn_nochange_pubk; eauto.
      subst; trivial.
    Qed.

    Lemma msg_filter_nochange_pubk :
      forall honestk pubk m,
        (forall k : NatMap.key, pubk $? k = Some true -> False)
        -> msg_filter (honestk $k++ pubk) m = msg_filter honestk m.
    Proof.
      unfold msg_filter, msg_honestly_signed; destruct m; intros; 
        cases m; unfold honest_keyb; simpl; auto.
      - cases (honestk $? k__sign); cases (pubk $? k__sign); simplify_key_merges1; auto;
          destruct b; auto.
        destruct b0; simpl; eauto; exfalso; eauto.
        exfalso; eauto.
      - cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; auto;
          destruct b; auto.
        destruct b0; simpl; eauto; exfalso; eauto.
        exfalso; eauto.
    Qed.

    Lemma clean_messages_nochange_pubk :
      forall honestk pubk qmsgs,
        (forall k, pubk $? k = Some true -> False)
        -> clean_messages (honestk $k++ pubk) qmsgs = clean_messages honestk qmsgs.
    Proof.
      induction qmsgs; intros; eauto.
      simpl.
      rewrite msg_filter_nochange_pubk; auto.
      rewrite IHqmsgs; eauto.
    Qed.

    Lemma clean_users_nochange_pubk :
      forall {A} (usrs: honest_users A) honestk pubk,
        (forall k, pubk $? k = Some true -> False)
        -> clean_users (honestk $k++ pubk) usrs = clean_users honestk usrs.
    Proof.
      intros; unfold clean_users.
      eapply map_eq_Equal; unfold Equal; intros.
      rewrite !map_o; simpl.
      cases (usrs $? y); eauto.
      simpl.
      f_equal. f_equal.
      rewrite clean_messages_nochange_pubk; trivial.
    Qed.

    Lemma honest_labeled_step_nochange_clean_ciphers_users_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok (findUserKeys usrs) cs usrs
        (* -> user_cipher_queues_ok (findUserKeys usrs) usrs cs *)
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') qmsgs' = clean_messages (findUserKeys usrs') qmsgs'
                /\ clean_users (findUserKeys usrs'') usrs'' =
                  clean_users (findUserKeys usrs') usrs' $+ (u_id, {| key_heap := ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := clean_messages (findUserKeys usrs') qmsgs'
                                                                    ; c_heap := mycs' |}).
    Proof.
      induction 1; inversion 4; inversion 2; intros; subst; try discriminate;
        eauto 2; autorewrite with find_user_keys;
          clean_context.

      - eapply Forall_natmap_in_prop in H8; eauto; simpl in *; invert H8.
        assert (message_no_adv_private msg /\ msgCiphersSigned (findUserKeys usrs') cs' msg) by eauto; split_ands.
        intuition eauto using clean_ciphers_nochange_pubk
                              , clean_messages_nochange_pubk.
                              (* , clean_users_nochange_pubk. *)

        eapply map_eq_Equal; unfold Equal; intros.
        cases (u_id ==n y); subst; clean_map_lookups.
        + erewrite clean_users_cleans_user; eauto. simpl.
          f_equal.
          rewrite clean_messages_nochange_pubk; auto.
        + unfold clean_users.
          rewrite !map_o.
          clean_map_lookups.
          cases (usrs' $? y); simpl; auto.
          f_equal. f_equal.
          rewrite clean_messages_nochange_pubk; auto.

      - destruct rec_u; simpl in *.
        intuition idtac.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups.
        * erewrite clean_users_cleans_user; eauto.
        * unfold clean_users; rewrite !map_o; clean_map_lookups; trivial.
    Qed.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a (b : B) suid,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok (findUserKeys usrs) cs usrs
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> forall cmdc cmdc' usrs'' honestk',
              usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
              -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
              -> honestk' = findUserKeys usrs''
              -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv',
                  cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' usrs'
                  -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
                  -> lbl = Action a
                  -> pwless_adv = {| key_heap := key_heap adv
                                  ; protocol := Return b
                                  ; msg_heap := adv.(msg_heap)
                                  ; c_heap   := adv.(c_heap) |}
                  -> pwless_adv' = {| key_heap := key_heap adv'
                                   ; protocol := Return b
                                   ; msg_heap := adv'.(msg_heap)
                                   ; c_heap   := adv'.(c_heap) |}
                  -> step_user lbl suid
                              (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                              (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 7; inversion 6; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
          autorewrite with find_user_keys.

 
      - eapply Forall_natmap_in_prop in H8; eauto; invert H8.
        assert (message_no_adv_private msg /\ msgCiphersSigned (findUserKeys usrs') cs' msg); eauto; split_ands.
        unfold message_no_adv_private in *.
        rewrite clean_users_nochange_pubk, clean_ciphers_nochange_pubk, clean_messages_nochange_pubk; eauto.

        assert ( msg_honestly_signed (findUserKeys usrs') msg = true ) by eauto.
        rewrite H3; econstructor; eauto.

      - econstructor; eauto.
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl.
        rewrite clean_messages_keeps_honestly_signed; auto.
    Qed.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv' :
      forall {A B C} cs cs' lbl u_id suid (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a (b : B),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Action a
              -> pwless_adv = {| key_heap := key_heap adv
                              ; protocol := Return b
                              ; msg_heap := adv.(msg_heap)
                              ; c_heap   := adv.(c_heap) |}
              -> pwless_adv' = {| key_heap := key_heap adv'
                               ; protocol := Return b
                               ; msg_heap := adv'.(msg_heap)
                               ; c_heap   := adv'.(c_heap) |}
              -> step_user lbl suid
                          (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                          (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 6; inversion 4; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
            autorewrite with find_user_keys.

      - assert ( msg_honestly_signed (findUserKeys usrs') msg = true ) by eauto.
        rewrite H.
        econstructor; eauto.

      - econstructor; eauto.
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl; eauto.
        rewrite clean_messages_keeps_honestly_signed; simpl; trivial.
    Qed.

    Lemma labeled_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B) lbl a,
        step_universe U lbl U'
        -> lbl = Action a
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      invert H; try discriminate.
      unfold adv_universe_ok in *.
      destruct U; destruct userData.
      unfold build_data_step in *; simpl in *.
      intuition
        eauto using honest_labeled_step_keys_good
                  , honest_labeled_step_user_cipher_queues_ok
                  , honest_labeled_step_message_queues_ok
                  , honest_labeled_step_adv_no_honest_keys.
    Qed.

    Lemma silent_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B),
        step_universe U Silent U'
        -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers)
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      invert H;
        unfold adv_universe_ok in *;
        destruct U; [destruct userData | destruct adversary];
          unfold build_data_step in *; simpl in *;
            intuition
              eauto using honest_silent_step_keys_good
                        , honest_silent_step_user_cipher_queues_ok
                        , honest_silent_step_message_queues_ok
                        , honest_silent_step_adv_no_honest_keys
                        , adv_step_keys_good
                        , adv_step_user_cipher_queues_ok
                        , adv_step_message_queues_ok
                        , adv_step_adv_no_honest_keys.
    Qed.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto;
        match goal with [H : Action _ = _ |- _] => invert H end.
    Qed.

    Lemma honest_labeled_step_nochange_adversary_protocol :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> adv.(protocol) = adv'.(protocol).
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
    Qed.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
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
        (usrs : honest_users A) (adv : user_data B) gks cs,
        step_universe U (Action a) U'
        -> U = {| users        := usrs
               ; adversary    := adv
               ; all_ciphers  := cs
               ; all_keys     := gks
              |}
        -> exists (u_id : user_id) u_d u_d' usrs' adv' cs' gks' ks' qmsgs' mycs' cmd',
            usrs $? u_id = Some u_d
          /\ step_user (Action a) (Some u_id) (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
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
                   |}.
    Proof.
      intros.
      invert H; eauto.
      invert H1.
      unfold build_data_step; simpl.
      repeat eexists; intuition eauto.
    Qed.


    Lemma honest_silent_step_nochange_honestk :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                -> findUserKeys usrs'' = findUserKeys usrs'.
    Proof.
      induction 1; inversion 2; inversion 4; intros; try discriminate; subst;
        eauto 2; autorewrite with find_user_keys; eauto.

      eapply Forall_natmap_in_prop in H20; eauto.
      simpl in *; unfold user_cipher_queue_ok in *; rewrite Forall_forall in H20.
      specialize (H20 _ H8); invert H20; split_ands.
      clean_map_lookups; unfold cipher_honestly_signed in H5; rewrite <- honest_key_honest_keyb in H5.

      erewrite cipher_message_keys_already_in_honest; eauto.
    Qed.

    Lemma honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                -> findUserKeys usrs'' = findUserKeys usrs'
                /\ clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') qmsgs' = clean_messages (findUserKeys usrs') qmsgs'
                /\ clean_users (findUserKeys usrs'') usrs' = clean_users (findUserKeys usrs') usrs'.
    Proof.
      induction 1; inversion 2; inversion 4; intros; try discriminate; subst;
        try (erewrite findUserKeys_readd_user_same_keys_idempotent' by (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial));
        eauto.

      eapply Forall_natmap_in_prop in H20; eauto.
      simpl in *; unfold user_cipher_queue_ok in *; rewrite Forall_forall in H20.
      specialize (H20 _ H8); invert H20; split_ands.
      clean_map_lookups; unfold cipher_honestly_signed in H5; rewrite <- honest_key_honest_keyb in H5.

      autorewrite with find_user_keys.
      erewrite cipher_message_keys_already_in_honest; eauto.
    Qed.

    Hint Extern 1 (user_keys _ _ = Some _ ) => unfold user_keys; context_map_rewrites.

    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs cmd,
        universe_ok U
        -> user_cipher_queues_ok U.(all_ciphers) (findUserKeys U.(users)) U.(users)
        -> U.(users) $? u_id = Some userData
        -> step_user Silent (Some u_id)
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs |}
        -> step_universe (strip_adversary U b) Silent (strip_adversary U' b)
        \/ strip_adversary U b = strip_adversary U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H1 as RW. clear HeqRW.

      (* assert (user_cipher_queue users u_id = Some (c_heap userData)); unfold user_cipher_queue; context_map_rewrites; eauto. *)
      unfold universe_ok in *; split_ands.
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv in RW; eauto.

      split_ors.
      - left.
        eapply StepUser; eauto.
        unfold build_data_step; simpl.
        + exact H3.
        + unfold strip_adversary, buildUniverse; simpl.
          rewrite clean_users_add_pull; simpl.
          clear H3.
          f_equal.

      - right.
        unfold strip_adversary, buildUniverse; simpl.
        invert H3.
        f_equal; simpl in *.

        assert (clean_users (findUserKeys users) users =
                clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}))) usrs)
          by (apply map_eq_elements_eq; simpl; auto); clear H5.
        erewrite clean_users_add_pull; simpl.
        rewrite <- H3.
        rewrite <- H12.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups; eauto.
        eapply clean_users_cleans_user; eauto.
    Qed.

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        (* -> adv_no_honest_keys (findUserKeys (RealWorld.users U)) (U.(adversary).(key_heap)) *)
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok (findUserKeys U.(users)) U.(all_ciphers) U.(users)
        -> step_universe U (Action act) U'
        -> step_universe (strip_adversary U b)
                        (Action act)
                        (strip_adversary U' b).
    Proof.
      intros.

      assert (universe_ok U) as UNIV_OK by assumption.
      assert (universe_ok (strip_adversary U b)) as STRIP_UNIV_OK by eauto using ok_universe_strip_adversary_still_ok.

      remember U as UU; destruct U; rename UU into U.

      repeat match goal with
             | [ H : step_universe _ _ _ |- _ ] => eapply labeled_univ_step_inv in H; eauto
             | [ H : exists _, _ |- _ ] => destruct H
             end; split_ands.

      rename H into for_split.
      unfold universe_ok in for_split; split_ands; simpl in *.

      rewrite HeqUU in H3; unfold build_data_step in H3; simpl in *.
      rewrite HeqUU; unfold strip_adversary; simpl; eapply StepUser with (u_id:=x).
      - simpl; eapply clean_users_cleans_user; eauto.
      - unfold build_data_step; simpl.
        eapply honest_labeled_step_advuniv_implies_honest_step_origuniv'; subst; eauto.
        + simpl; reflexivity.
        + simpl; reflexivity.
        + simpl; repeat f_equal.
        + simpl; trivial.
      - unfold buildUniverse; subst; simpl in *.
        destruct x0; subst; simpl in *.
        remember (x2 $+ (x, {| key_heap := x6; protocol := x9; msg_heap := x7 ; c_heap := x8 |})) as usrs''.
        assert (clean_ciphers (findUserKeys usrs'') x4 = clean_ciphers (findUserKeys x2) x4
              /\ clean_messages (findUserKeys usrs'') x7 = clean_messages (findUserKeys x2) x7
              /\ clean_users (findUserKeys usrs'') usrs'' =
                clean_users (findUserKeys x2) x2 $+ (x, {| key_heap := x6
                                                         ; protocol := x9
                                                         ; msg_heap := clean_messages (findUserKeys x2) x7
                                                         ; c_heap := x8 |})  ).
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.
        split_ands.

        rewrite H.
        rewrite H6.
        f_equal.
    Qed.

    Lemma adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> cs__s = clean_ciphers honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.
    Qed.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> usrs__s = clean_users honestk usrs
          -> forall cmd' honestk' usrs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto.

      (* Send *)
      erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.

      rewrite clean_users_add_pull; simpl.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.
      clear H5 H17.

      (* This is just not true *)
      assert (msg_honestly_signed (findUserKeys usrs) msg = false) by admit.

      rewrite clean_messages_drops_not_honestly_signed; auto.
      erewrite clean_users_cleans_user; eauto.

    Admitted.

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) (b : B)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> R (strip_adversary U__r b) U__i
        (* -> universe_ok U__r *)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := adv.(key_heap) $k++ ks
                                                            ; protocol := cmd
                                                            ; msg_heap := qmsgs
                                                            ; c_heap   := mycs |}) b) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.
      (* unfold universe_ok in *; split_ands. *)

      Hint Resolve
           adv_step_implies_no_user_impact_after_cleaning
           adv_step_implies_no_new_ciphers_after_cleaning.

      (* some rewrites to get the goal matching the R assumption *)
      match goal with
      | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs ; all_keys := _ |} _
          |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' ; all_keys := _ |} _ ] =>
        assert (cs = cs') as CS by eauto;
          assert (us = us') as US by eauto
      end; rewrite <- CS, <- US.

      (* need to match up the adversaries *)
      admit.

    Admitted.

  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user.

  Hint Extern 1 (rstepSilent _ (strip_adversary _)) => 
    unfold RealWorld.buildUniverse, RealWorld.buildUniverseAdv, strip_adversary, RealWorld.findUserKeys;
      simpl.

  Hint Extern 1 (rstepSilent _ _) => eapply RealWorld.StepUser.
  Hint Extern 1 (RealWorld.step_user _ _ (RealWorld.build_data_step _ _) _) =>
    progress unfold RealWorld.build_data_step.

  Hint Extern 1 (RealWorld.step_user _ _ (_, _, _ , RealWorld.protocol _) _) => 
    match goal with
    | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H
    end.

  Hint Extern 1 (_ = _) => progress m_equal.
  Hint Extern 1 (_ = _) => progress f_equal.
  Hint Extern 1 (_ = _) =>
    progress unfold RealWorld.build_data_step, RealWorld.buildUniverse; simpl.
  Hint Extern 1 (_ = _) =>
    match goal with
    | [ H : RealWorld.adversary _ = _ |- _ ] => rewrite <- H
    end.
  Hint Extern 1 (_ = RealWorld.adversary _) => solve [ symmetry ; assumption ].

  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      simulates_silent_step R
      (* (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A), *)
      (*     R U__r U__i *)
      (*     -> universe_ok U__r *)
      (*     -> forall U__r', *)
      (*         rstepSilent U__r U__r' *)
      (*         -> exists U__i', (istepSilent) ^* U__i U__i' /\ universe_ok U__r' /\ R U__r' U__i') *)
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      (* -> user_cipher_queues_ok U__ra.(RealWorld.all_ciphers) (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.users) *)
      (* -> adv_no_honest_keys (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.adversary).(RealWorld.key_heap) *)
      -> R (strip_adversary U__ra b) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 /\ universe_ok U__ra'
                 /\ R (strip_adversary U__ra' b) U__i'.
  Proof.
    intros.

    assert (universe_ok (strip_adversary U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok U__ra) as AOK by assumption;
      unfold adv_universe_ok in AOK; split_ands.

    assert (universe_ok U__ra')
      by (eauto using silent_step_advuniv_implies_univ_ok).

    match goal with
    | [ H : rstepSilent _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
               as U__ra'.

      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H0 H5 H9 H10 HeqU__ra'); split_ors.

      + admit.
        (* specialize (H _ _ H2 STRIP_UNIV_OK _ _ H3). *)
        (* repeat match goal with *)
        (*        | [ H : exists _, _ |- _ ] => destruct H *)
        (*        | [ H : _ /\ _ |- _ ] => destruct H *)
        (*        end. *)

        (* eexists; eauto. *)

      + exists U__i; intuition idtac; eauto.
        rewrite <- H3; trivial.

    (* Adversary step *)
    - exists U__i; intuition idtac.
      + eapply TrcRefl.
      + unfold RealWorld.buildUniverseAdv in *; simpl in *.
        admit.
        (* eapply adv_step_stays_in_R; eauto. *)
        (* need to start with adv has no honest keys *)

  Admitted.

  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      simulates_labeled_step R
      (* (forall U__r U__i, *)
      (*     R U__r U__i *)
      (*     -> universe_ok U__r *)
      (*     -> forall a1 U__r', *)
      (*         RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *) *)
      (*         -> exists a2 U__i' U__i'', *)
      (*           istepSilent^* U__i U__i' *)
      (*         /\ IdealWorld.lstep_universe U__i' (Action a2) U__i'' *)
      (*         /\ action_matches a1 a2 *)
      (*         /\ R U__r' U__i'' *)
      (*         /\ universe_ok U__r') *)
      -> (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
            R U__r U__i ->
            forall (a__r : RealWorld.action) (U__ra U__r' : RealWorld.universe A B),
              RealWorld.step_universe U__ra (Action a__r) U__r'
              -> RealWorld.findUserKeys (U__ra.(RealWorld.users)) = RealWorld.findUserKeys (U__r.(RealWorld.users))
              -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__r)) U__r.(RealWorld.all_ciphers) a__r)
      -> R (strip_adversary U__ra b) U__i
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      (* -> message_queues_ok (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.all_ciphers) U__ra.(RealWorld.users) *)
      -> forall a__r U__ra',
          RealWorld.step_universe U__ra (Action a__r) U__ra'
          -> exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__r a__i
            /\ R (strip_adversary U__ra' b) U__i''
            (* /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__ra.(RealWorld.users)) a__r *)
            /\ universe_ok U__ra'.
  Proof.
    intros.

    assert (RealWorld.action_adversary_safe
              (RealWorld.findUserKeys (RealWorld.users (strip_adversary U__ra b)))
              (RealWorld.all_ciphers (strip_adversary U__ra b))
              a__r)
      as ADV_SAFE
        by eauto using findUserKeys_same_stripped_univ.

    rewrite <- findUserKeys_same_stripped_univ in ADV_SAFE.

    assert (universe_ok (strip_adversary U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (RealWorld.step_universe (strip_adversary U__ra b) (Action a__r) (strip_adversary U__ra' b))
      as UNIV_STEP.
    eapply labeled_honest_step_advuniv_implies_stripped_univ_step; eauto.
    admit.

    (* specialize (H _ _ H1 STRIP_UNIV_OK _ _ UNIV_STEP). *)
    (* repeat match goal with *)
    (*        | [ H : exists _, _ |- _ ] => destruct H *)
    (*        | [ H : _ /\ _ |- _ ] => destruct H *)
    (*        end. *)
    (* do 3 eexists; intuition idtac; eauto. *)

    (* eapply honest_labeled_step_advuniv_implies_univ_ok; eauto. *)
    admit.

  Admitted.

  Lemma simulates_labeled_step_adversary_safe :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i ->
          forall (a__r : RealWorld.action) (U__ra U__r' : RealWorld.universe A B),
            RealWorld.step_universe U__ra (Action a__r) U__r'
          -> RealWorld.findUserKeys (U__ra.(RealWorld.users)) = RealWorld.findUserKeys (U__r.(RealWorld.users))
          -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__r)) U__r.(RealWorld.all_ciphers) a__r)
      -> R (strip_adversary U__ra b) U__i
      -> forall a__r (U U__ra' : RealWorld.universe A B),
          RealWorld.step_universe U (Action a__r) U__ra'
          -> RealWorld.findUserKeys (RealWorld.users U) = RealWorld.findUserKeys (RealWorld.users U__ra)
          -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__ra)) U__ra.(RealWorld.all_ciphers) a__r.
  Proof.
    intros.

    assert (RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users (strip_adversary U__ra b))) (RealWorld.all_ciphers (strip_adversary U__ra b)) a__r)
      as ADV_SAFE.
    eapply H; eauto.
    erewrite <- findUserKeys_same_stripped_univ; eauto.

    erewrite findUserKeys_same_stripped_univ; eauto.
  Admitted.

  Print Assumptions simulates_with_adversary_labeled.

  Definition universe_starts_ok {A B} (U : RealWorld.universe A B) :=
    let honestk := RealWorld.findUserKeys U.(RealWorld.users)
    in  Forall_natmap (fun u => Forall (fun m => msg_filter honestk m = true) u.(RealWorld.msg_heap)) U.(RealWorld.users)
      /\ Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) U.(RealWorld.all_ciphers)
  .

  Lemma clean_honest_messages_idempotent :
    forall msgs honestk,
      Forall (fun m => msg_filter honestk m = true) msgs
      -> clean_messages honestk msgs = msgs.
  Proof.
    induction msgs; eauto; intros.
    invert H.
    simpl.
    rewrite H2.
    rewrite IHmsgs; auto.
  Qed.

  Lemma universe_starts_ok_clean_users_idempotent :
    forall {A} (usrs : RealWorld.honest_users A) honestk,
      Forall_natmap (fun u => Forall (fun m => msg_filter honestk m = true) u.(RealWorld.msg_heap)) usrs
      -> honestk = RealWorld.findUserKeys usrs
      -> clean_users honestk usrs = usrs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in H.
    apply map_eq_Equal; unfold Equal, clean_users; intros; rewrite map_o.

    cases (usrs $? y); auto.
    specialize (H _ _ Heq).
    destruct u; simpl in *.
    f_equal; f_equal.
    apply clean_honest_messages_idempotent; auto.
  Qed.

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

  Lemma simulates_start_ok_adding_adversary :
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) b advcode,
        is_powerless (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary) b
      -> U__ra = add_adversary U__r advcode
      -> R U__r U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> universe_starts_ok U__r
      -> R (strip_adversary U__ra b) U__i
      /\ universe_ok U__ra
      /\ adv_universe_ok U__ra.
  Proof.
    intros.
    unfold universe_ok, adv_universe_ok, is_powerless in *; split_ands; subst; simpl in *.
    destruct U__r; destruct adversary; simpl in *.
    intuition eauto.

    unfold strip_adversary; subst; simpl.

    erewrite real_univ_eq_fields_eq;
      unfold universe_starts_ok in *;
      split_ands;
      eauto using
            clean_ciphers_idempotent
          , universe_starts_ok_clean_ciphers_idempotent
          , universe_starts_ok_clean_users_idempotent.
  Qed.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) b,
      U__r <| U__i
      -> is_powerless (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary) b
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i.
  Proof.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__advsafe H__start]; clear H__s.
    inversion H__start as [R__start OK__start]; clear H__start.

    unfold refines.
    exists (fun ur ui => R (strip_adversary ur b) ui); unfold simulates.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_labeled_step_adversary_safe
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, simulates_labeled_step_safe in *.
    assert (R (strip_adversary U__ra b) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition eauto.
  Qed.

  Print Assumptions simulates_ok_with_adversary.

End SingleAdversarySimulates.
