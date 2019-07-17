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
        Automation
        Simulation
        AdversaryUniverse.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Module Automation.

  Import RealWorld.

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

  Ltac msg_queue_prop :=
    match goal with
    | [ H1 : ?us $? _ = Some _, H2 : message_queues_ok _ _ ?us |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
    end;
    repeat match goal with
           | [ H : message_queue_ok _ _ (_ :: _) |- _ ] => invert H
           | [ H1: msg_honestly_signed _ _ = true -> _, H2: msg_honestly_signed _ _ = true |- _ ] =>
             specialize (H1 H2); split_ands
           end.

  Ltac user_cipher_queues_prop :=
    match goal with
    | [ H1 : ?us $? _ = Some _, H2 : user_cipher_queues_ok _ _ ?us |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
    end;
    repeat match goal with
           | [ H : user_cipher_queue_ok _ _ ?mycs, H1 : List.In _ ?mycs |- _ ] =>
             unfold user_cipher_queue_ok in H;
             rewrite Forall_forall in H;
             specialize (H _ H1);
             split_ex; split_ands; clean_map_lookups
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_findKeys in H
           | [ H : cipher_honestly_signed _ _ = true |- _ ] => simpl in H
           end.

  Ltac encrypted_ciphers_prop :=
    match goal with
    | [ H1 : ?cs $? _ = Some _, H2 : encrypted_ciphers_ok _ ?cs |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
    end;
    repeat match goal with
           | [ H : encrypted_cipher_ok _ _ _ |- _ ] => invert H
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_findKeys in H
           end; try contradiction.

End Automation.

Import Automation.

Section UniverseLemmas.
  Import RealWorld.

  Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
    {| users       := U__r.(users)
     ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                       ; msg_heap := U__r.(adversary).(msg_heap)
                       ; protocol := advcode
                       ; c_heap   := U__r.(adversary).(c_heap) |}
     ; all_ciphers := U__r.(all_ciphers)
     ; all_keys    := U__r.(all_keys)
    |}.

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

  Lemma keys_good_clean_keys :
    forall ks honestk,
      keys_good ks
      -> keys_good (clean_keys honestk ks).
  Proof.
    unfold keys_good; intros.
    eapply clean_keys_inv in H0; split_ands; eauto.
  Qed.

  (* Step user cipher queues ok *)

  (* Hint Rewrite @findUserKeys_multi_add_same_keys_idempotent *)
  (*      using (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial) : find_user_keys. *)

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
      autorewrite with find_user_keys; clean_context.

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

  Lemma adv_message_queue_ok_addnl_pubk :
    forall honestk pubk msgs,
      adv_message_queue_ok honestk msgs
      -> (forall k, pubk $? k = Some true -> False)
      -> adv_message_queue_ok (honestk $k++ pubk) msgs.
  Proof.
    unfold adv_message_queue_ok; induction 1; intros; econstructor; eauto.
    destruct x; intros.
    specialize (H _ H2).
    specialize (H1 k).
    cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; eauto.
    cases b; cases b0; subst; eauto.
  Qed.

  Hint Resolve adv_message_queue_ok_addnl_pubk.

  Lemma honest_labeled_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok honestk cs usrs
        -> adv_message_queue_ok honestk adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto;
      msg_queue_prop; eauto.

  Qed.

  Lemma honest_silent_step_adv_message_queue_ok :
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
        -> adv_message_queue_ok honestk adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto.

    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    rewrite merge_keys_mine; auto.
  Qed.

  Lemma adv_step_adv_message_queue_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> encrypted_ciphers_ok honestk cs
        -> adv_message_queue_ok honestk qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_message_queue_ok honestk' qmsgs'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; try discriminate; eauto;
        autorewrite with find_user_keys;
        try match goal with
            | [ H : adv_message_queue_ok _ (_ :: _) |- _] => invert H
            end; auto.
  Qed.

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
      specialize (H18 k_id).
      assert (findKeys msg $? k_id <> Some true) by eauto.
      intuition idtac.
      right; right.
      split; eauto.
      intros.
      eapply merge_perms_split in H9; split_ors; eauto.
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
        -> adv_message_queue_ok honestk qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - invert H19.
      unfold adv_no_honest_keys in *; intros.
      specialize (H1 k_id); specialize (H18 k_id); split_ors; intuition idtac.
      right; right; intuition eauto.
      eapply merge_perms_split in H; split_ors; auto.

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

  Qed.

  (* Encrypted ciphers ok adv step *)

  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Lemma encrypted_cipher_ok_addnl_pubk :
    forall honestk pubk c cs,
      encrypted_cipher_ok honestk cs c
      -> (forall k, pubk $? k = Some true -> False)
      -> encrypted_cipher_ok (honestk $k++ pubk) cs c.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
      cases (pubk $? k); simplify_key_merges1; eauto.
    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; eauto.
      + cases b; cases b0; subst; eauto.
      + invert H1; eauto.
    - eapply SigEncCipherAdvSignedOk.
      + unfold not; intros.
        cases (honestk $? k__s); cases (pubk $? k__s); simplify_key_merges1; clean_context; eauto.
        cases b; cases b0; subst; simpl in *; try discriminate; eauto.
      + intros. specialize (H0 _ H2).
        unfold not; intros.
        cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; clean_context; eauto.
        cases b; cases b0; subst; simpl in *; try discriminate; eauto.
    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      + cases (pubk $? k__s); simplify_key_merges1; eauto.
      + cases (pubk $? k__e); simplify_key_merges1; eauto.
      + unfold keys_mine in *; intros.
        specialize (H1 _ _ H4).
        split_ors; split_ands; subst;
          cases (pubk $? k_id); simplify_key_merges1; eauto.
          cases kp; cases b; subst; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_pubk :
    forall honestk pubk cs,
      encrypted_ciphers_ok honestk cs
      -> (forall k, pubk $? k = Some true -> False)
      -> encrypted_ciphers_ok (honestk $k++ pubk) cs.
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *; intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_pubk.
  Qed.

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

  Section RealWorldLemmas.
    Import RealWorld.

    Hint Extern 1 (_ $+ (?k, _) $? _ = Some _) => clean_map_lookups; trivial.

    Hint Resolve
         honest_cipher_filter_fn_proper
         honest_cipher_filter_fn_filter_proper
         honest_cipher_filter_fn_filter_transpose
         honest_cipher_filter_fn_filter_proper_eq
         honest_cipher_filter_fn_filter_transpose_eq.

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

    Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
    Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

    Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
         findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.



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
      forall {A B} (U : universe A B),
        findUserKeys U.(users) = findUserKeys (strip_adversary U).(s_users).
    Proof.
      intros; unfold strip_adversary; simpl.
      rewrite clean_users_no_change_findUserKeys; trivial.
    Qed.

    Lemma user_in_univ_user_in_stripped_univ :
      forall {A B} (U : universe A B) u_id user_data user_data',
        U.(users) $? u_id = Some user_data
        -> user_data' =
            {| key_heap := user_data.(key_heap)
             ; protocol := user_data.(protocol)
             ; msg_heap := clean_messages (findUserKeys U.(users)) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap) |}
        -> (strip_adversary U).(s_users) $? u_id = Some user_data'.
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

    Lemma msgCiphersSigned_before_clean_ciphers' :
      forall msgs honestk cs,
        Forall (msgCipherOk honestk (clean_ciphers honestk cs)) msgs
        -> Forall (msgCipherOk honestk cs) msgs.
    Proof.
      induction 1; econstructor; eauto.
      unfold msgCipherOk in *.
      destruct x; intuition idtac.
      destruct m; eauto.
      - repeat match goal with [H : exists _, _ |- _] => destruct H end.
        rewrite <- find_mapsto_iff in H; rewrite clean_ciphers_mapsto_iff in H;
          repeat eexists; split_ands;
            rewrite <- find_mapsto_iff; eauto.
      - rewrite <- find_mapsto_iff in H2; rewrite clean_ciphers_mapsto_iff in H2;
          repeat eexists; split_ands;
            rewrite <- find_mapsto_iff; eauto.
    Qed.

    Hint Resolve clean_ciphers_keeps_honest_cipher.

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
      repeat eexists; eauto.
    Qed.

    Lemma msgCiphersSigned_after_clean_ciphers :
      forall {t} (msg : message t) honestk cs,
        msgCiphersSigned honestk cs msg
        -> msgCiphersSigned honestk (clean_ciphers honestk cs) msg.
    Proof.
      intros; eapply msgCiphersSigned_after_clean_ciphers'; eauto.
    Qed.

    Lemma msgCiphersSigned_before_clean_ciphers :
      forall {t} (msg : message t) honestk cs,
        msgCiphersSigned honestk (clean_ciphers honestk cs) msg
        -> msgCiphersSigned honestk cs msg.
    Proof.
      intros; eapply msgCiphersSigned_before_clean_ciphers'; eauto.
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
      forall {A B} (U__ra U__r: universe A B) b,
          U__r = strip_adversary_univ U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      unfold universe_ok.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        rewrite clean_users_no_change_findUserKeys; subst; simpl in *; eauto.
    Qed.

    Lemma user_cipher_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        user_cipher_queues_ok cs honestk usrs
        -> honestk = findUserKeys usrs
        -> user_cipher_queues_ok (clean_ciphers honestk cs) honestk (clean_users honestk usrs).
    Proof.
      unfold user_cipher_queues_ok; intros.
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H1; unfold clean_users in H1; rewrite map_mapsto_iff in H1.
      invert H1; split_ands; rewrite H0. simpl in *.
      rewrite find_mapsto_iff in H1; specialize (H _ _ H1).
      unfold user_cipher_queue_ok in *; rewrite Forall_forall in *; intros.
      specialize (H _ H2); invert H; eexists.
      intuition eauto.
    Qed.

    Lemma message_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        message_queues_ok honestk cs usrs
        -> honestk = findUserKeys usrs
        -> message_queues_ok honestk (clean_ciphers honestk cs) (clean_users honestk usrs).
    Proof.
      unfold message_queues_ok; intros.
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H1; unfold clean_users in H1; rewrite map_mapsto_iff in H1.
      invert H1; split_ands; subst. simpl in *.
      rewrite find_mapsto_iff in H1; specialize (H _ _ H1).
      unfold message_queue_ok in *; rewrite Forall_forall in *; intros.
      destruct x0; simpl in *; intros.

      apply filter_In in H0; split_ands.
      specialize (H _ H0); simpl in H; intuition eauto.
    Qed.

    Lemma ok_adv_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary_univ U__ra b
        -> adv_universe_ok U__ra
        -> adv_universe_ok U__r.
    Proof.
      unfold adv_universe_ok.
      intros.
      subst; unfold adv_universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        try rewrite clean_users_no_change_findUserKeys;
        subst; simpl in *;
          eauto using user_cipher_queues_ok_after_cleaning
                    , message_queues_ok_after_cleaning
                    , keys_good_clean_keys.

    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         not_in_ciphers_not_in_cleaned_ciphers.

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

    Hint Resolve honest_key_filter_fn_proper honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose.

    Ltac solve_clean_keys :=
      match goal with
      | [  |- clean_keys ?honestk ?gks $? ?kid = Some _ ] =>
        match goal with
        | [ H : honestk $? kid = Some true |- _] => idtac
        | _ => assert (honestk $? kid = Some true) by eauto
        end; unfold clean_keys;
        rewrite <- find_mapsto_iff, filter_iff; auto; rewrite find_mapsto_iff;
        unfold honest_key_filter_fn;
        intuition context_map_rewrites; eauto
      end.

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
                  -> encrypted_ciphers_ok honestk' cs'
                  -> step_user lbl suid
                              (usrs__s, pwless_adv, cs__s, clean_keys honestk gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                              (usrs__s', pwless_adv', cs__s', clean_keys honestk' gks', ks', clean_messages honestk' qmsgs', mycs', cmd')
                  \/ (usrs__s, pwless_adv, cs__s, clean_keys honestk gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                    = (usrs__s', pwless_adv', cs__s', clean_keys honestk' gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 5; inversion 3; intros; subst; clean_context;
        try (erewrite findUserKeys_readd_user_same_keys_idempotent' by (trivial || unfold user_keys; context_map_rewrites; f_equal; trivial));
        (* autorewrite with find_user_keys in *; *)
        try solve [ left; econstructor; eauto; user_cipher_queues_prop; eauto; try solve_clean_keys ].

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
                                H32
                   ); split_ors.
        + clean_context.
          left; econstructor; eauto.

        + clean_context.
          right; invert H1; eauto.

      - cases (msg_honestly_signed (findUserKeys usrs') msg).
        + left. econstructor; eauto.
          unfold clean_messages, msg_filter; simpl; rewrite Heq; eauto.
        + right. simpl. rewrite Heq. trivial.

      - eapply Forall_natmap_in_prop with (k:= c_id) in H41; eauto; invert H41.
        * rewrite findUserKeys_readd_user_same_keys_idempotent' in H8.
          eapply findUserKeys_has_private_key_of_user in H36; eauto; contradiction.
          unfold user_keys; context_map_rewrites; auto.
        * rewrite findUserKeys_readd_user_same_keys_idempotent' in H11.
          2: unfold user_keys; context_map_rewrites; auto.
          left; econstructor; eauto; try solve_clean_keys.

      - left.
        autorewrite with find_user_keys.
        assert (findUserKeys usrs' $? k__encid = Some true) by eauto.
        clear H41; encrypted_ciphers_prop.
        + exfalso; unfold not in *.
          user_cipher_queues_prop.
          contradiction.

        + rewrite merge_keys_mine; eauto; econstructor; eauto; solve_clean_keys.

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

    Lemma clean_keys_nochange_pubk :
      forall honestk pubk ks,
        (forall k, pubk $? k = Some true -> False)
        -> clean_keys (honestk $k++ pubk) ks = clean_keys honestk ks.
    Proof.
      intros; unfold clean_keys, filter.

      induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
      rewrite !fold_add; eauto.
      rewrite IHks; trivial.

      assert (honest_key_filter_fn (honestk $k++ pubk) x e = honest_key_filter_fn honestk x e).
      unfold honest_key_filter_fn.
      specialize (H x).
      cases (honestk $? x); cases (pubk $? x); subst; simplify_key_merges1; eauto.
      destruct b0; try contradiction.
      rewrite orb_false_r; trivial.
      destruct b; try contradiction; auto.

      rewrite H1; trivial.
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
                                                                    ; c_heap := mycs' |})
                /\ clean_keys (findUserKeys usrs'') gks' = clean_keys (findUserKeys usrs') gks'.

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
        + erewrite clean_users_cleans_user; clean_map_lookups; eauto. simpl.
          f_equal.
          rewrite clean_messages_nochange_pubk; auto.
        + unfold clean_users.
          rewrite !map_o.
          clean_map_lookups.
          cases (usrs' $? y); simpl; auto.
          f_equal. f_equal.
          rewrite clean_messages_nochange_pubk; auto.
        + rewrite clean_keys_nochange_pubk; auto.

      - destruct rec_u; simpl in *.
        intuition idtac.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups.
        * erewrite clean_users_cleans_user; clean_map_lookups; eauto.
        * unfold clean_users; rewrite !map_o; clean_map_lookups; trivial.
    Qed.

      Lemma honest_labeled_step_encrypted_ciphers_ok :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok (findUserKeys usrs) cs usrs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs'.
    Proof.
      induction 1; inversion 5; inversion 2; intros; subst; try discriminate;
        eauto 2; autorewrite with find_user_keys;
          clean_context; eauto.

      assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
      msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
    Qed.

    Lemma honest_labeled_step_univ_ok :
      forall {A B} (U U' : universe A B) a__r,
        universe_ok U
        -> step_universe U (Action a__r) U'
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r
        -> message_queues_ok (findUserKeys U.(users)) U.(all_ciphers) U.(users)
        -> universe_ok U'.
    Proof.
      unfold universe_ok; intros.
      invert H0.
      destruct U; destruct userData.
      unfold buildUniverse, build_data_step in *; simpl in *.
      eapply honest_labeled_step_encrypted_ciphers_ok; eauto.
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
                          (usrs__s, pwless_adv, cs__s, clean_keys honestk gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                          (usrs__s', pwless_adv', cs__s', clean_keys honestk' gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
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
                  , honest_labeled_step_adv_message_queue_ok
                  , honest_labeled_step_adv_no_honest_keys.
    Qed.

    (* Lemma silent_step_adv_univ_implies_adv_universe_ok : *)
    (*   forall {A B} (U U' : universe A B), *)
    (*     step_universe U Silent U' *)
    (*     -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers) *)
    (*     -> adv_universe_ok U *)
    (*     -> adv_universe_ok U'. *)
    (* Proof. *)
    (*   intros. *)
    (*   invert H; *)
    (*     unfold adv_universe_ok in *; *)
    (*     destruct U; [destruct userData | destruct adversary]; *)
    (*       unfold build_data_step in *; simpl in *; *)
    (*         intuition *)
    (*           eauto using honest_silent_step_keys_good *)
    (*                     , honest_silent_step_user_cipher_queues_ok *)
    (*                     , honest_silent_step_message_queues_ok *)
    (*                     , honest_silent_step_adv_message_queue_ok *)
    (*                     , honest_silent_step_adv_no_honest_keys *)
    (*                     , adv_step_keys_good *)
    (*                     , adv_step_user_cipher_queues_ok *)
    (*                     , adv_step_message_queues_ok *)
    (*                     , adv_step_adv_message_queue_ok *)
    (*                     , adv_step_adv_no_honest_keys. *)
    (* Qed. *)

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
        -> universe_ok U'
        -> step_universe (strip_adversary_univ U b) Silent (strip_adversary_univ U' b)
        \/ strip_adversary_univ U b = strip_adversary_univ U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H1 as RW. clear HeqRW.

      (* assert (user_cipher_queue users u_id = Some (c_heap userData)); unfold user_cipher_queue; context_map_rewrites; eauto. *)
      unfold universe_ok in *; split_ands; simpl in *.
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv in RW; eauto.

      split_ors.
      - left.
        eapply StepUser; eauto; simpl.
        + eapply clean_users_cleans_user; eauto.
        + unfold build_data_step; simpl.
          exact H3.
        + unfold strip_adversary_univ, buildUniverse; simpl.
          rewrite clean_users_add_pull; simpl.
          clear H3.
          f_equal.

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        invert H3.
        f_equal; simpl in *.

        assert (clean_users (findUserKeys users) users =
                clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}))) usrs)
          by (apply map_eq_elements_eq; simpl; auto); clear H6.
        erewrite clean_users_add_pull; simpl.
        rewrite <- H3.
        rewrite <- H13.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups; eauto.
        eapply clean_users_cleans_user; eauto.
    Qed.

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok (findUserKeys U.(users)) U.(all_ciphers) U.(users)
        -> step_universe U (Action act) U'
        -> step_universe (strip_adversary_univ U b)
                        (Action act)
                        (strip_adversary_univ U' b).
    Proof.
      intros.

      assert (universe_ok U) as UNIV_OK by assumption.
      assert (universe_ok (strip_adversary_univ U b)) as STRIP_UNIV_OK by eauto using ok_universe_strip_adversary_still_ok.

      remember U as UU; destruct U; rename UU into U.

      repeat match goal with
             | [ H : step_universe _ _ _ |- _ ] => eapply labeled_univ_step_inv in H; eauto
             | [ H : exists _, _ |- _ ] => destruct H
             end; split_ands.

      rename H into for_split.
      unfold universe_ok in for_split; split_ands; simpl in *.

      rewrite HeqUU in H3; unfold build_data_step in H3; simpl in *.
      rewrite HeqUU; unfold strip_adversary_univ; simpl; eapply StepUser with (u_id:=x).
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
                                                         ; c_heap := x8 |})
              /\ clean_keys (findUserKeys usrs'') x5 = clean_keys (findUserKeys x2) x5 ).
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.
        split_ands.

        f_equal; auto.
    Qed.

    Hint Resolve dishonest_cipher_cleaned.

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

    Lemma adv_step_implies_no_new_keys_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk gks__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), cmd)
          -> honestk = findUserKeys usrs
          -> gks__s = clean_keys honestk gks
          -> forall cmd' honestk' gks__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> honestk' = findUserKeys usrs'
              -> gks__s' = clean_keys honestk' gks'
              -> gks__s = gks__s'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst; eauto;
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
      autorewrite with find_user_keys.

      rewrite clean_users_add_pull; simpl.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.
      clear H6 H18.

      erewrite clean_users_cleans_user; eauto; f_equal.
      cases (msg_honestly_signed (findUserKeys usrs) msg);
        eauto using clean_messages_drops_not_honestly_signed.

      exfalso.
      unfold msg_honestly_signed in Heq; destruct msg; try discriminate;
        simpl in *.


      admit.

    Admitted.

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : simpl_universe A -> IdealWorld.universe A -> Prop)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> R (strip_adversary U__r) U__i
        (* -> universe_ok U__r *)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := ks
                                                            ; protocol := cmd
                                                            ; msg_heap := qmsgs
                                                            ; c_heap   := mycs |})) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.

      Hint Resolve
           adv_step_implies_no_user_impact_after_cleaning
           adv_step_implies_no_new_keys_after_cleaning
           adv_step_implies_no_new_ciphers_after_cleaning.

      (* some rewrites to get the goal matching the R assumption *)
      match goal with
      | [ H : R {| s_users := ?us ; s_all_ciphers := ?cs ; s_all_keys := ?ks |} _
          |- R {| s_users := ?us' ; s_all_ciphers := ?cs' ; s_all_keys := ?ks' |} _ ] =>
        assert (cs = cs') as CS by eauto;
          assert (us = us') as US by eauto;
          assert (ks = ks') as KS by eauto
      end;
        rewrite <- CS, <- US, <- KS;
        trivial.
    Qed.

    Lemma honest_silent_step_adv_univ_enc_ciphers_ok' :
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
              -> forall cmdc cmdc' honestk',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> encrypted_ciphers_ok honestk' (clean_ciphers honestk' cs')
                -> encrypted_ciphers_ok honestk' cs'.
    Proof.
      induction 1; inversion 2; inversion 4; intros; subst;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        eauto.

      - rewrite clean_ciphers_keeps_added_honest_cipher in H34; simpl; eauto.
        eapply Forall_natmap_split in H34; auto; split_ands.
        econstructor; eauto.
        + assert ( (findUserKeys usrs') $? k__signid = Some true) by eauto.
          invert H7; try contradiction.
          eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
          unfold msgCiphersSigned in *.
          rewrite Forall_forall in *; intros.
          specialize (H18 _ H7).
          unfold msgCipherOk in *; destruct x; intuition idtac.
          destruct m; eauto.
          * destruct H12. destruct H12.
            repeat eexists.
            cases (c_id ==n msg_id); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H12; rewrite clean_ciphers_mapsto_iff in H12; split_ands; auto.
            rewrite find_mapsto_iff in H12; auto.
          * cases (c_id ==n sig); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H12; rewrite clean_ciphers_mapsto_iff in H12; split_ands; auto.
            rewrite find_mapsto_iff in H12; auto.
        + apply encrypted_ciphers_ok_addnl_cipher; auto.

      - user_cipher_queues_prop.
        encrypted_ciphers_prop.
        rewrite merge_keys_mine; auto.

      - rewrite clean_ciphers_keeps_added_honest_cipher in H30; simpl; eauto.
        eapply Forall_natmap_split in H30; auto; split_ands.
        assert (findUserKeys usrs' $? k_id = Some true) by eauto.
        invert H3; try contradiction.
        econstructor; eauto.
        + econstructor; eauto.
          unfold msgCiphersSigned in *.
          rewrite Forall_forall in *; intros.
          specialize (H12 _ H3).
          unfold msgCipherOk in *; destruct x; intuition idtac.
          destruct m; eauto.
          * destruct H8. destruct H8.
            repeat eexists.
            cases (c_id ==n msg_id); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H8; rewrite clean_ciphers_mapsto_iff in H8; split_ands; auto.
            rewrite find_mapsto_iff in H8; eauto.
          * cases (c_id ==n sig); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H8; rewrite clean_ciphers_mapsto_iff in H8; split_ands; auto.
            rewrite find_mapsto_iff in H8; auto.
        + eapply encrypted_ciphers_ok_addnl_cipher; auto.

    Qed.

    Lemma clean_ciphers_eq_absurd :
      forall cs honestk c_id c,
        ~ In c_id cs
        -> clean_ciphers honestk cs = clean_ciphers honestk cs $+ (c_id, c)
        -> False.
    Proof.
      intros.
      assert (Equal (clean_ciphers honestk cs) (clean_ciphers honestk cs $+ (c_id, c))) by (rewrite <- H0; apply Equal_refl).
      unfold Equal in H1; specialize (H1 c_id).
      clean_map_lookups; rewrite clean_ciphers_no_new_ciphers in H1; symmetry in H1; auto; clean_map_lookups.
    Qed.

    Hint Resolve clean_ciphers_eq_absurd.

    Lemma honest_silent_step_adv_univ_enc_ciphers_ok'' :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                b gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc' honestk' U__r U__r',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> U__r = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> U__r' = buildUniverse usrs' adv' cs' gks' u_id {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |}
                -> strip_adversary_univ U__r b = strip_adversary_univ U__r' b
                -> encrypted_ciphers_ok honestk' cs'.
    Proof.
      induction 1; inversion 2; inversion 4; unfold strip_adversary; intros; subst; simpl in *;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        eauto.

      - exfalso; invert H36.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H8; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H8; eauto.

      - invert H36.
        user_cipher_queues_prop.
        encrypted_ciphers_prop.
        rewrite merge_keys_mine; auto.

      - exfalso; invert H32.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H4; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H4; eauto.

    Qed.

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) (U__i : IdealWorld.universe A) (R : simpl_universe A -> IdealWorld.universe A -> Prop) lbl b,
        step_universe U lbl U'
        -> lbl = Silent
        -> adv_universe_ok U
        -> R (peel_adv (strip_adversary_univ U b)) U__i
        -> simulates_universe_ok R
        -> universe_ok U
        -> universe_ok U'.
     Proof.
       intros.
       rewrite peel_strip_univ_eq_strip_adv in H2.
       eapply H3; eauto.
     Qed.

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
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : B),
      simulates_silent_step (lameAdv b) R
      -> simulates_universe_ok R
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 (* /\ universe_ok U__ra' *)
                 /\ R (strip_adversary U__ra') U__i'.
  Proof.
    intros.

    assert (universe_ok (strip_adversary_univ U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok U__ra) as AOK by assumption;
      unfold adv_universe_ok in AOK; split_ands.

    assert (adv_universe_ok (strip_adversary_univ U__ra b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.

    assert (universe_ok U__ra')
      by (eauto using silent_step_advuniv_implies_univ_ok).

    match goal with
    | [ H : rstepSilent _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
               as U__ra'.

      (* pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H0 H5 H9 H10 HeqU__ra'). *)
      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H6 H11 H12 HeqU__ra' H10); split_ors.

      + assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
          as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).
        specialize (H _ _ H3 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ H4).
        repeat match goal with
               | [ H : exists _, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
               end.

        eexists; eauto.

      + exists U__i; intuition idtac; eauto.
        destruct U__ra; destruct U__ra'; simpl in *.
        unfold strip_adversary_univ in *; unfold strip_adversary in *; simpl in *.
        invert H4; auto.
        assert (clean_users (RealWorld.findUserKeys users) users = clean_users (RealWorld.findUserKeys users0) users0)
          as CLEAN_USERS by (unfold clean_users, map; auto).
        rewrite <- CLEAN_USERS; auto.

    (* Adversary step *)
    - exists U__i; intuition auto.
      eapply adv_step_stays_in_R; eauto.

  Qed.

  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : B),
      simulates_labeled_step (lameAdv b) R
      -> simulates_labeled_step_safe R
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      -> forall a__r U__ra',
          RealWorld.step_universe U__ra (Action a__r) U__ra'
          -> exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__r a__i
            /\ R (strip_adversary U__ra') U__i''.
  Proof.
    intros.

    assert (universe_ok (strip_adversary_univ U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok (strip_adversary_univ U__ra b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.
    unfold adv_universe_ok in H3; split_ands.

    assert (RealWorld.step_universe (strip_adversary_univ U__ra b) (Action a__r) (strip_adversary_univ U__ra' b))
      as UNIV_STEP.
    eapply labeled_honest_step_advuniv_implies_stripped_univ_step; eauto.

    assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
      as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).

    specialize (H _ _ H1 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ _ UNIV_STEP).
    repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 3 eexists; intuition idtac; eauto.
  Qed.

  Definition universe_starts_ok {A B} (U : RealWorld.universe A B) :=
    let honestk := RealWorld.findUserKeys U.(RealWorld.users)
    in  Forall_natmap (fun u => Forall (fun m => msg_filter honestk m = true) u.(RealWorld.msg_heap)) U.(RealWorld.users)
      /\ Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) U.(RealWorld.all_ciphers)
      /\ Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) U.(RealWorld.all_keys)
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

  Hint Unfold honest_cipher_filter_fn.

  Lemma universe_starts_ok_clean_keys_idempotent :
    forall honestk ks,
      Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) ks
      -> keys_good ks
      -> clean_keys honestk ks = ks.
  Proof.
    intros.
    rewrite Forall_natmap_forall in H.
    apply map_eq_Equal; unfold Equal; intros.
    cases (ks $? y); eauto using clean_keys_adds_no_keys.
    eapply clean_keys_keeps_honest_key; eauto.
    specialize (H _ _ Heq); invert H.
    specialize (H0 _ _ Heq).
    unfold honest_key_filter_fn; rewrite H0 in H1; context_map_rewrites; trivial.
  Qed.

  Lemma simulates_start_ok_adding_adversary :
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) b advcode,
        lameAdv b U__r.(RealWorld.adversary)
      -> U__ra = add_adversary U__r advcode
      -> R (RealWorld.peel_adv U__r) U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> universe_starts_ok U__r
      -> R (strip_adversary U__ra) U__i
      /\ universe_ok U__ra
      /\ adv_universe_ok U__ra.
  Proof.
    intros.
    unfold universe_ok, adv_universe_ok, lameAdv, RealWorld.peel_adv in *; split_ands; subst; simpl in *.
    destruct U__r; destruct adversary; simpl in *.
    intuition eauto.

    unfold strip_adversary; subst; simpl.

    unfold universe_starts_ok in *;
      split_ands.
    rewrite clean_ciphers_idempotent
          , universe_starts_ok_clean_keys_idempotent
          , universe_starts_ok_clean_users_idempotent; auto.
  Qed.

  Lemma strip_adv_simpl_peel_same_as_strip_adv :
    forall {A B} (U : RealWorld.universe A B),
      strip_adversary_simpl (RealWorld.peel_adv U) = strip_adversary U.
  Proof.
    unfold strip_adversary, strip_adversary_simpl, RealWorld.peel_adv; intros.
    trivial.
  Qed.

  Lemma strip_adv_simpl_strip_adv_idempotent :
    forall {A B} (U : RealWorld.universe A B),
      strip_adversary_simpl (strip_adversary U) = strip_adversary U.
  Proof.
    unfold strip_adversary_simpl, strip_adversary; simpl; intros.
    rewrite clean_users_no_change_findUserKeys,
            clean_users_idempotent,
            clean_ciphers_idempotent,
            clean_keys_idempotent
    ; eauto using clean_ciphers_honestly_signed.
  Qed. 

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : B),
        U__r <| U__i \ lameAdv b
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i \ @awesomeAdv B.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__univok H__o]; clear H__s.
    inversion H__o as [H__advsafe H__o']; clear H__o.
    inversion H__o' as [R__start OK__start]; clear H__o'.

    unfold refines.
    exists (fun ur ui => R (strip_adversary_simpl ur) ui); unfold simulates.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         (* simulates_labeled_step_adversary_safe *)
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, simulates_universe_ok, simulates_labeled_step_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.
      rewrite strip_adv_simpl_peel_same_as_strip_adv in H9.
      rewrite peel_strip_univ_eq_strip_adv; assumption.

    - eapply H__univok; eauto.
      rewrite <- strip_adv_simpl_strip_adv_idempotent; eassumption.

    - eapply  H__advsafe; eauto.
      rewrite <- strip_adv_simpl_strip_adv_idempotent; eassumption.
  Qed.

  Print Assumptions simulates_ok_with_adversary.

End SingleAdversarySimulates.


Inductive rCouldGenerate : forall {A B},
    RealWorld.universe A B -> list RealWorld.action -> Prop :=
| RCgNothing : forall A B (U : RealWorld.universe A B),
    rCouldGenerate U []
| RCgSilent : forall A B (U U' : RealWorld.universe A B) acts,
      rstepSilent U U'
    -> rCouldGenerate U' acts
    -> rCouldGenerate U acts
| RCgLabeled : forall A B (U U' : RealWorld.universe A B) acts a,
      RealWorld.step_universe U (Action a) U'
    -> rCouldGenerate U' acts
    -> rCouldGenerate U (a :: acts)
.

Inductive iCouldGenerate : forall {A},
    IdealWorld.universe A -> list IdealWorld.action -> Prop :=
| ICgNothing : forall A (U : IdealWorld.universe A),
    iCouldGenerate U []
| ICgSilent : forall A (U U' : IdealWorld.universe A) acts,
      istepSilent U U'
    -> iCouldGenerate U' acts
    -> iCouldGenerate U acts
| ICgLabeled : forall A (U U' : IdealWorld.universe A) acts a,
      IdealWorld.lstep_universe U (Action a) U'
    -> iCouldGenerate U' acts
    -> iCouldGenerate U (a :: acts)
.

Inductive traceMatches : list RealWorld.action -> list IdealWorld.action -> Prop :=
| TrMatchesNothing :
    traceMatches [] []
| TrMatchesLabel : forall {A B}(U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r acts__r a__i acts__i,
      rCouldGenerate U__r (a__r :: acts__r)
    -> iCouldGenerate U__i (a__i :: acts__i)
    -> traceMatches acts__r acts__i
    -> action_matches a__r a__i
    -> traceMatches (a__r :: acts__r) (a__i :: acts__i)
.

Lemma simulates_could_generate :
  forall A B (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop),
      simulates_silent_step (awesomeAdv (B:=B)) R
    -> simulates_labeled_step (awesomeAdv (B:=B)) R
    -> simulates_universe_ok R
    -> simulates_labeled_step_safe R
    -> forall (U__r : RealWorld.universe A B) acts__r,
        universe_ok U__r
        -> adv_universe_ok U__r
        -> rCouldGenerate U__r acts__r
        -> forall U__i,
            R (RealWorld.peel_adv U__r) U__i
            -> exists acts__i,
                iCouldGenerate U__i acts__i
              /\ traceMatches acts__r acts__i.
Proof.
  induction 7; intros; eauto.

  - eexists; split; swap 1 2; econstructor.
  - assert (awesomeAdv (RealWorld.adversary U)) as AWE by (unfold awesomeAdv; trivial).
    generalize (H _ _ H7 H3 H4 AWE _ H5); intro STEPPED;
      destruct STEPPED as [U__i' STEPPED]; split_ands.

    assert (exists acts__i : list IdealWorld.action, iCouldGenerate U__i' acts__i /\ traceMatches acts acts__i).
    eapply IHrCouldGenerate; eauto.
    eapply H1; eauto.
    unfold simulates_universe_ok in *.
    admit. admit.




Admitted.

Theorem refines_could_generate :
  forall A B (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
      U__r <| U__i \ @awesomeAdv B
    -> forall acts__r acts__i,
      rCouldGenerate U__r acts__r
      -> iCouldGenerate U__i acts__i
      /\ traceMatches acts__r acts__i.
Proof.
  unfold refines, simulates; intros.
  destruct H as [R H]; split_ands.

Admitted.
