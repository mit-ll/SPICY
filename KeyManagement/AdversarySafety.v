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

  Ltac msg_queue_prop :=
    match goal with
    | [ MQ : message_queues_ok _ _ ?us _ |- _ ] =>
      match goal with
      | [ H : us $? _ = Some _ |- _ ] => generalize (Forall_natmap_in_prop _ MQ H); simpl; intros
      | [ H : user_queue us ?uid = Some ?qmsgs |- _ ] =>
        idtac H;
        assert (exists cmd mycs ks, us $? uid = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs |})
          as USR by (unfold user_queue in H;
                     cases (us $? uid);
                     try discriminate;
                     match goal with
                     | [ H1 : Some _ = Some _ |- exists x y z, Some ?u = _ ] =>
                       invert H1; destruct u; eauto
                     end);
        do 3 (destruct USR as [?x USR]);
        generalize (Forall_natmap_in_prop _ MQ USR); simpl; intros
      end
    end;
    repeat match goal with
           | [ H : message_queue_ok _ _ (_ :: _) _ |- _ ] => invert H; split_ands
           | [ H1: msg_honestly_signed _ _ = true -> _, H2: msg_honestly_signed _ _ = true |- _ ] =>
             specialize (H1 H2); split_ands
           | [ MHS : msg_honestly_signed _ ?msg = _ , MTCH : match ?msg with _ => _ end |- _ ] =>
             unfold msg_honestly_signed in MHS; destruct msg; try discriminate; rewrite MHS in *;
             split_ands; simpl in *
           end.
    (* match goal with *)
    (* | [ H1 : ?us $? _ = Some _, H2 : message_queues_ok _ _ ?us _ |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros *)
    (* end; *)
    (* repeat match goal with *)
    (*        | [ H : message_queue_ok _ _ (_ :: _) _ |- _ ] => invert H *)
    (*        | [ H1: msg_honestly_signed _ _ = true -> _, H2: msg_honestly_signed _ _ = true |- _ ] => *)
    (*          specialize (H1 H2); split_ands *)
    (*        end. *)

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
    | [ H1 : ?cs $? _ = Some _, H2 : encrypted_ciphers_ok _ ?cs _ |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
    | [ H  : encrypted_ciphers_ok _ (?cs $+ (?cid,?c)) _ |- _ ] => generalize (Forall_natmap_in_prop_add H); intros
    end;
    repeat match goal with
           | [ H : encrypted_cipher_ok _ _ _ _ |- _ ] => invert H
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_findKeys in H
           end; try contradiction.

  Ltac keys_and_permissions_prop :=
    match goal with
    | [ H : keys_and_permissions_good ?gks ?usrs ?adv |- _ ] =>
      assert (keys_and_permissions_good gks usrs adv) as KPG by assumption; unfold keys_and_permissions_good in KPG; split_ands;
      match goal with
      | [H1 : ?usrs $? _ = Some _, H2 : Forall_natmap (fun u => permission_heap_good _ _) ?usrs |- _ ] =>
        generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
      end
    end.

  Ltac refine_signed_messages :=
    repeat
      match goal with
      | [ H1 : msg_pattern_safe ?honk _ ,
          H2 : msg_accepted_by_pattern _ ?msg,
          H3 : match ?msg with _ => _ end
          |- _ ] => assert (msg_honestly_signed honk msg = true) as HON_SIGN by eauto 2;
                  unfold msg_honestly_signed in *;
                  split_ands;
                  destruct msg;
                  try discriminate;
                  split_ands
      | [ COND : honest_keyb ?honk ?kid = _
        , H : if honest_keyb ?honk ?kid then _ else _ |- _ ] => rewrite COND in H
      end; split_ands.

  Ltac solve_maps1 :=
    match goal with
    | [ |- context [ _ $+ (?k1,_) $? ?k2 ] ] =>
      progress clean_map_lookups
      || destruct (k1 ==n k2); subst; clean_map_lookups
    | [ |- context [ ?m $? ?k ]] =>
      progress context_map_rewrites
      || cases (m $? k)
    end.

  Ltac process_keys_messages1 :=
    match goal with
    | [ H : msg_honestly_signed _ ?msg = _ |- _ ] => unfold msg_honestly_signed in H
    | [ |- context [ msg_honestly_signed _ ?msg ] ] => unfold msg_honestly_signed; destruct msg; try discriminate
    | [ |- let (_,_) := ?x in _] => destruct x
    | [ H : honest_keyb _ _ = _ |- _ ] => unfold honest_keyb in H
    | [ |- context [ honest_keyb _ _ ] ] => unfold honest_keyb
    | [ |- context [ if ?b then _ else _ ] ] => is_var b; destruct b
    end.

  Ltac process_keys_messages :=
    repeat process_keys_messages1;
    repeat solve_maps1;
    try discriminate; try contradiction; context_map_rewrites.

  Hint Resolve
       clean_honest_key_permissions_distributes
       adv_no_honest_key_honest_key
       honest_cipher_filter_fn_proper
       honest_cipher_filter_fn_filter_proper
       honest_cipher_filter_fn_filter_transpose
       honest_cipher_filter_fn_filter_proper_eq
       honest_cipher_filter_fn_filter_transpose_eq
       findUserKeys_foldfn_proper
       findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal
       findUserKeys_foldfn_transpose_Equal.


  Hint Extern 1 (_ $+ (?k, _) $? _ = Some _) => clean_map_lookups; trivial.
  Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
  Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

  Hint Extern 1 (honest_key_filter_fn _ _ _ = _) => unfold honest_key_filter_fn; context_map_rewrites.
  Hint Extern 1 (honest_perm_filter_fn _ _ _ = _) => unfold honest_perm_filter_fn; context_map_rewrites.

  Hint Extern 1 (user_cipher_queue _ _ = _) => unfold user_cipher_queue; context_map_rewrites.
  Hint Extern 1 (user_keys _ _ = Some _ ) => unfold user_keys; context_map_rewrites.

  (* Hint Extern 1 ( let (_,_) := ?x in ?x ) => destruct x. *)

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
    econstructor; intuition eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto using message_honestly_signed_after_add_keys.
  Qed.

  Lemma msgCiphersSigned_new_private_key :
    forall {t} (msg : message t) cs honestk k_id,
      msgCiphersSigned honestk cs msg
      -> msgCiphersSigned (honestk $+ (k_id,true)) cs msg.
  Proof.
    unfold msgCiphersSigned, msgCipherOk.
    induction 1; eauto.
    econstructor; eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto; process_keys_messages; eauto.
  Qed.

  Hint Resolve msgCiphersSigned_after_msg_keys msgCiphersSigned_new_private_key.

  (* Step keys and permissions good *)

  Lemma keys_and_permissions_good_user_new_pubk :
    forall {A B t} (usrs : honest_users A) gks (msg : message t) u_id u_d ks cmd qmsgs mycs (adv : user_data B),
      keys_and_permissions_good gks usrs adv
      -> (forall (k : NatMap.key) (kp : bool), findKeys msg $? k = Some kp -> gks $? k <> None)
      -> u_d = {| key_heap := ks $k++ findKeys msg
               ; msg_heap := qmsgs
               ; protocol := cmd
               ; c_heap := mycs |}
      -> user_keys usrs u_id = Some ks
      -> keys_and_permissions_good gks (usrs $+ (u_id,u_d)) adv.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition idtac.
    econstructor; eauto.
    subst; simpl.
    assert (user_keys usrs u_id = Some ks) as UKS by assumption.
    unfold user_keys in UKS; cases (usrs $? u_id); try discriminate; clean_map_lookups.
    destruct u; simpl in *.
    generalize (Forall_natmap_in_prop _ H Heq); simpl; intros.
    unfold permission_heap_good in H1; unfold permission_heap_good; intros.
    specialize (H1 k_id); specialize (H0 k_id).
    cases (key_heap $? k_id); cases (findKeys msg $? k_id); simplify_key_merges1; clean_map_lookups; eauto.
    specialize (H0 p).
    cases (gks $? k_id); eauto.
    exfalso; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_user_new_pubk.

  Lemma honest_labeled_step_keys_and_permissions_good :
    forall {A B C} suid u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> keys_and_permissions_good gks usrs adv
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> message_queues_ok (findUserKeys usrs) cs usrs gks
            -> action_adversary_safe (findUserKeys usrs) cs a
            -> forall usrs'' cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |}) 
                -> keys_and_permissions_good gks' usrs'' adv'.
  Proof.
    induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto; clean_context.

    - msg_queue_prop; split_ands.
      eapply keys_and_permissions_good_user_new_pubk; eauto.

    - unfold keys_and_permissions_good in *; split_ands; intuition idtac.
      + rewrite Forall_natmap_forall in *; intros.
        destruct (k ==n rec_u_id); destruct (k ==n u_id); subst; clean_map_lookups; simpl; eauto.
        specialize (H7 _ _ H3); eauto.
        specialize (H7 _ _ H29); eauto.
      + unfold permission_heap_good in *; intros.
        unfold keys_mine in *.
        simpl in *.
        cases (key_heap adv $? k_id); cases (findKeys msg $? k_id);
          simplify_key_merges1; clean_context; eauto.
        specialize (H0 _ _ Heq0); split_ors; split_ands;
          rewrite Forall_natmap_forall in H7; specialize (H7 _ _ H29 _ _ H0); simpl in H2; eauto.
  Qed.

  Lemma permission_heap_good_addnl_key :
    forall gks ks k_id k,
      permission_heap_good gks ks
      -> ~ In k_id gks
      -> keyId k = k_id
      -> permission_heap_good (gks $+ (k_id,k)) ks.
  Proof.
    unfold permission_heap_good; intros; subst.
    destruct (keyId k ==n k_id0); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve permission_heap_good_addnl_key.

  Lemma keys_and_permissions_good_addnl_key :
    forall {A B} gks (usrs : honest_users A) (adv : user_data B) k_id k,
      keys_and_permissions_good gks usrs adv
      -> ~ In k_id gks
      -> keyId k = k_id
      -> keys_and_permissions_good (gks $+ (k_id,k)) usrs adv.
  Proof.
    unfold keys_and_permissions_good; intros;
      rewrite Forall_natmap_forall in *; subst; split_ands; intuition eauto.
    destruct (keyId k ==n k_id); subst; clean_map_lookups; auto.
  Qed.

  Hint Resolve keys_and_permissions_good_addnl_key.

  Lemma honest_silent_step_keys_good :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> keys_and_permissions_good gks usrs adv
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc,
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> keys_and_permissions_good gks' usrs' adv'.
  Proof.
    induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto.
  Qed.

  Lemma adv_step_keys_good :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> ks = adv.(key_heap)
        -> keys_and_permissions_good gks usrs adv
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> keys_and_permissions_good gks' usrs' adv'.
  Proof.
    induction 1; inversion 1; inversion 3; intros; subst; try discriminate; eauto; clean_context.

    unfold keys_and_permissions_good in *;
      intros;
      split_ands;
      simpl in *; intuition idtac;
        rewrite Forall_natmap_forall in *; intros.

    - destruct (rec_u_id ==n k); subst; clean_map_lookups; simpl; eauto.
    - unfold permission_heap_good,keys_mine in *; intros.
      cases (key_heap adv $? k_id); cases (findKeys msg $? k_id); subst;
        simplify_key_merges1; clean_map_lookups; eauto.
      specialize (H0 _ _ Heq0); split_ors; split_ands; contra_map_lookup.
  Qed.

  Lemma permission_heap_good_clean_keys :
    forall honestk gks uks,                  (*  *)
      permission_heap_good gks uks
      -> permission_heap_good (clean_keys honestk gks) (clean_key_permissions honestk uks).
  Proof.
    unfold permission_heap_good; intros.
    apply clean_key_permissions_inv in H0; split_ands.
    specialize (H _ _ H0); split_ex.
    eexists; eapply clean_keys_keeps_honest_key; eauto.
  Qed.

  Hint Resolve permission_heap_good_clean_keys.

  Lemma keys_and_permissions_good_clean_keys :
    forall {A B} (usrs : honest_users A) (adv : user_data B) gks b,
      keys_and_permissions_good gks usrs adv
      -> keys_and_permissions_good
          (clean_keys (findUserKeys usrs) gks)
          (clean_users (findUserKeys usrs) usrs)
          (clean_adv adv (findUserKeys usrs) b).
  Proof.
    unfold keys_and_permissions_good; intros; split_ands.
    intuition (simpl; eauto).
    - eapply clean_keys_inv in H2; split_ands; eauto.
    - apply Forall_natmap_forall; intros.
      eapply clean_users_cleans_user_inv in H2; split_ex; split_ands.
      rewrite H3.
      eapply Forall_natmap_forall in H0; eauto; simpl in *; eauto.
  Qed.

  (* Step user cipher queues ok *)

  Lemma user_cipher_queues_ok_readd_user :
    forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs,
      usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok cs
          (findUserKeys usrs)
          (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok;
      rewrite Forall_natmap_forall; intros.
    cases (k ==n u_id); subst; clean_map_lookups; simpl;
      user_cipher_queues_prop; eauto.
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
    induction 1; intros; econstructor; eauto;
      split_ex; eexists; intuition eauto using cipher_honestly_signed_after_msg_keys.
  Qed.

  Lemma user_cipher_queues_ok_addnl_pubk :
    forall {A} (usrs : honest_users A) honestk pubk cs,
      user_cipher_queues_ok cs honestk usrs
      -> user_cipher_queues_ok cs (honestk $k++ pubk) usrs.
  Proof.
    induction 1; intros; econstructor; eauto using user_cipher_queue_ok_addnl_pubk.
  Qed.

  Lemma user_cipher_queue_ok_addnl_generated_key :
    forall honestk cs mycs k_id,
      user_cipher_queue_ok cs honestk mycs
      -> user_cipher_queue_ok cs (add_key_perm k_id true honestk) mycs.
  Proof.
    induction 1; intros; econstructor; eauto;
      split_ex; eexists; intuition eauto.

    destruct x0; unfold cipher_honestly_signed in *; simpl; 
      rewrite <- honest_key_honest_keyb in *;
      unfold add_key_perm;
      match goal with
      | [ H : honest_key _ ?kid |- _ ] => invert H; econstructor; destruct (k_id ==n kid); subst
      end; context_map_rewrites; clean_map_lookups; simpl; eauto;
        cases (honestk $? k_id); clean_map_lookups; auto.
  Qed.

  Lemma user_cipher_queues_ok_addnl_global_generated_key :
    forall {A} (usrs : honest_users A) ks cs k_id,
      ks = findUserKeys usrs
      -> Forall_natmap (fun u => user_cipher_queue_ok cs ks u.(c_heap)) usrs
      -> Forall_natmap (fun u => user_cipher_queue_ok cs (add_key_perm k_id true ks) u.(c_heap)) usrs.
  Proof.
    intros; rewrite Forall_natmap_forall in *;
      intros; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (add_key_perm k_id true (findUserKeys usrs))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok; rewrite Forall_natmap_forall; intros.

    assert (exists cmd' ks' qmsgs',
               usrs $? u_id = Some {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs |}).
    unfold user_cipher_queue in H; cases (usrs $? u_id); clean_map_lookups; destruct u; simpl in *;
      do 3 eexists; eauto.

    split_ex; destruct (k ==n u_id); subst; clean_map_lookups; simpl.
    user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
    clear H2; user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key' :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (findUserKeys usrs $+ (k_id,true))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |})).
  Proof.
    intros.
    pose proof (user_cipher_queues_ok_addnl_generated_key ks k_id _ cmd qmsgs H H0).
    unfold add_key_perm in H1 at 1; unfold greatest_permission in H1;
      cases (findUserKeys usrs $? k_id); simpl in *; eapply H1.
  Qed.

  Hint Resolve user_cipher_queues_ok_addnl_generated_key user_cipher_queues_ok_addnl_generated_key'.

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
        -> message_queues_ok honestk cs usrs gks
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
      invert H17.
      split_ands.
      destruct msg; simpl in *; try discriminate; split_ands;
        match goal with
        | [ H0 : honest_keyb _ ?kid = true, H : if honest_keyb _ ?kid then _ else _ |- _ ] =>
          rewrite H0 in H; simpl in H
        end; split_ands;
          rewrite ?merge_keys_right_identity; eapply user_cipher_queues_ok_add_user; autorewrite with find_user_keys; eauto.

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
        -> encrypted_ciphers_ok honestk cs gks
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

  Lemma message_no_adv_private_new_keys :
    forall {t} (msg : message t) honestk pubk,
      message_no_adv_private honestk msg
      -> message_no_adv_private (honestk $k++ pubk) msg.
  Proof.
    unfold message_no_adv_private; intros.
    specialize (H _ _ H0).
    cases (pubk $? k); simplify_key_merges; intuition eauto.
  Qed.

  Lemma message_no_adv_private_new_honestk :
    forall {t} (msg : message t) honestk k_id,
      message_no_adv_private honestk msg
      -> message_no_adv_private (honestk $+ (k_id,true)) msg.
  Proof.
    unfold message_no_adv_private; intros.
    specialize (H _ _ H0).
    destruct (k_id ==n k); subst; clean_map_lookups; intuition auto.
  Qed.

  Hint Resolve message_no_adv_private_new_keys message_no_adv_private_new_honestk.

  Lemma message_queue_ok_adding_public_keys :
    forall msgs cs honestk pubk ks,
      message_queue_ok honestk cs msgs ks
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> message_queue_ok (honestk $k++ pubk) cs msgs ks.
  Proof.
    unfold message_queue_ok; induction 1; eauto; intros;
      econstructor; eauto.

    destruct x; simpl in *; split_ands; split_ands; split; eauto; intros.
    destruct m; eauto;
      unfold honest_keyb in *;
      intuition idtac;
      repeat
        match goal with
        | [ |- context [ ?honk $k++ ?publick $? ?kid ]] =>
          cases (honestk $? kid); cases (pubk $? kid); simplify_key_merges1
        | [ |- context [ if ?b || _ then _ else _ ] ] => is_var b; destruct b
        | [ |- context [ if _ || ?b then _ else _ ] ] => is_var b; destruct b
        | [ |- context [ if ?b then _ else _ ] ] => is_var b; destruct b
        | [ PUB : pubk $? ?kid = Some _, H : (forall k kp, pubk $? k = Some kp -> _) |- _ ] => specialize (H _ _ PUB)
        end; simpl; intuition eauto; contra_map_lookup.
  Qed.

  Hint Resolve message_queue_ok_adding_public_keys.

  Lemma message_queues_ok_adding_public_keys :
    forall {A} (usrs : honest_users A) cs honestk pubk ks,
      message_queues_ok honestk cs usrs ks
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> message_queues_ok (honestk $k++ pubk) cs usrs ks.
  Proof.
    induction 1; intros; econstructor; eauto.
    eapply IHForall_natmap; intros; eauto.
  Qed.

  Hint Resolve message_queues_ok_adding_public_keys.

  Lemma message_queues_ok_readd_user_same_queue :
    forall {A} (usrs : honest_users A) cs honestk u_id ks ks' cmd cmd' qmsgs mycs mycs' gks,
      message_queues_ok honestk cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> message_queues_ok honestk cs (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; eauto; simpl.
    eapply Forall_natmap_in_prop in H; eauto; simpl in *; auto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_same_queue.

  Lemma message_queues_ok_readd_user_popped_queue :
    forall {A} (usrs : honest_users A) cs honestk u_id ks ks' cmd cmd' qmsgs mycs mycs' gks qmsg,
      message_queues_ok honestk cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsg :: qmsgs; c_heap := mycs |}
      -> message_queues_ok honestk cs (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_popped_queue.
  
  Hint Resolve msgCiphersSigned_addnl_cipher.

  Lemma message_queue_ok_addnl_cipher :
    forall msgs cs honestk c_id c gks,
      message_queue_ok honestk cs msgs gks
      -> ~ In c_id cs
      -> message_queue_ok honestk (cs $+ (c_id, c)) msgs gks.
  Proof.
    induction 1; intros; econstructor; eauto.
    - destruct x; simpl in *; intros.
      intuition idtac.
      destruct m; eauto.
      cases (honest_keyb honestk k__sign); intuition idtac; apply msgCiphersSigned_addnl_cipher; auto.
      cases (honest_keyb honestk k); intuition idtac; apply msgCiphersSigned_addnl_cipher; auto.
    - apply IHForall; auto.
  Qed.

  Hint Resolve message_queue_ok_addnl_cipher.

  Lemma message_queues_ok_addnl_cipher :
    forall {A} (usrs : honest_users A) cs honestk c_id c gks,
      message_queues_ok honestk cs usrs gks
      -> ~ In c_id cs
      -> message_queues_ok honestk (cs $+ (c_id,c)) usrs gks.
  Proof.
    induction 1; intros; econstructor; eauto.
    eapply IHForall_natmap; auto.
  Qed.

  Hint Resolve message_queues_ok_addnl_cipher.

  Lemma new_global_key_not_in_heaps :
    forall perms ks k_id,
      ~ In k_id ks
      -> permission_heap_good ks perms
      -> perms $? k_id = None.
  Proof.
    intros.
    cases (perms $? k_id); clean_map_lookups; trivial.
    match goal with
    | [ H : permission_heap_good _ ?perms, H1 : ?perms $? _ = _ |- _ ] =>
      specialize (H _ _ H1); split_ex; contra_map_lookup
    end.
  Qed.

  Hint Resolve new_global_key_not_in_heaps.

  Lemma message_queue_ok_addnl_global_key :
    forall msgs cs honestk k_id gks usage kt,
      message_queue_ok honestk cs msgs gks
      -> ~ In k_id gks
      -> permission_heap_good gks honestk
      -> message_queue_ok (honestk $+ (k_id,true)) cs msgs (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |} )).
  Proof.
    induction 1; intros; econstructor; eauto.
    - destruct x; simpl in *; intros.
      assert (honestk $? k_id = None) by eauto.
      split_ands.
      split.
      + intros.
        destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      + destruct m; split_ands; eauto;
            repeat
              match goal with
              | [ H : if honest_keyb ?honk ?k then _ else _ |- _ ] =>
                assert (k_id <> k) by (unfold not; intros; subst; clean_map_lookups; contradiction);
              cases (honest_keyb honk k)
              | [ H : honest_keyb ?honk ?k = ?tf |- _ ] =>
                assert (honest_keyb (honk $+ (k_id,true)) k = tf) as RW
                    by (unfold honest_keyb in *; cases (honk $? k); clean_map_lookups; context_map_rewrites; eauto);
            rewrite RW; clear RW H
              end; intuition eauto; clean_map_lookups; contradiction.

    - eapply IHForall; eauto.

  Qed.

  Lemma message_queues_ok_addnl_global_key :
    forall {A} (usrs : honest_users A) cs u_id k_id gks ks cmd cmd' qmsgs mycs usage kt,
      message_queues_ok (findUserKeys usrs) cs usrs gks
      -> ~ In k_id gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
      -> message_queues_ok (findUserKeys usrs $+ (k_id, true)) cs
                          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs |}))
                          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold message_queues_ok; rewrite Forall_natmap_forall; intros.
    destruct (k ==n u_id); subst; clean_map_lookups; simpl;
      msg_queue_prop;  eapply message_queue_ok_addnl_global_key; eauto.
  Qed.

  Hint Resolve message_queues_ok_addnl_global_key.

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
        -> message_queues_ok honestk cs usrs gks
        -> keys_and_permissions_good gks usrs adv
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok honestk' cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    - assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
      msg_queue_prop; econstructor; eauto.
      eapply message_queues_ok_adding_public_keys; eauto.

    - assert (message_queues_ok (findUserKeys usrs) cs' usrs gks') as MQOK by assumption.
      eapply message_queues_ok_readd_user_same_queue; clean_map_lookups; eauto.
      destruct rec_u; simpl in *.
      eapply Forall_natmap_in_prop with (k:=rec_u_id) in MQOK; eauto; simpl in *.
      econstructor; eauto; simpl.

      eapply Forall_app; econstructor; eauto.
      intuition idtac.
      + specialize (H0 _ _ H6).
        unfold keys_and_permissions_good in *; split_ands.
        eapply Forall_natmap_in_prop in H9; eauto; simpl in H9;
          split_ors; split_ands;
            match goal with
            | [ H : permission_heap_good _ ?ks , H1 : ?ks $? _ = _ |- _ ] =>
              specialize (H _ _ H1); split_ex; contra_map_lookup
            end.
      + destruct msg; try discriminate;
          unfold keys_and_permissions_good in *; split_ands;
            eapply Forall_natmap_in_prop in H7; eauto; simpl in H7;
              simpl in *;
              user_cipher_queues_prop;
              match goal with
              | [ H : msgCiphersSigned ?honk ?cphrs ?cipherMsg |- _ ] =>
                assert (msgCiphersSigned honk cphrs cipherMsg) as MCSGN by assumption;
                  unfold msgCiphersSigned in MCSGN;
                  apply Forall_inv in MCSGN; unfold msgCipherOk in MCSGN; split_ands; split_ex
              end; encrypted_ciphers_prop;
                unfold msg_honestly_signed in *;
                intuition contra_map_lookup;
                repeat
                  match goal with
                  | [ H : honest_keyb ?honk ?kid = _ |- context [ honest_keyb ?honk ?kid] ] => rewrite H
                  | [ |- context [ message_no_adv_private ] ] => unfold message_no_adv_private
                  | [ |- _ /\ _ ] => intuition eauto
                  end; simpl in *; clean_map_lookups; destruct p; eauto.
        exfalso; eauto.
        exfalso; eauto.
  Qed.

  Lemma merge_keys_addnl_honest :
    forall ks1 ks2,
      (forall k_id kp, ks2 $? k_id = Some kp -> ks1 $? k_id = Some true)
      -> ks1 $k++ ks2 = ks1.
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (ks1 $? y); cases (ks2 $? y); subst;
      try
        match goal with
        | [ H1 : ks2 $? _ = Some ?b
          , H2 : (forall _ _, ks2 $? _ = Some _ -> _) |- _ ]  => generalize (H2 _ _ H1); intros
        end; clean_map_lookups; simplify_key_merges; intuition eauto.
  Qed.

  Lemma honest_silent_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> permission_heap_good gks honestk
        -> message_queues_ok honestk cs usrs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok honestk' cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto.

    msg_queue_prop.
    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    econstructor; simpl; eauto.
    eapply message_queues_ok_adding_public_keys; eauto.
  Qed.

  Lemma adv_message_queue_ok_addnl_pubk :
    forall honestk pubk msgs gks,
      adv_message_queue_ok honestk msgs gks
      -> (forall k, pubk $? k = Some true -> False)
      -> adv_message_queue_ok (honestk $k++ pubk) msgs gks.
  Proof.
    unfold adv_message_queue_ok; induction 1; intros; econstructor; eauto.
    destruct x; intros.
    specialize (H _ H2).
    specialize (H1 k).
    split_ands; split; eauto.
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
        -> message_queues_ok honestk cs usrs gks
        -> adv_message_queue_ok honestk adv.(msg_heap) gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' adv'.(msg_heap) gks'.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.
    msg_queue_prop; eauto.
    eapply adv_message_queue_ok_addnl_pubk; eauto.
    intros.
    unfold message_no_adv_private in *; simpl in *; eauto.
    specialize (H2 _ _ H6); split_ands; discriminate.
  Qed.

  Lemma adv_message_queue_ok_addnl_honestk_key :
    forall {A} (usrs : honest_users A) adv_heap gks k_id usage kt,
      adv_message_queue_ok (findUserKeys usrs) adv_heap gks
      -> ~ In k_id gks
      -> adv_message_queue_ok
          (findUserKeys usrs $+ (k_id, true))
          adv_heap
          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold adv_message_queue_ok in *; apply Forall_forall; intros.
    rewrite Forall_forall in H; specialize (H x); destruct x; intros.
    specialize (H H1 _ H2); split_ands.
    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction; intuition idtac.
  Qed.

  Lemma adv_message_queue_ok_addnl_global_key :
    forall {A} (usrs : honest_users A) adv_heap gks k_id usage kt,
      adv_message_queue_ok (findUserKeys usrs) adv_heap gks
      -> ~ In k_id gks
      -> adv_message_queue_ok
          (findUserKeys usrs)
          adv_heap
          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold adv_message_queue_ok in *; apply Forall_forall; intros.
    rewrite Forall_forall in H; specialize (H x); destruct x; intros.
    specialize (H H1 _ H2); split_ands.
    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction; intuition idtac.
  Qed.

  Hint Resolve adv_message_queue_ok_addnl_honestk_key adv_message_queue_ok_addnl_global_key.

  Lemma honest_silent_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> message_queues_ok honestk cs usrs gks
        -> adv_message_queue_ok honestk adv.(msg_heap) gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' adv'.(msg_heap) gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context.

    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    rewrite merge_keys_addnl_honest; eauto.
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
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok honestk qmsgs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_message_queue_ok honestk' qmsgs' gks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; try discriminate; eauto;
        clean_context;
        autorewrite with find_user_keys;
        try match goal with
            | [ H : adv_message_queue_ok _ (_ :: _) _ |- _] => invert H
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
        -> message_queues_ok honestk cs usrs gks
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
      msg_queue_prop;
        unfold adv_no_honest_keys, message_no_adv_private in *;
        simpl in *;
        repeat
          match goal with
          | [ RW : honest_keyb ?honk ?kid = _ , H : if honest_keyb ?honk ?kid then _ else _ |- _] => rewrite RW in H
          | [ H : (forall k_id, findUserKeys _ $? k_id = None \/ _) |- (forall k_id, _) ] => intro KID; specialize (H KID)
          | [ |- context [ _ $k++ $0 ] ] => rewrite merge_keys_right_identity
          | [ FK : findKeys ?msg $? ?kid = Some _, H : (forall k p, findKeys ?msg $? k = Some p -> _)
              |- context [ _ $k++ findKeys ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try simplify_key_merges1
          | [ FK : findKeys ?msg $? ?kid = None |- context [ ?uks $k++ findKeys ?msg $? ?kid] ] =>
            split_ors; split_ands; simplify_key_merges1
          | [ H : (forall k p, findKeys ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeys ?msg $? ?kid] ] =>
            match goal with
            | [ H : findKeys msg $? kid = _ |- _ ] => fail 1
            | _ => cases (findKeys msg $? kid)
            end
          end; eauto.

      split_ors; split_ands; contra_map_lookup; eauto.

    - unfold adv_no_honest_keys in *; intros.
      specialize (H18 k_id).
      assert (findKeys msg $? k_id <> Some true) by eauto.
      intuition idtac.
      right; right; split; eauto; intros.

      eapply merge_perms_split in H8; split_ors; eauto.
  Qed.

  Lemma adv_no_honest_keys_after_new_honest_key :
    forall k_id adv_heap honestk gks,
      ~ In k_id gks
      -> adv_no_honest_keys honestk adv_heap
      -> permission_heap_good gks adv_heap
      -> adv_no_honest_keys (honestk $+ (k_id,true)) adv_heap.
  Proof.
    intros.
    unfold adv_no_honest_keys; intros.
    specialize (H0 k_id0).
    unfold permission_heap_good in *.
    destruct (k_id ==n k_id0); subst; clean_map_lookups; intuition eauto;
      right; right; split; auto; intros;
        match goal with
        | [ H : (forall kid kp, _ $? kid = Some kp -> _), ARG : adv_heap $? _ = Some _ |- _] => specialize (H _ _ ARG)
        end; split_ex; contra_map_lookup.
  Qed.

  Lemma adv_no_honest_keys_after_new_adv_key :
    forall k_id adv_heap honestk gks,
      ~ In k_id gks
      -> adv_no_honest_keys honestk adv_heap
      (* -> permission_heap_good gks adv_heap *)
      -> permission_heap_good gks honestk
      -> adv_no_honest_keys honestk (adv_heap $+ (k_id,true)).
  Proof.
    intros.
    unfold adv_no_honest_keys; intros.
    specialize (H0 k_id0).
    unfold permission_heap_good in *.
    destruct (k_id ==n k_id0); subst; clean_map_lookups; intuition eauto.
  Qed.

  Hint Resolve adv_no_honest_keys_after_new_honest_key adv_no_honest_keys_after_new_adv_key.

  Lemma honest_silent_step_adv_no_honest_keys :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> keys_and_permissions_good gks usrs adv
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
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context;
        match goal with
        | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
        end; eauto.

    assert (findUserKeys usrs' $? k__encid = Some true) by eauto using findUserKeys_has_private_key_of_user.
    user_cipher_queues_prop; encrypted_ciphers_prop.
    cases (findUserKeys usrs' $? k__signid); try discriminate; cases b; subst; try discriminate.
    rewrite merge_keys_addnl_honest; eauto.
  Qed.

  Hint Resolve
       findUserKeys_foldfn_proper_Equal
       findUserKeys_foldfn_transpose_Equal.

  Lemma users_permission_heaps_good_merged_permission_heaps_good :
    forall {A} (usrs : honest_users A) gks,
      Forall_natmap (fun u : user_data A => permission_heap_good gks (key_heap u)) usrs
      -> permission_heap_good gks (findUserKeys usrs).
  Proof.
    induction usrs using P.map_induction_bis; intros; Equal_eq; eauto.
    - unfold findUserKeys, fold, Raw.fold, permission_heap_good; simpl;
        intros; clean_map_lookups.

    - apply Forall_natmap_split in H0; auto; split_ands.
      specialize (IHusrs _ H0); clear H0.
      unfold permission_heap_good; intros.
      unfold permission_heap_good in H1.
      unfold findUserKeys in H0; rewrite fold_add in H0; eauto; rewrite findUserKeys_notation in H0.

      eapply merge_perms_split in H0; split_ors; eauto.
  Qed.

  Hint Resolve users_permission_heaps_good_merged_permission_heaps_good.

  Lemma add_key_perm_add_private_key :
    forall ks k_id,
      add_key_perm k_id true ks = ks $+ (k_id,true).
  Proof.
    intros; unfold add_key_perm; cases (ks $? k_id); subst; clean_map_lookups; eauto.
  Qed.

  Lemma adv_step_adv_no_honest_keys :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs adv
        -> adv_message_queue_ok honestk qmsgs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 7; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto;
        try rewrite add_key_perm_add_private_key; clean_context;
          match goal with
          | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
          end.

    - invert H20.
      unfold adv_no_honest_keys in *; intros.
      specialize (H1 k_id); specialize (H18 k_id); split_ors; intuition idtac.
      right; right; intuition eauto.
      eapply merge_perms_split in H2; split_ors; auto.
      specialize (H4 _ H2); split_ands; contradiction.

    - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (ADV k__encid); split_ors; split_ands; try contradiction;
        encrypted_ciphers_prop; clean_map_lookups; intuition idtac;
        unfold adv_no_honest_keys; intros;
          specialize (H21 k_id); clean_map_lookups; intuition idtac;
            right; right; split; eauto; intros;
              eapply merge_perms_split in H10; split_ors; eauto;
                specialize (H17 _ H10); split_ex; split_ands; contradiction.

    - eapply adv_no_honest_keys_after_new_adv_key; eauto.
    - eapply adv_no_honest_keys_after_new_adv_key; eauto.

  Qed.

  (* Encrypted ciphers ok adv step *)

  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Lemma encrypted_cipher_ok_addnl_pubk :
    forall honestk pubk gks c cs,
      encrypted_cipher_ok honestk cs gks c
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> encrypted_cipher_ok (honestk $k++ pubk) cs gks c.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
      cases (pubk $? k); simplify_key_merges; eauto.
      intros; cases (pubk $? k_id); simplify_key_merges; eauto.
    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; clean_map_lookups; eauto.
      specialize (H1 _ _ Heq0); split_ands; subst; clean_map_lookups; contradiction.
      specialize (H1 _ _ Heq0); split_ands; subst; contra_map_lookup.
    - eapply SigEncCipherAdvSignedOk; eauto.
      + unfold not; intros.
        cases (honestk $? k__s); cases (pubk $? k__s); simplify_key_merges1; clean_context; eauto.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups; contradiction.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups.

      + intros. specialize (H2 _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros.
        cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; clean_context; eauto.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups; contradiction.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups; contradiction.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      + cases (pubk $? k__s); simplify_key_merges1; eauto.
      + cases (pubk $? k__e); simplify_key_merges1; eauto.
      + unfold keys_mine in *; intros.
        specialize (H3 _ _ H6).
        split_ors; split_ands; subst;
          cases (pubk $? k_id); simplify_key_merges1; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_pubk :
    forall honestk pubk cs gks,
      encrypted_ciphers_ok honestk cs gks
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
      -> encrypted_ciphers_ok (honestk $k++ pubk) cs gks.
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *; intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_pubk.
  Qed.

  Hint Resolve encrypted_ciphers_ok_addnl_key.

  Lemma adv_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> adv_no_honest_keys honestk ks
        -> permission_heap_good gks ks
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context.

    - econstructor; eauto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H20 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros. clear H20.
        specialize (H4 _ _ H6); split_ors; split_ands; try discriminate.
        specialize (H21 _ _ H4); split_ex; eexists.
        specialize (ADV k); intuition eauto; contra_map_lookup.
    - econstructor; eauto.
      specialize (H16 k_id).
      eapply SigCipherNotHonestOk; eauto.
      unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
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

    Lemma user_cipher_queue_cleaned_users_nochange :
      forall {A} (usrs : honest_users A) honestk u_id,
        user_cipher_queue (clean_users honestk usrs) u_id
        = user_cipher_queue usrs u_id.
    Proof.
      unfold user_cipher_queue, clean_users; simpl; intros.
      rewrite map_o; unfold option_map; simpl.
      cases (usrs $? u_id); auto.
    Qed.

    Lemma user_in_univ_user_in_stripped_univ :
      forall {A B} (U : universe A B) u_id user_data user_data',
        U.(users) $? u_id = Some user_data
        -> user_data' =
            {| key_heap := clean_key_permissions (findUserKeys U.(users)) user_data.(key_heap)
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

    Hint Resolve clean_keys_keeps_honest_key.

    Lemma clean_ciphers_encrypted_ciphers_ok :
      forall honestk cs gks,
        encrypted_ciphers_ok honestk cs gks
        -> encrypted_ciphers_ok honestk (clean_ciphers honestk cs) (clean_keys honestk gks).
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

      (* findUserKeys usrs $? k_id = Some true *)
      (* -> findUserKeys (clean_users (findUserKeys usrs) usrs) $? k_id = Some true. *)

    Lemma clean_ciphers_encrypted_ciphers_ok' :
      forall honestk honestk' cs gks,
        encrypted_ciphers_ok honestk cs gks
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> encrypted_ciphers_ok honestk' (clean_ciphers honestk cs) (clean_keys honestk gks).
    Proof.
      unfold encrypted_ciphers_ok; intros; rewrite Forall_natmap_forall in *.
      intros.

      assert (clean_ciphers honestk cs $? k = Some v) as CSOK by assumption.
      rewrite <- find_mapsto_iff in CSOK.
      rewrite clean_ciphers_mapsto_iff in CSOK; split_ands.
      rewrite find_mapsto_iff in H2.
      specialize (H _ _ H2).
      unfold honest_cipher_filter_fn, cipher_honestly_signed in H3.

      destruct v;
        repeat
          match goal with
          | [ H : honest_keyb _ _ = true |- _ ] => eapply honest_keyb_true_findKeys in H
          | [ H : encrypted_cipher_ok _ _ _ _ |- _ ] => invert H; try contradiction
          end.

      - econstructor; eauto using msgCiphersSigned_cleaned_honestk.
      - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto using msgCiphersSigned_cleaned_honestk.
        intros KID KP FK; specialize (H12 _ _ FK); intuition eauto.
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
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac; subst; simpl in *; eauto.
      eapply clean_ciphers_encrypted_ciphers_ok'; eauto using clean_users_no_change_honestk.
    Qed.

    Lemma user_cipher_queue_ok_after_cleaning :
      forall cs honestk honestk' mycs,
        user_cipher_queue_ok cs honestk mycs
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> user_cipher_queue_ok (clean_ciphers honestk cs) honestk' mycs.
    Proof.
      unfold user_cipher_queue_ok; intros; rewrite Forall_forall in *;
        intros.
      specialize (H _ H1); split_ex; split_ands.
      eexists; intuition eauto.
      unfold cipher_honestly_signed in *.
      destruct x0; unfold honest_keyb in *;
        match goal with
        | [ |- context [ honestk' $? ?kid ]] =>
          cases (honestk $? kid); try discriminate;
            destruct b; try discriminate;
              assert (honestk' $? kid = Some true) as RW by auto 2;
              rewrite RW; trivial
        end.
    Qed.

    Lemma user_cipher_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk honestk' cs,
        user_cipher_queues_ok cs honestk usrs
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys (clean_users honestk usrs)
        -> user_cipher_queues_ok (clean_ciphers honestk cs) honestk' (clean_users honestk usrs).
    Proof.
      unfold user_cipher_queues_ok; intros.
      pose proof (clean_users_no_change_honestk usrs).
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H3; unfold clean_users in H3; rewrite map_mapsto_iff in H3.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H4; specialize (H _ _ H4).
      eapply user_cipher_queue_ok_after_cleaning; auto.
    Qed.

    Lemma message_queue_ok_after_cleaning :
      forall msgs honestk honestk' cs gks,
        message_queue_ok honestk cs msgs gks
        -> encrypted_ciphers_ok honestk cs gks
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> message_queue_ok honestk' (clean_ciphers honestk cs)
                           (clean_messages honestk msgs) (clean_keys honestk gks).
    Proof.
      intros; unfold message_queue_ok in *; rewrite Forall_forall in *; intros.
      destruct x; simpl in *; intros.

      apply filter_In in H2; split_ands.
      specialize (H _ H2); simpl in *.
      unfold msg_honestly_signed in H3; split_ands.

      split; intros.
      - specialize (H _ _ H5).
        unfold not; intros.
        cases (gks $? k); try contradiction.
        destruct m; simpl in *; try discriminate; split_ands.
        rewrite H3 in H7; split_ands.
        unfold message_no_adv_private in H7; simpl in *.
        unfold msgCiphersSigned in H8; simpl in H8; invert H8.
        unfold msgCipherOk in H11.
        specialize (H7 k); destruct kp; try contradiction.
        (* need to know all keys in signed message are honest *)
        split_ands; encrypted_ciphers_prop;
          assert (honestk $? k = Some true); auto.
        eapply clean_keys_keeps_honest_key with (honestk := honestk) in Heq; eauto.
        rewrite Heq in H6; discriminate.
        specialize (H7 _ H5); split_ands; discriminate.
        specialize (H7 _ H5); split_ands; discriminate.
        specialize (H7 _ H5); split_ands. eapply clean_keys_inv' in H6; eauto. unfold honest_key_filter_fn in H6; rewrite H7 in H6; discriminate.

      - destruct m; intuition eauto.
        + cases (gks $? k__sign); try contradiction.
          eapply clean_keys_keeps_honest_key with (honestk := honestk) in Heq; contra_map_lookup.
          unfold honest_key_filter_fn; unfold honest_keyb in *; assumption.
        + unfold honest_keyb in *; cases (honestk $? k__sign); try discriminate;
            destruct b; try discriminate.
          generalize (H1 _ Heq); intros.
          rewrite H4; intuition eauto.
          unfold message_no_adv_private; intros.
          specialize (H7 _ _ H6); intuition eauto.
          eapply msgCiphersSigned_cleaned_honestk; eauto.

        + cases (gks $? k); try contradiction.
          eapply clean_keys_keeps_honest_key with (honestk := honestk) in Heq; eauto.
          rewrite H4 in Heq; discriminate.
        + unfold honest_keyb in *; cases (honestk $? k); try discriminate; destruct b; try discriminate.
          generalize (H1 _ Heq); intros.
          rewrite H4; intuition eauto.
          unfold message_no_adv_private; intros.
          specialize (H7 _ _ H6); intuition eauto.
          eapply msgCiphersSigned_cleaned_honestk; eauto.

    Qed.

    Lemma message_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk honestk' cs gks,
        message_queues_ok honestk cs usrs gks
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys (clean_users honestk usrs)
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok honestk' (clean_ciphers honestk cs) (clean_users honestk usrs) (clean_keys honestk gks).
    Proof.
      unfold message_queues_ok; intros.
      pose proof (clean_users_no_change_honestk usrs).
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H4; unfold clean_users in H4; rewrite map_mapsto_iff in H4.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H5; specialize (H _ _ H5).
      eapply message_queue_ok_after_cleaning; auto.
    Qed.

    Lemma adv_no_honest_keys_after_cleaning :
      forall {A} (usrs : honest_users A) honestk honestk' adv_keys,
        adv_no_honest_keys honestk adv_keys
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys (clean_users honestk usrs)
        -> adv_no_honest_keys honestk' (clean_key_permissions honestk adv_keys).
    Proof.
      unfold adv_no_honest_keys; intros.
      pose proof (findUserKeys_clean_users_correct usrs); subst.
      repeat
        match goal with
        | [ K : NatMap.key, H : (forall k : NatMap.key, _) |- _ ] => specialize (H K)
        end.
      split_ors; split_ands;
        match goal with
        | [ H : findUserKeys ?usrs $? ?kid = _ , M : match findUserKeys ?usrs $? ?kid with _ => _ end |- _ ] =>
          rewrite H in M
        end; eauto.

      right; right; split; eauto.
      unfold not; intros.
      eapply clean_key_permissions_inv in H1; split_ands; contradiction.
    Qed.

    Lemma ok_adv_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary_univ U__ra b
        -> universe_ok U__ra
        -> adv_universe_ok U__ra
        -> adv_universe_ok U__r.
    Proof.
      unfold adv_universe_ok, universe_ok.
      intros.
      subst; unfold adv_universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        try rewrite clean_users_no_change_findUserKeys;
        subst; simpl in *;
          eauto using user_cipher_queues_ok_after_cleaning
                    , message_queues_ok_after_cleaning
                    , keys_and_permissions_good_clean_keys
                    , adv_no_honest_keys_after_cleaning.
      econstructor.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         not_in_ciphers_not_in_cleaned_ciphers.

    Lemma cipher_message_keys_already_in_honest :
      forall {A t} (msg : message t) (usrs : honest_users A) honestk cs c_id k__s k__e gks,
        honestk = findUserKeys usrs
        -> cs $? c_id = Some (SigEncCipher k__s k__e msg)
        -> honest_key honestk k__s
        -> honest_key honestk k__e
        -> encrypted_ciphers_ok honestk cs gks
        -> honestk $k++ findKeys msg = honestk.
    Proof.
      intros.
      invert H1; invert H2.
      eapply Forall_natmap_in_prop in H3; eauto; invert H3; try contradiction.
      rewrite merge_keys_addnl_honest; eauto.
    Qed.

    Hint Resolve
         honest_key_filter_fn_proper honest_key_filter_fn_filter_proper honest_key_filter_fn_filter_transpose
         honest_key_filter_fn_filter_proper_Equal honest_key_filter_fn_filter_transpose_Equal
         honest_perm_filter_fn_proper
         honest_perm_filter_fn_filter_proper honest_perm_filter_fn_filter_transpose
         honest_perm_filter_fn_filter_proper_Equal honest_perm_filter_fn_filter_transpose_Equal.

    (* Ltac solve_clean_keys := *)
    (*   match goal with *)
    (*   | [  |- clean_keys ?honestk ?gks $? ?kid = Some _ ] => *)
    (*     match goal with *)
    (*     | [ H : honestk $? kid = Some true |- _] => idtac *)
    (*     | _ => assert (honestk $? kid = Some true) by eauto *)
    (*     end; unfold clean_keys; *)
    (*     rewrite <- find_mapsto_iff, filter_iff; auto; rewrite find_mapsto_iff; *)
    (*     unfold honest_key_filter_fn; *)
    (*     intuition context_map_rewrites; eauto *)
    (*   end. *)
    Ltac solve_clean_keys_clean_key_permissions :=
      match goal with
      | [  |- clean_keys ?honestk ?gks $? ?kid = Some _ ] =>
        match goal with
        | [ H : honestk $? kid = Some true |- _] => idtac
        | _ => assert (honestk $? kid = Some true) by eauto
        end
      | [  |- clean_key_permissions ?honestk ?gks $? ?kid = Some _ ] =>
        match goal with
        | [ H : honestk $? kid = Some true |- _] => idtac
        | _ => assert (honestk $? kid = Some true) by eauto
        end
      end;
      unfold clean_keys, clean_key_permissions;
      rewrite <- find_mapsto_iff, filter_iff; auto; rewrite find_mapsto_iff;
      unfold honest_key_filter_fn, honest_perm_filter_fn;
      intuition context_map_rewrites; eauto.

    Lemma clean_ciphers_new_honest_key_idempotent :
      forall honestk k_id cs gks,
        encrypted_ciphers_ok honestk cs gks
        -> ~ In k_id gks
        -> clean_ciphers (honestk $+ (k_id, true)) cs = clean_ciphers honestk cs.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (cs $? y).
      - case_eq (honest_cipher_filter_fn honestk y c); intros.
        + assert (honest_cipher_filter_fn honestk y c = true) as HCFF by assumption.
          unfold honest_cipher_filter_fn, cipher_honestly_signed in HCFF; encrypted_ciphers_prop.
          * erewrite !clean_ciphers_keeps_honest_cipher; eauto.
            unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb.
            destruct (k_id ==n k); subst; clean_map_lookups; eauto.
          * erewrite !clean_ciphers_keeps_honest_cipher; eauto.
            unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb.
            destruct (k_id ==n k__s); subst; clean_map_lookups; eauto.
        + assert (honest_cipher_filter_fn honestk y c = false) as HCFF by assumption.
          unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb in HCFF.
          encrypted_ciphers_prop;
            try
              match goal with
              | [ H : honestk $? _ = _ |- _ ] => rewrite H in HCFF; discriminate
              end.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb.
            destruct (k_id ==n k); subst; clean_map_lookups; eauto.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb.
            destruct (k_id ==n k__s); subst; clean_map_lookups; eauto.
      - rewrite !clean_ciphers_no_new_ciphers; auto.
    Qed.

    Lemma clean_messages_new_honest_key_idempotent :
      forall honestk k_id msgs cs gks,
        (* permission_heap_good gks honestk *)
           message_queue_ok honestk cs msgs gks
        -> ~ In k_id gks
        -> clean_messages (honestk $+ (k_id, true)) msgs = clean_messages honestk msgs.
    Proof.
      induction msgs; intros; eauto.
      simpl.
      case_eq (msg_filter honestk a); intros.
      - assert (msg_filter (honestk $+ (k_id,true)) a = true).
        unfold msg_filter in *; destruct a; unfold msg_honestly_signed in *; destruct m; try discriminate;
          unfold honest_keyb in *.
        + destruct (k_id ==n k__sign); subst; clean_map_lookups; eauto.
        + destruct (k_id ==n k); subst; clean_map_lookups; eauto.
        + rewrite H2. invert H; erewrite IHmsgs; eauto.
      - assert (msg_filter (honestk $+ (k_id,true)) a = false).
        unfold msg_filter in *; destruct a; unfold msg_honestly_signed in *; destruct m; try discriminate;
          unfold honest_keyb in *; auto.
        + cases (honestk $? k__sign).
          * destruct (k_id ==n k__sign); subst; clean_map_lookups; eauto.
            invert H; split_ands.
            contradiction.
            destruct b; try discriminate; context_map_rewrites; trivial.
          * invert H. clear H5; split_ands.
            destruct (k_id ==n k__sign); subst; clean_map_lookups; eauto.
            contradiction.
            rewrite Heq; trivial.
        + cases (honestk $? k).
          * destruct (k_id ==n k); subst; clean_map_lookups; eauto.
            invert H; split_ands; contradiction.
            destruct b; try discriminate; context_map_rewrites; trivial.
          * invert H. clear H5; split_ands.
            destruct (k_id ==n k); subst; clean_map_lookups; eauto.
            contradiction.
            rewrite Heq; trivial.
        + rewrite H2. invert H; erewrite IHmsgs; eauto.
    Qed.

    Lemma clean_keys_new_honest_key' :
      forall honestk k_id gks,
        gks $? k_id = None
        -> clean_keys (honestk $+ (k_id, true)) gks = clean_keys honestk gks.
    Proof.
      intros.
      unfold clean_keys, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      subst; simpl.

      rewrite fold_add; eauto.
      assert (honest_key_filter_fn (honestk $+ (k_id,true)) k e = honest_key_filter_fn honestk k e)
        as RW.

      unfold honest_key_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      apply find_mapsto_iff in H0; contra_map_lookup.
      rewrite RW; trivial.
    Qed.

    Lemma clean_keys_new_honest_key :
      forall honestk k_id k gks,
        gks $? k_id = None
        -> permission_heap_good gks honestk
        -> clean_keys (honestk $+ (k_id, true)) (gks $+ (k_id,k)) =
          clean_keys honestk gks $+ (k_id, k).
    Proof.
      intros.

      apply map_eq_Equal; unfold Equal; intros.
      destruct (k_id ==n y); subst; clean_map_lookups; eauto.
      - apply clean_keys_keeps_honest_key; eauto.
        unfold honest_key_filter_fn; clean_map_lookups; eauto.
      - unfold clean_keys at 1.
        unfold filter.
        rewrite fold_add; eauto.
        unfold honest_key_filter_fn; clean_map_lookups; eauto.
        unfold clean_keys, filter, honest_key_filter_fn; eauto.
        pose proof (clean_keys_new_honest_key' honestk k_id gks H).
        unfold clean_keys, filter, honest_key_filter_fn in H1.
        rewrite H1; trivial.
    Qed.

    Lemma clean_key_permissions_new_honest_key' :
      forall honestk k_id gks,
        gks $? k_id = None
        -> clean_key_permissions (honestk $+ (k_id, true)) gks = clean_key_permissions honestk gks.
    Proof.
      intros.
      unfold clean_key_permissions, filter.
      apply P.fold_rec_bis; intros; Equal_eq; eauto.
      subst; simpl.

      rewrite fold_add; eauto.
      assert (honest_perm_filter_fn (honestk $+ (k_id,true)) k e = honest_perm_filter_fn honestk k e)
        as RW.

      unfold honest_perm_filter_fn; destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      apply find_mapsto_iff in H0; contra_map_lookup.
      rewrite RW; trivial.
    Qed.

    Lemma clean_key_permissions_new_honest_key :
      forall honestk k_id ks,
        ~ In k_id ks
        -> clean_key_permissions (honestk $+ (k_id, true)) (add_key_perm k_id true ks) =
          add_key_perm k_id true (clean_key_permissions honestk ks).
    Proof.
      intros; clean_map_lookups.
      unfold add_key_perm, greatest_permission.
      assert (clean_key_permissions honestk ks $? k_id = None)
        as CKP
          by (apply clean_key_permissions_adds_no_permissions; auto);
        rewrite CKP, H.
      unfold clean_key_permissions at 1; unfold filter; rewrite fold_add; eauto.
      unfold honest_perm_filter_fn; clean_map_lookups; eauto.

      apply map_eq_Equal; unfold Equal; intros.
      destruct (k_id ==n y); subst; clean_map_lookups; eauto.
      pose proof clean_key_permissions_new_honest_key';
        unfold clean_key_permissions, filter, honest_perm_filter_fn in *; eauto.
      rewrite H0; eauto.
    Qed.

    Lemma clean_adv_new_honest_key_idempotent :
      forall {B} (adv : user_data B) honestk k_id gks b,
        ~ In k_id gks
        -> permission_heap_good gks (key_heap adv)
        -> clean_adv adv (honestk $+ (k_id, true)) b = clean_adv adv honestk b.
    Proof.
      intros.
      unfold clean_adv.
      erewrite clean_key_permissions_new_honest_key'; clean_map_lookups; eauto.
      unfold permission_heap_good in *.
      cases (key_heap adv $? k_id); eauto.
      specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
    Qed.

    Lemma clean_users_new_honest_key_idempotent :
      forall {A B} (usrs : honest_users A) (adv : user_data B) honestk k_id cs gks,
        ~ In k_id gks
        -> message_queues_ok honestk cs usrs gks
        -> keys_and_permissions_good gks usrs adv
        -> clean_users (honestk $+ (k_id, true)) usrs = clean_users honestk usrs.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (usrs $? y).
      - erewrite !clean_users_cleans_user; eauto.
        unfold keys_and_permissions_good in *; split_ands.
        eapply Forall_natmap_in_prop in H2; eauto.
        msg_queue_prop; f_equal; symmetry; eauto using clean_messages_new_honest_key_idempotent
                                           , clean_key_permissions_new_honest_key'.
        apply clean_key_permissions_new_honest_key'.
        cases (key_heap u $? k_id); auto.
        specialize (H2 _ _ Heq0); split_ex; clean_map_lookups.
      - rewrite !clean_users_adds_no_users; eauto.
    Qed.

    Hint Resolve clean_keys_new_honest_key.

      (* forall {A B C} cs cs' lbl u_id suid (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
      (*           gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a a' (b : B), *)
      (*   step_user lbl suid bd bd' *)
      (*   -> suid = Some u_id *)
      (*   -> action_adversary_safe (findUserKeys usrs) cs a *)
      (*   -> message_queues_ok (findUserKeys usrs) cs usrs gks *)
      (*   -> forall (cmd : user_cmd C) cs__s usrs__s honestk, *)
      (*     honestk = findUserKeys usrs *)
      (*     -> cs__s = clean_ciphers honestk cs *)
      (*     -> usrs__s = clean_users honestk usrs *)
      (*     -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd) *)
      (*     -> forall cmd' cs__s' usrs__s' honestk', *)
      (*         honestk' = findUserKeys usrs' *)
      (*         -> cs__s' = clean_ciphers honestk' cs' *)
      (*         -> usrs__s' = clean_users honestk' usrs' *)
      (*         -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd') *)
      (*         -> lbl = Action a *)
      (*         -> forall cmdc, *)
      (*             usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |} *)
      (*         (* TODO TBRAJE :: ks and ks' should be cleaned  *) *)
      (*             -> a' = match a with *)
      (*                    | Input msg pat perms => Input msg pat (clean_key_permissions honestk perms) *)
      (*                    | output              => output *)
      (*                    end *)
      (*             -> step_user (Action a') suid *)
      (*                         (usrs__s, clean_adv adv (findUserKeys usrs) b, cs__s, clean_keys honestk gks, *)
      (*                          clean_key_permissions honestk ks, clean_messages honestk qmsgs, mycs, cmd) *)
      (*                         (usrs__s', clean_adv adv' (findUserKeys usrs) b, cs__s', clean_keys honestk' gks', *)
      (*                          clean_key_permissions honestk' ks', clean_messages honestk' qmsgs', mycs', cmd'). *)

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
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> message_queues_ok honestk cs usrs gks
          -> keys_and_permissions_good gks usrs adv
          -> forall cmd' cs__s' usrs__s' honestk',
                 bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' usrs'
                  -> encrypted_ciphers_ok honestk' cs' gks'
                  -> step_user lbl suid
                              (usrs__s, clean_adv adv honestk b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks, clean_messages honestk qmsgs, mycs, cmd)
                              (usrs__s', clean_adv adv' honestk' b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks', clean_messages honestk' qmsgs', mycs', cmd')
                  \/ (usrs__s, clean_adv adv honestk b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks, clean_messages honestk qmsgs, mycs, cmd)
                    = (clean_users honestk' usrs', clean_adv adv' honestk' b, cs__s', clean_keys honestk' gks',
                       clean_key_permissions honestk' ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 5; inversion 5; intros; subst; clean_context;
        autorewrite with find_user_keys;
        try solve [ left; econstructor; eauto; user_cipher_queues_prop; eauto; try solve_clean_keys_clean_key_permissions ].

      - remember (findUserKeys usrs) as honestk.
        remember (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs'; c_heap := mycs' |})) as usrs''.
        remember (findUserKeys usrs'') as honestk'.
        remember (clean_ciphers honestk cs) as cs__s.
        remember (clean_ciphers honestk' cs') as cs__s'.
        remember (clean_users honestk usrs) as usrs__s.
        remember (clean_users honestk' usrs') as usrs__s'.
        assert (@Silent action = Silent) as SIL by trivial.
        assert ((usrs,adv,cs,gks,ks,qmsgs,mycs,cmd1)=(usrs,adv,cs,gks,ks,qmsgs,mycs,cmd1)) as bd1 by trivial.
        assert ((usrs',adv',cs',gks',ks',qmsgs',mycs',cmd1')=(usrs',adv',cs',gks',ks',qmsgs',mycs',cmd1')) as bd1' by trivial.
        assert (Some u_id = Some u_id) by trivial.

        specialize (IHstep_user _ _ _ _ b H0 _ _ _ _
                                Heqhonestk
                                Heqcs__s
                                Hequsrs__s
                                bd1
                                H5
                                H14
                                H15
                                H16
                                _ _ _ _
                                bd1'
                                SIL
                                _ _ _
                                H27
                                Hequsrs''
                                Heqhonestk'
                                Heqcs__s'
                                Hequsrs__s'
                                H32
                   ); split_ors; clean_context.
        + left; econstructor; eauto.
        + right; unfold clean_adv; simpl; inversion H1; subst. f_equal.

      - cases (msg_honestly_signed (findUserKeys usrs') msg).
        + left. econstructor; eauto.
          unfold clean_messages, msg_filter; simpl; rewrite Heq; eauto.
        + right; simpl; rewrite Heq; f_equal.

      - clear H14; encrypted_ciphers_prop;
          autorewrite with find_user_keys in *.
        * eapply findUserKeys_has_private_key_of_user in H36; eauto; contradiction.
        * left; econstructor; eauto; try solve_clean_keys_clean_key_permissions.
          unfold keys_mine; intros.
          specialize (H15 _ _ H6); split_ands; subst.
          specialize (H4 _ _ H6); split_ors; split_ands; eauto.
          ** left; apply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial.
          ** right; intuition idtac;
               apply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial.

      - autorewrite with find_user_keys in *.
        assert (findUserKeys usrs' $? k__encid = Some true) by eauto 2.
        clear H41.
        user_cipher_queues_prop. encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.
        econstructor; econstructor; eauto; try solve_clean_keys_clean_key_permissions.

      - autorewrite with find_user_keys in *.
        msg_queue_prop.
        keys_and_permissions_prop.

        erewrite clean_users_new_honest_key_idempotent
               , clean_ciphers_new_honest_key_idempotent
               , clean_messages_new_honest_key_idempotent
               , clean_adv_new_honest_key_idempotent
               , clean_key_permissions_new_honest_key
        ; eauto.

        left; econstructor; eauto.
        eapply clean_keys_adds_no_keys; auto.
        eapply clean_keys_new_honest_key; eauto.
        apply users_permission_heaps_good_merged_permission_heaps_good; auto.
        cases (ks $? k_id); clean_map_lookups; eauto.
        specialize (H4 _ _ Heq); split_ex; contra_map_lookup.

      - autorewrite with find_user_keys in *.
        msg_queue_prop.
        keys_and_permissions_prop.

        erewrite clean_users_new_honest_key_idempotent
               , clean_ciphers_new_honest_key_idempotent
               , clean_messages_new_honest_key_idempotent
               , clean_adv_new_honest_key_idempotent
               , clean_key_permissions_new_honest_key
        ; eauto.

        left; econstructor; eauto.
        eapply clean_keys_adds_no_keys; auto.
        eapply clean_keys_new_honest_key; eauto.
        apply users_permission_heaps_good_merged_permission_heaps_good; auto.
        cases (ks $? k_id); clean_map_lookups; eauto.
        specialize (H4 _ _ Heq); split_ex; contra_map_lookup.

    Qed.

    Lemma honest_cipher_filter_fn_nochange_pubk :
      forall honestk pubk k v,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> honest_cipher_filter_fn honestk k v =
          honest_cipher_filter_fn (honestk $k++ pubk) k v.
    Proof.
      unfold honest_cipher_filter_fn; intros;
        unfold cipher_honestly_signed;
        cases v; unfold honest_keyb; simpl.

      - cases (honestk $? k_id); cases (pubk $? k_id); simplify_key_merges1; auto;
          cases b; auto;
            specialize (H _ _ Heq0); split_ands; subst; contra_map_lookup.

      - cases (honestk $? k__sign); cases (pubk $? k__sign); simplify_key_merges1; auto;
          cases b; auto;
            specialize (H _ _ Heq0); split_ands; subst; contra_map_lookup.
    Qed.

    Lemma clean_ciphers_nochange_pubk :
      forall honestk pubk cs,
        (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
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
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> msg_filter (honestk $k++ pubk) m = msg_filter honestk m.
    Proof.
      unfold msg_filter, msg_honestly_signed; destruct m; intros; 
        cases m; unfold honest_keyb; simpl; auto.
      - cases (honestk $? k__sign); cases (pubk $? k__sign); simplify_key_merges1; auto;
          destruct b; auto;
            specialize (H _ _ Heq0); split_ands; subst; contra_map_lookup.

      - cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; auto;
          destruct b; auto;
            specialize (H _ _ Heq0); split_ands; subst; contra_map_lookup.
    Qed.

    Lemma clean_messages_nochange_pubk :
      forall honestk pubk qmsgs,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_messages (honestk $k++ pubk) qmsgs = clean_messages honestk qmsgs.
    Proof.
      induction qmsgs; intros; eauto.
      simpl.
      rewrite msg_filter_nochange_pubk; auto.
      rewrite IHqmsgs; eauto.
    Qed.

    Lemma clean_key_permissions_nochange_pubk :
      forall honestk pubk perms,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_key_permissions (honestk $k++ pubk) perms = clean_key_permissions honestk perms.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (clean_key_permissions honestk perms $? y).
      - apply clean_key_permissions_inv in Heq; split_ands.
        apply clean_key_permissions_keeps_honest_permission; eauto.
        unfold honest_perm_filter_fn in *.
        cases (honestk $? y); try destruct b0; try discriminate.
        cases (pubk $? y); simplify_key_merges1; eauto.
      - cases (perms $? y).
        + eapply clean_key_permissions_inv' in Heq; eauto.
          eapply clean_key_permissions_drops_dishonest_permission; eauto.
          unfold honest_perm_filter_fn in *.
          specialize (H y).
          cases (honestk $? y); try destruct b0; try discriminate.
          cases (pubk $? y);
            match goal with
            | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
              assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
            | _ => simplify_key_merges1
            end; eauto.
          cases (pubk $? y);
            match goal with
            | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
              assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
            | _ => simplify_key_merges1
            end; eauto.
        + apply clean_key_permissions_adds_no_permissions; eauto.
    Qed.

    (* Lemma clean_key_permissions_nochange_pubk : *)
    (*   forall honestk pubk ks, *)
    (*     (forall k, pubk $? k = Some true -> False) *)
    (*     -> clean_key_permissions (honestk $k++ pubk) ks = clean_key_permissions honestk ks. *)
    (* Proof. *)
    (*   intros; unfold clean_key_permissions, filter. *)

    (*   induction ks using P.map_induction_bis; intros; Equal_eq; eauto. *)
    (*   rewrite !fold_add; eauto. *)
    (*   rewrite IHks; trivial. *)

    (*   assert (honest_perm_filter_fn (honestk $k++ pubk) x e = honest_perm_filter_fn honestk x e). *)
    (*   unfold honest_perm_filter_fn. *)
    (*   specialize (H x). *)
    (*   cases (honestk $? x); cases (pubk $? x); subst; simplify_key_merges1; eauto. *)
    (*   destruct b0; try contradiction. *)
    (*   rewrite orb_false_r; trivial. *)
    (*   destruct b; try contradiction; auto. *)

    (*   rewrite H1; trivial. *)
    (* Qed. *)

    Lemma clean_users_nochange_pubk :
      forall {A} (usrs: honest_users A) honestk pubk,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_users (honestk $k++ pubk) usrs = clean_users honestk usrs.
    Proof.
      intros; unfold clean_users.
      eapply map_eq_Equal; unfold Equal; intros.
      rewrite !map_o; simpl.
      cases (usrs $? y); eauto.
      simpl.
      f_equal. f_equal.
      - rewrite clean_key_permissions_nochange_pubk; eauto.
      - rewrite clean_messages_nochange_pubk; trivial.
    Qed.

    Lemma clean_users_nochange_pubk_step :
      forall {A} (usrs: honest_users A) honestk pubk u_id ks cmd qmsgs mycs u_d u_d',
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> u_d = {| key_heap := ks $k++ pubk
                 ; protocol := cmd
                 ; msg_heap := qmsgs
                 ; c_heap := mycs |}
        -> u_d' = {| key_heap := clean_key_permissions honestk (ks $k++ pubk)
                  ; protocol := cmd
                  ; msg_heap := clean_messages honestk qmsgs
                  ; c_heap := mycs |}
        -> clean_users (honestk $k++ pubk) (usrs $+ (u_id,u_d)) =
          clean_users honestk usrs $+ (u_id,u_d').
    Proof.
      intros.
      eapply map_eq_Equal; unfold Equal; intros.
      cases (u_id ==n y); subst; clean_map_lookups.
      + erewrite clean_users_cleans_user; clean_map_lookups; eauto. simpl.
        f_equal.
        rewrite clean_key_permissions_nochange_pubk; eauto.
        rewrite clean_messages_nochange_pubk; auto.
      + unfold clean_users.
        rewrite !map_o.
        clean_map_lookups.

        cases (usrs $? y); simpl; auto.
        f_equal. f_equal.
        rewrite clean_key_permissions_nochange_pubk; eauto.
        rewrite clean_messages_nochange_pubk; auto.
    Qed.

    Lemma clean_keys_nochange_pubk :
      forall honestk pubk ks,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_keys (honestk $k++ pubk) ks = clean_keys honestk ks.
    Proof.
      intros; unfold clean_keys, filter.

      induction ks using P.map_induction_bis; intros; Equal_eq; eauto.
      rewrite !fold_add; eauto.
      rewrite IHks; trivial.

      assert (honest_key_filter_fn (honestk $k++ pubk) x e = honest_key_filter_fn honestk x e).
      unfold honest_key_filter_fn.
      specialize (H x).
      cases (honestk $? x); cases (pubk $? x); subst;
            try match goal with
                | [ PUB : pubk $? x = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
                  assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; try discriminate
                end;
            simplify_key_merges1; eauto.
      assert (Some b0 = Some b0) as SOME by trivial; apply H in SOME; split_ands; subst; invert H1; simpl; trivial.

      rewrite H1; trivial.
    Qed.

    Lemma honest_labeled_step_nochange_clean_ciphers_users_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a b,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok (findUserKeys usrs) cs usrs gks
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
                  clean_users (findUserKeys usrs') usrs' $+ (u_id, {| key_heap := clean_key_permissions (findUserKeys usrs') ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := clean_messages (findUserKeys usrs') qmsgs'
                                                                    ; c_heap := mycs' |})
                /\ clean_adv adv' (findUserKeys usrs'') b = clean_adv adv' (findUserKeys usrs) b
                /\ clean_keys (findUserKeys usrs'') gks' = clean_keys (findUserKeys usrs') gks'.

    Proof.
      induction 1; inversion 4; inversion 2; intros; subst; try discriminate;
        eauto 2;
        (* try rewrite clean_key_permissions_distributes_clean_key_permissions; *)
        autorewrite with find_user_keys;
        clean_context;
        simpl.

      - eapply Forall_natmap_in_prop in H8; eauto; simpl in *; invert H8.
        split_ands.
        assert (msg_honestly_signed (findUserKeys usrs') msg = true) as HON_SIGN by eauto.
        unfold msg_honestly_signed in  HON_SIGN; destruct msg; try discriminate;
          rewrite HON_SIGN in H0; split_ands;
            unfold message_no_adv_private in *;
            intuition eauto using clean_ciphers_nochange_pubk
                                , clean_messages_nochange_pubk
                                , clean_users_nochange_pubk_step
                                , clean_key_permissions_nochange_pubk
                                , clean_keys_nochange_pubk.

        unfold clean_adv; f_equal; eauto using clean_key_permissions_nochange_pubk.
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
        -> message_queues_ok (findUserKeys usrs) cs usrs gks
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs' gks'.
    Proof.
      induction 1; inversion 5; inversion 2; intros; subst; try discriminate;
        eauto 2; autorewrite with find_user_keys;
          clean_context; eauto.

      msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
      split_ands; refine_signed_messages; eauto.

    Qed.

    Lemma honest_labeled_step_univ_ok :
      forall {A B} (U U' : universe A B) a__r,
        universe_ok U
        -> step_universe U (Action a__r) U'
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r
        -> message_queues_ok (findUserKeys U.(users)) U.(all_ciphers) U.(users) U.(all_keys)
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
        -> message_queues_ok (findUserKeys usrs) cs usrs gks
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
        split_ands; refine_signed_messages;
          rewrite clean_users_nochange_pubk, clean_ciphers_nochange_pubk, clean_messages_nochange_pubk; eauto;
            rewrite HON_SIGN; econstructor; eauto.

      - econstructor; eauto.
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl.
        rewrite clean_messages_keeps_honestly_signed; auto.
    Qed.

    Lemma message_contains_only_honest_public_keys_keys_honest :
      forall {t} (msg : message t) k kp honestk,
        msg_contains_only_honest_public_keys honestk msg
        -> findKeys msg $? k = Some kp
        -> honestk $? k = Some true.
    Proof.
      induction 1; simpl; intros; subst; clean_map_lookups; eauto.
      - destruct kp0; simpl in *.
        destruct (k0 ==n k); subst; clean_map_lookups; try discriminate; auto.
      - cases (findKeys msg1 $? k); cases (findKeys msg2 $? k); simplify_key_merges1; clean_context; try contradiction; eauto.
        cases b; cases b0; simpl in *; try contradiction; try discriminate; eauto.
    Qed.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv' :
      forall {A B C} cs cs' lbl u_id suid (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a a' (b : B),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok (findUserKeys usrs) cs usrs gks
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> forall cmd' cs__s' usrs__s' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Action a
              -> user_queue usrs u_id = Some qmsgs
              (* -> forall cmdc, *)
              (*     usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |} *)
                  -> a' = strip_action (findUserKeys usrs) a
                  -> step_user (Action a') suid
                              (usrs__s, clean_adv adv (findUserKeys usrs) b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks, clean_messages honestk qmsgs, mycs, cmd)
                              (usrs__s', clean_adv adv' (findUserKeys usrs) b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks', clean_messages honestk' qmsgs', mycs', cmd').
    Proof.
      induction 1; inversion 7; inversion 4; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
          autorewrite with find_user_keys.

      - assert ( msg_honestly_signed (findUserKeys usrs') msg = true ) by eauto.
        rewrite H.
        econstructor; eauto.

        msg_queue_prop.

        rewrite merge_perms_right_identity; trivial.
        unfold message_no_adv_private in *.
        rewrite clean_key_permissions_distributes_merge_key_permissions.
        assert (clean_key_permissions (findUserKeys usrs') (findKeys msg) = findKeys msg).
        apply map_eq_Equal; unfold Equal; intros.
        cases (findKeys msg $? y).
        apply clean_key_permissions_keeps_honest_permission; eauto.
        specialize (H2 _ _ Heq); split_ands; subst; eauto.
        unfold honest_perm_filter_fn; context_map_rewrites; trivial.
        apply clean_key_permissions_adds_no_permissions; eauto.

        rewrite H6; trivial.

      - econstructor; eauto.
        + unfold keys_mine in *; intros.
          pose proof (message_contains_only_honest_public_keys_keys_honest _ H H6).
          specialize (H0 _ _ H6); split_ors; split_ands; subst.
          * left; eapply clean_key_permissions_keeps_honest_permission; eauto.
          * right; intuition idtac.
            eapply clean_key_permissions_keeps_honest_permission; eauto.

        + unfold clean_adv, addUserKeys; simpl.
          destruct H; simpl in *; try discriminate; eauto.
          f_equal; eauto.
          rewrite clean_key_permissions_distributes_merge_key_permissions.
          apply map_eq_Equal; unfold Equal; intros.
          cases (findKeys msg $? y).
          * pose proof (message_contains_only_honest_public_keys_keys_honest _ H Heq).
            assert (clean_key_permissions (findUserKeys usrs) (findKeys msg) $? y = Some b0).
            apply clean_key_permissions_keeps_honest_permission; eauto.
            unfold honest_perm_filter_fn; context_map_rewrites; trivial.
            cases (clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y); simplify_key_merges; eauto.
          * assert (clean_key_permissions (findUserKeys usrs) (findKeys msg) $? y = None).
            apply clean_key_permissions_adds_no_permissions; eauto.
            cases (clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y); simplify_key_merges; eauto.
        + eapply clean_users_cleans_user; eauto.
        + simpl.
          rewrite clean_users_add_pull; simpl; eauto.
          rewrite clean_messages_keeps_honestly_signed; eauto.
    Qed.

    Lemma labeled_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B) lbl a,
        step_universe U lbl U'
        -> lbl = Action a
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a
        -> universe_ok U
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      invert H; try discriminate.
      unfold universe_ok, adv_universe_ok in *.
      destruct U; destruct userData.
      unfold build_data_step in *; simpl in *.
      split_ands.
      intuition
        eauto using honest_labeled_step_keys_and_permissions_good
                  , honest_labeled_step_user_cipher_queues_ok
                  , honest_labeled_step_message_queues_ok
                  , honest_labeled_step_adv_message_queue_ok
                  , honest_labeled_step_adv_no_honest_keys.
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

    Lemma honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok (findUserKeys usrs) cs usrs gks
          -> keys_and_permissions_good  gks usrs adv
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                ->  clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') qmsgs' = clean_messages (findUserKeys usrs') qmsgs'
                /\ clean_users (findUserKeys usrs'') usrs' = clean_users (findUserKeys usrs') usrs'.
    Proof.
      induction 1; inversion 2; inversion 6; intros; try discriminate; subst;
        autorewrite with find_user_keys; eauto; clean_context.

      - user_cipher_queues_prop; erewrite cipher_message_keys_already_in_honest; eauto.

      - msg_queue_prop.
        intuition eauto using clean_ciphers_new_honest_key_idempotent
                            , clean_messages_new_honest_key_idempotent
                            , clean_users_new_honest_key_idempotent.
      - msg_queue_prop.
        intuition eauto using clean_ciphers_new_honest_key_idempotent
                            , clean_messages_new_honest_key_idempotent
                            , clean_users_new_honest_key_idempotent.
    Qed.


    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs cmd,
        universe_ok U
        -> adv_universe_ok U
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
      unfold adv_universe_ok, universe_ok in *; split_ands; simpl in *.
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv in RW; eauto.

      split_ors.
      - destruct adversary; unfold strip_adversary_univ; simpl in *.
        left.
        eapply StepUser; simpl; eauto.
        + eapply clean_users_cleans_user; eauto.
        + unfold build_data_step; simpl.
          unfold clean_adv; simpl.
          exact H9.
        + unfold buildUniverse, clean_adv; simpl.
          f_equal.
          rewrite clean_users_add_pull; auto.

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        inversion H9; subst.
        unfold clean_adv; simpl; f_equal.
        + rewrite clean_users_add_pull; simpl.
          assert (clean_users (findUserKeys users) users =
                  clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}))) usrs).
          unfold clean_users, map; apply map_eq_elements_eq; simpl; auto.
          rewrite <- H10.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; trivial; eapply clean_users_cleans_user; eauto.
          f_equal; eauto.
        + f_equal; eauto.

    Qed.

    Lemma stripped_labeled_step_implies_advuniv_step_action_stripped :
       forall {A B C} cs cs' u_id suid (usrs usrs' usrs__ra usrs__ra': honest_users A) (adv adv' adv__ra adv__ra': user_data B)
         gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a (b : B)
         cs__ra gks__ra ks__ra qmsgs__ra cs__ra' gks__ra' ks__ra' qmsgs__ra'
         lbl,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> lbl = Action a
        -> forall (cmd : user_cmd C) honestk,
            honestk = findUserKeys usrs
            -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
            -> usrs = clean_users honestk usrs__ra
            -> adv = clean_adv adv__ra honestk b
            -> cs = clean_ciphers honestk cs__ra
            -> gks = clean_keys honestk gks__ra
            -> ks = clean_key_permissions honestk ks__ra
            -> qmsgs = clean_messages honestk qmsgs__ra
            -> forall cmd' bd__ra' a__ra,
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
                -> bd__ra' = (usrs__ra', adv__ra', cs__ra', gks__ra', ks__ra', qmsgs__ra', mycs', cmd')
                -> step_user (Action a__ra) suid (usrs__ra, adv__ra, cs__ra, gks__ra, ks__ra, qmsgs__ra, mycs, cmd) bd__ra'
                -> a = strip_action honestk a__ra.
    Proof.
      induction 1; inversion 4; inversion 7; intros; try discriminate; subst;
        match goal with
        | [ H : step_user (Action ?ara) _ _ _ |- _ = strip_action _ ?ara ] => invert H
        end; clean_context; try reflexivity; eauto.
    Qed.

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok (findUserKeys U.(users)) U.(all_ciphers) U.(users) U.(all_keys)
        -> step_universe U (Action act) U'
        -> step_universe (strip_adversary_univ U b)
                        (Action (strip_action (findUserKeys U.(users)) act))
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
        eapply honest_labeled_step_advuniv_implies_honest_step_origuniv'; eauto.
        + unfold action_adversary_safe in *; subst; eauto.
        + subst; eauto.
        + unfold user_queue; rewrite H2; trivial.
      - unfold buildUniverse; subst; simpl in *.
        destruct x0; subst; simpl in *.
        remember (x2 $+ (x, {| key_heap := x6; protocol := x9; msg_heap := x7 ; c_heap := x8 |})) as usrs''.

        assert (clean_ciphers (findUserKeys usrs'') x4 = clean_ciphers (findUserKeys x2) x4
              /\ clean_messages (findUserKeys usrs'') x7 = clean_messages (findUserKeys x2) x7
              /\ clean_users (findUserKeys usrs'') usrs'' =
                clean_users (findUserKeys x2) x2 $+ (x, {| key_heap := clean_key_permissions (findUserKeys x2) x6
                                                         ; protocol := x9
                                                         ; msg_heap := clean_messages (findUserKeys x2) x7
                                                         ; c_heap := x8 |})
              /\ clean_adv x3 (findUserKeys usrs'') b = clean_adv x3 (findUserKeys users) b
              /\ clean_keys (findUserKeys usrs'') x5 = clean_keys (findUserKeys x2) x5 ).
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.
        split_ands.

        f_equal; auto.
    Qed.

    Hint Resolve dishonest_cipher_cleaned.

    Lemma  adv_step_implies_no_new_ciphers_after_cleaning :
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
          -> keys_and_permissions_good gks usrs adv
          -> gks__s = clean_keys honestk gks
          -> forall cmd' honestk' gks__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> honestk' = findUserKeys usrs'
              -> gks__s' = clean_keys honestk' gks'
              -> gks__s = gks__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        autorewrite with find_user_keys; eauto; clean_context.

      - apply map_eq_Equal; unfold Equal; intros.
        unfold keys_and_permissions_good in H13; split_ands.
          assert (permission_heap_good gks (findUserKeys usrs'))
            by eauto using users_permission_heaps_good_merged_permission_heaps_good;
            clear H0 H1 H2.
        assert (findUserKeys usrs' $? k_id = None).
          cases (findUserKeys usrs' $? k_id); trivial;
            specialize (H3 _ _ Heq); split_ex; contra_map_lookup.

        cases (clean_keys (findUserKeys usrs') gks $? y); symmetry.
        + apply clean_keys_inv in Heq; split_ands.
          apply clean_keys_keeps_honest_key; eauto.
          destruct (k_id ==n y); subst; clean_map_lookups; eauto.
        + cases (findUserKeys usrs' $? y).
          * specialize (H3 _ _ Heq0); split_ex.
            eapply clean_keys_inv' in Heq; eauto.
            eapply clean_keys_drops_dishonest_key; eauto.
            destruct (k_id ==n y); subst; clean_map_lookups; eauto.
          * destruct (k_id ==n y); subst.
            ** eapply clean_keys_drops_dishonest_key; clean_map_lookups; eauto.
            ** cases (gks $? y).
               *** eapply clean_keys_drops_dishonest_key; clean_map_lookups; eauto.
               *** eapply clean_keys_adds_no_keys; clean_map_lookups; eauto.
      - apply map_eq_Equal; unfold Equal; intros.
        unfold keys_and_permissions_good in H13; split_ands.
          assert (permission_heap_good gks (findUserKeys usrs'))
            by eauto using users_permission_heaps_good_merged_permission_heaps_good;
            clear H0 H1 H2.
        assert (findUserKeys usrs' $? k_id = None).
          cases (findUserKeys usrs' $? k_id); trivial;
            specialize (H3 _ _ Heq); split_ex; contra_map_lookup.

        cases (clean_keys (findUserKeys usrs') gks $? y); symmetry.
        + apply clean_keys_inv in Heq; split_ands.
          apply clean_keys_keeps_honest_key; eauto.
          destruct (k_id ==n y); subst; clean_map_lookups; eauto.
        + cases (findUserKeys usrs' $? y).
          * specialize (H3 _ _ Heq0); split_ex.
            eapply clean_keys_inv' in Heq; eauto.
            eapply clean_keys_drops_dishonest_key; eauto.
            destruct (k_id ==n y); subst; clean_map_lookups; eauto.
          * destruct (k_id ==n y); subst.
            ** eapply clean_keys_drops_dishonest_key; clean_map_lookups; eauto.
            ** cases (gks $? y).
               *** eapply clean_keys_drops_dishonest_key; clean_map_lookups; eauto.
               *** eapply clean_keys_adds_no_keys; clean_map_lookups; eauto.

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
        -> keys_and_permissions_good U__r.(all_keys) U__r.(users) U__r.(adversary)
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
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> keys_and_permissions_good gks usrs adv
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc' honestk',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |})
                -> honestk' = findUserKeys usrs''
                -> encrypted_ciphers_ok honestk' (clean_ciphers honestk' cs') gks'
                -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 5; intros; subst;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        eauto.

      - rewrite clean_ciphers_keeps_added_honest_cipher in H35; simpl; eauto.
        eapply Forall_natmap_split in H35; auto; split_ands.
        econstructor; eauto.
        + assert ( (findUserKeys usrs') $? k__signid = Some true) by eauto.
          invert H7; try contradiction.
          eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
          unfold msgCiphersSigned in *.
          rewrite Forall_forall in *; intros.
          specialize (H25 _ H7).
          unfold msgCipherOk in *; destruct x; intuition idtac.
          destruct m; eauto.
          * split_ex.
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
        rewrite merge_keys_addnl_honest; eauto.

      - rewrite clean_ciphers_keeps_added_honest_cipher in H31; simpl; eauto.
        eapply Forall_natmap_split in H31; auto; split_ands.
        assert (findUserKeys usrs' $? k_id = Some true) by eauto.
        invert H3; try contradiction.
        econstructor; eauto.
        + econstructor; eauto.
          unfold msgCiphersSigned in *.
          rewrite Forall_forall in *; intros.
          specialize (H14 _ H3).
          unfold msgCipherOk in *; destruct x; intuition idtac.
          destruct m; eauto.
          * split_ex.
            repeat eexists.
            cases (c_id ==n msg_id); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H8; rewrite clean_ciphers_mapsto_iff in H8; split_ands; auto.
            rewrite find_mapsto_iff in H8; eauto.
          * cases (c_id ==n sig); subst; clean_map_lookups; eauto.
            rewrite <- find_mapsto_iff in H8; rewrite clean_ciphers_mapsto_iff in H8; split_ands; auto.
            rewrite find_mapsto_iff in H8; auto.
        + eapply encrypted_ciphers_ok_addnl_cipher; auto.

      - clean_context.
        assert (permission_heap_good gks (findUserKeys usrs'))
          by (unfold keys_and_permissions_good in *; split_ands; eauto using users_permission_heaps_good_merged_permission_heaps_good).
        eapply encrypted_ciphers_ok_addnl_honest_key; simpl; eauto.
        unfold permission_heap_good in *.
        cases (findUserKeys usrs' $? k_id); clean_map_lookups; eauto.
        specialize (H0 _ _ Heq); split_ex; contra_map_lookup.

      - clean_context.
        assert (permission_heap_good gks (findUserKeys usrs'))
          by (unfold keys_and_permissions_good in *; split_ands; eauto using users_permission_heaps_good_merged_permission_heaps_good).
        eapply encrypted_ciphers_ok_addnl_honest_key; simpl; eauto.
        unfold permission_heap_good in *.
        cases (findUserKeys usrs' $? k_id); clean_map_lookups; eauto.
        specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
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

    Ltac new_key_not_in_honestk :=
      repeat
          match goal with
          | [ H : keys_and_permissions_good ?global_keys ?honusrs _ |- _ ] =>
            assert (permission_heap_good global_keys (findUserKeys honusrs))
              by (unfold keys_and_permissions_good in *; split_ands; eauto using users_permission_heaps_good_merged_permission_heaps_good);
            clear H
          | [ H1 : findUserKeys ?honusrs $? ?kid = Some _
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- ~ In ?kid (findUserKeys ?honusrs) ] =>
            specialize (H2 _ _ H1); split_ex; contra_map_lookup
          | [ H1 : ?global_keys $? ?kid = None
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- ~ In ?kid (findUserKeys ?honusrs) ] =>
            cases (findUserKeys honusrs $? kid); clean_map_lookups; eauto 2
          end.

    Lemma honest_silent_step_adv_univ_enc_ciphers_ok'' :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                b gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> keys_and_permissions_good gks usrs adv
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
                -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 5; unfold strip_adversary; intros; subst; simpl in *;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        eauto; clean_context.

      - exfalso; invert H37.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H9; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H9; eauto.

      - invert H37.
        user_cipher_queues_prop.
        encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.

      - exfalso; invert H33.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H5; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H5; eauto.

      - eapply encrypted_ciphers_ok_addnl_honest_key; eauto; simpl; new_key_not_in_honestk.
      - eapply encrypted_ciphers_ok_addnl_honest_key; eauto; simpl; new_key_not_in_honestk.

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
      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H2 H6 H11 H12 HeqU__ra' H10); split_ors.

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


  Lemma stripped_action_matches_then_action_matches :
    forall honestk a__r a__i,
      action_matches (strip_action honestk a__r) a__i
      -> action_matches a__r a__i.
  Proof.
    intros.
    unfold strip_action in H.
    invert H; destruct a__r; try discriminate.
    invert H0; econstructor; eauto.
    invert H0.
    eapply Out; eauto.
  Qed.

  Hint Resolve stripped_action_matches_then_action_matches.

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

    assert (RealWorld.step_universe (strip_adversary_univ U__ra b)
                                    (Action (strip_action (RealWorld.findUserKeys U__ra.(RealWorld.users)) a__r))
                                    (strip_adversary_univ U__ra' b))
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
    in Forall_natmap (fun u => Forall (fun m => msg_filter honestk m = true) u.(RealWorld.msg_heap)
                          /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true)) U.(RealWorld.users)
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
      -> (forall k_id k,
            ks $? k_id = Some k
            -> keyId k = k_id)
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

  Lemma universe_starts_ok_clean_key_permissions_idempotent :
    forall honestk perms,
      (forall k_id kp, perms $? k_id = Some kp -> honestk $? k_id = Some true)
      -> clean_key_permissions honestk perms = perms.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (perms $? y); eauto using clean_key_permissions_adds_no_permissions.
    assert (honestk $? y = Some true) as HONK by eauto.
    eapply clean_key_permissions_keeps_honest_permission; eauto; unfold honest_perm_filter_fn; context_map_rewrites; trivial.
  Qed.

  Lemma universe_starts_ok_clean_users_idempotent :
    forall {A} (usrs : RealWorld.honest_users A) honestk,
      honestk = RealWorld.findUserKeys usrs
      -> Forall_natmap (fun u => Forall (fun m => msg_filter honestk m = true) u.(RealWorld.msg_heap)
                           /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true)) usrs
      -> clean_users honestk usrs = usrs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in *.
    apply map_eq_Equal; unfold Equal, clean_users; intros; rewrite map_o.
    cases (usrs $? y); auto.
    specialize (H0 _ _ Heq); split_ands.
    destruct u; simpl in *.
    f_equal; f_equal; eauto using clean_honest_messages_idempotent
                                , universe_starts_ok_clean_key_permissions_idempotent.
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
          , universe_starts_ok_clean_users_idempotent;
      unfold keys_and_permissions_good in *; split_ands;
      auto.
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
    f_equal; eauto using clean_users_idempotent'
                       , clean_keys_ok_extra_user_cleaning
                       , clean_ciphers_ok_extra_user_cleaning.
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

