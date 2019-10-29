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
        Messages
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
    | [ H : msg_honestly_signed _ _ ?msg = _ |- _ ] => unfold msg_honestly_signed in H
    | [ |- context [ msg_honestly_signed _ _ ?msg ] ] => unfold msg_honestly_signed; destruct msg; try discriminate; simpl in *
    | [ |- let (_,_) := ?x in _] => destruct x
    | [ H : context [ honest_keyb _ _ = _ ] |- _ ] => unfold honest_keyb in H
    | [ |- context [ honest_keyb _ _ ] ] => unfold honest_keyb
    | [ H : honest_key _ _ |- _ ] => invert H
    | [ |- honest_key _ _ ] => constructor
    | [ H : (if ?b then _ else _) = _ |- _ ] => is_var b; destruct b
    | [ H : (match ?honk $? ?k with _ => _ end) = _ |- _ ] => cases (honk $? k)
    | [ |- context [ if ?b then _ else _ ] ] => is_var b; destruct b
    | [ |- context [ match ?c with _ => _ end ] ] =>
      match type of c with
      | cipher => destruct c
      end
    end.

  Ltac process_keys_messages :=
    repeat process_keys_messages1;
    clean_context;
    repeat solve_maps1;
    try discriminate; try contradiction; context_map_rewrites.
  
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
    destruct msg; try discriminate; repeat process_keys_messages; eauto.
  Qed.

  Lemma msg_honestly_signed_signing_key_honest :
    forall {t} (msg : crypto t) honestk cs k,
      msg_honestly_signed honestk cs msg = true
      -> msg_signing_key cs msg = Some k
      -> honest_key honestk k.
  Proof.
    unfold msg_honestly_signed, msg_signing_key; intros.
    destruct msg; try discriminate; repeat process_keys_messages. constructor;
      clean_context; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_signing_key_honest.

  Ltac user_queue_lkup TAG :=
    match goal with
    | [ H : user_queue ?usrs ?uid = Some ?qmsgs |- _ ] =>
      assert (exists cmd mycs ks froms tos,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_ids := froms
                                     ; to_ids := tos |})
        as TAG by (unfold user_queue in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.

  Ltac user_cipher_queue_lkup TAG :=
    match goal with
    | [ H : user_cipher_queue ?usrs ?uid = Some ?mycs |- _ ] =>
      assert (exists cmd qmsgs ks froms tos,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_ids := froms
                                     ; to_ids := tos |})
        as TAG by (unfold user_cipher_queue in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.

  Ltac user_keys_lkup TAG :=
    match goal with
    | [ H : user_keys ?usrs ?uid = Some ?ks |- _ ] =>
      assert (exists cmd mycs qmsgs froms tos,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_ids := froms
                                     ; to_ids := tos |})
        as TAG by (unfold user_keys in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.

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
        , MAP :  msg_accepted_by_pattern ?cs _ _ ?msg |- _ ] =>
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

  Ltac msg_queue_prop :=
    match goal with
    | [ OK : message_queues_ok ?cs ?us ?gks |- _ ] =>
      match goal with
      | [ H : us $? _ = Some ?u |- _ ] =>
        prop_not_unifies (message_queue_ok (findUserKeys us) cs (msg_heap u) gks);
        generalize (Forall_natmap_in_prop _ OK H); simpl; intros
      | _ => let USR := fresh "USR"
            in user_queue_lkup USR;
               do 5 (destruct USR as [?x USR]);
               generalize (Forall_natmap_in_prop _ OK USR); simpl; intros
      end
    end;
    repeat
      match goal with
      | [ H : message_queue_ok _ _ (_ :: _) _ |- _ ] => invert H; split_ands
      | [ H : (forall k, msg_signing_key ?msg = Some k -> _) |- _] =>
        specialize_msg_queue_ok
      | [ MHS : msg_honestly_signed _ _ ?msg = _ , MTCH : match ?msg with _ => _ end |- _ ] =>
        unfold msg_honestly_signed in MHS; destruct msg; try discriminate; rewrite MHS in *;
        split_ands; simpl in *
      end.

  Ltac user_cipher_queues_prop :=
    match goal with
    | [ OK : user_cipher_queues_ok ?cs ?honk ?us |- _ ] => 
      match goal with
      | [ H : us $? _ = Some ?u |- _ ] =>
        prop_not_unifies (user_cipher_queue_ok cs honk (c_heap u));
        generalize (Forall_natmap_in_prop _ OK H); simpl; intros
      | _ => let USR := fresh "USR"
            in user_cipher_queue_lkup USR;
            do 5 (destruct USR as [?x USR]);
               generalize (Forall_natmap_in_prop _ OK USR); simpl; intros
      end
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

  Ltac permission_heaps_prop :=
    match goal with
    | [ OK : Forall_natmap (fun _ => permission_heap_good ?gks _) ?us |- _ ] => 
      match goal with
      | [ H : us $? _ = Some ?u |- _ ] =>
        prop_not_unifies (permission_heap_good gks (key_heap u));
        generalize (Forall_natmap_in_prop _ OK H); simpl; intros
      | _ => let USR := fresh "USR"
            in user_keys_lkup USR;
               do 5 (destruct USR as [?x USR]);
               generalize (Forall_natmap_in_prop _ OK USR); simpl; intros
      end
    end.
  
  Ltac keys_and_permissions_prop :=
    match goal with
    | [ H : keys_and_permissions_good ?gks ?usrs ?adv |- _ ] =>
      assert (keys_and_permissions_good gks usrs adv) as KPG by assumption; unfold keys_and_permissions_good in KPG; split_ands;
      match goal with
      | [ H : Forall_natmap (fun _ => permission_heap_good ?gks _) ?usrs |- _ ] =>
        assert_if_new (permission_heap_good gks (findUserKeys usrs)) eauto
      end;
      permission_heaps_prop
    end.

  Ltac encrypted_ciphers_prop :=
    match goal with
    | [ H  : encrypted_ciphers_ok _ (?cs $+ (?cid,?c)) _ |- _ ] => generalize (Forall_natmap_in_prop_add H); intros
    | [ H1 : ?cs $? _ = Some _, H2 : encrypted_ciphers_ok _ ?cs _ |- _ ] => generalize (Forall_natmap_in_prop _ H2 H1); simpl; intros
    end;
    repeat match goal with
           | [ H : encrypted_cipher_ok _ _ _ _ |- _ ] => invert H
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_findKeys in H
           end; try contradiction.

  Ltac refine_signed_messages :=
    repeat
      match goal with
      | [ H1 : msg_pattern_safe ?honk _ ,
          H2 : msg_accepted_by_pattern _ _ _ ?msg,
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

  Hint Extern 1 (_ $+ (?k, _) $? _ = Some _) => clean_map_lookups; trivial.
  Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
  Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

  Hint Extern 1 (honest_key_filter_fn _ _ _ = _) => unfold honest_key_filter_fn; context_map_rewrites.
  Hint Extern 1 (honest_perm_filter_fn _ _ _ = _) => unfold honest_perm_filter_fn; context_map_rewrites.

  Hint Extern 1 (user_cipher_queue _ _ = _) => unfold user_cipher_queue; context_map_rewrites.
  Hint Extern 1 (user_keys _ _ = Some _ ) => unfold user_keys; context_map_rewrites.

End Automation.

Import Automation.

Section UniverseLemmas.
  Import RealWorld.

  Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
    {| users       := U__r.(users)
     ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                       ; msg_heap := U__r.(adversary).(msg_heap)
                       ; protocol := advcode
                       ; c_heap   := U__r.(adversary).(c_heap)
                       ; from_ids := U__r.(adversary).(from_ids)
                       ; to_ids   := U__r.(adversary).(to_ids) |}
     ; all_ciphers := U__r.(all_ciphers)
     ; all_keys    := U__r.(all_keys)
    |}.

  Lemma adv_no_honest_keys_after_honestk_no_private_key_msg :
    forall {t} (msg : crypto t) honestk cs advk,
      adv_no_honest_keys honestk advk
      -> (forall (k_id : NatMap.key) (kp : bool), findKeysCrypto cs msg $? k_id = Some kp -> kp = false)
      -> adv_no_honest_keys (honestk $k++ findKeysCrypto cs msg) advk.
  Proof.
    unfold adv_no_honest_keys; intros; eauto;
      match goal with
      | [ kid : ?T, H : forall _ : ?T, _ \/ _ |- _ ] => specialize (H kid)
      end;
        split_ors; intuition idtac;
        cases (findKeysCrypto cs msg $? k_id);
        try match goal with
            | [ H1 : findKeysCrypto _ _ $? ?k_id = Some ?kp
              , H2 : forall k p, _ |- _ ] => specialize (H2 _ _ H1)
            end;
        subst; simplify_key_merges1; auto.
  Qed.

  Lemma msgCiphersSigned_after_msg_keys :
    forall {t} (msg : crypto t) cs honestk msgk,
      msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk (honestk $k++ msgk) cs msg.
  Proof.
    unfold msgCiphersSignedOk.
    induction 1; eauto.
    econstructor; intuition eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto using message_honestly_signed_after_add_keys.
  Qed.

  Lemma msgCiphersSigned_new_private_key :
    forall {t} (msg : crypto t) cs honestk k_id,
      msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk (honestk $+ (k_id,true)) cs msg.
  Proof.
    unfold msgCiphersSignedOk.
    induction 1; eauto.
    econstructor; eauto;
      match goal with
      | [ |- let (_,_) := ?x in _] => destruct x
      end; intuition eauto; repeat process_keys_messages; eauto.
  Qed.

  Hint Resolve msgCiphersSigned_after_msg_keys msgCiphersSigned_new_private_key.

  (* Step keys and permissions good *)

  Lemma keys_and_permissions_good_user_new_pubk :
    forall {A t} (usrs : honest_users A) gks (msg : message t) u_id u_d ks cmd qmsgs mycs froms tos adv_heap,
      keys_and_permissions_good gks usrs adv_heap
      -> (forall (k : NatMap.key) (kp : bool), findKeysMessage msg $? k = Some kp -> gks $? k <> None)
      -> u_d = {| key_heap := ks $k++ findKeysMessage msg
               ; msg_heap := qmsgs
               ; protocol := cmd
               ; c_heap   := mycs
               ; from_ids := froms
               ; to_ids   := tos |}
      -> user_keys usrs u_id = Some ks
      -> keys_and_permissions_good gks (usrs $+ (u_id,u_d)) adv_heap.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition idtac.
    econstructor; eauto; subst; simpl.
    
    permission_heaps_prop.
    unfold permission_heap_good; intros.
    cases (ks $? k_id); cases (findKeysMessage msg $? k_id); simplify_key_merges1; clean_map_lookups; eauto.
    cases (gks $? k_id); eauto.
    exfalso; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_user_new_pubk.

  Ltac process_permission_heaps :=
    repeat
      match goal with
      | [ H : keys_and_permissions_good _ _ _ |- keys_and_permissions_good _ _ _ ] =>
        unfold keys_and_permissions_good in *; split_ands; intuition idtac
      | [ |- permission_heap_good _ (RealWorld.key_heap ?u) ] => progress simpl || destruct u; simpl in *
      | [ |- Forall_natmap (fun _ => permission_heap_good _ _) ?usrs ] => rewrite Forall_natmap_forall; intros
      | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => destruct (k1 ==n k2); subst; clean_map_lookups
      | [ OK : Forall_natmap (fun _ => permission_heap_good _ _) ?usrs
        , USR : ?usrs $? _ = Some {| key_heap := ?ks ; protocol := _ ; msg_heap := _ ; c_heap := _ |}
          |- permission_heap_good _ ?ks ] => generalize (Forall_natmap_in_prop _ OK USR); intros; clear USR
      | [ OK : Forall_natmap (fun _ => permission_heap_good _ _) ?usrs
        , USR : ?usrs $? _ = Some {| key_heap := ?ks ; protocol := _ ; msg_heap := _ ; c_heap := _ |}
        , KS : ?ks $? _ = Some _
          |- permission_heap_good _ ?ks ] => generalize (Forall_natmap_in_prop _ OK USR); intros; idtac ks; clear USR
      | [ H : permission_heap_good _ _ |- _ ] => unfold permission_heap_good in H
      | [ |- permission_heap_good _ _ ] => unfold permission_heap_good; intros; simpl in *
      | [ H : ?m1 $k++ ?m2 $? ?kid = _ |- _ ] => cases (m1 $? kid); cases (m2 $? kid); simplify_key_merges1; clean_context
      | [ H : keys_mine _ ?othr_kys, KS : ?othr_kys $? _ = Some _ |- _ ] => specialize (H _ _ KS); split_ors; split_ands
      | [ H : (forall k kp, findKeysMessage ?msg $? k = Some kp -> _ ), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
        specialize (H _ _ ARG); split_ands; subst
      | [ H : (forall k_id kp, ?perms $? k_id = Some kp -> _), ARG : ?perms $? ?k = Some _ |- _ $? ?k <> None ] =>
        specialize (H _ _ ARG); split_ex
      end.

  Lemma honest_labeled_step_keys_and_permissions_good :
    forall {A B C} suid u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> message_queues_ok cs usrs gks
            -> action_adversary_safe (findUserKeys usrs) cs a
            -> forall usrs'' cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs'
                                            ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}) 
                -> keys_and_permissions_good gks' usrs'' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto 2;
      clean_context;
      msg_queue_prop;
      eauto;
      process_permission_heaps;
      permission_heaps_prop;
      specialize_msg_ok;
      eauto;
      clean_map_lookups.

    cases (gks' $? k_id); try contradiction; eauto.
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

  Lemma permission_heap_good_new_key_perm :
    forall gks ks k_id k,
      permission_heap_good gks ks
      -> ~ In k_id gks
      -> keyId k = k_id
      -> permission_heap_good (gks $+ (k_id,k)) (add_key_perm k_id true ks).
  Proof.
    unfold permission_heap_good; intros; subst.
    unfold add_key_perm in *.
    destruct (keyId k ==n k_id0); subst; clean_map_lookups; eauto.
    cases (ks $? keyId k); clean_map_lookups; eauto.
  Qed.

  Hint Resolve permission_heap_good_addnl_key permission_heap_good_new_key_perm.

  Lemma permission_heaps_good_addnl_key :
    forall {A} (usrs : honest_users A) gks k,
      ~ In (keyId k) gks
      -> Forall_natmap (fun u => permission_heap_good gks (key_heap u)) usrs
      -> Forall_natmap (fun u => permission_heap_good (gks $+ (keyId k, k)) (key_heap u)) usrs.
  Proof.
    intros; rewrite Forall_natmap_forall in *; intros; eauto.
  Qed.

  Hint Resolve permission_heaps_good_addnl_key.
  
  Lemma keys_and_permissions_good_addnl_key :
    forall {A} gks (usrs : honest_users A) adv_heap k_id k,
      keys_and_permissions_good gks usrs adv_heap
      -> ~ In k_id gks
      -> keyId k = k_id
      -> keys_and_permissions_good (gks $+ (k_id,k)) usrs adv_heap.
  Proof.
    intros. unfold keys_and_permissions_good in *; split_ands; subst; intuition eauto.
    destruct (keyId k ==n k_id); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_addnl_key.

  Lemma keys_and_permissions_good_readd_user_same_perms :
    forall {A} (usrs : honest_users A) adv_heap gks ks cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' tos tos' u_id,
      keys_and_permissions_good gks usrs adv_heap
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs; from_ids := froms; to_ids := tos |}
      -> keys_and_permissions_good gks (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs'; from_ids := froms'; to_ids := tos' |})) adv_heap.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition eauto.
    econstructor; eauto.
    simpl.
    eapply Forall_natmap_in_prop in H; eauto.
    simpl in *; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_readd_user_same_perms.

  Lemma keys_and_permissions_good_new_honest_key :
    forall {A} (usrs : honest_users A) gks k_id k ks u_id cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' tos tos' adv_heap,
      gks $? k_id = None
      -> keys_and_permissions_good gks usrs adv_heap
      -> k_id = keyId k
      -> usrs $? u_id = Some {| key_heap := ks ; protocol := cmd ; msg_heap := qmsgs ; c_heap := mycs; from_ids := froms; to_ids := tos |}
      -> keys_and_permissions_good (gks $+ (k_id,k))
                                  (usrs $+ (u_id,
                                            {| key_heap := add_key_perm k_id true ks
                                             ; protocol := cmd'
                                             ; msg_heap := qmsgs'
                                             ; c_heap   := mycs'
                                             ; from_ids := froms'
                                             ; to_ids   := tos' |}))
                                  adv_heap.
  Proof.
    intros.
    keys_and_permissions_prop.
    unfold keys_and_permissions_good; intuition eauto.
    - destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
    - econstructor; eauto; simpl.
      + unfold permission_heap_good; intros; simpl in *.
        destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
        unfold add_key_perm in *.
        cases (ks $? keyId k); clean_map_lookups; try discriminate; process_permission_heaps.
        specialize (H7 _ _ H8); auto.
        specialize (H7 _ _ H8); auto.
      + eapply keys_and_permissions_good_addnl_key; eauto; unfold keys_and_permissions_good; eauto.
  Qed.

  Hint Resolve keys_and_permissions_good_new_honest_key.

  Lemma honest_silent_step_keys_good :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                  -> keys_and_permissions_good gks'
                                              (usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}))
                                              adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst;
      try discriminate; eauto 2; clean_context.

    user_cipher_queues_prop;
      encrypted_ciphers_prop.

    eapply keys_and_permissions_good_user_new_pubk; eauto;
      keys_and_permissions_prop;
      process_permission_heaps;
      intuition contra_map_lookup.
  Qed.

  Lemma adv_step_keys_good :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> ks = adv.(key_heap)
        -> adv_message_queue_ok (findUserKeys usrs) cs gks qmsgs
        -> adv_cipher_queue_ok cs mycs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> keys_and_permissions_good gks usrs ks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> keys_and_permissions_good gks' usrs' ks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst; try discriminate;
      eauto; clean_context.

    - unfold keys_and_permissions_good in *; intuition eauto.
      unfold permission_heap_good in *; intros.
      cases (key_heap adv' $? k_id); eauto.
      invert H19; split_ands.
      cases (findKeysCrypto cs' msg $? k_id); simplify_key_merges1; try discriminate.
      specialize (H4 _ _ Heq0); split_ands; subst.
      cases (gks' $? k_id); try contradiction; eauto.
    - destruct rec_u; simpl in *.
      eapply keys_and_permissions_good_readd_user_same_perms; eauto.
    - unfold keys_and_permissions_good in *; intuition eauto.
      unfold permission_heap_good in *; intros.
      eapply merge_perms_split in H5; split_ors; eauto.
      encrypted_ciphers_prop; clean_map_lookups; eauto.
      + specialize_msg_ok; split_ex; intuition eauto.
      + assert (permission_heap_good gks' (findUserKeys usrs')) by eauto.
        specialize_msg_ok; subst.
        specialize (H9 _ _ H10); eauto.

    - unfold keys_and_permissions_good in *; intuition eauto.
      destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
      rewrite Forall_natmap_forall in *; intros.
      eapply permission_heap_good_addnl_key; eauto.
    - unfold keys_and_permissions_good in *; intuition eauto.
      destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
      rewrite Forall_natmap_forall in *; intros.
      eapply permission_heap_good_addnl_key; eauto.
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
    forall {A} (usrs : honest_users A) adv_heap cs gks,
      keys_and_permissions_good gks usrs adv_heap
      -> keys_and_permissions_good
          (clean_keys (findUserKeys usrs) gks)
          (clean_users (findUserKeys usrs) cs usrs)
          (clean_key_permissions (findUserKeys usrs) adv_heap).
  Proof.
    unfold keys_and_permissions_good; intros; split_ands.
    intuition (simpl; eauto).

    Ltac inv_cleans :=
      repeat
        match goal with
        | [ H : clean_keys _ _ $? _ = Some _ |- _ ] => eapply clean_keys_inv in H; split_ands
        | [ H : clean_keys _ _ $? _ = None |- _ ] => eapply clean_keys_inv' in H; split_ands
        | [ H : clean_users _ _ _ $? _ = Some _ |- _ ] => eapply clean_users_cleans_user_inv in H; split_ex; split_ands
        end.
    
    - inv_cleans; eauto.
    - apply Forall_natmap_forall; intros; inv_cleans.
      rewrite H3.
      permission_heaps_prop; eauto.
  Qed.

  (* Step user cipher queues ok *)

  Lemma user_cipher_queues_ok_readd_user :
    forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs froms froms' tos tos',
      usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok cs
          (findUserKeys usrs)
          (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs ; from_ids := froms' ; to_ids := tos' |})).
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
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms tos,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (add_key_perm k_id true (findUserKeys usrs))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok; rewrite Forall_natmap_forall; intros.
    user_cipher_queue_lkup UCQ.

    split_ex; destruct (k ==n u_id); subst; clean_map_lookups; simpl.
    user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
    clear H2; user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key' :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms tos,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (findUserKeys usrs $+ (k_id,true))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |})).
  Proof.
    intros.
    pose proof (user_cipher_queues_ok_addnl_generated_key ks k_id _ cmd qmsgs froms tos H H0).
    unfold add_key_perm in H1 at 1; unfold greatest_permission in H1;
      cases (findUserKeys usrs $? k_id); simpl in *; eapply H1.
  Qed.

  Hint Resolve user_cipher_queues_ok_addnl_generated_key user_cipher_queues_ok_addnl_generated_key'.

  Lemma msgCiphersSignedOk_user_cipher_queue_ok_findCiphers :
    forall {t} (msg : crypto t) honestk cs,
      msgCiphersSignedOk honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeysCrypto cs msg) (findCiphers msg).
  Proof.
    induction msg;
      intros;
      unfold user_cipher_queue_ok in *;
      repeat
        match goal with
        | [ H : msg_honestly_signed _ _ (SignedCiphertext ?cid) = true |- _ ] =>
          unfold msg_honestly_signed, msg_signing_key in H;
            cases (cs $? cid); try discriminate;
              destruct c; try discriminate; simpl in H
        | [ H : msgCiphersSignedOk _ _ _ |- _ ] => invert H; simpl in *; split_ands; split_ex
        | [ H : honest_keyb _ _ = true |- _ ] => apply honest_keyb_true_findKeys in H
        | [ |- Forall _ _ ] => econstructor
        | [ |- exists _, _ /\ _ ] => eexists; split
        | [ |- cipher_honestly_signed _ _ = _ ] => simpl; unfold honest_keyb; simplify_perm_merges; simplify_key_merges1
        | [ |- ?cs $? _ = _ ] => eassumption
        end; eauto.
  Qed.

  Hint Resolve
       cipher_honestly_signed_after_msg_keys
       msgCiphersSignedOk_user_cipher_queue_ok_findCiphers.

  Lemma user_cipher_queue_ok_add_user :
    forall {t} (msg : crypto t) cs honestk mycs,
      user_cipher_queue_ok cs honestk mycs
      -> msgCiphersSignedOk honestk cs msg
      -> user_cipher_queue_ok cs (honestk $k++ findKeysCrypto cs msg) (findCiphers msg ++ mycs).
  Proof.
    induction 1; unfold msgCiphersSignedOk; intros.
    - rewrite app_nil_r; eauto.
    - unfold user_cipher_queue_ok. rewrite Forall_app_sym, <- app_comm_cons.
      econstructor; split_ex; split_ands.
      + intuition eauto.
      + rewrite Forall_app_sym; 
          eapply IHForall; auto.
  Qed.

  Hint Resolve
       user_cipher_queue_ok_add_user
       user_cipher_queue_ok_addnl_pubk.

  Lemma user_cipher_queues_ok_add_user :
    forall {A t} (usrs usrs' : honest_users A) (msg : crypto t) honestk u_id ks cmd cmd' qmsgs qmsgs' mycs froms froms' tos tos' cs,
      user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> msgCiphersSignedOk (findUserKeys usrs) cs msg
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ findKeysCrypto cs msg; protocol := cmd'; msg_heap := qmsgs'; c_heap := findCiphers msg ++ mycs ; from_ids := froms';  to_ids := tos' |})
      -> honestk = findUserKeys usrs'
      -> user_cipher_queues_ok cs honestk usrs'.
  Proof.
    intros;
      unfold user_cipher_queues_ok.
    rewrite Forall_natmap_forall; intros; subst.
    autorewrite with find_user_keys.
    cases (u_id ==n k); subst; clean_map_lookups; user_cipher_queues_prop; eauto.
  Qed.

  Hint Resolve
       user_cipher_queues_ok_addnl_global_cipher
       user_cipher_queues_ok_add_user
       user_cipher_queues_ok_readd_user
       user_cipher_queues_ok_addnl_pubk
       findUserKeys_has_key_of_user
       findUserKeys_has_private_key_of_user
  .

  Lemma findUserKeys_keys_mine_user :
    forall {A} (usrs : honest_users A) msgk u_id ks qmsgs cmd mycs froms tos,
      keys_mine ks msgk
      -> usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> keys_mine (findUserKeys usrs) msgk.
  Proof.
    unfold keys_mine; intros.
    specialize (H _ _ H1); split_ors; split_ands; subst; eauto.
    cases kp; subst; eauto.
    assert (findUserKeys usrs $? k_id <> None); eauto.
    cases (findUserKeys usrs $? k_id); clean_map_lookups; try contradiction.
    cases b; eauto.
  Qed.

  Hint Resolve findUserKeys_keys_mine_user.

  Lemma merge_keys_mine :
    forall ks1 ks2,
      keys_mine ks1 ks2
      -> ks1 $k++ ks2 = ks1.
  Proof.
    unfold keys_mine; intros.
    apply map_eq_Equal; unfold Equal; intros.
    simplify_perm_merges;
      try match goal with
          | [ H : (forall kid kp, ?ks2 $? kid = Some kp -> _), H1 : ?ks2 $? _ = Some _ |- _ ] =>
            specialize (H _ _ H1); split_ors; split_ands; subst; clean_map_lookups
          end; simplify_key_merges; eauto.
  Qed.

  Lemma honest_labeled_step_user_cipher_queues_ok :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a suid,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate; eauto;
      autorewrite with find_user_keys; clean_context.

    - msg_queue_prop; eauto.
      specialize_msg_ok.
      eapply user_cipher_queues_ok_add_user; autorewrite with find_user_keys; eauto.

    - remember ((usrs $+ (rec_u_id,
                          {| key_heap := key_heap rec_u;
                             protocol := protocol rec_u;
                             msg_heap := msg_heap rec_u ++ [existT crypto t0 msg];
                             c_heap := c_heap rec_u |}))) as usrs'.

      assert (findUserKeys usrs = findUserKeys usrs') as RW
          by (subst; autorewrite with find_user_keys; eauto).

      rewrite RW; clear RW.
      destruct rec_u; simpl in *.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
      autorewrite with find_user_keys.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
  Qed.

  Lemma honest_silent_step_user_cipher_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        user_cipher_queues_prop;
        clean_context; eauto.

    - econstructor; simpl.
      +  econstructor; eauto.
         eexists; clean_map_lookups; intuition eauto.
         assert (findUserKeys usrs' $? k__signid = Some true) by eauto.
         simpl; unfold honest_keyb; context_map_rewrites; eauto.
      +  eapply user_cipher_queues_ok_addnl_global_cipher; eauto.

    - econstructor; simpl; eauto.
      + econstructor; clean_map_lookups; eauto.
        eexists; intuition eauto.
        assert (findUserKeys usrs' $? k_id = Some true) by eauto.
        simpl; unfold honest_keyb; context_map_rewrites; eauto.
        
      + eapply user_cipher_queues_ok_addnl_global_cipher; eauto.
  Qed.

  Lemma adv_step_user_cipher_queues_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> honestk' = findUserKeys usrs'
            -> user_cipher_queues_ok cs' honestk' usrs'.
  Proof.
    induction 1; inversion 1; inversion 4; intros; subst; eauto.

    destruct rec_u; simpl in *;
      autorewrite with find_user_keys; eauto.
  Qed.

  (* Message queues ok step *)

  Lemma message_no_adv_private_new_keys :
    forall {t} (msg : crypto t) honestk cs pubk,
      message_no_adv_private honestk cs msg
      -> message_no_adv_private (honestk $k++ pubk) cs msg.
  Proof.
    unfold message_no_adv_private; intros.
    specialize (H _ _ H0).
    cases (pubk $? k); simplify_key_merges; intuition eauto.
  Qed.

  Lemma message_no_adv_private_new_honestk :
    forall {t} (msg : crypto t) honestk cs k_id,
      message_no_adv_private honestk cs msg
      -> message_no_adv_private (honestk $+ (k_id,true)) cs msg.
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

    destruct x; simpl in *; intuition eauto;
      specialize_msg_ok; eauto;
        repeat
          match goal with
          | [ H : honest_key (_ $k++ _) _ |- _ ] => invert H
          | [ H : _ $k++ _ $? _ = Some true |- _ ] => apply merge_perms_split in H; split_ors
          end;
        specialize_msg_ok; eauto.
  Qed.

  Hint Resolve message_queue_ok_adding_public_keys.

  Lemma message_queues_ok_user_adding_public_keys :
    forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs mycs mycs' froms froms' tos tos',
      message_queues_ok cs usrs gks
      -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true /\ p = false)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := msg::msgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ pubk; protocol := cmd'; msg_heap := msgs; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
      -> message_queues_ok cs usrs' gks.
  Proof.
    intros; subst.
    unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros.
    destruct (u_id ==n k); subst; clean_map_lookups; autorewrite with find_user_keys; eauto; simpl.
    eapply message_queue_ok_adding_public_keys; eauto.
    specialize (H _ _ H1); invert H; eauto.
  Qed.

  Hint Resolve message_queues_ok_user_adding_public_keys.

  Lemma message_queues_ok_readd_user_same_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' tos tos' gks,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; autorewrite with find_user_keys; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_same_queue.

  Lemma message_queues_ok_readd_user_popped_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' tos tos' gks qmsg,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsg :: qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; autorewrite with find_user_keys; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve
       message_queues_ok_readd_user_popped_queue
       msgCiphersSignedOk_addnl_cipher
       msgCiphersSignedOk_new_honest_key'.

  Lemma message_queue_ok_addnl_cipher :
    forall msgs cs honestk c_id c gks,
      message_queue_ok honestk cs msgs gks
      -> ~ In c_id cs
      -> message_queue_ok honestk (cs $+ (c_id, c)) msgs gks.
  Proof.
    unfold message_queue_ok; induction 1; eauto; intros;
      econstructor; eauto.

    destruct x; simpl in *; split_ands.
    repeat (apply conj); intros.
    - unfold findKeysCrypto in *; destruct c0; eauto.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; simpl in *;
        assert ( cs $? c_id0 <> None ) by eauto; try contradiction.

      cases (cs $? c_id0); try contradiction; context_map_rewrites.
      assert ( Some (cipher_signing_key c0) = Some (cipher_signing_key c0) ) as CS by eauto.
      specialize (H3 _ CS); split_ands; eauto.

    - unfold msg_cipher_id in *; destruct (c_id ==n cid); subst; clean_map_lookups.
      destruct c0; eauto.
    - unfold msg_signing_key in *; destruct c0; try discriminate;
        destruct (c_id ==n c_id0); subst; clean_map_lookups; simpl in *; context_map_rewrites;
          assert (cs $? c_id0 <> None) by eauto; try contradiction.
      cases (cs $? c_id0); try discriminate; clean_context.
      assert (Some (cipher_signing_key c0) = Some (cipher_signing_key c0)) as SC by trivial.
      specialize (H3 _ SC); intuition eauto.
      unfold message_no_adv_private,findKeysCrypto in *; intros; clean_map_lookups; context_map_rewrites; eauto.
  Qed.

  Hint Resolve message_queue_ok_addnl_cipher.

  Lemma message_queues_ok_addnl_cipher :
    forall {A} (usrs : honest_users A) cs c_id c gks,
      message_queues_ok cs usrs gks
      -> ~ In c_id cs
      -> message_queues_ok (cs $+ (c_id,c)) usrs gks.
  Proof.
    unfold message_queues_ok in *; intros; rewrite Forall_natmap_forall in *; intros; eauto.
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

  Lemma msg_signing_key_cipher_id_in_ciphers :
    forall {t} (c : crypto t) cs k_id c_id,
      msg_signing_key cs c = Some k_id
      -> msg_cipher_id c = Some c_id
      -> exists c, cs $? c_id = Some c
             /\ (exists {t} (m : message t) msg_to nonce,
                   c = SigCipher k_id msg_to nonce m
                 \/ exists k__enc, c = SigEncCipher k_id k__enc msg_to nonce m).
  Proof.
    intros.
    unfold msg_signing_key, msg_cipher_id in *.
    destruct c; try discriminate; invert H0;
      cases (cs $? c_id); try discriminate.

    destruct c; try discriminate; clean_context;
      eexists; split; eauto 8.
  Qed.

  Lemma message_queue_ok_addnl_honest_key :
    forall msgs cs honestk k_id gks usage kt,
      message_queue_ok honestk cs msgs gks
      -> gks $? k_id = None
      -> honestk $? k_id = None
      -> encrypted_ciphers_ok honestk cs gks
      -> message_queue_ok (honestk $+ (k_id,true)) cs msgs (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |} )).
  Proof.
    induction 1; intros; econstructor; unfold message_queue_ok in *; eauto.

    destruct x; simpl in *; intros.
    assert (honestk $? k_id = None) by eauto.
    split_ands; repeat (apply conj); intros; eauto.
    - unfold not; intro; destruct (k_id ==n k); subst; split_ands; clean_map_lookups; specialize_msg_ok; eauto.
    - specialize_msg_ok; destruct (k_id ==n k); subst; clean_map_lookups; split_ands; try contradiction; eauto.
      split; eauto.
      intros; eauto.
      invert H9; clean_map_lookups; specialize_msg_ok; eauto.
  Qed.

  Lemma message_queue_ok_addnl_adv_key :
    forall msgs cs honestk k_id gks usage kt,
      message_queue_ok honestk cs msgs gks
      -> ~ In k_id gks
      -> permission_heap_good gks honestk
      -> message_queue_ok honestk cs msgs (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |} )).
  Proof.
    induction 1; intros; econstructor; eauto.
    - destruct x; simpl in *; intros.
      assert (honestk $? k_id = None) by eauto.
      intuition eauto; specialize_msg_ok; eauto.
      + destruct (k_id ==n k); subst; clean_map_lookups; eauto.
      + destruct (k_id ==n k); subst; clean_map_lookups; specialize_msg_ok; eauto.
    - eapply IHForall; eauto.
  Qed.

  Lemma message_queues_ok_addnl_honest_key :
    forall {A} (usrs : honest_users A) cs u_id k_id gks ks cmd cmd' qmsgs mycs froms tos usage kt,
      message_queues_ok cs usrs gks
      -> ~ In k_id gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
      -> message_queues_ok cs
                          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}))
                          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold message_queues_ok; rewrite Forall_natmap_forall; intros.
    destruct (k ==n u_id); subst; clean_map_lookups; simpl;
      msg_queue_prop;
      autorewrite with find_user_keys;
      eapply message_queue_ok_addnl_honest_key; eauto.
  Qed.

  Lemma message_queues_ok_addnl_adv_key :
    forall {A} (usrs : honest_users A) cs k_id gks usage kt,
      message_queues_ok cs usrs gks
      -> ~ In k_id gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> message_queues_ok cs
                          usrs
                          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})).
  Proof.
    intros.
    unfold message_queues_ok; rewrite Forall_natmap_forall; intros.
    destruct v; simpl.
    msg_queue_prop; eapply message_queue_ok_addnl_adv_key; eauto.
  Qed.

  Hint Resolve message_queues_ok_addnl_honest_key message_queues_ok_addnl_adv_key.

  Lemma content_only_honest_public_keys_findkeys_no_priv :
    forall {t} (msg : message.message t) k honestk,
      content_only_honest_public_keys honestk msg
      -> findKeysMessage msg $? k <> Some true.
  Proof.
    induction 1; simpl; unfold not; intros; clean_map_lookups; eauto.
    - destruct (fst kp ==n k); destruct kp; simpl in *; subst; clean_map_lookups.
    - eapply merge_perms_split in H1; split_ors; contradiction.
  Qed.

  Hint Resolve content_only_honest_public_keys_findkeys_no_priv.

  Lemma message_contains_only_honest_public_keys_findkeys_no_priv :
    forall {t} (msg : crypto t) k honestk cs,
      msg_contains_only_honest_public_keys honestk cs msg
      -> findKeysCrypto cs msg $? k <> Some true.
  Proof.
    induction 1; simpl; intros; eauto;
      context_map_rewrites; clean_map_lookups; eauto.
  Qed.

  Hint Resolve message_contains_only_honest_public_keys_findkeys_no_priv.

  Lemma msg_cipher_id_in_mycs :
    forall {t} (msg : crypto t) mycs c_id,
      incl (findCiphers msg) mycs
      -> msg_cipher_id msg = Some c_id
      -> List.In c_id mycs.
  Proof.
    intros; destruct msg; simpl in *; try discriminate;
      clean_context; eauto.
  Qed.

  Hint Resolve msg_cipher_id_in_mycs.
    
  Lemma honestly_signed_message_in_key_heap :
    forall {t} (msg : crypto t) honestk cs gks k_id,
      msg_honestly_signed honestk cs msg = true
      -> permission_heap_good gks honestk
      -> msg_signing_key cs msg = Some k_id
      -> gks $? k_id <> None.
  Proof.
    intros.
    unfold msg_honestly_signed in *;
      rewrite H1 in H;
      process_keys_messages.
    specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
  Qed.

  Hint Resolve honestly_signed_message_in_key_heap.

  Lemma honest_labeled_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                            ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context; msg_queue_prop; specialize_msg_ok; eauto.

    eapply message_queues_ok_readd_user_same_queue;
      clean_map_lookups; eauto.

    unfold keys_and_permissions_good in *; split_ands; permission_heaps_prop.
    msg_queue_prop.
    econstructor; autorewrite with find_user_keys; eauto.
    simpl.
    eapply Forall_app; simpl; econstructor; eauto.
    split; intros.
    - unfold not; intros.
      specialize (H0 _ _ H14).
      split_ors; split_ands;
        match goal with
        | [ H : permission_heap_good _ ?ks , H1 : ?ks $? _ = _ |- _ ] =>
          specialize (H _ _ H1); split_ex; contra_map_lookup
        end.

    - split; intros.
      + assert (List.In cid mycs') by eauto.
        user_cipher_queues_prop.
      + unfold msg_signing_key in *.

        destruct msg; try discriminate;
          cases (cs' $? c_id); try discriminate;
            clean_context;
            encrypted_ciphers_prop;
            intuition eauto;
            simpl in *;
            contra_map_lookup;
            unfold message_no_adv_private;
            intros;
            simpl in *;
            clean_context;
            context_map_rewrites;
            clean_map_lookups.

        * destruct p; specialize_msg_ok; eauto.
          exfalso; eauto.
        * unfold msg_honestly_signed in *; simpl in *; context_map_rewrites; simpl in *.
            unfold honest_keyb in *;
            cases (findUserKeys usrs $? k); try discriminate;
              destruct b; try discriminate; contradiction.
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> permission_heap_good gks honestk
        -> message_queues_ok cs usrs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> message_queues_ok cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    msg_queue_prop.
    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    econstructor; autorewrite with find_user_keys; simpl; eauto.
    rewrite Forall_natmap_forall; intros; eauto.
    msg_queue_prop; eauto.
  Qed.

  Lemma adv_step_adv_cipher_queue_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> adv_message_queue_ok (findUserKeys usrs) cs gks qmsgs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> adv_no_honest_keys (findUserKeys usrs) ks
        -> adv_cipher_queue_ok cs mycs
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> adv_cipher_queue_ok cs' mycs'.
  Proof.
   induction 1; inversion 1; inversion 8; intros; subst;
      eauto 2; try discriminate; eauto; clean_context;
        unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.
   - invert H21; split_ands.
     rewrite in_app_iff in H; split_ors; eauto.
   - destruct (c_id ==n x); subst; clean_map_lookups; eauto.
     invert H5; try contradiction; eauto.
   - destruct (c_id ==n x); subst; clean_map_lookups; eauto.
     invert H2; try contradiction; eauto.
  Qed.

  Lemma adv_cipher_in_cipher_heap :
    forall {t} (msg : crypto t) adv_heap cs cid,
      incl (findCiphers msg) adv_heap
      -> adv_cipher_queue_ok cs adv_heap
      -> msg_cipher_id msg = Some cid
      -> exists c, cs $? cid = Some c.
  Proof.
    intros.
    unfold msg_cipher_id, adv_cipher_queue_ok in *.
    rewrite Forall_forall in H0.
    destruct msg; try discriminate;
      invert H1;
      simpl in *;
      assert (List.In cid adv_heap) as LIN by eauto;
      specialize (H0 _ LIN); auto.
  Qed.

  Lemma msgCiphersSignedOk_honest_key :
    forall t cs honestk c_id c k_id,
      cs $? c_id = Some c
      -> cipher_signing_key c = k_id
      -> honest_key honestk k_id
      -> msgCiphersSignedOk honestk cs (@SignedCiphertext t c_id).
  Proof.
    intros.
    unfold msgCiphersSignedOk; simpl; econstructor; eauto.
    unfold msg_honestly_signed; simpl; context_map_rewrites.
    unfold cipher_signing_key in *; rewrite <- honest_key_honest_keyb; auto.
    destruct c; subst; eauto.
  Qed.

  Hint Resolve msgCiphersSignedOk_honest_key.

  Lemma adv_step_message_queues_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok cs usrs gks
        -> permission_heap_good gks honestk
        -> permission_heap_good gks ks
        -> adv_cipher_queue_ok cs mycs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> honestk' = findUserKeys usrs'
            -> message_queues_ok cs' usrs' gks'.
  Proof.
    induction 1; inversion 1; inversion 10; intros; subst;
      eauto 2; try discriminate; eauto;
        clean_context.
    
    unfold message_queues_ok in *;
      rewrite Forall_natmap_forall in *;
      intros.

    destruct (rec_u_id ==n k); subst; clean_map_lookups;
      eauto;
      autorewrite with find_user_keys;
      simpl; eauto.

    unfold message_queue_ok; eapply Forall_app.
    unfold message_queue_ok in *; econstructor; eauto.

    repeat (apply conj); intros; eauto.
    - specialize (H0 _ _ H); split_ors; split_ands; subst; eauto.
      specialize (H24 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
      specialize (H24 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
    - unfold not; intros.
      unfold keys_mine in *.
      destruct msg; simpl in *; try discriminate; clean_context.
      unfold adv_cipher_queue_ok in H25; rewrite Forall_forall in H25.
      assert (List.In cid (c_heap adv)) by eauto.
      specialize (H25 _ H); split_ex; contra_map_lookup.
    - unfold msg_signing_key in *; destruct msg; try discriminate;
        cases (cs' $? c_id); try discriminate;
          clean_context.
      simpl in *; context_map_rewrites.

      encrypted_ciphers_prop; simpl in *; eauto;
        clean_context; intuition clean_map_lookups; eauto;
          unfold message_no_adv_private; intros; simpl in *; context_map_rewrites;
            repeat
              match goal with
              | [ ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] => is_var b; destruct b
              | [ H : (forall k, findKeysMessage ?msg $? k = Some ?b -> _), ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] =>
                specialize (H _ ARG)
              | [ H : honest_key ?honk ?k, H2 : ?honk $? ?k = Some true -> False |- _ ] => invert H; contradiction
              end; try contradiction; clean_map_lookups; eauto.
  Qed.
  
  Lemma adv_message_queue_ok_addnl_pubk :
    forall honestk pubk msgs cs gks,
      adv_message_queue_ok honestk cs gks msgs
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> adv_message_queue_ok (honestk $k++ pubk) cs gks msgs.
  Proof.
    unfold adv_message_queue_ok; induction 1; intros; econstructor; eauto.
    destruct x; intuition eauto;
      specialize (H _ _ H6); split_ands; eauto.

    subst; apply merge_perms_split in H8; split_ors; eauto.
  Qed.
  
  Hint Resolve adv_message_queue_ok_addnl_pubk.

  Lemma honest_labeled_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> adv_message_queue_ok honestk cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' cs' gks' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.

    - assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.
      msg_queue_prop; specialize_msg_ok; eauto.
    - unfold adv_message_queue_ok; rewrite Forall_app; econstructor; eauto.
      unfold msgCiphersSignedOk, findMsgCiphers in *; simpl in *;
        invert H5; simpl in *;
          unfold msg_honestly_signed, msg_signing_key in *;
        destruct msg; try discriminate;
          cases (cs' $? c_id); try discriminate.
      invert H6; context_map_rewrites; simpl in *.
      repeat (apply conj); intros; clean_context.
      + unfold not; intros; contra_map_lookup.
      + context_map_rewrites; destruct c; clean_map_lookups.
        encrypted_ciphers_prop; eauto.
        destruct kp.
        * specialize (H17 _ H5); contradiction.
        * specialize (H18 _ H5).
          keys_and_permissions_prop.
          specialize (H12 _ _ H18); split_ex; intuition contra_map_lookup.
          rewrite <- H15 in H25; discriminate.
      + encrypted_ciphers_prop; simpl; unfold not; intros; contra_map_lookup.
      + split_ors; subst; try contradiction; eauto.
  Qed.

  Lemma honest_labeled_step_adv_cipher_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> adv_cipher_queue_ok cs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc,
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> adv_cipher_queue_ok cs' adv'.(c_heap).
  Proof.
    induction 1; inversion 2; inversion 3; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context.
  Qed.

  Lemma adv_message_queue_ok_addnl_honestk_key :
    forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt,
      adv_message_queue_ok (findUserKeys usrs) cs gks adv_heap
      -> ~ In k_id gks
      -> adv_message_queue_ok
          (findUserKeys usrs $+ (k_id, true))
          cs
          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |}))
          adv_heap.
  Proof.
    intros.
    unfold adv_message_queue_ok in *; apply Forall_forall; intros.
    rewrite Forall_forall in H; specialize (H x); destruct x; intros.
    specialize (H H1); split_ands.
    intuition eauto;
      try specialize (H2 _ _ H5); split_ands; subst; eauto.

    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction; intuition idtac.

    destruct (k_id ==n k); subst; clean_map_lookups; eauto.
    eapply H0; rewrite in_find_iff; unfold not; intros; contradiction.

    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction; intuition idtac.
    unfold msg_signing_key in *; destruct c; try discriminate;
      cases (cs $? c_id); try discriminate; clean_context.
    simpl in *; context_map_rewrites; eauto.
  Qed.

  Lemma honest_silent_step_adv_cipher_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> adv_cipher_queue_ok cs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Silent
            -> adv_cipher_queue_ok cs' adv'.(c_heap).
  Proof.
    induction 1; inversion 2; inversion 2; intros; subst; try discriminate;
      eauto 2; clean_context;
        unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros;
          destruct (c_id ==n x); subst; clean_map_lookups; eauto.
  Qed.

  Lemma adv_message_queue_ok_addnl_global_key :
    forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt,
      adv_message_queue_ok (findUserKeys usrs) cs gks adv_heap
      -> ~ In k_id gks
      -> adv_message_queue_ok
          (findUserKeys usrs)
          cs
          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |}))
          adv_heap.
  Proof.
    intros.
    unfold adv_message_queue_ok in *; apply Forall_forall; intros.
    rewrite Forall_forall in H; specialize (H x); destruct x; intros.
    specialize (H H1); split_ands.
    intuition eauto;
      try specialize (H2 _ _ H5); split_ands; eauto.

    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction.
    destruct (k_id ==n k); subst; clean_map_lookups; try contradiction.
    unfold msg_signing_key in *; destruct c; try discriminate;
      simpl in *.
    assert (cs $? c_id <> None) by eauto;
      cases (cs $? c_id); try discriminate;
        clean_context; eauto.
  Qed.

  Hint Resolve adv_message_queue_ok_addnl_honestk_key adv_message_queue_ok_addnl_global_key.

  Lemma adv_message_queue_ok_addnl_cipher :
    forall honestk adv_heap cs gks c_id c,
      ~ In c_id cs
      -> adv_message_queue_ok honestk cs gks adv_heap
      -> adv_message_queue_ok honestk (cs $+ (c_id,c)) gks adv_heap.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H1).
    destruct x; split_ands.

    intuition eauto.
    - destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
    - unfold findKeysCrypto in H4.
      destruct c0; eauto; simpl in *.
      + specialize (H2 _ _ H5); split_ands; eauto.
      + specialize (H0 c_id0).
        rewrite in_find_iff in H.
        
        destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        cases (cs $? c_id0); eauto.
        destruct c0; clean_map_lookups.
        specialize (H2 _ _ H5); split_ands; eauto.
    - unfold findKeysCrypto in H5; destruct c0; simpl in *; eauto.
      * specialize (H2 _ _ H5); split_ands; eauto.
      * destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        ** assert (~ In c_id0 cs) by eauto; clean_map_lookups; context_map_rewrites.
           specialize (H0 c_id0); exfalso; eauto.
        ** cases (cs $? c_id0); clean_map_lookups.
           destruct c0; clean_map_lookups.
           specialize (H2 _ _ H5); split_ands; eauto.

    - unfold msg_signing_key in *; destruct c0; try discriminate.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; simpl in *;
        assert (exists c : cipher, cs $? c_id0 = Some c) by eauto;
        split_ex; context_map_rewrites; clean_context.
      + eapply H; rewrite in_find_iff; unfold not; intros; contra_map_lookup.
      + eapply H3; eauto.
           
    - unfold findKeysCrypto in H5; destruct c0; simpl in *; split_ors; subst; try discriminate; try contradiction.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
  Qed.
           
  Hint Resolve adv_message_queue_ok_addnl_cipher.

  Lemma honest_silent_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> message_queues_ok cs usrs gks
        -> adv_message_queue_ok honestk cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok honestk' cs' gks' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context.

    user_cipher_queues_prop.
    encrypted_ciphers_prop.
    rewrite merge_keys_addnl_honest; eauto.
  Qed.

  Lemma adv_step_adv_message_queue_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok honestk cs gks qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_message_queue_ok honestk' cs' gks' qmsgs'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; try discriminate; eauto;
        clean_context;
        autorewrite with find_user_keys;
        try match goal with
            | [ H : adv_message_queue_ok _ _ _ (_ :: _) |- _] => invert H
            end; auto.
  Qed.

  (* Step adv no honest keys *)

  Lemma honest_labeled_step_adv_no_honest_keys :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst;
      try discriminate; eauto 2;
        autorewrite with find_user_keys; eauto;
          clean_context.

    - msg_queue_prop; specialize_msg_ok;
        unfold adv_no_honest_keys, message_no_adv_private in *;
        simpl in *;
        repeat
          match goal with
          | [ RW : honest_keyb ?honk ?kid = _ , H : if honest_keyb ?honk ?kid then _ else _ |- _] => rewrite RW in H
          | [ H : (forall k_id, findUserKeys _ $? k_id = None \/ _) |- (forall k_id, _) ] => intro KID; specialize (H KID)
          | [ |- context [ _ $k++ $0 ] ] => rewrite merge_keys_right_identity
          | [ FK : findKeysCrypto _ ?msg $? ?kid = Some _, H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)
              |- context [ _ $k++ findKeysCrypto _ ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try simplify_key_merges1
          | [ FK : findKeysCrypto _ ?msg $? ?kid = None |- context [ ?uks $k++ findKeysCrypto _ ?msg $? ?kid] ] =>
            split_ors; split_ands; simplify_key_merges1
          | [ H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeysCrypto ?cs ?msg $? ?kid] ] =>
            match goal with
            | [ H : findKeysCrypto cs msg $? kid = _ |- _ ] => fail 1
            | _ => cases (findKeysCrypto cs msg $? kid)
            end
          end; eauto.

      split_ors; split_ands; contra_map_lookup; eauto.

    - unfold adv_no_honest_keys in *; intros.
      specialize (H20 k_id).
      assert (findKeysCrypto cs' msg $? k_id <> Some true) by eauto.
      intuition idtac.
      right; right; split; eauto; intros.

      eapply merge_perms_split in H10; split_ors; eauto.
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs ks
        -> adv_message_queue_ok honestk cs gks qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 7; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto;
        try rewrite add_key_perm_add_private_key; clean_context;
          match goal with
          | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
          end.

    - invert H23; split_ands.
      unfold adv_no_honest_keys in *; intros.
      specialize (H21 k_id); intuition idtac.
      right; right; intuition eauto.
      eapply merge_perms_split in H9; split_ors; auto.
      specialize (H3 _ _ H9); split_ands; eauto.
      
    - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (ADV k__encid); split_ors; split_ands; try contradiction;
        encrypted_ciphers_prop; clean_map_lookups; intuition idtac;
        unfold adv_no_honest_keys; intros;
          specialize (H22 k_id); clean_map_lookups; intuition idtac;
            right; right; split; eauto; intros;
              eapply merge_perms_split in H10; split_ors;
                try contradiction;
                specialize (H19 _ _ H10); split_ex; split_ands; eauto.

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

      + intros. specialize (H2 _ _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros.
        cases (honestk $? k); cases (pubk $? k); simplify_key_merges1; clean_context; eauto.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups.
        assert (Some true <> Some true) by auto; contradiction.
        assert (Some true <> Some true) by auto; contradiction.
        specialize (H3 _ _ Heq0); split_ands; subst; clean_map_lookups; eauto.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      + cases (pubk $? k__s); simplify_key_merges1; eauto.
      + cases (pubk $? k__e); simplify_key_merges1; eauto.
      + unfold keys_mine in *; intros.
        specialize (H3 _ _ H5).
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> mycs = adv.(c_heap)
        -> adv_no_honest_keys honestk ks
        -> permission_heap_good gks ks
        -> adv_cipher_queue_ok cs mycs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 1; inversion 8; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context.

    - econstructor; eauto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H24 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros; clear H24.
        specialize (H4 _ _ H5); destruct H4; split_ands; subst; eauto.
        specialize (H25 _ _ H4); split_ex; eexists.
        specialize (ADV k); intuition eauto; contra_map_lookup; subst; eauto.
        specialize (H25 _ _ H4); split_ex; eexists.
        specialize (ADV k); intuition eauto; contra_map_lookup; subst; eauto.
    - econstructor; eauto.
      specialize (H21 k_id).
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
  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

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
      forall {A} (usrs : honest_users A) honestk cs u_id,
        user_cipher_queue (clean_users honestk cs usrs) u_id
        = user_cipher_queue usrs u_id.
    Proof.
      unfold user_cipher_queue, clean_users; simpl; intros.
      rewrite mapi_o; intros; subst; auto; unfold option_map; simpl.
      cases (usrs $? u_id); auto.
    Qed.

    Lemma user_in_univ_user_in_stripped_univ :
      forall {A B} (U : universe A B) u_id user_data user_data',
        U.(users) $? u_id = Some user_data
        -> user_data' =
            {| key_heap := clean_key_permissions (findUserKeys U.(users)) user_data.(key_heap)
             ; protocol := user_data.(protocol)
             ; msg_heap := clean_messages (findUserKeys U.(users)) U.(all_ciphers) (Some u_id) user_data.(from_ids) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap)
             ; from_ids := user_data.(from_ids)
             ; to_ids   := user_data.(to_ids) |}
        -> (strip_adversary U).(s_users) $? u_id = Some user_data'.
    Proof.
      unfold strip_adversary, clean_users; destruct user_data; simpl; intros.
      rewrite <- find_mapsto_iff in H.
      rewrite <- find_mapsto_iff, mapi_mapsto_iff; intros; subst; auto; eexists; subst; simpl; intuition eauto.
      simpl; trivial.
    Qed.

    Hint Resolve user_in_univ_user_in_stripped_univ.

    Lemma prop_in_adv_message_queues_still_good_after_cleaning :
      forall msgs honestk cs suid froms P,
        Forall P msgs
        -> Forall P (clean_messages honestk cs suid froms msgs).
    Proof.
      induction msgs; intros; eauto.
      invert H.
      unfold clean_messages, clean_messages'; simpl.
      unfold msg_filter at 2; destruct a.
      destruct (msg_signed_addressed honestk cs suid c); eauto; simpl.
      cases (msg_nonce_ok cs froms c); eauto.
      rewrite fold_clean_messages2'.
      rewrite clean_messages'_fst_pull; eauto.
    Qed.

    Hint Resolve prop_in_adv_message_queues_still_good_after_cleaning.

    Hint Resolve honest_cipher_filter_fn_true_honest_signing_key.
    Hint Extern 1 (honest_key _ _) => process_keys_messages.
    Hint Resolve
         msg_honestly_signed_after_without_cleaning
         msg_honestly_signed_before_after_cleaning.
                                               
    Lemma msgCiphersSigned_before_clean_ciphers' :
      forall (msgs : queued_messages) honestk cs,
        Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk (clean_ciphers honestk cs) m = true end) msgs
        -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs.
    Proof.
      induction 1; econstructor; eauto.
      destruct x; intuition eauto.
    Qed.

    Hint Resolve clean_ciphers_keeps_honest_cipher.

    Lemma msgCiphersSigned_after_clean_ciphers' :
      forall (msgs : queued_messages) honestk honestk' cs,
        Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk' (clean_ciphers honestk cs) m = true end) msgs.
    Proof.
      induction 1; econstructor; eauto.
      destruct x.
      eapply msg_honestly_signed_before_after_cleaning in H.
      unfold msg_honestly_signed in *.
      cases ( msg_signing_key (clean_ciphers honestk cs) c ); try discriminate.
      unfold honest_keyb in *.
      cases (honestk $? k); try discriminate; destruct b; try discriminate.
      specialize (H1 _ Heq0); rewrite H1; trivial.
    Qed.

    Lemma msgCiphersSigned_after_clean_ciphers :
      forall {t} (msg : crypto t) honestk honestk' cs,
        msgCiphersSignedOk honestk cs msg
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> msgCiphersSignedOk honestk' (clean_ciphers honestk cs) msg.
    Proof.
      intros; eapply msgCiphersSigned_after_clean_ciphers'; eauto.
    Qed.

    Lemma msgCiphersSigned_before_clean_ciphers :
      forall {t} (msg : crypto t) honestk cs,
        msgCiphersSignedOk honestk (clean_ciphers honestk cs) msg
        -> msgCiphersSignedOk honestk cs msg.
    Proof.
      intros; eapply msgCiphersSigned_before_clean_ciphers'; eauto.
    Qed.

    Hint Resolve
         msgCiphersSigned_after_clean_ciphers
         clean_keys_keeps_honest_key.

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
        intros KID KP FK; specialize (H14 _ _ FK); intuition eauto.
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
        -> honestk' = findUserKeys (clean_users honestk cs usrs)
        -> user_cipher_queues_ok (clean_ciphers honestk cs) honestk' (clean_users honestk cs usrs).
    Proof.
      unfold user_cipher_queues_ok; intros.
      pose proof (clean_users_no_change_honestk usrs).
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H3; unfold clean_users in H3; rewrite mapi_mapsto_iff in H3; intros; subst; trivial.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H1; specialize (H _ _ H1).
      eapply user_cipher_queue_ok_after_cleaning; auto.
    Qed.

    Lemma msg_honestly_signed_cipher_honestly_signed :
      forall {t} (msg : crypto t) honestk c cs cid,
        msg_honestly_signed honestk cs msg = true
        -> msg_cipher_id msg = Some cid
        -> cs $? cid = Some c
        (* -> msgCipherOk cs msg *)
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

    Hint Resolve msg_honestly_signed_cipher_honestly_signed.

    Lemma findKeysCrypto_ok_clean_global_keys :
      forall {t} (msg : crypto t) cs gks honestk,
        (forall k kp, findKeysCrypto cs msg $? k = Some kp -> gks $? k <> None)
        -> message_no_adv_private honestk cs msg
        -> (forall k kp, findKeysCrypto cs msg $? k = Some kp -> clean_keys honestk gks $? k <> None).
    Proof.
      unfold message_no_adv_private; intros.
      specialize (H _ _ H1).
      specialize (H0 _ _ H1); split_ands; subst.
      cases (gks $? k); try contradiction.
      unfold not; intros.
      erewrite clean_keys_keeps_honest_key in H2; eauto.
    Qed.
    
    Hint Resolve findKeysCrypto_ok_clean_global_keys.

    Lemma msg_signing_key_same_after_cleaning :
      forall {t} (msg : crypto t) cs honestk k1 k2,
        msg_signing_key cs msg = Some k1
        -> msg_signing_key (clean_ciphers honestk cs) msg = Some k2
        -> k1 = k2.
    Proof.
      unfold msg_signing_key; intros.
      destruct msg; try discriminate.
      - cases (cs $? c_id); cases (clean_ciphers honestk cs $? c_id); try discriminate.
        rewrite <- find_mapsto_iff in Heq0; rewrite clean_ciphers_mapsto_iff in Heq0; rewrite find_mapsto_iff in Heq0;
          split_ands; clean_map_lookups.
        destruct c0; try discriminate; clean_context; trivial.
    Qed.

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
      - simpl in H; cases (msg_nonce_ok cs froms c); apply msg_nonce_ok_eq in Heq0;
          split_ors; split_ex; split_ands; try discriminate; clean_context; eauto.
        
        + rewrite fold_clean_messages2', clean_messages'_fst_pull in H; invert H;
            intuition eauto;
            specialize (IHmsgs _ H0); intuition eauto.
        + rewrite fold_clean_messages2', clean_messages'_fst_pull in H; invert H;
            intuition eauto;
            specialize (IHmsgs _ H0); intuition eauto.
        + specialize (IHmsgs _ H); intuition eauto.
        
      - specialize (IHmsgs _ H); intuition eauto.
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

    Lemma message_queue_ok_after_cleaning :
      forall msgs honestk honestk' cs gks suid mycs,
        message_queue_ok honestk cs msgs gks
        -> encrypted_ciphers_ok honestk cs gks
        -> (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
        -> message_queue_ok honestk' (clean_ciphers honestk cs)
                           (clean_messages honestk cs suid mycs msgs) (clean_keys honestk gks).
    Proof.
      intros; unfold message_queue_ok in *; rewrite Forall_forall in *; intros.
      eapply clean_messages_list_in_safe in H2; split_ands; destruct x.
      specialize (H _ H2); simpl in *; split_ands.

      repeat (apply conj); intros; specialize_msg_ok; eauto;
        unfold msg_signed_addressed in H3; eapply andb_prop in H3; split_ands;
          unfold msg_honestly_signed, msg_signing_key in *;
          destruct c; try discriminate.
      
      - unfold not; intros.

        unfold findKeysCrypto in *;
            cases (cs $? c_id); try discriminate;
              simpl in *.

        assert (clean_ciphers honestk cs $? c_id = Some c) by eauto;
          context_map_rewrites;
          destruct c; clean_map_lookups.
        specialize (H _ _ H6).

        assert (Some k__sign = Some k__sign) as KSEQ by trivial.
        specialize (H5 _ KSEQ); split_ands.
        simpl in H3; rewrite <- honest_key_honest_keyb in H3; specialize (H10 H3); split_ands.
        unfold message_no_adv_private in H10.
        simpl in *; context_map_rewrites.
        specialize (H10 _ _ H6); split_ands; subst.
        cases (gks $? k); try contradiction.
        eapply clean_keys_inv' in H8; eauto.
        unfold honest_key_filter_fn in H8; context_map_rewrites; discriminate.

      - simpl in *; clean_context;
          cases (cs $? cid); try discriminate.

        unfold not; intros;
          eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto;
            contra_map_lookup.

      - cases (clean_ciphers honestk cs $? c_id); try discriminate;
          clean_context.

        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq;
          split_ands; context_map_rewrites.
        assert (Some (cipher_signing_key c) = Some (cipher_signing_key c)) as CSK by trivial.
        specialize (H5 _ CSK); split_ands.
        rewrite <- honest_key_honest_keyb in H3.
        specialize (H9 H3); split_ands.
        cases (gks $? cipher_signing_key c); try contradiction.

        intuition eauto.

        + eapply clean_keys_inv' in H11; eauto.
          unfold honest_key_filter_fn in *; invert H3; context_map_rewrites; discriminate.

        + unfold message_no_adv_private in *; intros; clean_context; simpl in *.
          context_map_rewrites; eapply clean_ciphers_keeps_honest_cipher in H6;
            eauto; context_map_rewrites.

          destruct c; clean_map_lookups.
          specialize (H9 _ _ H12); intuition eauto.
    Qed.

    Lemma message_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs gks,
        message_queues_ok cs usrs gks
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs) (clean_keys honestk gks).
    Proof.
      unfold message_queues_ok; intros.
      pose proof (clean_users_no_change_honestk usrs).
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H3; unfold clean_users in H3; rewrite mapi_mapsto_iff in H3; intros; subst; trivial.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H3; specialize (H _ _ H3).
      eapply message_queue_ok_after_cleaning; auto.
    Qed.



    (* Lemma adv_message_queue_ok_after_cleaning : *)
    (*   forall honestk honestk' cs gks suid mycs msgs, *)
    (*     adv_message_queue_ok honestk cs gks msgs *)
    (*     -> encrypted_ciphers_ok honestk cs gks *)
    (*     -> (forall k, honestk $? k = Some true -> honestk' $? k = Some true) *)
    (*     -> adv_message_queue_ok *)
    (*         honestk' *)
    (*         (clean_ciphers honestk cs) *)
    (*         (clean_keys honestk gks) *)
    (*         (clean_messages honestk cs suid mycs msgs). *)
    (* Proof. *)
    (*   unfold adv_message_queue_ok; intros. *)
    (*   rewrite Forall_forall in *; intros. *)
    (*   eapply clean_messages_list_in_safe in H2; split_ands; destruct x. *)
    (*   specialize (H _ H2); simpl in *; split_ands. *)

    (*   repeat (apply conj); intros; *)
    (*     repeat *)
    (*       match goal with *)
    (*       | [ H : (forall cid, msg_cipher_id ?c = Some cid -> _), ARG : msg_cipher_id ?c = Some _ |- _ ] => *)
    (*         specialize (H _ ARG) *)
    (*       | [ H : (forall k kp, findKeysCrypto ?cs ?c $? k = Some kp -> _), ARG : findKeysCrypto ?cs ?c $? _ = Some _ |- _ ] => *)
    (*         specialize (H _ _ ARG) *)
    (*       | [ H : (forall cid, List.In cid ?c -> _), ARG : List.In _ ?c |- _ ] => specialize (H _ ARG) *)
    (*       | [ H : msg_filter _ _ _ _ _ = _ |- _ ] => unfold msg_filter,msg_honestly_signed in H *)
    (*       | [ H : match ?arg with _ => _ end = _ |- _ ] => cases arg; try discriminate *)
    (*       | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] => *)
    (*         unfold msg_signed_addressed in H; apply andb_prop in H; split_ands *)
    (*       (* | [ H : honest_keyb _ _ = _ |- _ ] => unfold honest_keyb in H *) *)
    (*       end; unfold msg_honestly_signed, msg_signing_key, msg_cipher_id in *; destruct c; try discriminate; *)
    (*       clean_context. *)

    (*   - unfold not; intros. *)
    (*     cases (cs $? cid); try contradiction; clean_context. *)
    (*     apply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto; *)
    (*       contra_map_lookup. *)

    (*   - unfold findKeysCrypto in *. *)
    (*     cases (cs $? c_id); try discriminate. *)
    (*     cases (clean_ciphers honestk cs $? c_id); clean_map_lookups. *)
    (*     apply clean_ciphers_keeps_honest_cipher with (honestk :=honestk) in Heq; contra_map_lookup; eauto. *)
    (*     destruct c0; clean_map_lookups; specialize_msg_ok. *)
    (*     rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq; split_ands. *)
    (*     encrypted_ciphers_prop. *)
    (*     destruct kp; *)
    (*       match goal with *)
    (*       | [ H : (forall k, findKeysMessage ?msg $? k = Some ?tf -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _] => *)
    (*         specialize (H _ ARG) *)
    (*       end; try contradiction; intuition eauto. *)
    (*     cases (gks $? k); try contradiction. *)
    (*     apply clean_keys_keeps_honest_key with (honestk := honestk) in Heq; eauto; contra_map_lookup. *)

    (*   - cases (cs $? c_id); try discriminate. *)
    (*     cases ( clean_ciphers honestk cs $? c_id ); try discriminate; clean_context. *)
    (*     eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto; clean_map_lookups. *)
    (*     unfold not; intros. *)
    (*     assert (gks $? cipher_signing_key c0 <> None) by eauto. *)
    (*     cases (gks $? cipher_signing_key c0); try contradiction. *)
    (*     eapply clean_keys_keeps_honest_key with (honestk := honestk) in Heq0; eauto; contra_map_lookup. *)

    (*   - unfold msg_filter, msg_honestly_signed in *. *)
    (*     cases (cs $? c_id0); try discriminate; clean_context; simpl in *; *)
    (*       split_ors; subst; try contradiction; eauto. *)
    (* Qed. *)

    Lemma adv_message_queue_ok_after_cleaning :
      forall honestk honestk' cs gks msgs,
        adv_message_queue_ok honestk cs gks msgs
        -> encrypted_ciphers_ok honestk cs gks
        -> (forall k, honestk $? k = Some true -> honestk' $? k = Some true)
        -> adv_message_queue_ok
            honestk'
            (clean_ciphers honestk cs)
            (clean_keys honestk gks)
            (clean_adv_msgs honestk cs msgs).
    Proof.
      unfold adv_message_queue_ok; intros.
      rewrite Forall_forall in *; intros.
      apply filter_In in H2; split_ands; destruct x.
      specialize (H _ H2); simpl in *; split_ands.

      repeat (apply conj); intros;
        repeat
          match goal with
          | [ H : (forall cid, msg_cipher_id ?c = Some cid -> _), ARG : msg_cipher_id ?c = Some _ |- _ ] =>
            specialize (H _ ARG)
          | [ H : (forall k kp, findKeysCrypto ?cs ?c $? k = Some kp -> _), ARG : findKeysCrypto ?cs ?c $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG)
          | [ H : (forall cid, List.In cid ?c -> _), ARG : List.In _ ?c |- _ ] => specialize (H _ ARG)
          | [ H : msg_filter _ _ _ _ _ = _ |- _ ] => unfold msg_filter,msg_honestly_signed in H
          | [ H : match ?arg with _ => _ end = _ |- _ ] => cases arg; try discriminate
          | [ H : msg_signed_addressed _ _ _ _ = true |- _ ] =>
            unfold msg_signed_addressed in H; apply andb_prop in H; split_ands
          (* | [ H : honest_keyb _ _ = _ |- _ ] => unfold honest_keyb in H *)
          end; unfold msg_honestly_signed, msg_signing_key, msg_cipher_id in *; destruct c; try discriminate;
          clean_context.

      - unfold not; intros.
        cases (cs $? cid); try contradiction; clean_context.
        apply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto;
          contra_map_lookup.

      - unfold findKeysCrypto in *.
        cases (cs $? c_id); try discriminate.
        cases (clean_ciphers honestk cs $? c_id); clean_map_lookups.
        apply clean_ciphers_keeps_honest_cipher with (honestk :=honestk) in Heq; contra_map_lookup; eauto.
        destruct c0; clean_map_lookups; specialize_msg_ok.
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq; split_ands.
        encrypted_ciphers_prop.
        destruct kp;
          match goal with
          | [ H : (forall k, findKeysMessage ?msg $? k = Some ?tf -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _] =>
            specialize (H _ ARG)
          end; try contradiction; intuition eauto.
        cases (gks $? k); try contradiction.
        apply clean_keys_keeps_honest_key with (honestk := honestk) in Heq; eauto; contra_map_lookup.

      - cases (cs $? c_id); try discriminate.
        cases ( clean_ciphers honestk cs $? c_id ); try discriminate; clean_context.
        eapply clean_ciphers_keeps_honest_cipher with (honestk := honestk) in Heq; eauto; clean_map_lookups.
        unfold not; intros.
        assert (gks $? cipher_signing_key c0 <> None) by eauto.
        cases (gks $? cipher_signing_key c0); try contradiction.
        eapply clean_keys_keeps_honest_key with (honestk := honestk) in Heq0; eauto; contra_map_lookup.

      - unfold msg_filter, msg_honestly_signed in *.
        cases (cs $? c_id0); try discriminate; clean_context; simpl in *;
          split_ors; subst; try contradiction; eauto.
    Qed.


    Lemma adv_no_honest_keys_after_cleaning :
      forall {A} (usrs : honest_users A) honestk honestk' cs adv_keys,
        adv_no_honest_keys honestk adv_keys
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys (clean_users honestk cs usrs)
        -> adv_no_honest_keys honestk' (clean_key_permissions honestk adv_keys).
    Proof.
      unfold adv_no_honest_keys; intros.
      pose proof (findUserKeys_clean_users_correct usrs cs k_id); subst.
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
                    (* , adv_message_queue_ok_after_cleaning *)
                    , adv_no_honest_keys_after_cleaning.
      econstructor.
      apply adv_message_queue_ok_after_cleaning; eauto using clean_users_no_change_honestk.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         not_in_ciphers_not_in_cleaned_ciphers.

    Lemma cipher_message_keys_already_in_honest :
      forall {A t} (msg : message t) (usrs : honest_users A) honestk cs msg_to nonce c_id k__s k__e gks,
        honestk = findUserKeys usrs
        -> cs $? c_id = Some (SigEncCipher k__s k__e msg_to nonce msg) 
        -> honest_key honestk k__s
        -> honest_key honestk k__e
        -> encrypted_ciphers_ok honestk cs gks
        -> honestk $k++ findKeysMessage msg = honestk.
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

    Hint Resolve msg_filter_same_new_honest_key.
    
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

    Lemma clean_adv_msgs_new_honest_key_idempotent :
      forall honestk k_id msgs cs gks,
           adv_message_queue_ok honestk cs gks msgs
        -> ~ In k_id gks
        -> clean_adv_msgs (honestk $+ (k_id, true)) cs msgs
          = clean_adv_msgs honestk cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H; split_ands.
      cases (msg_honestly_signed honestk cs c); simpl in *;
            match goal with
            | [ H : msg_honestly_signed honestk cs c = ?tf |- _] =>
              assert (msg_honestly_signed (honestk $+ (k_id,true)) cs c = tf)
                as MHS by eauto using msg_honestly_signed_nochange_addnl_honest_key
            end; rewrite MHS; simpl; eauto.
      f_equal; eauto.
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

    Hint Resolve clean_key_permissions_new_honest_key'.

    Lemma clean_adv_new_honest_key_idempotent :
      forall {B} (adv : user_data B) honestk k_id cs gks b,
        ~ In k_id gks
        -> permission_heap_good gks (key_heap adv)
        -> adv_message_queue_ok honestk cs gks adv.(msg_heap)
        -> clean_adv adv (honestk $+ (k_id, true)) cs b = clean_adv adv honestk cs b.
    Proof.
      intros.
      unfold clean_adv.
      cases (key_heap adv $? k_id).
      specialize (H0 _ _ Heq); split_ex; clean_map_lookups.
      erewrite clean_key_permissions_new_honest_key', clean_adv_msgs_new_honest_key_idempotent; clean_map_lookups; eauto.
    Qed.

    Lemma clean_users_new_honest_key_idempotent :
      forall {A} (usrs : honest_users A) adv_heap honestk k_id cs gks,
        ~ In k_id gks
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv_heap
        -> clean_users (honestk $+ (k_id, true)) cs usrs = clean_users honestk cs usrs.
    Proof.
      intros; subst.
      apply map_eq_Equal; unfold Equal; intros.
      cases (usrs $? y).
      - erewrite !clean_users_cleans_user; eauto.
        unfold keys_and_permissions_good in *; split_ands.
        eapply Forall_natmap_in_prop in H2; eauto.
        msg_queue_prop. unfold permission_heap_good in *.
        cases (key_heap u $? k_id). specialize (H2 _ _ Heq0); split_ex; clean_map_lookups.
        f_equal; symmetry; eauto using clean_messages_new_honest_key_idempotent.
      - rewrite !clean_users_adds_no_users; eauto.
    Qed.

    Hint Resolve clean_keys_new_honest_key.

    Lemma honestly_signed_message_accepted_by_pattern_same_after_cleaning :
      forall {t} (msg : crypto t) cs msg_to pat honestk,
        msg_accepted_by_pattern cs pat msg_to msg
        -> msg_honestly_signed honestk cs msg = true
        -> msg_accepted_by_pattern (clean_ciphers honestk cs) pat msg_to msg.
    Proof.
      intros.
      unfold msg_honestly_signed in *.
      invert H; econstructor; simpl in *; context_map_rewrites; eauto.
    Qed.
    
    Lemma message_not_accepted_by_pattern_same_after_cleaning :
      forall {t} (msg : crypto t) cs msg_to pat honestk,
        ~ msg_accepted_by_pattern cs pat msg_to msg
        -> ~ msg_accepted_by_pattern (clean_ciphers honestk cs) pat msg_to msg.
    Proof.
      unfold not; intros; apply H.
      invert H0; econstructor;
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H2; split_ands; eauto.
    Qed.

    Hint Resolve
         honestly_signed_message_accepted_by_pattern_same_after_cleaning
         message_not_accepted_by_pattern_same_after_cleaning.

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

    Lemma clean_adv_msgs_addnl_cipher_idempotent :
      forall msgs honestk cs c_id c gks,
        ~ In c_id cs
        -> adv_message_queue_ok honestk cs gks msgs
        -> clean_adv_msgs honestk (cs $+ (c_id,c)) msgs
          = clean_adv_msgs honestk cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H0; split_ands.
      cases (msg_honestly_signed honestk cs c0);
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

    Hint Resolve clean_messages_addnl_cipher_idempotent clean_adv_msgs_addnl_cipher_idempotent.

    Lemma clean_users_addnl_cipher_idempotent :
      forall {A} (usrs : honest_users A) honestk cs c_id c gks,
        ~ In c_id cs
        -> message_queues_ok cs usrs gks
        -> honestk = findUserKeys usrs
        -> clean_users honestk (cs $+ (c_id,c)) usrs = clean_users honestk cs usrs.
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      unfold clean_users.
      rewrite !mapi_o; simpl; intros; subst; trivial.
      cases (usrs $? y); eauto; simpl.
      msg_queue_prop.
      f_equal; subst.
      f_equal; eauto.
    Qed.

    Hint Resolve clean_users_addnl_cipher_idempotent.
    
    Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' (b: B),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> adv_message_queue_ok honestk cs gks adv.(msg_heap)
          -> forall cmd' cs__s' usrs__s' honestk',
                 bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_ids := froms
                                       ; to_ids := tos |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_ids := froms'
                                              ; to_ids := tos' |})
                  -> honestk' = findUserKeys usrs''
                  -> cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' cs' usrs'
                  -> encrypted_ciphers_ok honestk' cs' gks'
                  -> step_user lbl suid
                              (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks,
                               clean_messages honestk cs suid froms qmsgs, mycs, froms, tos, cmd)
                              (usrs__s', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks',
                               clean_messages honestk' cs' suid froms qmsgs', mycs', froms', tos', cmd')
                  \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs suid froms qmsgs, mycs, froms, tos, cmd)
                    = (clean_users honestk' cs' usrs', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                       clean_key_permissions honestk' ks',
                       clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', tos', cmd').
    Proof.
      induction 1; inversion 5; inversion 6; intros; subst; clean_context;
        autorewrite with find_user_keys in *;
        try solve [ left; econstructor; eauto;
                    user_cipher_queues_prop; eauto;
                    try solve_clean_keys_clean_key_permissions ].

      - remember (findUserKeys usrs) as honestk.
        remember (usrs' $+ (u_id, {| key_heap := ks'
                                   ; protocol := cmdc'
                                   ; msg_heap := qmsgs'
                                   ; c_heap := mycs'
                                   ; from_ids := froms'
                                   ; to_ids := tos' |})) as usrs''.
        remember (findUserKeys usrs'') as honestk'.
        remember (clean_ciphers honestk cs) as cs__s.
        remember (clean_ciphers honestk' cs') as cs__s'.
        remember (clean_users honestk cs usrs) as usrs__s.
        remember (clean_users honestk' cs' usrs') as usrs__s'.
        assert (@Silent action = Silent) as SIL by trivial.
        assert ((usrs,adv,cs,gks,ks,qmsgs,mycs,froms,tos,cmd1)
                =(usrs,adv,cs,gks,ks,qmsgs,mycs,froms,tos,cmd1)) as bd1 by trivial.
        assert ((usrs',adv',cs',gks',ks',qmsgs',mycs',froms',tos',cmd1')
                =(usrs',adv',cs',gks',ks',qmsgs',mycs',froms',tos',cmd1')) as bd1' by trivial.
        assert (Some u_id = Some u_id) by trivial.

        specialize (IHstep_user _ _ _ _ b H0 _ _ _ _
                                Heqhonestk
                                Heqcs__s
                                Hequsrs__s
                                bd1
                                H5
                                H16
                                H17
                                H18
                                H19
                                _ _ _ _
                                bd1'
                                SIL
                                _ _ _
                                H32
                                Hequsrs''
                                Heqhonestk'
                                Heqcs__s'
                                Hequsrs__s'
                                H37
                   ); split_ors; clean_context.
        + left; econstructor; eauto.
        + right; unfold clean_adv; simpl; inversion H1; subst. f_equal.

      - cases (msg_signed_addressed (findUserKeys usrs') cs' (Some u_id) msg).

        + cases (msg_nonce_ok cs' froms' msg).
          * left. econstructor; eauto.
            unfold clean_messages at 1.
            unfold clean_messages', msg_filter; simpl.
            rewrite Heq , Heq0, fold_clean_messages1'; trivial.
            rewrite clean_messages'_fst_pull, fold_clean_messages; eauto.
            admit. (* TODO need to know this was original honest message *)

          * right; simpl.
            unfold clean_messages at 1.
            unfold clean_messages', msg_filter; simpl.
            rewrite Heq , Heq0, fold_clean_messages1'; trivial.
          
        + right; simpl.
          unfold clean_messages at 1.
          unfold clean_messages', msg_filter; simpl.
          rewrite Heq, fold_clean_messages1'; trivial.

      - assert (findUserKeys usrs' $? k__signid = Some true) by eauto.
        encrypted_ciphers_prop.
        msg_queue_prop.
        left.
        erewrite clean_messages_addnl_cipher_idempotent, clean_users_addnl_cipher_idempotent; eauto.

        Hint Resolve clean_key_permissions_keeps_honest_permission.
        
        eapply StepEncrypt; eauto.
        unfold keys_mine in *; intros.
        specialize (H18 _ _ H7); split_ands; subst.
        specialize (H4 _ _ H7); split_ors; split_ands; subst; eauto.

      - assert (findUserKeys usrs' $? k__encid = Some true) by eauto.
        user_cipher_queues_prop;
          encrypted_ciphers_prop;
          clean_map_lookups.

        + assert ( findUserKeys usrs' $k++ findKeysMessage msg $? k__signid = Some true ).
          cases (findKeysMessage msg $? k__signid); simplify_key_merges1; eauto.
          contradiction.
        + left.
          rewrite merge_keys_addnl_honest; eauto.
          * econstructor; auto.
            ** eapply clean_ciphers_keeps_honest_cipher; eauto.
            ** eauto.
            ** eauto.
            ** eauto.
            ** eauto.
            ** rewrite clean_key_permissions_distributes_merge_key_permissions.
               assert (clean_key_permissions (findUserKeys usrs') (findKeysMessage msg) = findKeysMessage msg)
                 as CKP.
               apply map_eq_Equal; unfold Equal; intros.
               cases (findKeysMessage msg $? y).
               *** eapply clean_key_permissions_keeps_honest_permission; eauto.
                   unfold honest_perm_filter_fn.
                   specialize (H19 _ _ Heq); split_ands; subst.
                   eapply merge_perms_split in H5; split_ors; contra_map_lookup; context_map_rewrites; eauto.
               *** eapply clean_key_permissions_adds_no_permissions; eauto.
               *** rewrite CKP; eauto.
               
          * intros.
            specialize (H19 _ _ H5); split_ands; subst.
            apply merge_perms_split in H8; split_ors; contra_map_lookup; eauto.
            
      - assert (findUserKeys usrs' $? k_id = Some true) by eauto.
        encrypted_ciphers_prop.
        msg_queue_prop.
        left.
        erewrite clean_messages_addnl_cipher_idempotent, clean_users_addnl_cipher_idempotent; eauto.
        eapply StepSign; eauto.
        
      - msg_queue_prop.
        keys_and_permissions_prop.

        erewrite clean_users_new_honest_key_idempotent
               , clean_ciphers_new_honest_key_idempotent
               , clean_messages_new_honest_key_idempotent
               , clean_adv_new_honest_key_idempotent
               , clean_key_permissions_new_honest_key
        ; eauto.

        left; econstructor; eauto.
        eapply clean_keys_adds_no_keys; auto.
        cases (ks $? k_id); clean_map_lookups; eauto.
        specialize (H5 _ _ Heq); split_ex; contra_map_lookup.

      - msg_queue_prop.
        keys_and_permissions_prop.

        erewrite clean_users_new_honest_key_idempotent
               , clean_ciphers_new_honest_key_idempotent
               , clean_messages_new_honest_key_idempotent
               , clean_adv_new_honest_key_idempotent
               , clean_key_permissions_new_honest_key
        ; eauto.

        left; econstructor; eauto.
        eapply clean_keys_adds_no_keys; auto.
        cases (ks $? k_id); clean_map_lookups; eauto.
        specialize (H5 _ _ Heq); split_ex; contra_map_lookup.
    Admitted.

    Lemma honest_cipher_filter_fn_nochange_pubk :
      forall honestk pubk k v,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> honest_cipher_filter_fn honestk k v =
          honest_cipher_filter_fn (honestk $k++ pubk) k v.
    Proof.
      unfold honest_cipher_filter_fn; intros;
        unfold cipher_honestly_signed;
        cases v; unfold honest_keyb; simpl;
          cases (honestk $? k__sign); cases (pubk $? k__sign); simplify_key_merges1; auto;
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
        simplify_key_merges1; eauto;
          destruct b; eauto;
            specialize (H _ _ Heq1); split_ands; subst; contra_map_lookup.
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
        cases (pubk $? cipher_signing_key c); simplify_key_merges1; eauto;
          f_equal; eauto.
      - cases (honestk $? cipher_signing_key c); try discriminate.
        + destruct b; try discriminate.
          cases (pubk $? cipher_signing_key c); simplify_key_merges1; eauto;
            f_equal; eauto.
          generalize (H _ _ Heq2); intros; split_ands; subst; eauto.
       + cases (pubk $? cipher_signing_key c); simplify_key_merges1; eauto;
           f_equal; eauto.
         generalize (H _ _ Heq2); intros; split_ands; subst; eauto.
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

    Lemma clean_users_nochange_pubk :
      forall {A} (usrs: honest_users A) honestk cs pubk,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> clean_users (honestk $k++ pubk) cs usrs = clean_users honestk cs usrs.
    Proof.
      intros; unfold clean_users.
      eapply map_eq_Equal; unfold Equal; intros.
      rewrite !mapi_o; simpl; intros; subst; trivial.
      cases (usrs $? y); eauto.
      simpl.
      f_equal. f_equal.
      - rewrite clean_key_permissions_nochange_pubk; eauto.
      - rewrite clean_messages_nochange_pubk; trivial.
    Qed.

    Lemma clean_users_nochange_pubk_step :
      forall {A} (usrs: honest_users A) honestk cs pubk u_id ks cmd qmsgs mycs froms tos u_d u_d',
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> u_d = {| key_heap := ks $k++ pubk
                 ; protocol := cmd
                 ; msg_heap := qmsgs
                 ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
        -> u_d' = {| key_heap := clean_key_permissions honestk (ks $k++ pubk)
                  ; protocol := cmd
                  ; msg_heap := clean_messages honestk cs (Some u_id) froms qmsgs
                  ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
        -> clean_users (honestk $k++ pubk) cs (usrs $+ (u_id,u_d)) =
          clean_users honestk cs usrs $+ (u_id,u_d').
    Proof.
      intros.
      eapply map_eq_Equal; unfold Equal; intros.
      cases (u_id ==n y); subst; clean_map_lookups.
      + erewrite clean_users_cleans_user; clean_map_lookups; eauto. simpl.
        f_equal.
        rewrite clean_key_permissions_nochange_pubk; eauto.
        rewrite clean_messages_nochange_pubk; auto.
      + unfold clean_users.
        rewrite !mapi_o; intros; subst; trivial.
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
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a b,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        (* -> user_cipher_queues_ok (findUserKeys usrs) usrs cs *)
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                /\ clean_users (findUserKeys usrs'') cs' usrs'' =
                  clean_users (findUserKeys usrs') cs' usrs' $+ (u_id, {| key_heap := clean_key_permissions (findUserKeys usrs') ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                                                                    ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                /\ clean_adv adv' (findUserKeys usrs'') cs' b = clean_adv adv' (findUserKeys usrs) cs' b
                /\ clean_keys (findUserKeys usrs'') gks' = clean_keys (findUserKeys usrs') gks'.

    Proof.
      induction 1; inversion 4; inversion 2; intros; subst; try discriminate;
        eauto 2;
        autorewrite with find_user_keys;
        clean_context;
        simpl.

      - msg_queue_prop.
        split_ands; specialize_msg_ok.
        intuition eauto using clean_ciphers_nochange_pubk
                            , clean_messages_nochange_pubk
                            , clean_users_nochange_pubk_step
                            , clean_key_permissions_nochange_pubk
                            , clean_keys_nochange_pubk.
        unfold clean_adv; f_equal; eauto using clean_key_permissions_nochange_pubk, clean_adv_msgs_nochange_pubk.

      - destruct rec_u; simpl in *.
        intuition idtac.

        eapply map_eq_Equal; unfold Equal; intros.
        cases (y ==n u_id); subst; clean_map_lookups.
        * erewrite clean_users_cleans_user; clean_map_lookups; eauto.
        * unfold clean_users; rewrite !mapi_o; intros; subst; clean_map_lookups; trivial.
    Qed.

    Lemma honest_labeled_step_encrypted_ciphers_ok :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs' gks'.
    Proof.
      induction 1; inversion 5; inversion 2; intros; subst; try discriminate;
        eauto 2; autorewrite with find_user_keys;
          clean_context; eauto.

      msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
      specialize_msg_ok; eauto.
    Qed.

    Lemma honest_labeled_step_univ_ok :
      forall {A B} (U U' : universe A B) a__r,
        universe_ok U
        -> step_universe U (Action a__r) U'
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r
        -> message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        -> universe_ok U'.
    Proof.
      unfold universe_ok; intros.
      invert H0.
      destruct U; destruct userData.
      unfold buildUniverse, build_data_step in *; simpl in *.
      eapply honest_labeled_step_encrypted_ciphers_ok; eauto.
    Qed.

    Lemma honest_message_findKeysCrypto_same_after_cleaning :
      forall {t} (msg : crypto t) honestk cs,
        msg_honestly_signed honestk cs msg = true
        -> findKeysCrypto cs msg = findKeysCrypto (clean_ciphers honestk cs) msg.
    Proof.
      intros.
      unfold message_no_adv_private, msg_honestly_signed, findKeysCrypto in *.
      destruct msg; eauto.
      cases (cs $? c_id); simpl in *; context_map_rewrites.
      - destruct c; eauto;
          eapply clean_ciphers_reduces_or_keeps_same_ciphers with (honestk := honestk) in Heq;
          eauto; simpl in *; split_ors; split_ands; context_map_rewrites; eauto.
        rewrite H in H1; discriminate.
              
      - eapply clean_ciphers_no_new_ciphers with (honestk := honestk) in Heq.
        rewrite Heq; trivial.
    Qed.

    Lemma updateRecvNonce_clean_ciphers_idempotent_honest_msg :
      forall {t} (msg : crypto t) froms cs honestk,
        msg_honestly_signed honestk cs msg = true
        -> updateRecvNonce froms cs msg = updateRecvNonce froms (clean_ciphers honestk cs) msg.
    Proof.
      unfold updateRecvNonce; intros.
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

    Hint Resolve updateRecvNonce_clean_ciphers_idempotent_honest_msg.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a (b : B) suid,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> forall cmdc cmdc' usrs'' honestk',
              usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
              -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
              -> honestk' = findUserKeys usrs''
              -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv',
                  cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' cs' usrs'
                  -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
                  -> lbl = Action a
                  -> pwless_adv = {| key_heap := key_heap adv
                                  ; protocol := Return b
                                  ; msg_heap := adv.(msg_heap)
                                  ; c_heap   := adv.(c_heap)
                                  ; from_ids := adv.(from_ids)
                                  ; to_ids   := adv.(to_ids) |}
                  -> pwless_adv' = {| key_heap := key_heap adv'
                                   ; protocol := Return b
                                   ; msg_heap := adv'.(msg_heap)
                                   ; c_heap   := adv'.(c_heap)
                                   ; from_ids := adv'.(from_ids)
                                   ; to_ids   := adv'.(to_ids) |}
                  -> step_user (strip_label honestk cs lbl) suid
                              (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk cs suid froms qmsgs, mycs, froms, tos, cmd)
                              (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', tos', cmd').
    Proof.
      induction 1; inversion 7; inversion 6; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
          autorewrite with find_user_keys.
 
      - subst; msg_queue_prop; split_ands; specialize_msg_ok.
        rewrite clean_users_nochange_pubk, clean_ciphers_nochange_pubk, clean_messages_nochange_pubk; eauto.
        assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as HON_SIGN by eauto.
        assert (msg_to_this_user cs' (Some u_id) msg = true) as MSG_TO by eauto.
        unfold clean_messages at 1.
        unfold clean_messages'; simpl.
        unfold msg_signed_addressed.
        rewrite HON_SIGN, MSG_TO; econstructor; simpl; eauto.
        + subst.
          unfold msg_nonce_ok; context_map_rewrites.
          unfold cipher_nonce_absent_or_gt in H12; split_ors; split_ex; split_ands; simpl;
            context_map_rewrites.
          * simpl; rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; trivial.
          * cases (cipher_nonce x2 <=? x3); cases (x3 <? cipher_nonce x2); try Nat.order.
            ** simpl; rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; trivial.
            ** rewrite nat_compare_lt in l;
                 rewrite Nat.ltb_compare in Heq;
                 rewrite l in Heq; discriminate.
                                                                                 
        + erewrite honest_message_findKeysCrypto_same_after_cleaning; eauto.

      - eapply StepSend with (rec_u0 := {| key_heap := clean_key_permissions (findUserKeys usrs) rec_u.(key_heap)
                                         ; protocol := rec_u.(protocol)
                                         ; msg_heap := clean_messages (findUserKeys usrs) cs' (Some rec_u_id) rec_u.(from_ids) rec_u.(msg_heap)
                                         ; c_heap   := rec_u.(c_heap)
                                         ; from_ids := rec_u.(from_ids)
                                         ; to_ids   := rec_u.(to_ids) |});
          try (erewrite <- honest_message_findKeysCrypto_same_after_cleaning by solve [ eauto ] );
          eauto.
        
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl.
        rewrite clean_messages_keeps_honestly_signed; auto.
        unfold msg_signed_addressed; rewrite H4, H5; auto.
    Qed.

    Lemma content_contains_only_honest_public_keys_keys_honest :
      forall {t} (msg : message.message t) k kp honestk,
        content_only_honest_public_keys honestk msg
        -> findKeysMessage msg $? k = Some kp
        -> honestk $? k = Some true.
    Proof.
      induction 1; intros; simpl in *; clean_map_lookups; eauto.
      - destruct kp0; simpl in *.
        destruct (k0 ==n k); subst; clean_map_lookups; eauto.
      - apply merge_perms_split in H1; split_ors; split_ands; eauto.
    Qed.

    Hint Resolve content_contains_only_honest_public_keys_keys_honest.
    
    Lemma message_contains_only_honest_public_keys_keys_honest :
      forall {t} (msg : crypto t) k kp honestk cs,
        msg_contains_only_honest_public_keys honestk cs msg
        -> findKeysCrypto cs msg $? k = Some kp
        -> honestk $? k = Some true.
    Proof.
      induction 1; simpl; intros; subst; context_map_rewrites; clean_map_lookups; eauto.
    Qed.

    Lemma honestly_signed_message_to_this_user_None_always_true :
      forall {t} (msg : crypto t) honestk cs,
        msg_honestly_signed honestk cs msg = true
        -> msg_to_this_user cs None msg = true.
    Proof.
      intros.
      unfold msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in *.
      destruct msg; try discriminate.
      cases (cs $? c_id); try discriminate; trivial.
    Qed.

    Hint Resolve honestly_signed_message_to_this_user_None_always_true.

    Lemma clean_adv_msgs_keeps_honest_msg :
      forall {t} (msg : crypto t) honestk cs msgs,
        msg_honestly_signed honestk cs msg = true
        -> clean_adv_msgs honestk cs (msgs ++ [existT _ _ msg])
          = clean_adv_msgs honestk cs msgs ++ [existT _ _ msg].
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; simpl; eauto.
      - rewrite H; trivial.
      - destruct a.
        cases (msg_honestly_signed honestk cs c); eauto.
        rewrite <- app_comm_cons; f_equal; eauto.
    Qed.

    Hint Resolve clean_adv_msgs_keeps_honest_msg.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv' :
      forall {A B C} cs cs' lbl u_id suid (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a a' (b : B),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> forall cmd' cs__s' usrs__s' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> lbl = Action a
              -> user_queue usrs u_id = Some qmsgs
                  -> a' = strip_action (findUserKeys usrs) cs a
                  -> step_user (Action a') suid
                              (usrs__s, clean_adv adv (findUserKeys usrs) cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks, clean_messages honestk cs suid froms qmsgs, mycs, froms, tos, cmd)
                              (usrs__s', clean_adv adv' (findUserKeys usrs) cs' b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks', clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', tos', cmd').
    Proof.
      induction 1; inversion 7; inversion 4; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          clean_context;
          autorewrite with find_user_keys.

      - assert ( msg_honestly_signed (findUserKeys usrs') cs' msg = true ) as MHS by eauto.
        assert ( msg_to_this_user cs' (Some u_id) msg = true ) as MSGTO by eauto.
        split_ex; split_ands.
        unfold clean_messages at 1; unfold clean_messages'; simpl.
        unfold msg_signed_addressed; rewrite MHS, MSGTO; simpl.

        unfold msg_nonce_ok; subst; context_map_rewrites.
        unfold cipher_nonce_absent_or_gt in H2; split_ors; split_ex; split_ands;
          context_map_rewrites.

        + rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages.
          econstructor; eauto.

          * unfold updateRecvNonce; context_map_rewrites; trivial.
          * rewrite clean_key_permissions_distributes_merge_key_permissions.
            
            assert (clean_key_permissions (findUserKeys usrs') (@findKeysCrypto t0 cs' (SignedCiphertext x))
                    = @findKeysCrypto t0 (clean_ciphers (findUserKeys usrs') cs') (SignedCiphertext x)) as RW.

            unfold msg_honestly_signed in MHS; simpl in *;
              context_map_rewrites.
            assert (cs' $? x = Some x0) as CS by assumption.
            apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs') in CS; eauto.
            context_map_rewrites.

            msg_queue_prop. specialize_msg_ok.
            unfold message_no_adv_private in H11; simpl in H11; context_map_rewrites.
            destruct x0; eauto.
            apply map_eq_Equal; unfold Equal; intros.
            cases (findKeysMessage msg $? y); eauto.
            ** apply clean_key_permissions_keeps_honest_permission; eauto.
               unfold honest_perm_filter_fn.
               specialize (H11 _ _ Heq); split_ands; subst; context_map_rewrites; trivial.
            ** apply clean_key_permissions_adds_no_permissions; auto.
            ** rewrite RW; trivial.

        + cases (cipher_nonce x0 <=? x1); cases (x1 <? cipher_nonce x0); try Nat.order.
          * rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages.
            econstructor; eauto.
            
            ** unfold updateRecvNonce; context_map_rewrites; trivial.
               rewrite Heq; trivial.
               
            ** rewrite clean_key_permissions_distributes_merge_key_permissions.
            
               assert (clean_key_permissions (findUserKeys usrs') (@findKeysCrypto t0 cs' (SignedCiphertext x))
                       = @findKeysCrypto t0 (clean_ciphers (findUserKeys usrs') cs') (SignedCiphertext x)) as RW.

               unfold msg_honestly_signed in MHS; simpl in *;
                 context_map_rewrites.
               assert (cs' $? x = Some x0) as CS by assumption.
               apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs') in CS; eauto.
               context_map_rewrites.

               msg_queue_prop. specialize_msg_ok.
               unfold message_no_adv_private in H11; simpl in H11; context_map_rewrites.
               destruct x0; eauto.
               apply map_eq_Equal; unfold Equal; intros.
               cases (findKeysMessage msg $? y); eauto.
               *** apply clean_key_permissions_keeps_honest_permission; eauto.
                   unfold honest_perm_filter_fn.
                   simpl in H3; context_map_rewrites.
                   unfold message_no_adv_private in H12; simpl in H12; context_map_rewrites.
                   specialize (H12 _ _ Heq0); split_ands; subst; context_map_rewrites; trivial.
               *** apply clean_key_permissions_adds_no_permissions; auto.
               *** rewrite RW; trivial.

          *  rewrite nat_compare_lt in l;
               rewrite Nat.ltb_compare in Heq;
               rewrite l in Heq; discriminate.

      - eapply StepSend with (rec_u0 := {| key_heap := clean_key_permissions (findUserKeys usrs) rec_u.(key_heap)
                                         ; protocol := rec_u.(protocol)
                                         ; msg_heap := clean_messages (findUserKeys usrs) cs' (Some rec_u_id) rec_u.(from_ids) rec_u.(msg_heap)
                                         ; c_heap   := rec_u.(c_heap)
                                         ; from_ids := rec_u.(from_ids)
                                         ; to_ids   := rec_u.(to_ids) |});
          try (erewrite <- honest_message_findKeysCrypto_same_after_cleaning by solve [ eauto ] );
          eauto.

        + unfold keys_mine in *; intros.

          (* erewrite <- honest_message_findKeysCrypto_same_after_cleaning in H7 by solve [ eauto ]. *)
          pose proof (message_contains_only_honest_public_keys_keys_honest _ H H9).
          specialize (H0 _ _ H9); split_ors; split_ands; subst.
          * left; eapply clean_key_permissions_keeps_honest_permission; eauto.
          * right; intuition idtac.
            eapply clean_key_permissions_keeps_honest_permission; eauto.

        + eapply clean_users_cleans_user; eauto.
        + simpl.
          rewrite clean_users_add_pull; simpl; eauto.
          rewrite clean_messages_keeps_honestly_signed; eauto.
          unfold msg_signed_addressed.
          rewrite H4 , H5; trivial.
          
        + unfold clean_adv, addUserKeys; simpl.

          f_equal; eauto.
          rewrite clean_key_permissions_distributes_merge_key_permissions.
          apply map_eq_Equal; unfold Equal; intros.

          assert (clean_key_permissions (findUserKeys usrs) (findKeysCrypto cs' msg) $? y
                  = findKeysCrypto cs' msg $? y) as RW.
          
          cases (findKeysCrypto cs' msg $? y).
          * pose proof (message_contains_only_honest_public_keys_keys_honest _ H Heq); eauto.
          * eapply clean_key_permissions_adds_no_permissions; eauto.

          * cases ( clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y );
              cases ( findKeysCrypto cs' msg $? y );
              simplify_key_merges; eauto.
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
                  , honest_labeled_step_adv_cipher_queue_ok
                  , honest_labeled_step_adv_message_queue_ok
                  , honest_labeled_step_adv_no_honest_keys.
    Qed.

    Lemma silent_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B),
        step_universe U Silent U'
        -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers) U.(all_keys)
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      invert H;
        unfold adv_universe_ok in *;
        destruct U; [destruct userData | destruct adversary];
          unfold build_data_step in *; simpl in *;
            intuition idtac.

      eapply honest_silent_step_keys_good; eauto.
      eapply honest_silent_step_user_cipher_queues_ok; eauto.
      eapply honest_silent_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good; unfold keys_and_permissions_good in *; split_ands; eauto.
      eapply honest_silent_step_adv_cipher_queue_ok; eauto.
      eapply honest_silent_step_adv_message_queue_ok; eauto.
      eapply honest_silent_step_adv_no_honest_keys; eauto.
      eapply adv_step_keys_good; eauto.
      eapply adv_step_user_cipher_queues_ok; eauto.
      
      eapply adv_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good; unfold keys_and_permissions_good in *; split_ands; eauto.
      unfold keys_and_permissions_good in *; split_ands; eauto.
      
      eapply adv_step_adv_cipher_queue_ok; eauto.
      eapply adv_step_adv_message_queue_ok; eauto.
      eapply adv_step_adv_no_honest_keys; eauto.
    Qed.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto;
        match goal with [H : Action _ = _ |- _] => invert H end.
    Qed.

    Lemma honest_labeled_step_nochange_adversary_protocol :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
            -> adv.(protocol) = adv'.(protocol).
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
    Qed.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
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
        -> exists (u_id : user_id) u_d u_d' usrs' adv' cs' gks' ks' qmsgs' froms' tos' mycs' cmd',
            usrs $? u_id = Some u_d
          /\ step_user (Action a) (Some u_id) (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
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
                    ; from_ids := froms'
                    ; to_ids   := tos'
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
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                ->  clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs'') cs' suid froms qmsgs'
                /\ clean_users (findUserKeys usrs'') cs' usrs' = clean_users (findUserKeys usrs') cs' usrs'.
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

    (* Lemma honest_silent_step_nochange_clean_adv_messages : *)
    (*   forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
    (*             gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd', *)
    (*     step_user lbl suid bd bd' *)
    (*     -> suid = Some u_id *)
    (*     -> forall (cmd : user_cmd C), *)
    (*       bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd) *)
    (*       -> encrypted_ciphers_ok (findUserKeys usrs) cs gks *)
    (*       -> user_cipher_queues_ok cs (findUserKeys usrs) usrs *)
    (*       -> message_queues_ok cs usrs gks *)
    (*       -> keys_and_permissions_good  gks usrs adv.(key_heap) *)
    (*       -> adv_message_queue_ok (findUserKeys usrs) cs gks adv.(msg_heap) *)
    (*       -> lbl = Silent *)
    (*       -> forall cmd' usrs'', *)
    (*           bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd') *)
    (*           -> forall cmdc cmdc', *)
    (*             usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |} *)
    (*             -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}) *)
    (*             -> clean_messages (findUserKeys usrs'') cs' None adv'.(msg_heap) = clean_messages (findUserKeys usrs'') cs None adv'.(msg_heap). *)
    (* Proof. *)
    (*   induction 1; inversion 2; inversion 7; intros; try discriminate; subst; *)
    (*     autorewrite with find_user_keys; eauto; clean_context; *)
    (*       eauto using *)
    (*             clean_adv_messages_new_honest_key_idempotent *)
    (*           , clean_adv_messages_addnl_cipher_idempotent. *)
    (* Qed. *)

    Lemma honest_silent_step_nochange_clean_adv_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> adv_message_queue_ok (findUserKeys usrs) cs gks adv.(msg_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> clean_adv_msgs (findUserKeys usrs'') cs'  adv'.(msg_heap) = clean_adv_msgs (findUserKeys usrs'') cs  adv'.(msg_heap).
    Proof.
      induction 1; inversion 2; inversion 7; intros; try discriminate; subst;
        autorewrite with find_user_keys; eauto; clean_context;
          eauto using
                clean_adv_msgs_new_honest_key_idempotent
              , clean_adv_msgs_addnl_cipher_idempotent.
    Qed.


    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs froms tos cmd,
        universe_ok U
        -> adv_universe_ok U
        -> user_cipher_queues_ok U.(all_ciphers) (findUserKeys U.(users)) U.(users)
        -> U.(users) $? u_id = Some userData
        -> step_user Silent (Some u_id)
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
        -> universe_ok U'
        -> step_universe (strip_adversary_univ U b) Silent (strip_adversary_univ U' b)
        \/ strip_adversary_univ U b = strip_adversary_univ U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H1 as RW. clear HeqRW.

      unfold adv_universe_ok, universe_ok in *; split_ands; simpl in *.
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv in RW; eauto.

      split_ors.
      - destruct adversary; unfold strip_adversary_univ; simpl in *.
        left.
        eapply StepUser; simpl; eauto.
        + eapply clean_users_cleans_user; eauto.
        + unfold build_data_step; simpl.
          unfold clean_adv; simpl.
          exact H10.
        + unfold buildUniverse, clean_adv; simpl.
          f_equal.
          rewrite clean_users_add_pull; simpl.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          f_equal; f_equal.
          eapply honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs in H3; eauto; split_ands; eassumption.

          f_equal.
          eapply honest_silent_step_nochange_clean_adv_messages.
          exact H3.
          all: (reflexivity || eassumption).

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        inversion H10; subst.
        unfold clean_adv; simpl; f_equal.
        + rewrite clean_users_add_pull; simpl.
          assert (clean_users (findUserKeys users) all_ciphers users =
                  clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_ids := froms ; to_ids := tos |}))) cs usrs).
          unfold clean_users, map; apply map_eq_elements_eq; simpl; auto.
          rewrite <- H11.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          eapply clean_users_cleans_user; eauto.
          f_equal; eauto.
        + f_equal; eauto.
          rewrite H14.
          symmetry; eapply honest_silent_step_nochange_clean_adv_messages.
          exact H3.
          all : (reflexivity || eassumption).
    Qed.

    (* Lemma stripped_labeled_step_implies_advuniv_step_action_stripped : *)
    (*    forall {A B C} cs cs' u_id suid (usrs usrs' usrs__ra usrs__ra': honest_users A) (adv adv' adv__ra adv__ra': user_data B) *)
    (*      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd' a (b : B) *)
    (*      cs__ra gks__ra ks__ra qmsgs__ra cs__ra' gks__ra' ks__ra' qmsgs__ra' *)
    (*      lbl, *)
    (*     step_user lbl suid bd bd' *)
    (*     -> suid = Some u_id *)
    (*     -> lbl = Action a *)
    (*     -> forall (cmd : user_cmd C) honestk, *)
    (*         honestk = findUserKeys usrs *)
    (*         -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd) *)
    (*         -> usrs = clean_users honestk cs usrs__ra *)
    (*         -> adv = clean_adv adv__ra honestk cs b *)
    (*         -> cs = clean_ciphers honestk cs__ra *)
    (*         -> gks = clean_keys honestk gks__ra *)
    (*         -> ks = clean_key_permissions honestk ks__ra *)
    (*         -> qmsgs = clean_messages honestk cs suid froms qmsgs__ra *)
    (*         -> forall cmd' bd__ra' a__ra, *)
    (*             bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd') *)
    (*             -> bd__ra' = (usrs__ra', adv__ra', cs__ra', gks__ra', ks__ra', qmsgs__ra', mycs', froms', tos', cmd') *)
    (*             -> step_user (Action a__ra) suid (usrs__ra, adv__ra, cs__ra, gks__ra, ks__ra, qmsgs__ra, mycs, froms, tos, cmd) bd__ra' *)
    (*             -> a = strip_action honestk cs__ra a__ra. *)
    (* Proof. *)
    (*   induction 1; inversion 4; inversion 7; intros; try discriminate; subst; *)
    (*     match goal with *)
    (*     | [ H : step_user (Action ?ara) _ _ _ |- _ = strip_action _ _ ?ara ] => invert H *)
    (*     end; clean_context; try reflexivity; eauto. *)

    (*   rewrite H10 in H2. *)
    (*   apply clean_users_cleans_user_inv in H2; split_ex. *)
    (*   rewrite H33 in H. *)
    (*   destruct rec_u0; destruct rec_u; invert H; simpl in *. *)
    (*   invert H2; split_ands; subst. *)
    (*   f_equal. *)
      
    (* Admitted. *)

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        -> step_universe U (Action act) U'
        -> step_universe (strip_adversary_univ U b)
                        (Action (strip_action (findUserKeys U.(users)) U.(all_ciphers) act))
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
        remember (x2 $+ (x, {| key_heap := x6
                             ; protocol := x11
                             ; msg_heap := x7
                             ; from_ids := x8
                             ; to_ids := x9
                             ; c_heap := x10 |})) as usrs''.

        assert (clean_ciphers (findUserKeys usrs'') x4 = clean_ciphers (findUserKeys x2) x4
              /\ clean_messages (findUserKeys usrs'') x4 (Some x) x8 x7 = clean_messages (findUserKeys x2) x4 (Some x) x8 x7
              /\ clean_users (findUserKeys usrs'') x4 usrs'' =
                clean_users (findUserKeys x2) x4 x2 $+ (x, {| key_heap := clean_key_permissions (findUserKeys x2) x6
                                                         ; protocol := x11
                                                         ; msg_heap := clean_messages (findUserKeys x2) x4 (Some x) x8 x7
                                                         ; from_ids := x8
                                                         ; to_ids := x9
                                                         ; c_heap := x10 |})
              /\ clean_adv x3 (findUserKeys usrs'') x4 b = clean_adv x3 (findUserKeys users) x4 b
              /\ clean_keys (findUserKeys usrs'') x5 = clean_keys (findUserKeys x2) x5 ).
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.
        split_ands.

        f_equal; auto.
    Qed.

    Hint Resolve dishonest_cipher_cleaned.

    Lemma  adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' froms' tos' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_ids), adv.(to_ids), cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> cs__s = clean_ciphers honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.
    Qed.

    Lemma clean_keys_drops_added_dishonest_key :
      forall honestk gks k_id ku kt,
        honestk $? k_id = None
        -> clean_keys honestk (gks $+ (k_id, {| keyId := k_id; keyUsage := ku; keyType := kt |}))
          = clean_keys honestk gks.
    Proof.
      intros; unfold clean_keys, filter; apply map_eq_Equal; unfold Equal; intros.
                   
    Lemma adv_step_implies_no_new_keys_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' froms' tos' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk gks__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_ids), adv.(to_ids), cmd)
          -> honestk = findUserKeys usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)

          -> gks__s = clean_keys honestk gks
          -> forall cmd' honestk' gks__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> honestk' = findUserKeys usrs'
              -> gks__s' = clean_keys honestk' gks'
              -> gks__s = gks__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        autorewrite with find_user_keys; eauto; clean_context.


      unfold keys_and_permissions_good in *; split_ands.
      assert (permission_heap_good gks (findUserKeys usrs')) as PHG by eauto.
      unfold permission_heap_good in PHG.
      cases (findUserKeys usrs' $? k_id).
      specialize (PHG _ _ Heq); split_ex; contra_map_lookup.
      rewrite clean_keys_drops_dishonest_key; eauto.

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
          -> message_queues_ok cs usrs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> adv_cipher_queue_ok cs adv.(c_heap)
          -> usrs__s = clean_users honestk cs usrs
          -> forall cmd' honestk' usrs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 7; intros; subst; eauto;
        autorewrite with find_user_keys;
        clean_context.

      (* Send *)
      - rewrite clean_users_add_pull; simpl.
        apply map_eq_Equal; unfold Equal; intros.
        cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.

        erewrite clean_users_cleans_user; eauto; f_equal.
        cases (msg_filter (findUserKeys usrs) cs' (Some rec_u_id) (existT crypto t0 msg));
          eauto using clean_messages_drops_msg_filter_false.
        unfold msg_filter in *; rewrite andb_true_iff in *; split_ands.

        exfalso.
        unfold msg_honestly_signed, msg_to_this_user in *; destruct msg; try discriminate;
          simpl in *.

        unfold adv_cipher_queue_ok in H19; rewrite Forall_forall in H19;
          assert (exists c : cipher, cs' $? c_id = Some c) by eauto;
          split_ex;
          context_map_rewrites.

        encrypted_ciphers_prop; simpl in *.
        (* both of these cases are the adversary sending honestly signed messages 
         * 
         * messages have intended recipient
         * increasing identifier for each of those pairs
         *) 
        + admit.
        + admit.
        
      - erewrite clean_users_addnl_cipher_idempotent; eauto.
      - erewrite clean_users_addnl_cipher_idempotent; eauto.

    Admitted.

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : simpl_universe A -> IdealWorld.universe A -> Prop)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
        -> R (strip_adversary U__r) U__i

        -> keys_and_permissions_good U__r.(all_keys) U__r.(users) U__r.(adversary).(key_heap)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))

        -> message_queues_ok U__r.(all_ciphers) U__r.(users) U__r.(all_keys)
        -> encrypted_ciphers_ok (findUserKeys (users U__r)) U__r.(all_ciphers) U__r.(all_keys)
        -> adv_cipher_queue_ok U__r.(all_ciphers) U__r.(adversary).(c_heap)

                             
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

    Lemma encrypted_ciphers_ok_new_honest_cipher_adv_univ :
      forall honestk cs cs' c_id c k gks,
        ~ In c_id cs
        -> cs' = cs $+ (c_id,c)
        -> cipher_signing_key c = k
        -> honest_key honestk k
        -> encrypted_ciphers_ok honestk cs gks
        -> encrypted_ciphers_ok honestk (clean_ciphers honestk cs') gks
        -> encrypted_ciphers_ok honestk cs' gks.
    Proof.
      intros; subst.
      rewrite clean_ciphers_keeps_added_honest_cipher in H4; simpl; eauto.
      eapply Forall_natmap_split in H4; split_ands; eauto.
      econstructor; eauto.
      invert H1; solve [ econstructor; eauto ].
    Qed.

    Hint Resolve encrypted_ciphers_ok_new_honest_cipher_adv_univ.

    Lemma encrypted_ciphers_ok_new_honest_key_adv_univ :
      forall honestk honestk' cs k_id k gks gks',
        ~ In k_id gks
        -> permission_heap_good gks honestk
        -> k_id = keyId k
        -> gks' = gks $+ (k_id, k)
        -> honestk' = honestk $+ (k_id, true)
        -> encrypted_ciphers_ok honestk cs gks
        -> encrypted_ciphers_ok honestk' (clean_ciphers honestk' cs) gks'
        -> encrypted_ciphers_ok honestk' cs gks'.
    Proof.
      intros; subst; eapply encrypted_ciphers_ok_addnl_honest_key; eauto.
      cases (honestk $? keyId k); clean_map_lookups; eauto.
      specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
    Qed.

    Hint Resolve encrypted_ciphers_ok_new_honest_key_adv_univ.
    Hint Resolve users_permission_heaps_good_merged_permission_heaps_good.

    Lemma honest_silent_step_adv_univ_enc_ciphers_ok' :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc' honestk',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> encrypted_ciphers_ok honestk' (clean_ciphers honestk' cs') gks'
                -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 5; intros; subst;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        keys_and_permissions_prop;
        eauto;
        clean_context.

      - user_cipher_queues_prop.
        encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
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
                b gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' tos tos' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cmd')
              -> forall cmdc cmdc' honestk' U__r U__r',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |})
                -> honestk' = findUserKeys usrs''
                -> U__r = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_ids := froms ; to_ids := tos |}
                -> U__r' = buildUniverse usrs' adv' cs' gks' u_id {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_ids := froms' ; to_ids := tos' |}
                -> strip_adversary_univ U__r b = strip_adversary_univ U__r' b
                -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 5; unfold strip_adversary; intros; subst; simpl in *;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        eauto; clean_context.

      - exfalso; invert H36.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H9; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H9; eauto.

      - invert H36.
        user_cipher_queues_prop.
        encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.

      - exfalso; invert H33.
        erewrite clean_ciphers_added_honest_cipher_not_cleaned in H6; eauto.
        2: simpl; econstructor; rewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        rewrite !findUserKeys_readd_user_same_keys_idempotent' in H6; eauto.

      - eapply encrypted_ciphers_ok_addnl_honest_key; eauto; simpl; new_key_not_in_honestk.
      - eapply encrypted_ciphers_ok_addnl_honest_key; eauto; simpl; new_key_not_in_honestk.

    Qed.

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) (U__i : IdealWorld.universe A) (R : simpl_universe A -> IdealWorld.universe A -> Prop) lbl (b:B),
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

      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H2 H6 H12 H13 HeqU__ra' H11); split_ors.

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
        assert (clean_users (RealWorld.findUserKeys users) all_ciphers users = clean_users (RealWorld.findUserKeys users0) all_ciphers0 users0)
          as CLEAN_USERS by (unfold clean_users, mapi; auto).
        rewrite <- CLEAN_USERS; auto.

    (* Adversary step *)
    - exists U__i; intuition auto.
      eapply adv_step_stays_in_R; eauto.

  Qed.

  (* Lemma stripped_action_matches_then_action_matches : *)
  (*   forall  {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r a__i honestk, *)
  (*     action_matches (strip_action honestk a__r) U__ra a__i U__i *)
  (*     -> action_matches a__r U__ra a__i U__i. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold strip_action in H. *)
  (*   invert H. destruct a__r; try discriminate. *)
  (*   invert H2; econstructor; eauto. *)
  (*   invert H2. *)
  (*   eapply Out; eauto. *)
  (* Qed. *)

  (* Hint Resolve stripped_action_matches_then_action_matches. *)

  Lemma action_matches_strip :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r a__i b,
      action_matches a__r (strip_adversary_univ U__ra b) a__i U__i
      -> action_matches a__r U__ra a__i U__i.
  Proof.
  Admitted.

  Hint Resolve action_matches_strip.

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
            /\ action_matches a__r U__ra a__i U__i'
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
    in  (forall u_id u,
            U.(RealWorld.users) $? u_id = Some u
            -> Forall (fun m => msg_filter honestk U.(RealWorld.all_ciphers) (Some u_id) m = true) u.(RealWorld.msg_heap)
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
        (* Forall_natmap (fun u => Forall (fun m => msg_filter honestk U.(RealWorld.all_ciphers) m = true) u.(RealWorld.msg_heap) *)
        (*                   /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true)) U.(RealWorld.users) *)
      /\ Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) U.(RealWorld.all_ciphers)
      /\ Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) U.(RealWorld.all_keys)
  .

  Lemma clean_honest_messages_idempotent :
    forall cs msgs honestk suid,
      Forall (fun m => msg_filter honestk cs suid m = true) msgs
      -> clean_messages honestk cs suid msgs = msgs.
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
    forall {A} (usrs : RealWorld.honest_users A) honestk cs,
      honestk = RealWorld.findUserKeys usrs
      -> (forall u_id u,
            usrs $? u_id = Some u
            -> Forall (fun m => msg_filter honestk cs (Some u_id) m = true) u.(RealWorld.msg_heap)
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
      -> clean_users honestk cs usrs = usrs.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal, clean_users; intros; rewrite mapi_o; intros; subst; trivial.
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
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : B),
      simulates (lameAdv b) R U__r U__i
      -> lameAdv b U__r.(RealWorld.adversary)
      -> universe_starts_ok U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__ra advcode R',
          U__ra = add_adversary U__r advcode
          -> R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
          -> simulates (@awesomeAdv B) R' U__ra U__i.
    intros.
    (* inversion H as [R SIM]. *)
    inversion H as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__univok H__o]; clear H__s.
    inversion H__o as [H__advsafe H__o']; clear H__o.
    inversion H__o' as [R__start OK__start]; clear H__o'.

    (* unfold refines. *)
    
    (* exists (fun ur ui => R (strip_adversary_simpl ur) ui); unfold simulates. *)

    unfold simulates; rewrite H5.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, simulates_universe_ok, simulates_labeled_step_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.

    - eapply H__univok; eauto.
      rewrite <- strip_adv_simpl_strip_adv_idempotent; eassumption.

    - eapply  H__advsafe; eauto.
      rewrite <- strip_adv_simpl_strip_adv_idempotent; eassumption.
  Qed.

  Theorem simulates_ok_with_adversary' :
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
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, simulates_universe_ok, simulates_labeled_step_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.

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

Hint Constructors rCouldGenerate iCouldGenerate.

Lemma ideal_multi_silent_stays_could_generate :
  forall {A} (U__i U__i' : IdealWorld.universe A),
      istepSilent ^* U__i U__i'
      -> forall acts__i,
        iCouldGenerate U__i' acts__i
      -> iCouldGenerate U__i acts__i.
Proof.
  induction 1; intros; eauto.
Qed.

Hint Resolve ideal_multi_silent_stays_could_generate.

Inductive traceMatches : list RealWorld.action -> list IdealWorld.action -> Prop :=
| TrMatchesNothing :
    traceMatches [] []
| TrMatchesLabel : forall {A B}(U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r acts__r a__i acts__i,
      rCouldGenerate U__r (a__r :: acts__r)
    -> iCouldGenerate U__i (a__i :: acts__i)
    -> traceMatches acts__r acts__i
    -> action_matches a__r U__r a__i U__i
    -> traceMatches (a__r :: acts__r) (a__i :: acts__i)
.

Hint Constructors traceMatches.
Hint Resolve
     silent_step_adv_univ_implies_adv_universe_ok
     silent_step_advuniv_implies_univ_ok
     honest_labeled_step_univ_ok
     labeled_step_adv_univ_implies_adv_universe_ok.


Lemma strip_adversary_same_as_peel_strip_simpl :
  forall {A B} (U : RealWorld.universe A B) b,
    strip_adversary U = RealWorld.peel_adv (strip_adversary_univ U b).
Proof.
  unfold strip_adversary, strip_adversary_simpl, RealWorld.peel_adv; intros.
  trivial.
Qed.

Lemma simulation_relation_multi_stripped :
  forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A)
          (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) R',

    R' = (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui)
    -> R (strip_adversary_simpl (RealWorld.peel_adv U__r)) U__i
    -> R' (strip_adversary U__r) U__i.
Proof.
  intros; subst.
  rewrite strip_adv_simpl_strip_adv_idempotent.
  rewrite strip_adv_simpl_peel_same_as_strip_adv in H0.
  assumption.
Qed.

Lemma simulates_could_generate :
  forall A B (R R' : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b:B),
    R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
    -> simulates_silent_step (awesomeAdv (B:=B)) R'
    -> simulates_labeled_step (awesomeAdv (B:=B)) R'
    -> simulates_universe_ok R'
    -> simulates_labeled_step_safe R'
    -> forall (U__r : RealWorld.universe A B) acts__r,
        universe_ok U__r
        -> adv_universe_ok U__r
        -> rCouldGenerate U__r acts__r
        -> forall U__i,
            R' (RealWorld.peel_adv U__r) U__i
            -> exists acts__i,
                iCouldGenerate U__i acts__i
              /\ traceMatches acts__r acts__i.
Proof.
  induction 9; intros; subst; intuition eauto;
    assert (awesomeAdv (RealWorld.adversary U)) as AWE by (unfold awesomeAdv; trivial).

  - generalize (H0 _ _ H8 H4 H5 AWE _ H6); intro STEPPED;
      destruct STEPPED as [U__i' STEPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H9.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H9.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.
    assert (R' (RealWorld.peel_adv U') U__i') as INR' by (subst; eauto).
    assert (universe_ok U') as UOK.
    eapply silent_step_advuniv_implies_univ_ok with (R0:=R') (b0:=b) (U__i0 := U__i); eauto.
    subst.
    rewrite strip_adv_simpl_peel_same_as_strip_adv in H8.
    rewrite <- strip_adversary_same_as_peel_strip_simpl, strip_adv_simpl_strip_adv_idempotent; eauto.
    
    assert (adv_universe_ok U') as AUOK by eauto.
    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 H3 UOK AUOK _ INR'); split_ex; split_ands.

    eapply ideal_multi_silent_stays_could_generate with (acts__i:=x) in H; eauto.

  - generalize (H1 _ _ H8 H4 H5 AWE _ _ H6); intro STEPPED;
      destruct STEPPED as [a__i STEPPED];
      destruct STEPPED as [U__i' STEPPED];
      destruct STEPPED as [U__i'' STEPPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H11.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H11.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.

    assert (R' (RealWorld.peel_adv U') U__i'') as INR' by (subst; eauto).

    assert (universe_ok U') as UOK.
    eapply honest_labeled_step_univ_ok; unfold adv_universe_ok, simulates_labeled_step_safe in *;
      split_ands; eauto.

    eapply H3 with (U__i := U__i); eauto.
    eapply simulation_relation_multi_stripped; eauto.

    assert (adv_universe_ok U') as AUOK.
    eapply labeled_step_adv_univ_implies_adv_universe_ok; eauto.
    eapply H3 with (U__i := U__i); eauto.
    eapply simulation_relation_multi_stripped; eauto.

    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 H3 UOK AUOK _ INR'); split_ex; split_ands.

    exists (a__i :: x); split; eauto using ideal_multi_silent_stays_could_generate.
Qed.

Theorem refines_could_generate :
  forall A B (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : B),
    U__r <| U__i \ lameAdv b
    -> lameAdv b U__r.(RealWorld.adversary)
    -> universe_starts_ok U__r
    -> forall U__ra advcode acts__r,
      U__ra = add_adversary U__r advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate U__i acts__i
        /\ traceMatches acts__r acts__i.
Proof.
  intros.
  unfold refines in H; destruct H as [R H].

  assert (simulates (lameAdv b) R U__r U__i) as SIM by assumption;
    unfold simulates in SIM; split_ands.
  assert (simulates (lameAdv b) R U__r U__i) as SIM by assumption;
    eapply simulates_ok_with_adversary in SIM; eauto.
  2: reflexivity.

  unfold simulates in SIM; split_ands.
  eapply simulates_could_generate
    with (R := R)
         (B := B)
         (U__r := U__ra)
         (R' := (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui)); auto.
  Qed.

