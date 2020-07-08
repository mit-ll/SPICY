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
.

Require Import
        MyPrelude
        Maps
        Common
        Keys
        KeysTheory
        Tactics
        Messages
        MessageEq
        Automation
        Simulation
        AdversaryUniverse
        CipherTheory
        UsersTheory
.

Set Implicit Arguments.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Module SafetyAutomation.

  Import RealWorld.

  Ltac dismiss_adv :=
    repeat
      match goal with
      | [ LAME : lameAdv _ (adversary ?ru), STEP : step_user _ None _ _ |- _ ] =>
        destruct ru; unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
      | [ LAME : lameAdv _ _, STEP : step_user _ None _ _ |- _ ] =>
        unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
      | [ ADVP : protocol ?adv = Return _, STEP : step_user _ None (_,_,_,_,_,_,_,_,_,_,protocol ?adv) _ |- _ ] =>
        rewrite ADVP in STEP; invert STEP
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
    repeat solve_simple_maps1;
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
      assert (exists cmd mycs ks froms sents cur_n,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_nons := froms
                                     ; sent_nons := sents
                                     ; cur_nonce := cur_n |})
        as TAG by (unfold user_queue in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists t v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.

  Ltac user_cipher_queue_lkup TAG :=
    match goal with
    | [ H : user_cipher_queue ?usrs ?uid = Some ?mycs |- _ ] =>
      assert (exists cmd qmsgs ks froms sents cur_n,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_nons := froms
                                     ; sent_nons := sents
                                     ; cur_nonce := cur_n |})
        as TAG by (unfold user_cipher_queue in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists t v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
                   end)
    end.

  Ltac user_keys_lkup TAG :=
    match goal with
    | [ H : user_keys ?usrs ?uid = Some ?ks |- _ ] =>
      assert (exists cmd mycs qmsgs froms sents cur_n,
                 usrs $? uid = Some {| key_heap := ks
                                     ; msg_heap := qmsgs
                                     ; protocol := cmd
                                     ; c_heap := mycs
                                     ; from_nons := froms
                                     ; sent_nons := sents
                                     ; cur_nonce := cur_n |})
        as TAG by (unfold user_keys in H;
                   cases (usrs $? uid); try discriminate;
                   match goal with
                   | [ H1 : Some _ = Some _ |- exists t v w x y z, Some ?u = _ ] => invert H1; destruct u; repeat eexists; reflexivity
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
        , MAP :  msg_accepted_by_pattern ?cs _ _ _ ?msg |- _ ] =>
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
               do 6 (destruct USR as [?x USR]);
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

  Lemma honest_keyb_true_honestk_has_key :
    forall honestk k,
      honest_keyb honestk k = true -> honestk $? k = Some true.
  Proof. intros * H; rewrite <- honest_key_honest_keyb in H; destruct H; assumption. Qed.

  Ltac user_cipher_queues_prop :=
    match goal with
    | [ OK : user_cipher_queues_ok ?cs ?honk ?us |- _ ] => 
      match goal with
      | [ H : us $? _ = Some ?u |- _ ] =>
        prop_not_unifies (user_cipher_queue_ok cs honk (c_heap u));
        generalize (Forall_natmap_in_prop _ OK H); simpl; intros
      | _ => let USR := fresh "USR"
            in user_cipher_queue_lkup USR;
            do 6 (destruct USR as [?x USR]);
               generalize (Forall_natmap_in_prop _ OK USR); simpl; intros
      end
    end;
    repeat match goal with
           | [ H : user_cipher_queue_ok _ _ ?mycs, H1 : List.In _ ?mycs |- _ ] =>
             unfold user_cipher_queue_ok in H;
             rewrite Forall_forall in H;
             specialize (H _ H1);
             split_ex; split_ands; clean_map_lookups
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_honestk_has_key in H
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
               do 6 (destruct USR as [?x USR]);
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
           | [ H : honest_keyb _ _ = true |- _] => apply honest_keyb_true_honestk_has_key in H
           end; try contradiction.

  Ltac refine_signed_messages :=
    repeat
      match goal with
      | [ H1 : msg_pattern_safe ?honk _ ,
          H2 : msg_accepted_by_pattern _ _ _ _ ?msg,
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

  Hint Extern 1 (_ $+ (?k, _) $? _ = Some _) => progress (clean_map_lookups; trivial).
  Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
  Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

  Hint Extern 1 (honest_key_filter_fn _ _ _ = _) => unfold honest_key_filter_fn; context_map_rewrites.
  Hint Extern 1 (honest_perm_filter_fn _ _ _ = _) => unfold honest_perm_filter_fn; context_map_rewrites.

  Hint Extern 1 (user_cipher_queue _ _ = _) => unfold user_cipher_queue; context_map_rewrites.
  Hint Extern 1 (user_keys _ _ = Some _ ) => unfold user_keys; context_map_rewrites.

End SafetyAutomation.
