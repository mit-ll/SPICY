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
     Program.Equality (* for dependent induction *)
.

From Coq Require Classical_Prop.

Require Import
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
        CipherTheory
        KeysTheory
        MessagesTheory
        UsersTheory
        InvariantsTheory
.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Module Automation.

  Import RealWorld.

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

  Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd (Base B)) :=
    {| users       := U__r.(users)
     ; adversary   := {| key_heap := U__r.(adversary).(key_heap)
                       ; msg_heap := U__r.(adversary).(msg_heap)
                       ; protocol := advcode
                       ; c_heap   := U__r.(adversary).(c_heap)
                       ; from_nons := U__r.(adversary).(from_nons)
                       ; sent_nons := U__r.(adversary).(sent_nons)
                       ; cur_nonce := U__r.(adversary).(cur_nonce) |}
     ; all_ciphers := U__r.(all_ciphers)
     ; all_keys    := U__r.(all_keys)
    |}.

  Lemma adv_no_honest_keys_after_honestk_no_private_key_msg :
    forall {t} (msg : crypto t) honestk cs advk,
      adv_no_honest_keys honestk advk
      -> (forall (k_id : NatMap.Map.key) (kp : bool), findKeysCrypto cs msg $? k_id = Some kp -> kp = false)
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
        subst; solve_perm_merges; auto.
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
    forall {A t} (usrs : honest_users A) gks (msg : message t) u_id u_d ks cmd qmsgs mycs froms sents cur_n adv_heap,
      keys_and_permissions_good gks usrs adv_heap
      -> (forall (k : NatMap.Map.key) (kp : bool), findKeysMessage msg $? k = Some kp -> gks $? k <> None)
      -> u_d = {| key_heap := ks $k++ findKeysMessage msg
               ; msg_heap := qmsgs
               ; protocol := cmd
               ; c_heap   := mycs
               ; from_nons := froms
               ; sent_nons := sents
               ; cur_nonce := cur_n |}
      -> user_keys usrs u_id = Some ks
      -> keys_and_permissions_good gks (usrs $+ (u_id,u_d)) adv_heap.
  Proof.
    intros.
    unfold keys_and_permissions_good in *; intuition idtac.
    econstructor; eauto; subst; simpl.

    permission_heaps_prop.
    unfold permission_heap_good; intros.
    cases (ks $? k_id); cases (findKeysMessage msg $? k_id); solve_perm_merges; eauto.
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
          |- permission_heap_good _ ?ks ] => generalize (Forall_natmap_in_prop _ OK USR); intros; clear USR
      | [ H : permission_heap_good _ _ |- _ ] => unfold permission_heap_good in H
      | [ |- permission_heap_good _ _ ] => unfold permission_heap_good; intros; simpl in *
      | [ H : ?m1 $k++ ?m2 $? ?kid = _ |- _ ] => cases (m1 $? kid); cases (m2 $? kid); solve_perm_merges; clean_context
      | [ H : keys_mine _ ?othr_kys, KS : ?othr_kys $? _ = Some _ |- _ ] => specialize (H _ _ KS); split_ors; split_ands
      | [ H : (forall k kp, findKeysMessage ?msg $? k = Some kp -> _ ), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
        specialize (H _ _ ARG); split_ands; subst
      | [ H : (forall k_id kp, ?perms $? k_id = Some kp -> _), ARG : ?perms $? ?k = Some _ |- _ $? ?k <> None ] =>
        specialize (H _ _ ARG); split_ex
      end.

  Lemma honest_labeled_step_keys_and_permissions_good :
    forall {A B C} suid u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> message_queues_ok cs usrs gks
            -> forall usrs'' cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs'
                                            ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}) 
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
    forall {A} (usrs : honest_users A) adv_heap gks ks cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' u_id,
      keys_and_permissions_good gks usrs adv_heap
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> keys_and_permissions_good gks (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs'
                                                         ; from_nons := froms'; sent_nons := sents' ; cur_nonce := cur_n' |})) adv_heap.
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
    forall {A} (usrs : honest_users A) gks k_id k ks u_id cmd cmd' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' adv_heap,
      gks $? k_id = None
      -> keys_and_permissions_good gks usrs adv_heap
      -> k_id = keyId k
      -> usrs $? u_id = Some {| key_heap := ks ; protocol := cmd ; msg_heap := qmsgs ; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> keys_and_permissions_good (gks $+ (k_id,k))
                                  (usrs $+ (u_id,
                                            {| key_heap := add_key_perm k_id true ks
                                             ; protocol := cmd'
                                             ; msg_heap := qmsgs'
                                             ; c_heap   := mycs'
                                             ; from_nons := froms'
                                             ; sent_nons := sents'
                                             ; cur_nonce := cur_n' |}))
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> keys_and_permissions_good gks'
                                              (usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}))
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> ks = adv.(key_heap)
        -> adv_message_queue_ok usrs cs gks qmsgs
        -> adv_cipher_queue_ok cs usrs mycs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> keys_and_permissions_good gks usrs ks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> keys_and_permissions_good gks' usrs' ks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst; try discriminate;
      eauto; clean_context.

    - unfold keys_and_permissions_good in *; intuition eauto.
      unfold permission_heap_good in *; intros.
      cases (key_heap adv' $? k_id); eauto.
      invert H20; split_ands.
      cases (findKeysCrypto cs' msg $? k_id); solve_perm_merges.
      specialize (H4 _ _ H9); split_ands; subst.
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
        specialize (H9 _ _ H20); eauto.

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
    forall honestk gks uks,
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
    forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs froms froms' sents sents' cur_n cur_n',
      usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok cs
          (findUserKeys usrs)
          (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})).
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
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms sents cur_n,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (add_key_perm k_id true (findUserKeys usrs))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |})).
  Proof.
    intros.
    unfold user_cipher_queues_ok; rewrite Forall_natmap_forall; intros.
    user_cipher_queue_lkup UCQ.

    split_ex; destruct (k ==n u_id); subst; clean_map_lookups; simpl.
    user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
    clear H2; user_cipher_queues_prop; eauto using user_cipher_queue_ok_addnl_generated_key.
  Qed.

  Lemma user_cipher_queues_ok_addnl_generated_key' :
    forall {A} (usrs : honest_users A) ks cs k_id u_id cmd qmsgs mycs froms sents cur_n,
        user_cipher_queue usrs u_id = Some mycs
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> user_cipher_queues_ok
          cs
          (findUserKeys usrs $+ (k_id,true))
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |})).
  Proof.
    intros.
    pose proof (user_cipher_queues_ok_addnl_generated_key ks k_id _ cmd qmsgs froms sents cur_n H H0).
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
        | [ H : honest_keyb _ _ = true |- _ ] => apply honest_keyb_true_honestk_has_key in H2
        | [ |- Forall _ _ ] => econstructor
        | [ |- exists _, _ /\ _ ] => eexists; split
        | [ |- cipher_honestly_signed _ _ = _ ] => simpl; unfold honest_keyb; solve_perm_merges
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
    forall {A t} (usrs usrs' : honest_users A) (msg : crypto t) honestk u_id ks cmd cmd' qmsgs qmsgs' mycs froms froms' sents sents' cur_n cur_n' cs,
      user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> msgCiphersSignedOk (findUserKeys usrs) cs msg
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ findKeysCrypto cs msg; protocol := cmd'; msg_heap := qmsgs'
                                  ; c_heap := findCiphers msg ++ mycs ; from_nons := froms'; sent_nons := sents' ; cur_nonce := cur_n' |})
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
    forall {A} (usrs : honest_users A) msgk u_id ks qmsgs cmd mycs froms sents cur_n,
      keys_mine ks msgk
      -> usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
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
    solve_perm_merges;
      try match goal with
          | [ H : (forall kid kp, ?ks2 $? kid = Some kp -> _), H1 : ?ks2 $? _ = Some _ |- _ ] =>
            specialize (H _ _ H1); split_ors; split_ands; subst; clean_map_lookups
          end; solve_perm_merges; eauto.
  Qed.

  Lemma honest_labeled_step_user_cipher_queues_ok :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a suid,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> user_cipher_queues_ok cs honestk usrs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
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
    cases (pubk $? k); solve_perm_merges; intuition eauto.
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
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true)
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

  Lemma message_queue_ok_adding_public_keys' :
    forall msgs cs honestk pubk ks,
      message_queue_ok honestk cs msgs ks
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> message_queue_ok (honestk $k++ pubk) cs msgs ks.
  Proof.
    intros; eapply message_queue_ok_adding_public_keys; eauto.
  Qed.

  Hint Resolve message_queue_ok_adding_public_keys message_queue_ok_adding_public_keys'.

  Lemma message_queues_ok_user_adding_public_keys :
    forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs mycs mycs' froms froms' sents sents' cur_n cur_n',
      message_queues_ok cs usrs gks
      -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := msg::msgs
                             ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ pubk; protocol := cmd'; msg_heap := msgs
                                ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
      -> message_queues_ok cs usrs' gks.
  Proof.
    intros; subst.
    unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros.
    destruct (u_id ==n k); subst; clean_map_lookups; autorewrite with find_user_keys; eauto; simpl.
    eapply message_queue_ok_adding_public_keys; eauto.
    specialize (H _ _ H1); invert H; eauto.
  Qed.

  Lemma message_queues_ok_user_adding_public_keys' :
    forall {A} (usrs usrs' : honest_users A) cs gks u_id pubk ks cmd cmd' msg msgs mycs mycs' froms froms' sents sents' cur_n cur_n',
      message_queues_ok cs usrs gks
      -> (forall k p, pubk $? k = Some p -> (findUserKeys usrs) $? k = Some true /\ p = false)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := msg::msgs
                             ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> usrs' = usrs $+ (u_id, {| key_heap := ks $k++ pubk; protocol := cmd'; msg_heap := msgs
                                ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
      -> message_queues_ok cs usrs' gks.
  Proof.
    intros; subst.
    eapply message_queues_ok_user_adding_public_keys; eauto.
  Qed.

  Hint Resolve message_queues_ok_user_adding_public_keys message_queues_ok_user_adding_public_keys'.

  Lemma message_queues_ok_readd_user_same_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' sents sents' cur_n cur_n' gks,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                             ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})) gks.
  Proof.
    intros; unfold message_queues_ok; intros.
    econstructor; autorewrite with find_user_keys; eauto; simpl.
    msg_queue_prop; eauto.
  Qed.

  Hint Resolve message_queues_ok_readd_user_same_queue.

  Lemma message_queues_ok_readd_user_popped_queue :
    forall {A} (usrs : honest_users A) cs u_id ks cmd cmd' qmsgs mycs mycs' froms froms' sents sents' cur_n cur_n' gks qmsg,
      message_queues_ok cs usrs gks
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsg :: qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})) gks.
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
      split; intros; repeat invert_base_equalities1; eauto.
      invert H4; clean_map_lookups; specialize_msg_ok; eauto.
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
    forall {A} (usrs : honest_users A) cs u_id k_id gks ks cmd cmd' qmsgs mycs froms sents cur_n usage kt,
      message_queues_ok cs usrs gks
      -> ~ In k_id gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> permission_heap_good gks (findUserKeys usrs)
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
      -> message_queues_ok cs
                          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks; protocol := cmd'; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}))
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
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
    - specialize (H0 _ _ H16);
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
        end; solve_perm_merges; intuition eauto.
  Qed.

  Lemma honest_silent_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> permission_heap_good gks honestk
        -> message_queues_ok cs usrs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
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

  Lemma adv_cipher_queue_ok_read_msg :
    forall {A} (usrs : honest_users A) cs {t} (msg : crypto t) gks qmsgs advcs,
      adv_message_queue_ok usrs cs gks (existT _ _ msg :: qmsgs)
      -> adv_cipher_queue_ok cs usrs advcs
      -> adv_cipher_queue_ok cs usrs (findCiphers msg ++ advcs).
  Proof.
    unfold adv_cipher_queue_ok; intros;
      rewrite Forall_forall in *; intros.

    destruct msg; simpl in *; eauto.
    split_ors; subst; eauto.
    clear H0.
    unfold adv_message_queue_ok in H.
    invert H; split_ands; simpl in *.
    assert (cs $? x <> None) by eauto; cases (cs $? x); try contradiction.
    assert (x = x \/ False) as ARG by (left; trivial).
    specialize (H2 _ ARG); split_ex; split_ands; clear ARG; clean_map_lookups.
    eexists; split; eauto.
  Qed.

  Lemma adv_cipher_queue_ok_readd_user_same_mycs_froms_msgs :
    forall {A} (usrs : honest_users A) cs u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n cur_n',
      adv_cipher_queue_ok cs usrs adv_mycs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> adv_cipher_queue_ok cs
                            (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs
                                               ; c_heap := mycs; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n' |})) adv_mycs.
  Proof.
    unfold adv_cipher_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H _ H1); split_ex; split_ands.
    eexists; split; eauto.
    autorewrite with find_user_keys; split_ors; eauto.

    right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0); subst; clean_map_lookups; simpl in *; eauto 10.
  Qed.

  Lemma msg_to_this_user_addnl_cipher :
    forall {t} (msg : crypto t) cs suid c_id c,
      ~ In c_id cs
      -> msg_to_this_user cs suid msg = true
      -> msg_to_this_user (cs $+ (c_id,c)) suid msg = true.
  Proof.
    unfold msg_to_this_user, msg_destination_user; intros.
    destruct msg; try discriminate.
    solve_simple_maps; eauto.
  Qed.

  Hint Resolve
       msg_honestly_signed_addnl_cipher
       msg_to_this_user_addnl_cipher.

  Lemma adv_cipher_queue_ok_msg_send :
    forall {A t} (usrs : honest_users A) (msg : crypto t) cs u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n cur_n',
      adv_cipher_queue_ok cs usrs adv_mycs
      -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                               ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
      -> adv_cipher_queue_ok cs
                            (usrs $+ (u_id, {| key_heap := ks; protocol := cmd'; msg_heap := qmsgs ++ [existT _ _ msg]
                                               ; c_heap := mycs; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n' |})) adv_mycs.
  Proof.
    unfold adv_cipher_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H _ H1); split_ex; split_ands.
    eexists; autorewrite with find_user_keys; split; eauto.
    split_ors; split_ex; split_ands; eauto.
    right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0); subst; try contradiction;
        clean_map_lookups; simpl in *; eauto 10.

    do 3 eexists; split; eauto.
    split; clean_map_lookups; eauto.
    split; eauto.
    split; eauto.
    split.
    reflexivity.
    simpl; split_ors; eauto.
    right.
    rewrite Exists_exists in *; split_ex; split_ands; destruct x3.
    eexists.
    rewrite in_app_iff; split.
    left; eauto.
    simpl; eauto.
  Qed.

  Lemma adv_cipher_queue_ok_new_cipher :
    forall {A} (usrs : honest_users A) cs c_id c u_id adv_mycs ks cmd cmd' qmsgs mycs froms sents cur_n gks,
    ~ In c_id cs
    -> adv_cipher_queue_ok cs usrs adv_mycs
    -> message_queues_ok cs usrs gks
    -> usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs
                             ; from_nons := froms; sent_nons := sents ; cur_nonce := cur_n |}
    -> adv_cipher_queue_ok (cs $+ (c_id, c))
                          (usrs $+ (u_id,
                                    {| key_heap := ks;
                                       protocol := cmd';
                                       msg_heap := qmsgs;
                                       c_heap := c_id :: mycs;
                                       from_nons := froms;
                                       sent_nons := sents;
                                       cur_nonce := 1 + cur_n |})) adv_mycs.
  Proof.
    unfold adv_cipher_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H3); split_ex; split_ands.
    destruct (c_id ==n x); subst; clean_map_lookups; eauto.
    eexists; split; eauto.
    autorewrite with find_user_keys; split_ors; split_ex; split_ands; eauto 9.
    right.
    destruct (x1 ==n u_id); subst; clean_map_lookups; simpl; eauto.
    - do 3 eexists; split; eauto.
      split; clean_map_lookups; eauto.
      split; eauto.
      simpl; split; eauto.
      split; eauto.
      split_ors; eauto.
      right; rewrite Exists_exists in *; split_ex; split_ands.
      destruct x1; split_ands.
      eexists; split; eauto.
      simpl; split; eauto.
      unfold msg_signed_addressed in *.
      rewrite andb_true_iff in H9.
      rewrite andb_true_iff; split_ands; split; eauto.
      unfold msg_nonce_same in *; intros; subst.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      simpl in *.
      msg_queue_prop.
      unfold message_queue_ok in H11.
      rewrite Forall_forall in H11; specialize (H11 _ H2); simpl in H11; split_ands.
      context_map_rewrites.
      assert (cs $? c_id0 <> None) by eauto; contradiction.
    - destruct (u_id ==n cipher_to_user x0); subst; clean_map_lookups.
      + do 3 eexists; split; eauto.
        split; clean_map_lookups; eauto.
        split; eauto.
        simpl; split; eauto.
        split; eauto.
        simpl in *; split_ors; eauto.
        right; rewrite Exists_exists in *; split_ex; split_ands.
        destruct x3; split_ands.
        eexists; split; eauto.
        simpl; split; eauto.
        unfold msg_signed_addressed in *.
        rewrite andb_true_iff in H9.
        rewrite andb_true_iff; split_ands; split; eauto.
        unfold msg_nonce_same in *; intros; subst.
        destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        simpl in *.
        msg_queue_prop.
        unfold message_queue_ok in H11.
        rewrite Forall_forall in H11; specialize (H11 _ H2); simpl in H11; split_ands.
        context_map_rewrites.
        assert (cs $? c_id0 <> None) by eauto; contradiction.
      + do 3 eexists; split; eauto.
        split; clean_map_lookups; eauto.
        split; eauto.
        simpl; split; eauto.
        split; eauto.
        simpl in *; split_ors; eauto.
        right; rewrite Exists_exists in *; split_ex; split_ands.
        destruct x4; split_ands.
        eexists; split; eauto.
        simpl; split; eauto.
        unfold msg_signed_addressed in *.
        rewrite andb_true_iff in H10.
        rewrite andb_true_iff; split_ands; split; eauto.
        unfold msg_nonce_same in *; intros; subst.
        destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        msg_queue_prop.
        msg_queue_prop.
        unfold message_queue_ok in H13.
        rewrite Forall_forall in H13; specialize (H13 _ H9); simpl in H13; split_ands.
        context_map_rewrites.
        assert (cs $? c_id0 <> None) by eauto; contradiction.
  Qed.

  Lemma adv_cipher_queue_ok_new_adv_cipher :
    forall {A} (usrs : honest_users A) cs c_id c adv_mycs gks,
      ~ In c_id cs
      -> fst (cipher_nonce c) = None
      -> cipher_honestly_signed (findUserKeys usrs) c = false
      -> message_queues_ok cs usrs gks
      -> adv_cipher_queue_ok cs usrs adv_mycs
      -> adv_cipher_queue_ok (cs $+ (c_id, c)) usrs (c_id :: adv_mycs).
  Proof.
    unfold adv_cipher_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    simpl in H4; split_ors; subst; eauto.
    destruct (c_id ==n x); subst; clean_map_lookups; eauto.
    specialize (H3 _ H4); split_ex; split_ands.
    eexists; split; eauto.
    split_ors; eauto.
    split_ex; split_ands.
    right.
    do 3 eexists; split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split_ors; eauto.
    rewrite Exists_exists in *; split_ex; split_ands.
    destruct x4; split_ands.
    right; eexists; split; eauto.
    simpl; split; eauto.

    unfold msg_signed_addressed in *.
    rewrite andb_true_iff in H11.
    rewrite andb_true_iff; split_ands; split; eauto.
    unfold msg_nonce_same in *; intros; subst.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.

    msg_queue_prop.
    unfold message_queue_ok in H13.
    rewrite Forall_forall in H13; specialize (H13 _ H10); simpl in H13; split_ands.
    context_map_rewrites.
    assert (cs $? c_id0 <> None) by eauto; contradiction.
    
  Qed.
    
  Hint Resolve
       adv_cipher_queue_ok_read_msg
       adv_cipher_queue_ok_msg_send
       adv_cipher_queue_ok_readd_user_same_mycs_froms_msgs
       adv_cipher_queue_ok_new_cipher
       adv_cipher_queue_ok_new_adv_cipher
  .

  Lemma adv_step_adv_cipher_queue_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) suid
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> suid = None
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> adv_message_queue_ok usrs cs gks qmsgs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> adv_no_honest_keys (findUserKeys usrs) ks
        -> message_queues_ok cs usrs gks
        -> adv_cipher_queue_ok cs usrs mycs
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> adv_cipher_queue_ok cs' usrs' mycs'.
  Proof.
   induction 1; inversion 1; inversion 10; intros; subst;
     eauto 2; clean_context;
       eauto.
   
   destruct rec_u;
     eapply adv_cipher_queue_ok_msg_send; eauto.

   eapply adv_cipher_queue_ok_new_adv_cipher; eauto.
   unfold cipher_honestly_signed.
   unfold honest_keyb.
   specialize (H27 k__signid); contra_map_lookup; split_ors; split_ands; context_map_rewrites;
     try contradiction; trivial.

   eapply adv_cipher_queue_ok_new_adv_cipher; eauto.
   unfold cipher_honestly_signed.
   unfold honest_keyb.
   specialize (H24 k_id); contra_map_lookup; split_ors; split_ands; context_map_rewrites;
     try contradiction; trivial.

  Qed.

  Lemma adv_cipher_in_cipher_heap :
    forall {A t} (msg : crypto t) (usrs : honest_users A) adv_heap cs cid,
      incl (findCiphers msg) adv_heap
      -> adv_cipher_queue_ok cs usrs adv_heap
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
      specialize (H0 _ LIN);
      split_ex; split_ands; eauto.
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok cs usrs gks
        -> permission_heap_good gks honestk
        -> permission_heap_good gks ks
        -> adv_cipher_queue_ok cs usrs mycs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
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
      specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
      specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
    - unfold not; intros.
      unfold keys_mine in *.
      destruct msg; simpl in *; try discriminate; clean_context.
      unfold adv_cipher_queue_ok in H27; rewrite Forall_forall in H27.
      assert (List.In cid (c_heap adv)) by eauto.
      specialize (H27 _ H); split_ex; split_ands; contra_map_lookup.
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

  Lemma cipher_honestly_signed_honest_keyb_iff :
    forall honestk c tf,
      cipher_honestly_signed honestk c = tf <-> honest_keyb honestk (cipher_signing_key c) = tf.
  Proof.
    intros.
    unfold cipher_honestly_signed, cipher_signing_key; split; destruct c; trivial.
  Qed.

  Lemma cipher_honestly_signed_false_same_msg_recv :
    forall honestk pubk c,
      cipher_honestly_signed honestk c = false
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true /\ p = false)
      -> cipher_honestly_signed (honestk $k++ pubk) c = false.
  Proof.
    intros.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); solve_perm_merges; eauto;
      match goal with
      | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG); split_ands; subst
      end; eauto.
  Qed.

  Lemma cipher_honestly_signed_false_same_msg_recv' :
    forall honestk pubk c,
      cipher_honestly_signed honestk c = false
      -> (forall k p, pubk $? k = Some p -> honestk $? k = Some true)
      -> cipher_honestly_signed (honestk $k++ pubk) c = false.
  Proof.
    intros.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); solve_perm_merges; eauto;
      match goal with
      | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG); split_ands; subst
      end; clean_map_lookups; eauto.
  Qed.

  Hint Resolve cipher_honestly_signed_false_same_msg_recv cipher_honestly_signed_false_same_msg_recv'.

  Lemma msg_honestly_signed_new_msg_keys :
    forall {t} (msg : crypto t) {t1} (c : crypto t1) honestk cs,
      message_no_adv_private honestk cs msg
      -> msg_honestly_signed honestk cs c = true
      -> msg_honestly_signed (honestk $k++ findKeysCrypto cs msg) cs c = true.
  Proof.
    unfold message_no_adv_private, msg_honestly_signed, msg_signing_key, honest_keyb; intros;
      destruct c; try discriminate;
        cases (cs $? c_id); try discriminate.
    cases (honestk $? cipher_signing_key c);
      cases (findKeysCrypto cs msg $? cipher_signing_key c);
      try discriminate; solve_perm_merges; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_new_msg_keys.

  Lemma msg_signed_addressed_new_msg_keys :
    forall {t} (msg : crypto t) {t1} (c : crypto t1) honestk cs suid,
      message_no_adv_private honestk cs msg
      -> msg_signed_addressed honestk cs suid c = true
      -> msg_signed_addressed (honestk $k++ findKeysCrypto cs msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros;
      rewrite andb_true_iff in *; split_ands; split; eauto.
  Qed.

  Hint Resolve msg_signed_addressed_new_msg_keys.

  Lemma msg_signed_addressed_new_msg_keys' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; split; eauto.
    unfold msg_honestly_signed, msg_signing_key in *;
      destruct c; try discriminate.
    cases (cs $? c_id);
      try discriminate.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); try discriminate.
    destruct b; try discriminate.
    cases (findKeysMessage msg $? cipher_signing_key c);
      solve_perm_merges; eauto.
  Qed.

  Lemma msg_signed_addressed_new_msg_keys'' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    intros; apply msg_signed_addressed_new_msg_keys'; eauto.
  Qed.

  Lemma msg_signed_addressed_new_msg_keys''' :
    forall {t} (msg : message t) {t1} (c : crypto t1) honestk cs suid,
      msg_signed_addressed honestk cs suid c = true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> msg_signed_addressed (honestk $k++ findKeysMessage msg) cs suid c = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; split; eauto.
    unfold msg_honestly_signed, msg_signing_key in *;
      destruct c; try discriminate.
    cases (cs $? c_id);
      try discriminate.
    unfold honest_keyb in *.
    cases (honestk $? cipher_signing_key c); try discriminate.
    destruct b; try discriminate.
    cases (findKeysMessage msg $? cipher_signing_key c);
      solve_perm_merges; eauto.
  Qed.

  Hint Resolve msg_signed_addressed_new_msg_keys' msg_signed_addressed_new_msg_keys'' msg_signed_addressed_new_msg_keys'''.

  Lemma msg_signed_addressed_addnl_honest_key :
    forall {t} (msg : crypto t) honestk cs suid k_id,
      ~ In k_id honestk
      -> msg_signed_addressed honestk cs suid msg = true
      -> msg_signed_addressed (honestk $+ (k_id,true)) cs suid msg = true.
  Proof.
    unfold msg_signed_addressed; intros.
    rewrite andb_true_iff in *; split_ands; eauto using msg_honestly_signed_addnl_honest_key.
  Qed.

  Hint Resolve msg_signed_addressed_addnl_honest_key.

   Lemma adv_message_queue_ok_msg_recv :
    forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
      message_queues_ok cs usrs gks
      -> msg_honestly_signed (findUserKeys usrs) cs msg = true
      -> (exists c_id c, msg = SignedCiphertext c_id /\ cs $? c_id = Some c /\ ~ List.In (cipher_nonce c) froms)
      -> usrs $? u_id =
        Some
          {|
          key_heap := ks;
          protocol := cmd;
          msg_heap := existT _ _ msg :: qmsgs;
          c_heap := mycs;
          from_nons := froms;
          sent_nons := sents;
          cur_nonce := cur_n |}
      -> adv_message_queue_ok usrs cs gks adv_msgs
      -> adv_message_queue_ok
          (usrs $+ (u_id,
                    {|
                      key_heap := ks $k++ findKeysCrypto cs msg;
                      protocol := cmd';
                      msg_heap := qmsgs;
                      c_heap := findCiphers msg ++ mycs;
                      from_nons := updateTrackedNonce (Some u_id) froms cs msg;
                      sent_nons := sents;
                      cur_nonce := cur_n |})) cs gks adv_msgs.
  Proof.
    unfold adv_message_queue_ok; intros.
    msg_queue_prop.
    rewrite Forall_forall in *; intros.
    specialize (H3 _ H7); destruct x; simpl in *.
    rewrite findUserKeys_readd_user_addnl_keys in *; eauto.
    intuition eauto.

    - specialize (H3 _ _ H11); split_ands; eauto.
    - specialize (H3 _ _ H11); split_ands; subst.
      apply merge_perms_split in H14; split_ors; eauto.
      specialize_simply.
    - specialize (H12 _ H11); split_ex; split_ands; clean_map_lookups.
      eexists; split; eauto.
      split_ors; split_ex; split_ands; eauto.
      + left; split; eauto.
        eapply cipher_honestly_signed_false_same_msg_recv; eauto.
        specialize_simply; eauto.
        destruct p; specialize_simply; trivial.
        
      + right.
        destruct (x3 ==n u_id); subst; clean_map_lookups; eauto.
        * do 3 eexists; split; eauto.
          split; clean_map_lookups; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          split_ors; eauto.
          rewrite Exists_exists in *; split_ex; split_ands; destruct x3.
          right; eexists; split; eauto.
          split_ands; split; eauto.
          split_ands; unfold msg_signed_addressed in *.
          rewrite andb_true_iff in *; split_ands; split; eauto.
          specialize_simply; eauto.

        * destruct (u_id ==n cipher_to_user x0); subst; clean_map_lookups.
          ** do 3 eexists; split; eauto.
             split; clean_map_lookups; eauto.
             split; eauto.
             split; eauto.
             split; eauto.
             specialize_simply.

             split_ors; specialize_simply.
             *** left.
                 simpl.
                 cases (cs $? x1); try discriminate.
                 cases (cipher_to_user x0 ==n cipher_to_user c0); eauto.
                 cases (count_occ msg_seq_eq froms (cipher_nonce c0)); simpl; eauto.
                 
             *** rewrite Exists_exists in *; split_ex; split_ands.
                 simpl in H20; destruct x6.
                 split_ors; clean_context; specialize_simply; eauto.
                 
                 **** generalize (eq_sigT_fst H20); intros; subst.
                      apply inj_pair2 in H20; subst.
                      simpl; context_map_rewrites.

                      unfold msg_signed_addressed in H23; rewrite andb_true_iff in H23; split_ands.
                      unfold msg_to_this_user, msg_destination_user in H23;
                        context_map_rewrites.
                      destruct (cipher_to_user x2 ==n cipher_to_user x0); subst; try discriminate.
                      rewrite e.
                      destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
                      assert (~ List.In (cipher_nonce x2) froms) as NOTIN by eauto.
                      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in NOTIN.
                      rewrite NOTIN.
                      

                      unfold msg_nonce_same in H24.
                      assert (cipher_nonce x0 = cipher_nonce x2) as EQ by eauto.
                      rewrite EQ.
                      left; eauto.

                 **** right; eexists; split; eauto.
                      split_ands; split; eauto.

          ** do 3 eexists; split; eauto.
             split; clean_map_lookups; eauto.
             split; eauto.
             split; eauto.
             split; eauto.

             split_ors; specialize_simply; eauto.
             right; rewrite Exists_exists in *; split_ex;
               destruct x7.
             eexists; split; eauto.
             split_ands; split; eauto.
  Qed.

  Hint Resolve adv_message_queue_ok_msg_recv.

  Ltac process_predicate :=
    repeat (
        contradiction
        || discriminate
        || match goal with
          | [ H : msg_to_this_user _ _ _ = true |- _ ] =>
            unfold msg_to_this_user, msg_destination_user in H; context_map_rewrites
          | [ H : (if ?cond then _ else _) = _ |- _ ] => destruct cond; try discriminate; try contradiction
          | [ |- ?c1 /\ _ ] =>
            match c1 with
            (* simplify *)
            | List.In _ (sent_nons ?sents) => is_not_var sents; simpl
            | List.In _ ?arg => match arg with
                               | context [ _ $? _ ] => context_map_rewrites
                               | context [ if ?cond then _ else _ ] => destruct cond
                               end
            (* process *)
            | _ => 
              split; [
                match c1 with
                | (_ $+ (?k1,_) $? ?k2 = _) =>
                  solve [ subst; clean_map_lookups; eauto ]
                | _ => solve [ eauto 2 ]
                end | ]
            end
          | [ H : List.In ?cn _ \/ Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] =>
            split_ors; eauto
          | [ H : Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] =>
            rewrite Exists_exists in *; split_ex
          | [ H : let (_,_) := ?x in msg_signed_addressed _ _ _ _ = true /\ _ |- _ ] => destruct x; split_ands
          | [ H : List.In ?m ?heap |- context [ ?heap ++ _ ] ] => right; simpl; exists m; rewrite in_app_iff; eauto
          end).

  Lemma honest_labeled_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok usrs'' cs' gks' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 7; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context;
        eauto 8.

    unfold adv_message_queue_ok in *;
      rewrite Forall_forall in *; intros.
    apply in_app_or in H7; simpl in H7; split_ors; subst; try contradiction.
    - specialize (H25 _ H7); destruct x; intuition (split_ex; split_ands; subst; eauto);
        repeat
          match goal with
          | [ H : (forall k v, findKeysCrypto ?cs ?c $? k = Some v -> _ ), ARG : findKeysCrypto ?cs ?c $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG)
          | [ H : (forall c_id, List.In c_id ?lst -> _), ARG : List.In _ ?lst |- _ ] =>
            specialize (H _ ARG)
          end; split_ex; eauto.

      + destruct (rec_u_id ==n u_id); subst; try rewrite map_add_eq in H15;
          autorewrite with find_user_keys in *; eauto.
      + eexists; split; eauto.
        split_ors; split_ex; split_ands; autorewrite with find_user_keys; eauto.
        
        right.
        destruct (x3 ==n u_id);
          subst; clean_map_lookups; simpl in *; eauto.

        * destruct (cipher_to_user x1 ==n cipher_to_user x2); clean_map_lookups;
            do 3 eexists; process_predicate.
        * destruct (cipher_to_user x1 ==n x3);
            destruct (u_id ==n cipher_to_user x2);
            destruct (rec_u_id ==n cipher_to_user x2);
            subst; clean_map_lookups;
              do 3 eexists; process_predicate; eauto.

    - autorewrite with find_user_keys; simpl.
      clear H25.
      split_ex; subst; simpl in *.
      repeat (apply conj); intros;
        clean_context;
        clean_map_lookups; eauto.

      + context_map_rewrites.
        destruct x1; clean_map_lookups.
        specialize (H0 _ _ H6);
          split_ors; split_ands; subst;
            keys_and_permissions_prop;
            eauto.

        * specialize (H14 _ _ H0); split_ex; split; intros; clean_map_lookups; subst; eauto.
          assert (List.In x0 mycs') by eauto.
          user_cipher_queues_prop.
          encrypted_ciphers_prop.
          unfold not; intros; eauto.
          specialize (H29 _ _ H6); split_ands; discriminate.

        * specialize (H14 _ _ H0); split_ex; split; intros; clean_map_lookups; eauto.

      + context_map_rewrites; clean_context.
        assert (List.In x0 mycs') by eauto.
        user_cipher_queues_prop.
        unfold cipher_honestly_signed in H11.
        encrypted_ciphers_prop; simpl; clean_map_lookups.

      + split_ors; subst; try contradiction;
          context_map_rewrites.

        eexists; split; eauto.
        right.

        do 3 eexists.
        split; eauto.

        split; clean_map_lookups; eauto.
        unfold msg_to_this_user, msg_destination_user in H5;
          context_map_rewrites.
        cases (cipher_to_user x1 ==n rec_u_id); try discriminate.

        split.
        rewrite e; eauto.

        simpl.
        destruct (rec_u_id ==n cipher_to_user x1); try congruence.
        rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H10.
        rewrite H10.
        split; eauto.
        assert (u_id <> cipher_to_user x1).
        rewrite e.
        eauto.
        split; clean_map_lookups; eauto.
        simpl.
        right.
        rewrite Exists_exists.
        match goal with
        | [ |- exists x, List.In x (?msgs ++ [?msg]) /\ _ ] =>
          exists msg
        end.

        rewrite in_app_iff; simpl; split; eauto.
        unfold msg_signed_addressed; rewrite andb_true_iff;
          repeat (apply conj); subst; eauto.
        (* unfold msg_to_this_user, msg_destination_user; context_map_rewrites. *)
        (* destruct (cipher_to_user x1 ==n cipher_to_user x1); try contradiction; trivial. *)
        unfold msg_nonce_same; intros.
        invert H6; clean_map_lookups; trivial.
        simpl.
        unfold msg_to_this_user, msg_destination_user in H4; context_map_rewrites;
          destruct (cipher_to_user x1 ==n rec_u_id); try congruence.

        Unshelve.
        all: auto.
  Qed.

  Lemma honest_labeled_step_adv_cipher_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> message_queues_ok cs usrs gks
        -> honest_nonces_ok cs usrs
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_cipher_queue_ok cs usrs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> adv_cipher_queue_ok cs' usrs'' adv'.(c_heap).
  Proof.
    induction 1; inversion 2; inversion 8; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context;
        unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.

    - specialize (H26 _ H1); split_ex; split_ands.
      eexists; split; eauto.
      autorewrite with find_user_keys; split_ors; split_ex; split_ands; subst; eauto.
      + left; split; eauto; subst.
        assert (@msg_honestly_signed (findUserKeys usrs') t0 cs' (SignedCiphertext x0) = true ) by eauto.
        msg_queue_prop; context_map_rewrites; destruct x1; eauto.
        simpl in *; context_map_rewrites; simpl in *.
        assert (Some k__sign = Some k__sign) as SK by trivial.
        specialize (H10 _ SK); split_ands.
        unfold msg_honestly_signed, msg_signing_key in H0; context_map_rewrites;
          simpl in H0.
        rewrite <- honest_key_honest_keyb in H0.
        specialize (H11 H0); split_ands.

        rewrite cipher_honestly_signed_honest_keyb_iff in *;
          unfold honest_keyb in *.
        unfold message_no_adv_private in H11; simpl in H11; context_map_rewrites.
        cases (findKeysMessage msg $? cipher_signing_key x2).
        * specialize (H11 _ _ Heq); split_ands; subst; context_map_rewrites; discriminate.
        * cases (findUserKeys usrs' $? cipher_signing_key x2); solve_perm_merges;
            eauto.

      + right.
        destruct (u_id ==n x3);
          [|destruct (u_id ==n cipher_to_user x2)];
          subst; clean_map_lookups; simpl in *;
          do 3 eexists;
          process_predicate; eauto; simpl.

        * right.
          eexists.
          split; eauto.
          simpl.
          context_map_rewrites; destruct x1; eauto.
          split; eauto.
          eapply accepted_safe_msg_pattern_honestly_signed in H; eauto.
          unfold msg_honestly_signed, msg_signing_key in H;
            context_map_rewrites;
            simpl in *;
            encrypted_ciphers_prop; eauto.
        * context_map_rewrites.
          destruct (cipher_to_user x2 ==n cipher_to_user x1); eauto.
          rewrite count_occ_not_In in H4; rewrite H4; eauto.
        * context_map_rewrites.
          destruct (cipher_to_user x2 ==n cipher_to_user x1); eauto.
          ** rewrite count_occ_not_In in H4; rewrite H4; eauto.
             simpl in H0; split_ors; eauto.
             *** generalize (eq_sigT_fst H0); intros; subst.
                 apply inj_pair2 in H0; subst.
                 unfold msg_nonce_same in H12.
                 assert (cipher_nonce x2 = cipher_nonce x1) as EQ by eauto.
                 rewrite EQ; eauto.
             *** right; eexists; split; eauto.
                 simpl; split; eauto.
                 destruct x1; eauto.
                 eapply accepted_safe_msg_pattern_honestly_signed in H; eauto;
                   unfold msg_honestly_signed, msg_signing_key in H;
                   context_map_rewrites;
                   simpl in *;
                   encrypted_ciphers_prop; eauto.
          ** simpl in H0; split_ors; eauto.
             *** generalize (eq_sigT_fst H0); intros; subst.
                 apply inj_pair2 in H0; subst.
                 unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H11;
                   context_map_rewrites;
                   rewrite andb_true_iff in H11;
                   split_ands.
                 destruct (cipher_to_user x1 ==n cipher_to_user x2); try discriminate.
                 congruence.

             *** right; eexists; split; eauto.
                 simpl; split; eauto.
                 destruct x1; eauto.
                 eapply accepted_safe_msg_pattern_honestly_signed in H; eauto;
                   unfold msg_honestly_signed, msg_signing_key in H;
                   context_map_rewrites;
                   simpl in *;
                   encrypted_ciphers_prop; eauto.

        * right; eexists; split; eauto.
          simpl; context_map_rewrites.
          destruct x1; eauto.
          split; eauto.
          eapply accepted_safe_msg_pattern_honestly_signed in H; eauto;
            unfold msg_honestly_signed, msg_signing_key in H;
            context_map_rewrites;
            simpl in *;
            encrypted_ciphers_prop; eauto.

    - specialize (H26 _ H7); split_ex; split_ands.
      eexists; split; eauto.
      autorewrite with find_user_keys; split_ors; split_ex; split_ands; eauto.
      right; subst; simpl in *.

      process_predicate.
      clean_context.
      symmetry in e; subst.
      assert (u_id <> cipher_to_user x1) by eauto; clear H3.

      destruct (cipher_to_user x1 ==n cipher_to_user x2);
      destruct (cipher_to_user x1 ==n x3);
        destruct (u_id ==n x3);
        destruct (u_id ==n cipher_to_user x2);
        subst;
        try contradiction;
        clean_map_lookups;
          do 3 eexists;
          process_predicate; eauto.
  Qed.

  Lemma cipher_honestly_signed_false_addnl_honest_key :
    forall honestk c k_id (gks : keys),
      ~ In k_id gks
      -> (forall k, cipher_signing_key c = k -> gks $? k <> None)
      -> cipher_honestly_signed honestk c = false
      -> cipher_honestly_signed (honestk $+ (k_id, true)) c = false.

  Proof.
    intros.
    rewrite cipher_honestly_signed_honest_keyb_iff in *.
    unfold honest_keyb in *.
    destruct (k_id ==n cipher_signing_key c); subst; clean_map_lookups; eauto.

    exfalso.
    assert (gks $? cipher_signing_key c <> None) by eauto.
    contradiction.
  Qed.

  Hint Resolve cipher_honestly_signed_false_addnl_honest_key.

  Lemma adv_message_queue_ok_addnl_honestk_key :
    forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt u_id ks cmd cmd' qmsgs mycs froms sents n adv_keys,
      ~ In k_id gks
      -> adv_message_queue_ok usrs cs gks adv_heap
      -> keys_and_permissions_good gks usrs adv_keys
      -> usrs $? u_id = Some {|
                            key_heap := ks;
                            protocol := cmd;
                            msg_heap := qmsgs;
                            c_heap := mycs;
                            from_nons := froms;
                            sent_nons := sents;
                            cur_nonce := n |}
      -> adv_message_queue_ok
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                            protocol := cmd';
                            msg_heap := qmsgs;
                            c_heap := mycs;
                            from_nons := froms;
                            sent_nons := sents;
                            cur_nonce := n |}))
          cs
          (gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |}))
          adv_heap.
  Proof.
    unfold adv_message_queue_ok; intros;
      rewrite Forall_forall in *; intros.
    specialize (H0 _ H3); destruct x; split_ands;
      repeat (apply conj);
      autorewrite with find_user_keys in *; intros; eauto.

    - destruct (k_id ==n k); subst; clean_map_lookups; split; unfold not; intros; subst;
        try discriminate.
      + specialize (H4 _ _ H7); split_ands; contradiction.
      + specialize (H4 _ _ H7); split_ands; contradiction.
      + specialize (H4 _ _ H7); split_ands.
        assert (findUserKeys usrs $? k <> Some true) by auto; contradiction.
    - destruct (k_id ==n k); subst; clean_map_lookups; eauto.
    - specialize (H6 _ H7); split_ex; split_ands;
        eexists; split; eauto.
      split_ors; split_ex; split_ands; eauto.
      + left; split; eauto.
        rewrite cipher_honestly_signed_honest_keyb_iff in *.
        unfold honest_keyb in *.
        destruct (k_id ==n cipher_signing_key x0); subst; clean_map_lookups; eauto.

        exfalso.
        destruct c; simpl in *; try contradiction.
        split_ors; subst; try contradiction.
        context_map_rewrites.
        assert (gks $? cipher_signing_key x0 <> None) by eauto; contradiction.
        
      + right.
        destruct (u_id ==n x1);
          destruct (u_id ==n cipher_to_user x0);
          subst; clean_map_lookups;
            do 3 eexists;
            simpl in *; process_predicate; eauto; simpl.
        * right; eexists; split; eauto.
          keys_and_permissions_prop.
          simpl; split; eauto.
        * right; eexists; split; eauto.
          keys_and_permissions_prop.
          simpl; split; eauto.
        * right; eexists; split; eauto.
          keys_and_permissions_prop.
          simpl; split; eauto.

          Unshelve.
          all: contradiction.
  Qed.

  Lemma adv_cipher_queue_ok_addnl_honest_key :
    forall {A} (usrs : honest_users A) adv_cs cs gks k_id u_id ks cmd cmd' qmsgs mycs froms sents n adv_ks,
      ~ In k_id gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> adv_cipher_queue_ok cs usrs adv_cs
      -> keys_and_permissions_good gks usrs adv_ks
      -> usrs $? u_id = Some {|
                            key_heap := ks;
                            protocol := cmd;
                            msg_heap := qmsgs;
                            c_heap := mycs;
                            from_nons := froms;
                            sent_nons := sents;
                            cur_nonce := n |}
      -> adv_cipher_queue_ok cs
          (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                            protocol := cmd';
                            msg_heap := qmsgs;
                            c_heap := mycs;
                            from_nons := froms;
                            sent_nons := sents;
                            cur_nonce := n |}))
          adv_cs.
  Proof.
    unfold adv_cipher_queue_ok; intros;
      rewrite Forall_forall in *; intros.
    specialize (H1 _ H4); split_ands.

    autorewrite with find_user_keys; split_ex; split_ands; eexists; split; eauto.
    split_ors; split_ex; split_ands.

    - left.
      split; eauto.
      rewrite cipher_honestly_signed_honest_keyb_iff in *.
      unfold honest_keyb in *.
      destruct (k_id ==n cipher_signing_key x0); subst; clean_map_lookups; eauto.
      exfalso.
      encrypted_ciphers_prop; simpl in *; clean_map_lookups.
      
    - right.
      destruct (u_id ==n x1);
        destruct (u_id ==n cipher_to_user x0);
        subst; clean_map_lookups;
          do 3 eexists;
          simpl in *; process_predicate; eauto; simpl.
      * right; eexists; split; eauto.
        keys_and_permissions_prop.
        simpl; split; eauto.
      * right; eexists; split; eauto.
        keys_and_permissions_prop.
        simpl; split; eauto.
      * right; eexists; split; eauto.
        keys_and_permissions_prop.
        simpl; split; eauto.
        
        Unshelve.
        all:contradiction.
  Qed.

  Hint Resolve adv_cipher_queue_ok_addnl_honest_key.

  Lemma honest_silent_step_adv_cipher_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> message_queues_ok cs usrs gks
        -> adv_cipher_queue_ok cs usrs adv.(c_heap)
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                     ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                            ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> adv_cipher_queue_ok cs' usrs'' adv'.(c_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; clean_context;
        eauto.

    - unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.
      specialize (H20 _ H); split_ex; split_ands.
      eexists; split; eauto.
      autorewrite with find_user_keys; split_ors; split_ex; split_ands; eauto.
      right.
      destruct (u_id ==n x1);
        destruct (u_id ==n cipher_to_user x0);
        subst; clean_map_lookups;
          do 3 eexists;
          simpl in *; process_predicate; eauto; simpl.

      + cases ( msg_signed_addressed (findUserKeys usrs') cs' (Some (cipher_to_user x0)) msg ); eauto.
        unfold updateTrackedNonce; destruct msg; eauto.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in Heq;
          cases (cs' $? c_id); eauto.
        cases (cipher_to_user x0 ==n cipher_to_user c); eauto.
        cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto.
      + simpl in H8.
        split_ors.
        * generalize (eq_sigT_fst H8); intros; subst.
          apply inj_pair2 in H8; subst.
          rewrite H9.
          unfold updateTrackedNonce.
          unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in H9;
            destruct c; try discriminate;
              cases (cs' $? c_id); try discriminate;
                cases (cipher_to_user c ==n cipher_to_user x0);
                apply andb_true_iff in H9;
                split_ands; try discriminate.
          rewrite e.
          destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
          cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto.
          ** unfold msg_nonce_same in H10.
             assert ( cipher_nonce x0 = cipher_nonce c) by eauto.
             rewrite H11; eauto.
          ** unfold msg_nonce_same in H10.
             assert ( cipher_nonce x0 = cipher_nonce c) by eauto.
             assert (count_occ msg_seq_eq froms (cipher_nonce c) > 0).
             rewrite Heq0. apply gt_Sn_O.
             
             rewrite <- count_occ_In in H12; rewrite H11; eauto.
        * right.
          eexists; split; eauto.
          simpl; split; eauto.

    - unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros.
      specialize (H25 _ H4); split_ex; split_ands.
      eexists; split; eauto.
      autorewrite with find_user_keys; split_ors; split_ex; split_ands.
      + left; split; eauto.
        rewrite cipher_honestly_signed_honest_keyb_iff in *.
        unfold honest_keyb in *.

        user_cipher_queues_prop.
        clear H5; encrypted_ciphers_prop.
        cases (findKeysMessage msg $? cipher_signing_key x0).
        * specialize (H21 _ _ Heq); split_ands; subst; context_map_rewrites; discriminate.
        * cases (findUserKeys usrs' $? cipher_signing_key x0); try discriminate;
            solve_perm_merges; eauto.
      + right.
        destruct (u_id ==n x1);
          destruct (u_id ==n cipher_to_user x0);
          subst; clean_map_lookups;
            do 3 eexists;
            simpl in *; process_predicate; eauto; simpl.

        * right; eexists; split; eauto; simpl; split; eauto.
          user_cipher_queues_prop.
          user_cipher_queues_prop.
          clear H5.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups; eauto.

        * right; eexists; split; eauto; simpl; split; eauto.
          clear H5.
          user_cipher_queues_prop.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups; eauto.
        * right; eexists; split; eauto; simpl; split; eauto.
          clear H5.
          user_cipher_queues_prop.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups; eauto.

          Unshelve.
          all:contradiction.
  Qed.

  Lemma adv_message_queue_ok_addnl_global_key :
    forall {A} (usrs : honest_users A) adv_heap cs gks k_id usage kt,
      adv_message_queue_ok usrs cs gks adv_heap
      -> ~ In k_id gks
      -> adv_message_queue_ok
          usrs
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
    forall {A} (usrs : honest_users A) adv_heap cs gks c_id c,
      ~ In c_id cs
      -> adv_message_queue_ok usrs cs gks adv_heap
      -> adv_message_queue_ok usrs (cs $+ (c_id,c)) gks adv_heap.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H1).
    destruct x; split_ands.

    intuition (intros; eauto);
      try
        match goal with
        | [ H : context [cs $+ (?cid1,_) $? ?cid2] |- _ ] =>
          destruct (cid1 ==n cid2); subst; clean_map_lookups
        | [ |- context [cs $+ (?cid1,_) $? ?cid2] ] =>
          destruct (cid1 ==n cid2); subst; clean_map_lookups
        end; eauto.

    - unfold findKeysCrypto in H2 , H5; destruct c0; eauto.
      + specialize (H2 _ _ H5); split_ands; eauto.
      + destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        * simpl in *.
          assert (~ In c_id0 cs) by eauto.
          rewrite not_find_in_iff in H7; context_map_rewrites; eauto.
        * specialize (H2 _ _ H5); split_ands; eauto.
    - unfold findKeysCrypto in H2 , H5; destruct c0; subst; eauto.
      + specialize (H2 _ _ H5); split_ands; eauto.
      + destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        * simpl in *.
          assert (~ In c_id0 cs) by eauto.
          rewrite not_find_in_iff in H6; context_map_rewrites; eauto.
        * specialize (H2 _ _ H5); split_ands; eauto.
    - unfold msg_signing_key in H5; destruct c0; try discriminate.
      destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
      simpl in *.
      assert (~ In c_id0 cs) by eauto.
      rewrite not_find_in_iff in H5; context_map_rewrites; eauto.
    - eexists; split; intros; eauto.
      specialize (H4 _ H5); split_ex; split_ands.
      exfalso.
      assert (~ In c_id0 cs) by eauto.
      rewrite not_find_in_iff in H7; contra_map_lookup.
    - specialize (H4 _ H5); split_ex.
      eexists; split; eauto.
      split_ors; eauto.
      split_ex; right.
      do 3 eexists; process_predicate.
      right; eexists; split; eauto.
      simpl; split.
      + unfold msg_signed_addressed in *.
        rewrite andb_true_iff in *; split_ands; split; eauto.
      + unfold msg_nonce_same in *; intros; clean_map_lookups.
        destruct (c_id ==n c_id1); subst; clean_map_lookups; eauto.
        exfalso.
        assert (~ In c_id1 cs) by eauto; clean_map_lookups.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in H12;
          split_ands;
          context_map_rewrites;
          discriminate.
  Qed.

  Lemma adv_message_queue_ok_users_same_keys_sents :
    forall {A} (usrs : honest_users A) cs gks adv_msgs u_id ks cmd cmd' qmsgs mycs mycs' froms sents n n',
      adv_message_queue_ok usrs cs gks adv_msgs
      -> usrs $? u_id = Some {|
                           key_heap := ks;
                           protocol := cmd;
                           msg_heap := qmsgs;
                           c_heap := mycs;
                           from_nons := froms;
                           sent_nons := sents;
                           cur_nonce := n |}
      ->  adv_message_queue_ok
           (usrs $+ (u_id, {|
                       key_heap := ks;
                       protocol := cmd';
                       msg_heap := qmsgs;
                       c_heap := mycs';
                       from_nons := froms;
                       sent_nons := sents;
                       cur_nonce := n' |})) cs gks adv_msgs.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H _ H1); destruct x;
      split_ands; repeat (apply conj);
        autorewrite with find_user_keys; eauto.

    intros.
    specialize (H4 _ H5); split_ex; eexists; split_ands; split; intros; eauto.
    split_ors; split_ex; split_ands; eauto.
    right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0);
      subst; clean_map_lookups;
        do 3 eexists;
        simpl in *;
        process_predicate.

    Unshelve.
    all:contradiction.
  Qed.

  Hint Resolve adv_message_queue_ok_addnl_cipher adv_message_queue_ok_users_same_keys_sents.

  Lemma updateTrackedNonce_same_or_one_added :
    forall {t} (msg : crypto t) suid froms cs,
        updateTrackedNonce suid froms cs msg = froms
      \/ exists c_id c, msg_cipher_id msg = Some c_id
                /\ cs $? c_id = Some c
                /\ ~ List.In (cipher_nonce c) froms
                /\ updateTrackedNonce suid froms cs msg = cipher_nonce c :: froms.
  Proof.
    intros; unfold updateTrackedNonce.
    destruct msg; eauto.
    cases (cs $? c_id); eauto.
    destruct suid; eauto.
    destruct (u ==n cipher_to_user c); eauto.
    cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto.
    rewrite <- count_occ_not_In in Heq0.
    simpl; eauto 8.
  Qed.

  Lemma adv_message_queue_ok_msg_recv_drop :
    forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
      usrs $? u_id =
        Some
          {|
          key_heap := ks;
          protocol := cmd;
          msg_heap := existT _ _ msg :: qmsgs;
          c_heap := mycs;
          from_nons := froms;
          sent_nons := sents;
          cur_nonce := cur_n |}
      -> adv_message_queue_ok usrs cs gks adv_msgs
      -> adv_message_queue_ok
          (usrs $+ (u_id,
                    {|
                      key_heap := ks;
                      protocol := cmd';
                      msg_heap := qmsgs;
                      c_heap := mycs;
                      from_nons := updateTrackedNonce (Some u_id) froms cs msg;
                      sent_nons := sents;
                      cur_nonce := cur_n |})) cs gks adv_msgs.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H1); destruct x; simpl in *.
    autorewrite with find_user_keys.
    split_ands; repeat (apply conj); eauto; intros.

    specialize (H4 _ H5).
    split_ex.
    eexists; split; eauto.
    split_ors; eauto.
    split_ex; right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0);
      subst; clean_map_lookups;
        simpl in *;
        do 3 eexists; process_predicate; eauto; simpl.

    - match goal with
      | [ |- context [ updateTrackedNonce ?suid ?froms ?cs ?msg ]] =>
        pose proof (updateTrackedNonce_same_or_one_added msg suid froms cs)
      end.

      subst.
      split_ors; split_ex.
      rewrite H11; eauto.
      rewrite H14; eauto.

    - simpl in H10; split_ors.
      + generalize (eq_sigT_fst H10); intros; subst.
        apply inj_pair2 in H10; subst.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key, msg_to_this_user, msg_destination_user in H11;
          rewrite andb_true_iff in H11; split_ands.
        unfold updateTrackedNonce.
        destruct c0; try discriminate.
        cases (cs $? c_id0); try discriminate.
        cases (cipher_to_user c0 ==n cipher_to_user x0); try discriminate.
        rewrite e.
        destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.

        unfold msg_nonce_same in H12.
        assert (cipher_nonce x0 = cipher_nonce c0) as EQ by eauto.
        rewrite EQ.

        cases (count_occ msg_seq_eq froms (cipher_nonce c0)); eauto.
        assert (count_occ msg_seq_eq froms (cipher_nonce c0) > 0) by (rewrite Heq0; apply gt_Sn_O); eauto.
        rewrite <- count_occ_In in H13; eauto.

      + right.
        eexists; split; eauto; simpl.
        split; eauto.

        Unshelve.
        all:contradiction.
  Qed.

  Lemma adv_message_queue_ok_msg_recv_drop' :
    forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
      usrs $? u_id =
        Some
          {|
          key_heap := ks;
          protocol := cmd;
          msg_heap := existT _ _ msg :: qmsgs;
          c_heap := mycs;
          from_nons := froms;
          sent_nons := sents;
          cur_nonce := cur_n |}
      -> adv_message_queue_ok usrs cs gks adv_msgs
      -> msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg = false
      -> adv_message_queue_ok
          (usrs $+ (u_id,
                    {|
                      key_heap := ks;
                      protocol := cmd';
                      msg_heap := qmsgs;
                      c_heap := mycs;
                      from_nons := froms;
                      sent_nons := sents;
                      cur_nonce := cur_n |})) cs gks adv_msgs.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H2); destruct x; simpl in *.
    autorewrite with find_user_keys.
    split_ands; repeat (apply conj); eauto; intros.

    specialize (H5 _ H6).
    split_ex.
    eexists; split; eauto.
    split_ors; eauto.
    split_ex; right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0);
      subst; clean_map_lookups;
        simpl in *;
        do 3 eexists; process_predicate; eauto; simpl.

    simpl in H11; split_ors.
    - generalize (eq_sigT_fst H11); intros; subst.
      apply inj_pair2 in H11; subst.
      unfold msg_signed_addressed in *.
      rewrite andb_true_iff in H12; split_ands.
      unfold msg_honestly_signed, msg_signing_key, honest_keyb, msg_to_this_user, msg_destination_user in *;
        destruct c0; try discriminate;
          cases (cs $? c_id0); try discriminate;
            cases (findUserKeys usrs $? cipher_signing_key c0); try discriminate;
              destruct b; try discriminate;
                cases (cipher_to_user c0 ==n cipher_to_user x0); try discriminate.

    - right; eexists; split; eauto.
      simpl; split; eauto.

      Unshelve.
      all:contradiction.
  Qed.

  Hint Resolve
       adv_message_queue_ok_msg_recv_drop
       adv_message_queue_ok_msg_recv_drop'.

  Lemma adv_message_queue_ok_msg_adv_send :
    forall {A t} (usrs : honest_users A) (msg : crypto t) cs gks u_id ks cmd cmd' qmsgs mycs froms sents cur_n adv_msgs,
      usrs $? u_id =
        Some
          {|
          key_heap := ks;
          protocol := cmd;
          msg_heap := qmsgs;
          c_heap := mycs;
          from_nons := froms;
          sent_nons := sents;
          cur_nonce := cur_n |}
      -> adv_message_queue_ok usrs cs gks adv_msgs
      -> adv_message_queue_ok
          (usrs $+ (u_id,
                    {|
                      key_heap := ks;
                      protocol := cmd';
                      msg_heap := qmsgs ++ [existT _ _ msg];
                      c_heap := mycs;
                      from_nons := froms;
                      sent_nons := sents;
                      cur_nonce := cur_n |})) cs gks adv_msgs.
  Proof.
    unfold adv_message_queue_ok; intros.
    rewrite Forall_forall in *; intros.
    specialize (H0 _ H1); destruct x; simpl in *.
    autorewrite with find_user_keys.
    split_ands; repeat (apply conj); eauto; intros.

    specialize (H4 _ H5).
    split_ex.
    eexists; split; eauto.
    split_ors; eauto.
    split_ex; right.
    destruct (u_id ==n x1);
      destruct (u_id ==n cipher_to_user x0);
      subst; clean_map_lookups;
        simpl in *;
        do 3 eexists; process_predicate; eauto; simpl.

    Unshelve.
    all:contradiction.
  Qed.

  Hint Resolve adv_message_queue_ok_msg_adv_send.

  Lemma honest_silent_step_adv_message_queue_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> message_queues_ok cs usrs gks
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_message_queue_ok usrs'' cs' gks' adv'.(msg_heap).
  Proof.
    induction 1; inversion 2; inversion 7; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto; clean_context.

    - cases (msg_signed_addressed (findUserKeys usrs') cs' (Some u_id) msg); eauto.

    - user_cipher_queues_prop.
      encrypted_ciphers_prop.
      unfold adv_message_queue_ok in *;
        rewrite Forall_forall in *; intros.
      specialize (H26 _ H4); destruct x;
        split_ands; repeat (apply conj); eauto; intros; eauto.

      +  specialize (H8 _ _ H11); autorewrite with find_user_keys; split_ands;
           split; intros; eauto.
         specialize (H13 H18); unfold not; intros.
         apply merge_perms_split in H19; split_ors; try contradiction; subst.
         specialize (H17 _ _ H19); split_ands; subst; eauto.
      + specialize (H10 _ H11); split_ex; split_ands;
          eexists; split; eauto; intros.
        split_ors; split_ex; split_ands; autorewrite with find_user_keys; eauto.
        right.
        destruct (u_id ==n x1);
          destruct (u_id ==n cipher_to_user x0);
          subst; clean_map_lookups;
            do 3 eexists;
            process_predicate; eauto; simpl.
        * right; eexists; split; eauto; simpl; eauto.
        * right; eexists; split; eauto; simpl; eauto.
        * right; eexists; split; eauto; simpl; eauto.
  Qed.

  Lemma adv_step_adv_message_queue_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok usrs cs gks qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_message_queue_ok usrs' cs' gks' qmsgs'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst;
      eauto 2; try discriminate; eauto;
        clean_context;
        autorewrite with find_user_keys;
        try match goal with
            | [ H : adv_message_queue_ok _ _ _ (_ :: _) |- _] => invert H
            end; eauto.

    destruct rec_u; simpl; eauto.
  Qed.

  (* Step adv no honest keys *)

  Lemma honest_labeled_step_adv_no_honest_keys :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Action a
            -> action_adversary_safe honestk cs a
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> adv_no_honest_keys honestk' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst;
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
              |- context [ _ $k++ findKeysCrypto _ ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try solve_perm_merges
          | [ FK : findKeysCrypto _ ?msg $? ?kid = None |- context [ ?uks $k++ findKeysCrypto _ ?msg $? ?kid] ] =>
            split_ors; split_ands; solve_perm_merges
          | [ H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeysCrypto ?cs ?msg $? ?kid] ] =>
            match goal with
            | [ H : findKeysCrypto cs msg $? kid = _ |- _ ] => fail 1
            | _ => cases (findKeysCrypto cs msg $? kid)
            end
          end; eauto.

      split_ors; split_ands; contra_map_lookup; eauto.

    - unfold adv_no_honest_keys in *; intros.
      specialize (H24 k_id).
      split_ex; subst; simpl in *.
      assert (List.In x mycs') by eauto.
      user_cipher_queues_prop.
      rewrite cipher_honestly_signed_honest_keyb_iff in H11.
      encrypted_ciphers_prop; eauto.
      intuition idtac.
      right; right; split; eauto; intros.
      solve_perm_merges;
        specialize (H14 _ _ H17); split_ands; discriminate.
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_no_honest_keys honestk adv.(key_heap)
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> lbl = Silent
            -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
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
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs ks
        -> adv_message_queue_ok usrs cs gks qmsgs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 7; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto;
        try rewrite add_key_perm_add_private_key; clean_context;
          match goal with
          | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
          end.

    - invert H24; split_ands.
      unfold adv_no_honest_keys in *; intros.
      specialize (H22 k_id); intuition idtac.
      right; right; intuition eauto.
      eapply merge_perms_split in H9; split_ors; auto.
      specialize (H3 _ _ H9); split_ands; eauto.
      
    - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (ADV k__encid); split_ors; split_ands; try contradiction;
        encrypted_ciphers_prop; clean_map_lookups; intuition idtac;
        unfold adv_no_honest_keys; intros;
          specialize (H23 k_id); clean_map_lookups; intuition idtac;
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
      solve_perm_merges; eauto. 
      intros;
        cases (pubk $? k_id);
        repeat
          match goal with
          | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          | [ H : (forall k, ?fkm $? k = Some ?tf -> _), ARG : ?fkm $? _ = Some ?tf |- _ ] =>
            specialize (H _ ARG)
          end; solve_perm_merges; eauto.

    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); solve_perm_merges;
        match goal with
        | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG); split_ands; subst
        end; clean_map_lookups.
    - eapply SigEncCipherAdvSignedOk; eauto.
      + unfold not; intros.
        solve_perm_merges; clean_context; eauto.

      + intros. specialize (H2 _ _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros; subst.
        specialize (H5 (eq_refl true)).
        solve_perm_merges; clean_context; eauto.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto;
        solve_perm_merges; eauto.
      unfold keys_mine in *; intros.
      specialize (H3 _ _ H5).
      solve_perm_merges.
  Qed.

  Lemma encrypted_cipher_ok_addnl_pubk' :
    forall honestk pubk gks c cs,
      encrypted_cipher_ok honestk cs gks c
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true)
      -> encrypted_cipher_ok (honestk $k++ pubk) cs gks c.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
      solve_perm_merges; eauto. 
      intros;
        cases (pubk $? k_id);
        repeat
          match goal with
          | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          | [ H : (forall k, ?fkm $? k = Some ?tf -> _), ARG : ?fkm $? _ = Some ?tf |- _ ] =>
            specialize (H _ ARG)
          end; solve_perm_merges; eauto.

    - eapply SigCipherNotHonestOk; eauto.
      unfold not; intros.
      cases (honestk $? k); cases (pubk $? k); solve_perm_merges;
        match goal with
        | [ H : (forall k v, ?pubk $? k = Some v -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG); split_ands; subst
        end; clean_map_lookups.
    - eapply SigEncCipherAdvSignedOk; eauto.
      + unfold not; intros.
        solve_perm_merges; clean_context; eauto.

      + intros. specialize (H2 _ _ H4); split_ex; split_ands; eexists; split; eauto.
        unfold not; intros; subst.
        specialize (H5 (eq_refl true)).
        solve_perm_merges; clean_context; eauto.

    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto;
        solve_perm_merges; eauto.
      unfold keys_mine in *; intros.
      specialize (H3 _ _ H5).
      solve_perm_merges.
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

  Lemma encrypted_ciphers_ok_addnl_pubk' :
    forall honestk pubk cs gks,
      encrypted_ciphers_ok honestk cs gks
      -> (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true)
      -> encrypted_ciphers_ok (honestk $k++ pubk) cs gks.
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *; intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_pubk'.
  Qed.

  Hint Resolve encrypted_ciphers_ok_addnl_key encrypted_ciphers_ok_addnl_pubk'.

  Lemma adv_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> mycs = adv.(c_heap)
        -> adv_no_honest_keys honestk ks
        -> permission_heap_good gks ks
        -> adv_cipher_queue_ok cs usrs mycs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
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
             ; msg_heap := clean_messages (findUserKeys U.(users)) U.(all_ciphers) (Some u_id) user_data.(from_nons) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap)
             ; from_nons := user_data.(from_nons)
             ; sent_nons := user_data.(sent_nons)
             ; cur_nonce := user_data.(cur_nonce) |}
        -> (strip_adversary U).(s_users) $? u_id = Some user_data'.
    Proof.
      unfold strip_adversary, clean_users; destruct user_data; simpl; intros.
      rewrite <- find_mapsto_iff in H.
      rewrite <- find_mapsto_iff, mapi_mapsto_iff; intros;
        subst; auto; eexists; subst; simpl; intuition eauto.
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
      - eapply honest_keyb_true_honestk_has_key in H2.
        invert H; try contradiction.
        econstructor; eauto.
      - eapply honest_keyb_true_honestk_has_key in H2.
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
          | [ H : honest_keyb _ _ = true |- _ ] => eapply honest_keyb_true_honestk_has_key in H
          | [ H : encrypted_cipher_ok _ _ _ _ |- _ ] => invert H; try contradiction
          end.

      - econstructor; eauto using msgCiphersSigned_cleaned_honestk.
        intros * ARG; specialize (H11 _ _ ARG); split_ands; eauto.

      - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto using msgCiphersSigned_cleaned_honestk.
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
      rewrite <- find_mapsto_iff in H3; unfold clean_users in H3;
        rewrite mapi_mapsto_iff in H3; intros; subst; trivial.
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
        rewrite <- find_mapsto_iff in Heq0;
          rewrite clean_ciphers_mapsto_iff in Heq0; rewrite find_mapsto_iff in Heq0;
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

      - simpl in H; cases (msg_nonce_ok cs froms c).
        + unfold msg_nonce_ok in Heq0; destruct c; try discriminate;
            cases (cs $? c_id); try discriminate;
              cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate;
                clean_context; eauto.

          rewrite !fold_clean_messages2' in *.
          rewrite clean_messages'_fst_pull in H; simpl in H.
          split_ors; subst; eauto.
          specialize (IHmsgs _ H); intuition eauto.
        + unfold msg_nonce_ok in Heq0; destruct c; try discriminate.
          specialize (IHmsgs _ H); intuition eauto.
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

    Hint Resolve clean_users_no_change_honestk clean_users_no_change_honestk'.

    Lemma message_queues_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs gks,
        message_queues_ok cs usrs gks
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs) (clean_keys honestk gks).
    Proof.
      unfold message_queues_ok; intros.
      rewrite Forall_natmap_forall in *; intros.
      rewrite <- find_mapsto_iff in H2;
        unfold clean_users in H2; rewrite mapi_mapsto_iff in H2; intros; subst; trivial.
      split_ex; split_ands; subst; simpl in *.
      rewrite find_mapsto_iff in H2; specialize (H _ _ H2).
      eapply message_queue_ok_after_cleaning; auto.
    Qed.

    Hint Resolve
         msg_to_this_user_before_after_cleaning
         msg_to_this_user_false_before_after_cleaning.

    Ltac instantiate_cs_lkup :=
      match goal with 
      | [ H : forall c_id c, ?cs $? c_id = Some c -> _ |- _ ] =>
        match goal with
        | [ CS : cs $? _ = Some _ |- _ ] =>
          let INST := fresh "INST" in
          generalize (H _ _ CS); intro INST;
          let toh := type of INST in
          clear INST; match goal with
                      | [ OH : toh |- _ ] => fail 1
                      | _ => generalize (H _ _ CS); intro INST
                      end
        end
      end.

    Ltac instantiate_cs_lkup' :=
      match goal with 
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

    Ltac instantiate_cs_lkup_uni :=
      match goal with 
      | [ H : forall c_id c, ?cs $? c_id = Some c -> _ |- _ ] =>
        let cid := fresh "cid" in
        let c := fresh "c" in
        evar (cid : cipher_id); evar (c : cipher);
        let cidsome := fresh "CS" in
        let cid' := eval unfold cid in cid in
        let c' := eval unfold c in c in
            clear cid; clear c; evar (cidsome : cs $? cid' = Some c');
        let cidsome' := eval unfold cidsome in cidsome in
            clear cidsome; specialize (H _ _ cidsome')
      end.
        
    Ltac process_nonce_ok1 :=
        match goal with
        | [ H : _ $+ (?uid1,_) $? ?uid2 = _ |- _ ] => destruct (uid1 ==n uid2); subst; clean_map_lookups; simpl
        | [ H : ?cs $? ?cid = _ |- context [ ?cs $? ?cid ] ] => rewrite H
        | [ H : SignedCiphertext _ = SignedCiphertext _ |- _ ] => invert H
        | [ H : ~ List.In ?cn ?lst |- context [ count_occ msg_seq_eq ?lst ?cn ] ] =>
          rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H; rewrite H
        | [ |- honest_nonce_tracking_ok _ _ _ _ _ (if ?cond then _ else _) _ ] => destruct cond; subst
        | [ H1 : msg_to_this_user _ _ _ = true, H2 : msg_to_this_user _ _ _ = false |- _ ] =>
          rewrite H1 in H2; invert H2
        | [ H : forall _ _ _ _, _ <> _ -> _
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
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ ?froms ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some {|
                                     key_heap := _;
                                     protocol := _;
                                     msg_heap := (_ :: ?qmsgs);
                                     c_heap := _;
                                     from_nons := ?froms;
                                     sent_nons := _;
                                     cur_nonce := _ |}
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ ?froms ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some {|
                                     key_heap := _;
                                     protocol := _;
                                     msg_heap := (_ :: ?qmsgs);
                                     c_heap := _;
                                     from_nons := ?froms;
                                     sent_nons := _;
                                     cur_nonce := _ |}
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ (_ :: ?froms) ?qmsgs ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : forall _ _ _ _, _ <> _ -> _
          , NE: ?uid1 <> ?uid2
          , U1 : ?usrs $? ?uid1 = _
          , U2 : ?usrs $? ?uid2 = Some ?rec_u
            |- honest_nonce_tracking_ok _ (Some ?uid1) _ _ _ (from_nons ?rec_u) _ ] => specialize (H _ _ _ _ NE U1 U2); simpl in H
        | [ H : honest_nonce_tracking_ok _ _ _ _ _ _ _ |- honest_nonce_tracking_ok _ _ _ _ _ _ _ ] =>
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
        | [ H : Forall _ (_ :: _) |- _ ] => invert H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ H : List.In _ (_ :: _) |- _ ] => simpl in H; split_ors
        | [ H : ~ List.In _ (if ?cond then _ else _) |- _ ] => destruct cond; subst; simpl in H
        | [ H : ~ (_ \/ _) |- _ ] => apply Decidable.not_or in H; split_ands
        | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] => eapply accepted_safe_msg_pattern_to_this_user in H; eauto 2
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
        (* | [ |- ~ List.In _ (_ :: _) ] => simpl; apply Classical_Prop.and_not_or *)
        | [ |- ~ (_ \/ _) ] => apply Classical_Prop.and_not_or
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

    Hint Extern 1 (message_queue_ok _ _ _ _) => eassumption || (msg_queue_prop; eassumption).

    Ltac process_nonce_ok :=
      repeat ( simpl in *; clean_map_lookups1 || congruence || discriminate || process_nonce_ok1 || instantiate_cs_lkup' || Nat.order).

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

    Hint Resolve clean_ciphers_nochange_cipher.
    
    Lemma honest_nonce_tracking_ok_after_cleaning :
      forall honestk cs me my_sents my_non you your_froms your_msgs,
        honest_nonce_tracking_ok cs me my_sents my_non you your_froms your_msgs
        -> honest_nonce_tracking_ok (clean_ciphers honestk cs) me my_sents my_non
                            you your_froms
                            (clean_messages honestk cs (Some you) your_froms your_msgs).
    Proof.
      unfold honest_nonce_tracking_ok; intros; rewrite !Forall_forall in *; intros; split_ands.
      repeat (apply conj); intros; eauto.

      - destruct x; intros; subst.
        eapply clean_messages_list_in_safe in H3; split_ands.
        specialize (H1 _ H3); simpl in H1.
        eapply H1; eauto.

      - rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H3;
          split_ands.
        specialize (H2 _ _ H3 H4); intuition eauto.
        + rewrite Forall_forall in *; intros.
          eapply clean_messages_list_in_safe in H7; split_ands.
          specialize (H10 _ H7); destruct x.

          split_ors.
          * left; unfold msg_to_this_user, msg_destination_user in *;
              destruct c0; try discriminate.
            unfold msg_signed_addressed in H11; rewrite andb_true_iff in H11; split_ands.
            cases (cs $? c_id0); try discriminate; eauto.
            ** erewrite clean_ciphers_keeps_honest_cipher; eauto.
               unfold honest_cipher_filter_fn, cipher_honestly_signed, msg_honestly_signed, msg_signing_key in *;
                 context_map_rewrites; destruct c0; eauto.
            ** rewrite clean_ciphers_no_new_ciphers; eauto.
          
          * right; unfold msg_nonce_not_same in *; intros; eauto.
    Qed.

    Hint Resolve honest_nonce_tracking_ok_after_cleaning.

    Lemma honest_nonces_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        honest_nonces_ok cs usrs
        -> honestk = findUserKeys usrs
        -> honest_nonces_ok (clean_ciphers honestk cs) (clean_users honestk cs usrs).
    Proof.
      unfold honest_nonces_ok; intros.
      eapply clean_users_cleans_user_inv with (honestk := honestk) in H2; split_ex; split_ands.
      eapply clean_users_cleans_user_inv with (honestk := honestk) in H3; split_ex; split_ands.
      rewrite H7.
      specialize (H _ _ _ _ H1 H2 H3); simpl in *; subst; split_ands; eauto.
    Qed.

    Lemma honest_labeled_step_honest_nonces_ok :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
            -> honestk = findUserKeys usrs
            -> encrypted_ciphers_ok honestk cs gks
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
      induction 1; inversion 2; inversion 4; intros; subst; try discriminate;
        eauto;
        clean_context;
        split_ex; split_ands; subst;
          unfold honest_nonces_ok in *; intros;
            process_nonce_ok; eauto.
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
        process_nonce_ok; eauto.
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

  Hint Resolve nonce_not_in_msg_queue_addnl_cipher.
    
  Lemma honest_nonce_tracking_ok_new_msg :
    forall suid sents cur_n cs froms to_usr qmsgs msg,
        honest_nonce_tracking_ok cs suid sents cur_n to_usr froms (msg :: qmsgs)
      -> honest_nonce_tracking_ok cs suid sents cur_n to_usr froms qmsgs.
  Proof.
    unfold honest_nonce_tracking_ok; intros; process_nonce_ok.
  Qed.

  Hint Resolve
       honest_nonce_tracking_ok_new_msg.
  
  Lemma honest_nonces_ok_new_honest_key :
    forall {A} (usrs : honest_users A) k_id cs u_id ks cmd cmd' qmsgs mycs froms sents cur_n,
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
                                     key_heap := add_key_perm k_id true ks;
                                     protocol := cmd';
                                     msg_heap := qmsgs;
                                     c_heap := mycs;
                                     from_nons := froms;
                                     sent_nons := sents;
                                     cur_nonce := cur_n |})).
  Proof.
    unfold honest_nonces_ok; intros;
      process_nonce_ok; eauto.
  Qed.

  Hint Resolve
       honest_nonces_ok_newuser_nochange_froms_sents_msgs
       honest_nonces_ok_new_honest_key.

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
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         forall c_id c,
                                           msg = SignedCiphertext c_id
                                           -> cs $? c_id = Some c
                                           -> cipher_to_user c = to_usr
                                           -> fst (cipher_nonce c) = from_usr
                                           -> snd (cipher_nonce c) < cur_n end) qmsgs
      -> cur_n <= cur_n'
      -> Forall (fun sigM => match sigM with (existT _ _ msg) =>
                                         forall c_id c,
                                           msg = SignedCiphertext c_id
                                           -> cs $+ (newcid, newc) $? c_id = Some c
                                           -> cipher_to_user c = to_usr
                                           -> fst (cipher_nonce c) = from_usr
                                           -> snd (cipher_nonce c) < cur_n' end) qmsgs.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    destruct x; intros.
    destruct (newcid ==n c_id); subst; clean_map_lookups;
      process_nonce_ok; eauto.

    specialize (H1 _ H3); simpl in H1.
    assert (snd (cipher_nonce c0) < cur_n) by eauto.
    Nat.order.
  Qed.

  Hint Resolve
       msg_queue_nonces_good_new_cipher
       msg_queue_values_ok_new_cipher
       sents_ok_increase_nonce
       froms_ok_increase_nonce.

  Lemma nat_lt_nat_plus_one :
    forall n, n < n + 1.
  Proof.
    intros; rewrite Nat.add_1_r; eauto.
  Qed.

  Lemma nat_le_nat_plus_one :
    forall n, n <= n + 1.
  Proof.
    intros; rewrite Nat.add_1_r; eauto.
  Qed.

  Hint Resolve nat_lt_nat_plus_one nat_le_nat_plus_one.

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
    induction 1; inversion 2; inversion 5; intros; subst; try discriminate;
      eauto; clean_context;
        msg_queue_prop; process_nonce_ok; eauto.

    - cases (msg_signed_addressed (findUserKeys usrs') cs' (Some u_id) msg);
        unfold honest_nonces_ok in *; intros;
          process_nonce_ok; eauto.

      unfold updateTrackedNonce, msg_signed_addressed, msg_honestly_signed, msg_signing_key in *.
      destruct msg; try discriminate.
      cases (cs' $? c_id); try discriminate; simpl in *.
      destruct (rec_u_id ==n cipher_to_user c); subst;
        process_nonce_ok; eauto.

    - unfold honest_nonces_ok in *; intros;
        simpl in *; subst;
          process_nonce_ok; subst; eauto.

      + rewrite Forall_forall in H9; unfold not; intro LIN;
          specialize (H9 _ LIN); simpl in H9; process_nonce_ok.

      + rewrite Forall_forall; intros; destruct x.
        right; unfold msg_nonce_not_same; intros; subst; simpl.
        cases (c_id0 ==n c_id); subst; clean_map_lookups; simpl; process_nonce_ok.
        unfold not; intros; process_nonce_ok.
        rewrite <- H17 in H15; simpl in H15;
          process_nonce_ok.

    - unfold honest_nonces_ok in *; intros;
        process_nonce_ok; eauto.
    - unfold honest_nonces_ok in *; intros;
        process_nonce_ok; eauto.

      + rewrite Forall_forall in H6; unfold not; intro LIN; specialize (H6 _ LIN); simpl in H6.
        assert (Some u_id0 = Some u_id0) as SUID by trivial; specialize (H6 SUID); Nat.order.

      + rewrite Forall_forall; intros; destruct x.
        right; unfold msg_nonce_not_same; intros; subst; simpl.
        cases (c_id0 ==n c_id); subst; clean_map_lookups; process_nonce_ok.
        unfold not; intros; process_nonce_ok.
        rewrite <- H13 in H9; simpl in H9;
          process_nonce_ok.
  Qed.

  Lemma honest_nonce_tracking_ok_new_adv_cipher :
    forall cs c_id c me my_sents my_n you your_froms your_msgs honestk gks,
      ~ In c_id cs
      -> message_queue_ok honestk cs your_msgs gks
      -> fst (cipher_nonce c) = None
      -> honest_nonce_tracking_ok cs (Some me) my_sents my_n you your_froms your_msgs
      -> honest_nonce_tracking_ok (cs $+ (c_id,c)) (Some me) my_sents my_n you your_froms your_msgs.
  Proof.
    unfold honest_nonce_tracking_ok; intros; split_ands;
      repeat (apply conj); eauto.

    intros.
    destruct (c_id ==n c_id0); subst; clean_map_lookups.
    - rewrite H1 in H7; invert H7.
    - specialize (H5 _ _ H6 H7); eauto; split_ands; split; eauto; intros.
      specialize (H8 H9 H10); split_ands; split; eauto.
  Qed.

  Lemma honest_nonces_ok_adv_new_cipher :
    forall {A} (usrs : honest_users A) cs c_id c gks,
      ~ In c_id cs
      -> message_queues_ok cs usrs gks
      -> fst (cipher_nonce c) = None
      -> honest_nonces_ok cs usrs
      -> honest_nonces_ok (cs $+ (c_id,c)) usrs.
  Proof.
    unfold honest_nonces_ok; intros.
    specialize (H2 _ _ _ _ H3 H4 H5).
    repeat msg_queue_prop.
    eapply honest_nonce_tracking_ok_new_adv_cipher; eauto.
  Qed.

  Hint Resolve honest_nonces_ok_adv_new_cipher.

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
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> honest_nonces_ok cs' usrs'.
  Proof.
    induction 1; inversion 1; inversion 12; intros; subst;
      eauto;
      clean_context.
 
    unfold honest_nonces_ok in *; intros;
      process_nonce_ok; eauto.

    subst.

    unfold adv_cipher_queue_ok in H29;
      rewrite Forall_forall in H29.

    unfold msg_nonce_not_same; destruct msg.
    - right; intros; discriminate.
    - simpl in H1.
      assert (List.In c_id0 (c_heap adv)) as LIN by eauto.
      specialize (H29 _ LIN); split_ex; split_ands.
      unfold msg_to_this_user, msg_destination_user; context_map_rewrites.
      destruct (cipher_to_user x ==n cipher_to_user c); eauto.
      right; intros; process_nonce_ok.
  Qed.

    Lemma adv_message_queue_ok_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs gks msgs,
        adv_message_queue_ok usrs cs gks msgs
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_message_queue_ok
            (clean_users honestk cs usrs)
            (clean_ciphers honestk cs)
            (clean_keys honestk gks)
            (clean_adv_msgs honestk cs msgs).
    Proof.
      unfold adv_message_queue_ok; intros; subst.
      rewrite Forall_forall in *; intros.
      apply filter_In in H0; split_ands; destruct x.
      specialize (H _ H0); simpl in *; split_ands.

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
          end; unfold msg_honestly_signed, msg_signing_key, msg_cipher_id in *; destruct c; try discriminate;
          clean_context.

      - unfold not; intros.
        cases (cs $? cid); try contradiction; clean_context.
        apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; eauto;
          contra_map_lookup.

      - unfold findKeysCrypto in *.
        cases (cs $? c_id); try discriminate.
        cases (clean_ciphers (findUserKeys usrs) cs $? c_id); clean_map_lookups.
        apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; contra_map_lookup; eauto.
        destruct c0; clean_map_lookups; specialize_msg_ok.
        rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in Heq; split_ands.
        encrypted_ciphers_prop.
        destruct kp;
          match goal with
          | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _] =>
            specialize (H _ _ ARG)
          end; try contradiction; intuition eauto; try discriminate.
        cases (gks $? k); try contradiction.
        apply clean_keys_keeps_honest_key with (honestk := findUserKeys usrs) in Heq; eauto; contra_map_lookup.

      - cases (cs $? c_id); try discriminate.
        cases ( clean_ciphers (findUserKeys usrs) cs $? c_id ); try discriminate; clean_context.
        eapply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs) in Heq; eauto; clean_map_lookups.
        unfold not; intros.
        assert (gks $? cipher_signing_key c0 <> None) by eauto.
        cases (gks $? cipher_signing_key c0); try contradiction.
        eapply clean_keys_keeps_honest_key with (honestk := findUserKeys usrs) in Heq0; eauto; contra_map_lookup.

      - unfold msg_filter, msg_honestly_signed in *.
        split_ex; split_ands.
        simpl in H6; split_ors; split_ex; split_ands;
          subst; try contradiction; context_map_rewrites;
            eexists; split; eauto.

        + left; split; eauto.
          rewrite cipher_honestly_signed_honest_keyb_iff in *;
            unfold honest_keyb in *.
          cases (findUserKeys usrs $? cipher_signing_key x); try discriminate; destruct b; try discriminate.
          
        + right; do 3 eexists; split; eauto.
          split.
          eapply clean_users_cleans_user; eauto.
          split; eauto.
          simpl; split; eauto.
          split.
          eapply clean_users_cleans_user; eauto.
          simpl.


          assert (
              {List.In (cipher_nonce x) (from_nons x2)} + {~ List.In (cipher_nonce x) (from_nons x2)}).
          apply in_dec; eauto using msg_seq_eq.

          destruct H6; eauto.
          split_ors; try contradiction.

          right; rewrite Exists_exists in *.
          split_ex; destruct x3.

          split_ands.
          eapply list_in_msgs_list_in_cleaned_msgs_not_in_froms
            with (honestk := findUserKeys usrs) (honestk' := findUserKeys (clean_users (findUserKeys usrs) cs usrs)) in H6; eauto.
          split_ex; eexists; split; eauto.
          simpl; eauto 9.
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
        | [ K : NatMap.Map.key, H : (forall k : NatMap.Map.key, _) |- _ ] => specialize (H K)
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

    Lemma honest_users_only_honest_keys_after_cleaning :
      forall {A} (usrs : honest_users A) honestk cs,
        honest_users_only_honest_keys usrs
        -> honestk = findUserKeys usrs
        -> honest_users_only_honest_keys (clean_users honestk cs usrs).
    Proof.
      intros.
      unfold honest_users_only_honest_keys in *; intros.
      apply clean_users_cleans_user_inv in H1; split_ex.
      simpl in *.
      specialize (H _ _ H1); simpl in *.
      rewrite H3 in H2.
      apply clean_key_permissions_inv in H2; split_ands.
      specialize (H _ _ H2).
      pose proof (findUserKeys_clean_users_correct usrs cs k_id);
        context_map_rewrites; subst; eauto.
    Qed.

    Lemma ok_adv_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : <<(Base B)>>),
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
                    , honest_nonces_ok_after_cleaning
                    (* , adv_message_queue_ok_after_cleaning *)
                    , adv_no_honest_keys_after_cleaning
                    , honest_users_only_honest_keys_after_cleaning.
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
      encrypted_ciphers_prop; eauto.
      rewrite merge_keys_addnl_honest; eauto.
    Qed.

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
          unfold honest_cipher_filter_fn, cipher_honestly_signed in HCFF; encrypted_ciphers_prop;
            erewrite !clean_ciphers_keeps_honest_cipher; eauto.
        + assert (honest_cipher_filter_fn honestk y c = false) as HCFF by assumption.
          unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_keyb in HCFF.
          encrypted_ciphers_prop;
            try
              match goal with
              | [ H : honestk $? _ = _ |- _ ] => rewrite H in HCFF; discriminate
              end.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb;
              solve_simple_maps; eauto.
          * erewrite !clean_ciphers_eliminates_dishonest_cipher; eauto.
            unfold cipher_signing_key, honest_keyb;
              solve_simple_maps; eauto.
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
      forall {A} (usrs : honest_users A) k_id msgs cs gks,
           adv_message_queue_ok usrs cs gks msgs
        -> ~ In k_id gks
        -> clean_adv_msgs (findUserKeys usrs $+ (k_id, true)) cs msgs
          = clean_adv_msgs (findUserKeys usrs) cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H; split_ands.
      cases (msg_honestly_signed (findUserKeys usrs) cs c); simpl in *;
            match goal with
            | [ H : msg_honestly_signed (findUserKeys usrs) cs c = ?tf |- _] =>
              assert (msg_honestly_signed (findUserKeys usrs $+ (k_id,true)) cs c = tf)
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
      forall {A B} (usrs : honest_users A) (adv : user_data B) k_id cs gks b,
        ~ In k_id gks
        -> permission_heap_good gks (key_heap adv)
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> clean_adv adv (findUserKeys usrs $+ (k_id, true)) cs b = clean_adv adv (findUserKeys usrs) cs b.
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
      forall {t} (msg : crypto t) cs msg_to froms pat honestk,
        msg_accepted_by_pattern cs froms pat msg_to msg
        -> msg_honestly_signed honestk cs msg = true
        -> msg_accepted_by_pattern (clean_ciphers honestk cs) froms pat msg_to msg.
    Proof.
      intros.
      unfold msg_honestly_signed in *.
      invert H; econstructor; simpl in *; context_map_rewrites; eauto.
    Qed.
    
    Lemma message_not_accepted_by_pattern_same_after_cleaning :
      forall {t} (msg : crypto t) cs msg_to froms pat honestk,
        ~ msg_accepted_by_pattern cs froms pat msg_to msg
        -> ~ msg_accepted_by_pattern (clean_ciphers honestk cs) froms pat msg_to msg.
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
      forall {A} (usrs : honest_users A) msgs cs c_id c gks,
        ~ In c_id cs
        -> adv_message_queue_ok usrs cs gks msgs
        -> clean_adv_msgs (findUserKeys usrs) (cs $+ (c_id,c)) msgs
          = clean_adv_msgs (findUserKeys usrs) cs msgs.
    Proof.
      unfold clean_adv_msgs; induction msgs; intros; eauto; simpl; destruct a.
      invert H0; split_ands.
      cases (msg_honestly_signed (findUserKeys usrs) cs c0);
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

    Lemma clean_messages_keeps_signed_addressed_unseen_nonce :
      forall t honestk u_id cs c_id c froms msgs,
        @msg_signed_addressed honestk cs (Some u_id) t (SignedCiphertext c_id) = true
        -> cs $? c_id = Some c
        -> ~ List.In (cipher_nonce c) froms
        -> clean_messages honestk cs (Some u_id) froms (existT _ t (SignedCiphertext c_id) :: msgs)
          = existT _ t (SignedCiphertext c_id) ::
                   clean_messages honestk cs (Some u_id) (@updateTrackedNonce t (Some u_id) froms cs (SignedCiphertext c_id)) msgs.
    Proof.
      intros; unfold updateTrackedNonce.
      unfold clean_messages at 1; unfold clean_messages'; simpl.
      rewrite H; context_map_rewrites.
      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H1; rewrite H1.
      unfold msg_signed_addressed in H; rewrite andb_true_iff in H; split_ands.
      unfold msg_to_this_user, msg_destination_user in H2; context_map_rewrites.
      destruct (cipher_to_user c ==n u_id); try discriminate.
      destruct (u_id ==n cipher_to_user c); try discriminate; subst; try contradiction.
      rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; trivial.
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

    Hint Resolve
         clean_messages_keeps_signed_addressed_unseen_nonce
         clean_key_permissions_keeps_honest_permission
         msg_nonce_ok_none_updateTrackedNonce_idempotent
         updateRecvNonce_clean_ciphers_honestly_signed.
(* <<<<<<< HEAD *)

    Lemma honest_silent_recv_implies_honest_or_no_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs : honest_users A) (adv : user_data B) usrs__s cs__s
        cs gks  u_id honestk pat ks qmsgs mycs froms froms' sents cur_n b,
        ~ msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> honestk = findUserKeys usrs
        -> froms' = (if msg_signed_addressed honestk cs (Some u_id) msg
                   then updateTrackedNonce (Some u_id) froms cs msg
                   else froms)
        -> cs__s = clean_ciphers honestk cs
        -> usrs__s = clean_users honestk cs usrs
        -> step_user Silent (Some u_id)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
(* ======= *)
    
(*     Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv : *)
(*       forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
(*                 gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' (b: <<(Base B)>>), *)
(*         step_user lbl suid bd bd' *)
(*         -> suid = Some u_id *)
(*         -> forall (cmd : user_cmd C) cs__s usrs__s honestk, *)
(*           honestk = findUserKeys usrs *)
(*           -> cs__s = clean_ciphers honestk cs *)
(*           -> usrs__s = clean_users honestk cs usrs *)
(*           -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*           -> encrypted_ciphers_ok honestk cs gks *)
(*           -> user_cipher_queues_ok cs honestk usrs *)
(*           -> message_queues_ok cs usrs gks *)
(*           -> keys_and_permissions_good gks usrs adv.(key_heap) *)
(*           -> adv_message_queue_ok usrs cs gks adv.(msg_heap) *)
(*           -> forall cmd' cs__s' usrs__s' honestk', *)
(*                  bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*               -> lbl = Silent *)
(*               -> forall cmdc cmdc' usrs'', *)
(*                   usrs $? u_id = Some {| key_heap := ks *)
(*                                        ; msg_heap := qmsgs *)
(*                                        ; protocol := cmdc *)
(*                                        ; c_heap := mycs *)
(*                                        ; from_nons := froms *)
(*                                        ; sent_nons := sents *)
(*                                        ; cur_nonce := cur_n |} *)
(*                   -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' *)
(*                                               ; msg_heap := qmsgs' *)
(*                                               ; protocol := cmdc' *)
(*                                               ; c_heap := mycs' *)
(*                                               ; from_nons := froms' *)
(*                                               ; sent_nons := sents' *)
(*                                               ; cur_nonce := cur_n' |}) *)
(*                   -> honestk' = findUserKeys usrs'' *)
(*                   -> cs__s' = clean_ciphers honestk' cs' *)
(*                   -> usrs__s' = clean_users honestk' cs' usrs' *)
(*                   -> encrypted_ciphers_ok honestk' cs' gks' *)
(*                   -> step_user lbl suid *)
(*                               (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks, *)
(*                                clean_key_permissions honestk ks, *)
(*                                clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*                               (usrs__s', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks', *)
(*                                clean_key_permissions honestk' ks', *)
(*                                clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*                   \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks, *)
(* >>>>>>> type-codes *)
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs),
                     mycs, froms, sents, cur_n, @Recv t pat)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms' qmsgs, mycs, froms', sents, cur_n, Recv pat)
          \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
             clean_key_permissions honestk ks,
             clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs), mycs, froms, sents, cur_n, @Recv t pat)
            = (clean_users honestk cs usrs, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
               clean_key_permissions honestk ks,
               clean_messages honestk cs (Some u_id) froms' qmsgs, mycs, froms', sents, cur_n, Recv pat).
    Proof.
      intros; subst.
      cases (msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg).

      - cases (msg_nonce_ok cs froms msg).
        + repeat
            match goal with
            | [H : msg_nonce_ok _ _ _ = _ |- _ ] =>
              unfold msg_nonce_ok in H; destruct msg; try discriminate;
                cases (cs $? c_id); try discriminate;
                  cases (count_occ msg_seq_eq froms (cipher_nonce c)); try discriminate; clean_context
            | [ H : count_occ _ _ _ = 0 |- _ ] => 
              rewrite <- count_occ_not_In in H
            end.

          left; econstructor; eauto.
          rewrite msg_signed_addressed_true_after_cipher_cleaning; eauto; intros; eauto.

        + right; simpl.

          unfold clean_messages at 1.
          unfold clean_messages', msg_filter; simpl.
          rewrite Heq , Heq0, fold_clean_messages1', fold_clean_messages.
          repeat f_equal; eauto.
            
      - right; simpl.
        unfold clean_messages at 1.
        unfold clean_messages', msg_filter; simpl.
        rewrite Heq, fold_clean_messages1'; trivial.
    Qed.

    Lemma clean_ciphers_eq_absurd :
      forall cs honestk c_id c,
        ~ In c_id cs
        -> clean_ciphers honestk cs = clean_ciphers honestk cs $+ (c_id, c)
        -> False.
    Proof.
      intros.
      assert (Equal (clean_ciphers honestk cs) (clean_ciphers honestk cs $+ (c_id, c)))
        by (rewrite <- H0; apply Equal_refl).
      unfold Equal in H1; specialize (H1 c_id).
      clean_map_lookups; rewrite clean_ciphers_no_new_ciphers in H1; symmetry in H1; auto; clean_map_lookups.
    Qed.

    Hint Resolve clean_ciphers_eq_absurd.

    Lemma honest_silent_new_key_implies_honest_step_origuniv :
      forall {A B} (usrs : honest_users A) (adv : user_data B) 
        cs gks gks' k_id usage u_id honestk honestk' ks qmsgs mycs froms sents cur_n b keygen_cmd kt,
          gks $? k_id = None
        -> honestk = findUserKeys usrs
        -> honestk' = findUserKeys usrs $+ (k_id,true)
        -> gks' = gks $+ (k_id, {| keyId := k_id; keyUsage := usage; keyType := kt |})
        -> ( (keygen_cmd = GenerateAsymKey usage /\ kt = AsymKey)
          \/ (keygen_cmd = GenerateSymKey usage /\ kt = SymKey) )
        -> message_queues_ok cs usrs gks
        -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, keygen_cmd)
                    (  clean_users honestk' cs usrs
                     , clean_adv adv honestk' cs b
                     , clean_ciphers honestk' cs
                     , clean_keys honestk' gks'
                     , clean_key_permissions honestk' (add_key_perm k_id true ks)
                     , clean_messages honestk' cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, @Return (Base Access) (k_id,true) ).
    Proof.
      intros; split_ors; subst;
        msg_queue_prop;
        keys_and_permissions_prop;
        erewrite clean_users_new_honest_key_idempotent
        , clean_ciphers_new_honest_key_idempotent
        , clean_messages_new_honest_key_idempotent
        , clean_adv_new_honest_key_idempotent
        , clean_key_permissions_new_honest_key
        ; eauto;
          repeat
            match goal with
            | [ |- step_user _ _ _ _ ] => econstructor
            | [ |- ~ In ?kid ?ks ] => cases (ks $? k_id); clean_map_lookups
            | [ H : permission_heap_good _ ?ks , ARG : ?ks $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG); split_ex; contra_map_lookup
            end; eauto using clean_keys_adds_no_keys.
    Qed.

    Lemma honest_silent_decrypt_implies_honest_step_origuniv :
      forall {t A B} (usrs : honest_users A) (adv : user_data B) (msg : message t)
        cs c_id gks k__encid k__signid kp nonce msg_to u_id honestk honestk' ks qmsgs mycs froms sents cur_n b,
        honestk = findUserKeys usrs
        -> honestk' = honestk $k++ findKeysMessage msg
        -> cs $? c_id = Some (SigEncCipher k__signid k__encid msg_to nonce msg)
        -> ks $? k__signid = Some kp
        -> ks $? k__encid = Some true
        -> List.In c_id mycs
        -> user_cipher_queues_ok cs honestk usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, Decrypt (SignedCiphertext c_id) )
                    (  clean_users honestk' cs usrs
                     , clean_adv adv honestk' cs b
                     , clean_ciphers honestk' cs
                     , clean_keys honestk' gks
                     , clean_key_permissions honestk' (ks $k++ findKeysMessage msg)
                     , clean_messages honestk' cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, @Return (Message t) msg ).
    Proof.
      intros; subst.

      assert (findUserKeys usrs $? k__encid = Some true) by eauto 2.
      user_cipher_queues_prop;
        encrypted_ciphers_prop;
        clean_map_lookups.

      rewrite merge_keys_addnl_honest by eauto.
      econstructor; eauto 2; eauto.

      rewrite clean_key_permissions_distributes_merge_key_permissions.
      apply map_eq_Equal; unfold Equal; intros y.
      solve_perm_merges; eauto;
        repeat match goal with
               | [ H : clean_key_permissions _ (findKeysMessage msg) $? y = Some _ |- _ ] => apply clean_key_permissions_inv in H
               | [ H : clean_key_permissions _ (findKeysMessage msg) $? y = None |- _ ] => eapply clean_key_permissions_inv' in H; eauto 2
               | [ H : (forall _ _, findKeysMessage msg $? _ = Some _ -> _), ARG : findKeysMessage msg $? _ = Some _ |- _ ] =>
                 specialize (H _ _ ARG)
               | [ H : honest_perm_filter_fn _ _ _ = _ |- _] => unfold honest_perm_filter_fn in H; context_map_rewrites
               end; clean_map_lookups; eauto.
    Qed.

    Lemma honest_cipher_filter_fn_nochange_pubk :
      forall honestk pubk k v,
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> honest_cipher_filter_fn honestk k v =
          honest_cipher_filter_fn (honestk $k++ pubk) k v.
    Proof.
      unfold honest_cipher_filter_fn; intros;
        unfold cipher_honestly_signed;
        cases v; unfold honest_keyb; simpl;
          solve_perm_merges; auto;
            match goal with
            | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG); split_ands; subst
            end; clean_map_lookups; eauto.
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
        solve_perm_merges; eauto;
          match goal with
          | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; split_ands; subst; clean_map_lookups; eauto.
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

        assert (honestk $k++ pubk $? cipher_signing_key c = Some true) as RW by solve_perm_merges.
        rewrite RW; f_equal; eauto.

      - cases (honestk $? cipher_signing_key c); try discriminate.
        + destruct b; try discriminate.
          repeat ( maps_equal1 || solve_perm_merges1 );
            f_equal; eauto.
          
          destruct b; solve_perm_merges; eauto.

          match goal with
          | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; split_ands; subst; clean_map_lookups; eauto.
          
       + solve_perm_merges; eauto;
           f_equal; eauto.
         destruct b; solve_perm_merges; eauto.

         match goal with
         | [ H : (forall _ _, ?pubk $? _ = Some _ -> _), ARG : ?pubk $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
         end; split_ands; subst; clean_map_lookups; eauto.
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
        cases (pubk $? y); solve_perm_merges; eauto.
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
            | _ => solve_perm_merges
            end; eauto.
          cases (pubk $? y);
            match goal with
            | [ PUB : pubk $? y = Some ?b, H : (forall kp, Some ?b = Some kp -> ?conc) |- _ ] =>
              assert (Some b = Some b) as SOME by trivial; apply H in SOME; split_ands; discriminate
            | _ => solve_perm_merges
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
      forall {A} (usrs: honest_users A) honestk cs pubk u_id ks cmd qmsgs mycs froms sents cur_n u_d u_d',
        (forall k kp, pubk $? k = Some kp -> honestk $? k = Some true /\ kp = false)
        -> u_d = {| key_heap := ks $k++ pubk
                 ; protocol := cmd
                 ; msg_heap := qmsgs
                 ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        -> u_d' = {| key_heap := clean_key_permissions honestk (ks $k++ pubk)
                  ; protocol := cmd
                  ; msg_heap := clean_messages honestk cs (Some u_id) froms qmsgs
                  ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
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
            solve_perm_merges; eauto.

      rewrite H1; trivial.
    Qed.

    Lemma honest_labeled_step_nochange_clean_ciphers_users_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a b,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                /\ clean_users (findUserKeys usrs'') cs' usrs'' =
                  clean_users (findUserKeys usrs') cs' usrs' $+ (u_id, {| key_heap := clean_key_permissions (findUserKeys usrs') ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := clean_messages (findUserKeys usrs') cs' suid froms' qmsgs'
                                                                    ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
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
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
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

    Hint Resolve updateTrackedNonce_clean_ciphers_idempotent_honest_msg.


    Lemma clean_messages_keeps_hon_signed :
      forall {t} qmsgs (msg : crypto t) honestk cs rec_u_id froms u_id sents n,
        honest_nonce_tracking_ok cs u_id sents n rec_u_id froms qmsgs
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

      - unfold clean_messages'; simpl; rewrite H0;
          context_map_rewrites; process_nonce_ok; eauto.
        unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H0; rewrite andb_true_iff in H0;
          context_map_rewrites;
          split_ands.
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
            split.
            ** econstructor; process_nonce_ok; eauto.
            ** split; eauto.
               intros.
               specialize (H5 _ _ H3 H6); split_ands; split; eauto.
               intros.
               specialize (H7 H10 H11); split_ands.
               invert H12.
               split; eauto.
               unfold not; intros.
               unfold msg_signed_addressed in Heq; rewrite andb_true_iff in Heq;
                 split_ands.
               split_ors.
               rewrite H14 in H13; invert H13.
               unfold msg_nonce_not_same in H14; assert ( cipher_nonce c0 <> cipher_nonce c ) by eauto.
               simpl in H10; split_ors; congruence.
                   
          * invert H3.
            eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.
              
        + invert H3.
          eapply IHqmsgs; eauto 6; repeat (apply conj); eauto 6; process_nonce_ok.

    Qed.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a (b : <<(Base B)>>) suid,
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> action_adversary_safe (findUserKeys usrs) cs a
        -> message_queues_ok cs usrs gks
        -> honest_nonces_ok cs usrs
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall cmdc cmdc' usrs'' honestk',
              usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
              -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
              -> honestk' = findUserKeys usrs''
              -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv',
                  cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' cs' usrs'
                  -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
                  -> lbl = Action a
                  -> pwless_adv = {| key_heap := key_heap adv
                                  ; protocol := Return b
                                  ; msg_heap := adv.(msg_heap)
                                  ; c_heap   := adv.(c_heap)
                                  ; from_nons := adv.(from_nons)
                                  ; sent_nons := adv.(sent_nons)
                                  ; cur_nonce := adv.(cur_nonce) |}
                  -> pwless_adv' = {| key_heap := key_heap adv'
                                   ; protocol := Return b
                                   ; msg_heap := adv'.(msg_heap)
                                   ; c_heap   := adv'.(c_heap)
                                   ; from_nons := adv'.(from_nons)
                                   ; sent_nons := adv'.(sent_nons)
                                   ; cur_nonce := adv'.(cur_nonce) |}
                  -> step_user (strip_label honestk cs lbl) suid
                              (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd').
    Proof.
      induction 1; inversion 8; inversion 6; intros;
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
          unfold updateTrackedNonce.
          unfold msg_nonce_ok; context_map_rewrites.
          rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H12;
            rewrite H12 , fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; eauto.

          unfold msg_to_this_user, msg_destination_user in MSG_TO; context_map_rewrites.
          destruct (cipher_to_user x2 ==n u_id); subst; try discriminate.
          destruct (cipher_to_user x2 ==n cipher_to_user x2); try contradiction; trivial.

        + erewrite honest_message_findKeysCrypto_same_after_cleaning; eauto.

      - eapply StepSend with (rec_u0 := {| key_heap := clean_key_permissions (findUserKeys usrs) rec_u.(key_heap)
                                         ; protocol := rec_u.(protocol)
                                         ; msg_heap := clean_messages (findUserKeys usrs) cs' (Some rec_u_id) rec_u.(from_nons) rec_u.(msg_heap)
                                         ; c_heap   := rec_u.(c_heap)
                                         ; from_nons := rec_u.(from_nons)
                                         ; sent_nons := rec_u.(sent_nons)
                                         ; cur_nonce := rec_u.(cur_nonce) |});
          try (erewrite <- honest_message_findKeysCrypto_same_after_cleaning by solve [ eauto ] );
          eauto.
        
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl.

        Ltac count_occ_list_in1 :=
          match goal with
          | [ H : ~ List.In ?x ?xs |- context [ count_occ _ ?xs ?x ] ] => rewrite count_occ_not_In in H; rewrite H
          | [ H : count_occ _ ?xs ?x = 0 |- context [ ~ List.In ?x ?xs ] ] => rewrite count_occ_not_In
          end.

        erewrite clean_messages_keeps_hon_signed; eauto.
        unfold msg_signed_addressed; rewrite andb_true_iff; eauto.

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
(* <<<<<<< HEAD *)
(*                 gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a a' (b : B) honestk, *)
(* ======= *)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a a' (b : <<(Base B)>>) honestk,
(* >>>>>>> type-codes *)
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> honestk = findUserKeys usrs
        -> action_adversary_safe honestk cs a
        -> honest_nonces_ok cs usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok cs usrs gks
        -> forall (cmd : user_cmd C) cs__s usrs__s,
            cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall cmd' cs__s' usrs__s' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Action a
              -> forall cmdc,
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                         ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> a' = strip_action (findUserKeys usrs) cs a
                  -> step_user (Action a') suid
                              (usrs__s, clean_adv adv (findUserKeys usrs) cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks, clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs__s', clean_adv adv' (findUserKeys usrs) cs' b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks', clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd').
    Proof.
      induction 1; inversion 9; inversion 4; intros;
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
        count_occ_list_in1.

        econstructor; eauto.

        + simpl; context_map_rewrites.
          unfold msg_to_this_user, msg_destination_user in MSGTO;
            context_map_rewrites.
          destruct (cipher_to_user x0 ==n u_id); subst; try discriminate.
          destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
          rewrite H2; simpl.
          rewrite fold_clean_messages2', clean_messages'_fst_pull.
          trivial.

        +  rewrite clean_key_permissions_distributes_merge_key_permissions.
            
           assert (clean_key_permissions (findUserKeys usrs') (@findKeysCrypto t0 cs' (SignedCiphertext x))
                   = @findKeysCrypto t0 (clean_ciphers (findUserKeys usrs') cs') (SignedCiphertext x)) as RW.

            unfold msg_honestly_signed in MHS; simpl in *;
              context_map_rewrites.
            assert (cs' $? x = Some x0) as CS by assumption.
            apply clean_ciphers_keeps_honest_cipher with (honestk := findUserKeys usrs') in CS; eauto.
            context_map_rewrites.

            msg_queue_prop. specialize_msg_ok.
            unfold message_no_adv_private in H12; simpl in H12; context_map_rewrites.
            destruct x0; eauto.
            apply map_eq_Equal; unfold Equal; intros.
            cases (findKeysMessage msg $? y); eauto.
            ** apply clean_key_permissions_keeps_honest_permission; eauto.
               unfold honest_perm_filter_fn.
               simpl in H0; context_map_rewrites.
               encrypted_ciphers_prop.
               specialize (H24 _ _ Heq); split_ands; context_map_rewrites; trivial.
            ** apply clean_key_permissions_adds_no_permissions; auto.
            ** rewrite RW; trivial.

      - eapply StepSend with (rec_u0 := {| key_heap := clean_key_permissions (findUserKeys usrs) rec_u.(key_heap)
                                         ; protocol := rec_u.(protocol)
                                         ; msg_heap := clean_messages (findUserKeys usrs) cs' (Some rec_u_id) rec_u.(from_nons) rec_u.(msg_heap)
                                         ; c_heap   := rec_u.(c_heap)
                                         ; from_nons := rec_u.(from_nons)
                                         ; sent_nons := rec_u.(sent_nons)
                                         ; cur_nonce := rec_u.(cur_nonce) |});
          try (erewrite <- honest_message_findKeysCrypto_same_after_cleaning by solve [ eauto ] );
          eauto.

        + unfold keys_mine in *; intros.

          split_ex; subst.
          specialize (H0 _ _ H7).

          unfold msg_honestly_signed, msg_signing_key in H; context_map_rewrites.
          encrypted_ciphers_prop; simpl in *; clean_map_lookups;
            match goal with
            | [ H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _), ARG : findKeysMessage _ $? _ = Some _ |- _ ] =>
              specialize (H _ _ ARG)
            end; split_ors; subst; eauto.

        + eapply clean_users_cleans_user; eauto.
        + simpl.
          rewrite clean_users_add_pull; simpl; eauto.
          erewrite clean_messages_keeps_hon_signed; eauto.
          (* unfold honest_nonces_ok in H9; process_nonce_ok. *)
          unfold msg_signed_addressed.
          rewrite andb_true_iff; split_ex; subst; eauto.
          
        + unfold clean_adv, addUserKeys; simpl.

          f_equal; eauto.
          rewrite clean_key_permissions_distributes_merge_key_permissions.
          apply map_eq_Equal; unfold Equal; intros.

          assert (clean_key_permissions (findUserKeys usrs) (findKeysCrypto cs' msg) $? y
                  = findKeysCrypto cs' msg $? y) as RW.

          split_ex.
          rewrite H6 in H; unfold msg_honestly_signed in H.
          match goal with
          | [ H : match ?mtch with _ => _ end = _ |- _ ] => cases mtch; try discriminate
          end.
          subst.
          simpl in Heq; context_map_rewrites; clean_context.
          encrypted_ciphers_prop; simpl in *; context_map_rewrites; eauto.
          cases (findKeysMessage msg $? y); eauto using clean_key_permissions_adds_no_permissions.
          specialize (H15 _ _ Heq); split_ands; subst; eauto.

          * cases ( clean_key_permissions (findUserKeys usrs) (key_heap adv) $? y );
              cases ( findKeysCrypto cs' msg $? y );
              solve_perm_merges; eauto.
    Qed.

    Lemma honest_users_only_honest_keys_nochange_keys :
      forall {A} u_id (usrs : honest_users A) (cmd cmd' : user_cmd (Base A))
                ks qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        honest_users_only_honest_keys usrs
        -> usrs $? u_id = Some {| key_heap := ks;
                                 protocol := cmd;
                                 msg_heap := qmsgs;
                                 c_heap := mycs;
                                 from_nons := froms;
                                 sent_nons := sents;
                                 cur_nonce := cur_n |}
        -> honest_users_only_honest_keys
            (usrs $+ (u_id, {| key_heap := ks;
                               protocol := cmd';
                               msg_heap := qmsgs';
                               c_heap := mycs';
                               from_nons := froms';
                               sent_nons := sents';
                               cur_nonce := cur_n' |})).
    Proof.
      intros.
      unfold honest_users_only_honest_keys in *;
        autorewrite with find_user_keys;
        intros;
        eauto.
      
      destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto 2.
    Qed.

    Hint Resolve honest_users_only_honest_keys_nochange_keys.

    Lemma merge_perms_true_either_true :
      forall ks1 ks2 k_id,
        ks1 $? k_id = Some true \/ ks2 $? k_id = Some true
        -> ks1 $k++ ks2 $? k_id = Some true.
    Proof.
      intros; split_ors; solve_perm_merges.
    Qed.

    Hint Resolve merge_perms_true_either_true.

    Lemma honest_users_only_honest_keys_gen_key :
      forall {A} u_id (usrs : honest_users A) (cmd cmd' : user_cmd (Base A)) k_id
                 ks qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        honest_users_only_honest_keys usrs
        -> usrs $? u_id = Some {| key_heap := ks;
                                 protocol := cmd;
                                 msg_heap := qmsgs;
                                 c_heap := mycs;
                                 from_nons := froms;
                                 sent_nons := sents;
                                 cur_nonce := cur_n |}
        -> honest_users_only_honest_keys
            (usrs $+ (u_id, {| key_heap := add_key_perm k_id true ks;
                               protocol := cmd';
                               msg_heap := qmsgs';
                               c_heap := mycs';
                               from_nons := froms';
                               sent_nons := sents';
                               cur_nonce := cur_n' |})).
    Proof.
      intros.
      unfold honest_users_only_honest_keys in *; intros.
      assert (add_key_perm k_id true ks = ks $+ (k_id,true))
        as RW1 by (unfold add_key_perm; cases (ks $? k_id); eauto).
      assert (ks $+ (k_id,true) = ks $k++ ($0 $+ (k_id,true))) as RW2 by eauto.
      rewrite RW1, RW2; clear RW1 RW2.
      rewrite findUserKeys_readd_user_addnl_keys; eauto.

      destruct (u_id ==n u_id0);
        destruct (k_id ==n k_id0); subst;
          clean_map_lookups; simpl in *;
            eauto.

      specialize (H _ _ H0); simpl in H.
      unfold add_key_perm in *.
      cases (ks $? k_id); clean_map_lookups; eauto.
    Qed.

    Hint Resolve honest_users_only_honest_keys_gen_key.

    Lemma next_action_next_cmd_safe :
      forall honestk cs uid froms sents {A} (cmd : user_cmd A) {B} (cmd__n : user_cmd B),
        nextAction cmd cmd__n
        -> next_cmd_safe honestk cs uid froms sents cmd
        -> next_cmd_safe honestk cs uid froms sents cmd__n.
    Proof.
      intros.
      unfold next_cmd_safe in *; intros.
      specialize (H0 _ _ H).
      apply nextAction_couldBe in H.
      cases cmd__n; try contradiction; invert H1; eauto.
    Qed.

    Lemma next_action_next_cmd_safe_bind :
      forall honestk cs uid froms sents {A B} (cmd1 : user_cmd A) (cmd2 : <<A>> -> user_cmd B),
        next_cmd_safe honestk cs uid froms sents (x <- cmd1 ; cmd2 x)
        -> next_cmd_safe honestk cs uid froms sents cmd1.
    Proof.
      intros.
      unfold next_cmd_safe in *; intros; eauto.
      eapply H; econstructor; eauto.
    Qed.

    Hint Resolve
         next_action_next_cmd_safe
         next_action_next_cmd_safe_bind.

    Ltac process_next_cmd_safe :=
      try
        match goal with
        | [ H : next_cmd_safe _ _ _ _ _ ?c |- _] =>
          let NA := fresh "NA" in 
          match c with
          | (Bind (Return ?r) ?c2) =>
            assert (nextAction c (Return r)) as NA by (repeat econstructor)
          | _ =>
            assert (nextAction c c) as NA by econstructor
          end
          ; specialize (H _ _ NA)
          ; simpl in H
          ; split_ex
        end.

    Lemma honest_users_only_honest_keys_honest_steps :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
          honestk = findUserKeys usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honest_users_only_honest_keys usrs
          -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok  cs honestk usrs
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_nons := froms
                                       ; sent_nons := sents
                                       ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_nons := froms'
                                              ; sent_nons := sents'
                                              ; cur_nonce := cur_n' |})
                  -> honest_users_only_honest_keys usrs''.
    Proof.
      induction 1; inversion 3; inversion 5; intros;
        subst;
        autorewrite with find_user_keys;
        process_next_cmd_safe;
        eauto;
        clean_context.

      - unfold honest_users_only_honest_keys in *; intros.
        destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto;
          simpl in *;
          rewrite findUserKeys_readd_user_addnl_keys; eauto.

        specialize (H10 _ _ H26); simpl in *.
        solve_perm_merges;
          try
            match goal with
            | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
            end; clean_map_lookups; eauto;
            assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by eauto.

        + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
          unfold msg_cipher_id in H2; destruct msg; try discriminate;
            clean_context; simpl in *.
          cases (cs' $? x); try discriminate.
          clean_context; invert MHS.
          destruct c; simpl in *; clean_map_lookups; eauto.
          encrypted_ciphers_prop; eauto.
          specialize (H12 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

        + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
          unfold msg_cipher_id in H2; destruct msg; try discriminate;
            clean_context; simpl in *.
          cases (cs' $? x); try discriminate.
          clean_context; invert MHS.
          destruct c; simpl in *; clean_map_lookups; eauto.
          encrypted_ciphers_prop; eauto.
          specialize (H12 _ _ H0); split_ands; subst; clean_map_lookups; eauto.

      - unfold honest_users_only_honest_keys in *; intros.
        assert (rec_u_id <> u_id) by eauto.
        destruct (u_id ==n u_id0); destruct (u_id ==n rec_u_id);
          subst;
          try contradiction;
          clean_map_lookups;
          simpl in *;
          eauto.

        + specialize (H10 _ _ H26 _ _ H12).
          autorewrite with find_user_keys; eauto.

        + destruct (u_id0 ==n rec_u_id); subst;
            clean_map_lookups;
            autorewrite with find_user_keys;
            eauto 2.

      - user_cipher_queues_prop.
        encrypted_ciphers_prop.
        unfold honest_users_only_honest_keys in *; intros.
        rewrite findUserKeys_readd_user_addnl_keys; eauto.
        destruct (u_id ==n u_id0);
          subst;
          try contradiction;
          clean_map_lookups;
          simpl in *;
          eauto.

        apply merge_perms_split in H6; split_ors;
          match goal with
          | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; eauto.
    Qed.

    Lemma honest_users_only_honest_keys_adv_steps :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' suid,
        step_user lbl suid bd bd'
        -> forall (cmd : user_cmd C) honestk,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> suid = None
          -> honestk = findUserKeys usrs
          -> honest_users_only_honest_keys usrs
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honest_users_only_honest_keys usrs'.
    Proof.
      induction 1; inversion 1; inversion 4;
        intros; subst;
          eauto.

      clean_context.
      destruct rec_u; eauto.
    Qed.

    Lemma honest_cmd_implies_safe_action :
      forall {A B C} (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
                u_id suid bd bd' lbl a__r (cmd cmd' : user_cmd C)
                ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        step_user lbl suid bd bd'
      -> suid = Some u_id
      -> lbl = Action a__r
      -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc,
          usrs $? u_id = Some {| key_heap := ks
                                 ; protocol := cmdc
                                 ; msg_heap := qmsgs
                                 ; c_heap := mycs
                                 ; from_nons := froms
                                 ; sent_nons := sents
                                 ; cur_nonce := cur_n |}
          -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd
          -> action_adversary_safe (findUserKeys usrs) cs a__r.
    Proof.
      induction 1; inversion 3; inversion 1; intros;
        try discriminate; subst;
          process_next_cmd_safe;
          eauto;
          clean_context;
          eauto 12.
    Qed.

    Lemma honest_cmds_implies_safe_actions :
      forall {A B} (U U' : universe A B) a__r,
        step_universe U (Action a__r) U'
        -> honest_cmds_safe U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) a__r.
    Proof.
      invert 1; intros; eauto.
      unfold honest_cmds_safe in H.
      destruct U; destruct userData; simpl in *.
      specialize (H _ _ _ eq_refl H0); simpl in *.
      eapply honest_cmd_implies_safe_action; eauto.
      reflexivity.
    Qed.

    Lemma labeled_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B) lbl a,
        step_universe U lbl U'
        -> lbl = Action a
        -> honest_cmds_safe U
        -> universe_ok U
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      subst.
      generalize (honest_cmds_implies_safe_actions H H1); intros.
      invert H; try discriminate.
      unfold universe_ok, adv_universe_ok in *.
      destruct U; destruct userData.
      unfold build_data_step in *; simpl in *.
      split_ands.
      specialize (H1 _ _ _ eq_refl H4);
        simpl in *.
      intuition       
        eauto using honest_labeled_step_keys_and_permissions_good
                  , honest_labeled_step_user_cipher_queues_ok
                  , honest_labeled_step_message_queues_ok
                  , honest_labeled_step_adv_cipher_queue_ok
                  , honest_labeled_step_adv_message_queue_ok
                  , honest_labeled_step_adv_no_honest_keys
                  , honest_labeled_step_honest_nonces_ok.

      eapply honest_users_only_honest_keys_honest_steps; eauto.
    Qed.

    Lemma silent_step_adv_univ_implies_adv_universe_ok :
      forall {A B} (U U' : universe A B),
        step_universe U Silent U'
        -> honest_cmds_safe U
        -> encrypted_ciphers_ok (findUserKeys U.(users)) U.(all_ciphers) U.(all_keys)
        -> adv_universe_ok U
        -> adv_universe_ok U'.
    Proof.
      intros.
      unfold honest_cmds_safe in *.
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
      eapply honest_silent_step_honest_nonces_ok; eauto.

      specialize (H0 _ _ _ eq_refl H3); simpl in H0.
      eapply honest_users_only_honest_keys_honest_steps; eauto.
      
      eapply adv_step_keys_good; eauto.
      eapply adv_step_user_cipher_queues_ok; eauto.
      
      eapply adv_step_message_queues_ok; eauto.
      eapply users_permission_heaps_good_merged_permission_heaps_good; unfold keys_and_permissions_good in *; split_ands; eauto.
      unfold keys_and_permissions_good in *; split_ands; eauto.
      
      eapply adv_step_adv_cipher_queue_ok; eauto.
      eapply adv_step_adv_message_queue_ok; eauto.
      eapply adv_step_adv_no_honest_keys; eauto.
      eapply adv_step_honest_nonces_ok; eauto.
      eapply honest_users_only_honest_keys_adv_steps; eauto.
    Qed.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto;
        match goal with [H : Action _ = _ |- _] => invert H end.
    Qed.

    Lemma honest_labeled_step_nochange_adversary_protocol :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> adv.(protocol) = adv'.(protocol).
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
    Qed.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
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
        -> exists (u_id : user_id) u_d u_d' usrs' adv' cs' gks' ks' qmsgs' froms' sents' cur_n' mycs' cmd',
            usrs $? u_id = Some u_d
          /\ step_user (Action a) (Some u_id) (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
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
                    ; from_nons := froms'
                    ; sent_nons := sents'
                    ; cur_nonce := cur_n'
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
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                ->  clean_ciphers (findUserKeys usrs'') cs' = clean_ciphers (findUserKeys usrs') cs'
                /\ clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs' = clean_messages (findUserKeys usrs'') cs' suid froms' qmsgs'
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

        Unshelve.
        auto.
    Qed.

    Lemma honest_silent_step_nochange_clean_adv_messages :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good  gks usrs adv.(key_heap)
          -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> clean_adv_msgs (findUserKeys usrs'') cs'  adv'.(msg_heap) = clean_adv_msgs (findUserKeys usrs'') cs  adv'.(msg_heap).
    Proof.
      induction 1; inversion 2; inversion 7; intros; try discriminate; subst;
        autorewrite with find_user_keys; eauto; clean_context;
          eauto using
                clean_adv_msgs_new_honest_key_idempotent
              , clean_adv_msgs_addnl_cipher_idempotent.
    Qed.

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        -> action_adversary_safe (findUserKeys U.(users)) U.(all_ciphers) act
        -> message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        -> honest_nonces_ok U.(all_ciphers) U.(users)
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
      destruct x0; simpl in *.

      rewrite HeqUU in H4; unfold build_data_step in H4; simpl in *.
      rewrite HeqUU; unfold strip_adversary_univ; simpl; eapply StepUser with (u_id:=x).
      - simpl; eapply clean_users_cleans_user; eauto.
      - unfold build_data_step; simpl.
        eapply honest_labeled_step_advuniv_implies_honest_step_origuniv'; subst; eauto.

      - unfold buildUniverse; subst; simpl in *.
        subst; simpl in *.
        remember (x2 $+ (x, {| key_heap := x6
                             ; protocol := x12
                             ; msg_heap := x7
                             ; from_nons := x8
                             ; sent_nons := x9
                             ; cur_nonce := x10
                             ; c_heap := x11 |})) as usrs''.

        assert (clean_ciphers (findUserKeys usrs'') x4 = clean_ciphers (findUserKeys x2) x4
              /\ clean_messages (findUserKeys usrs'') x4 (Some x) x8 x7 = clean_messages (findUserKeys x2) x4 (Some x) x8 x7
              /\ clean_users (findUserKeys usrs'') x4 usrs'' =
                clean_users (findUserKeys x2) x4 x2 $+ (x, {| key_heap := clean_key_permissions (findUserKeys x2) x6
                                                         ; protocol := x12
                                                         ; msg_heap := clean_messages (findUserKeys x2) x4 (Some x) x8 x7
                                                         ; from_nons := x8
                                                         ; sent_nons := x9
                                                         ; cur_nonce := x10
                                                         ; c_heap := x11 |})
              /\ clean_adv x3 (findUserKeys usrs'') x4 b = clean_adv x3 (findUserKeys users) x4 b
              /\ clean_keys (findUserKeys usrs'') x5 = clean_keys (findUserKeys x2) x5 ).
        eapply honest_labeled_step_nochange_clean_ciphers_users_messages; eauto.
        split_ands.

        f_equal; auto.
    Qed.

    Hint Resolve dishonest_cipher_cleaned.

    Lemma  adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' froms' sents' cur_n' mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> cs__s = clean_ciphers honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.
    Qed.

    Lemma clean_keys_drops_added_dishonest_key :
      forall honestk gks k_id ku kt,
        ~ In k_id gks
        -> honestk $? k_id = None
        -> clean_keys honestk (gks $+ (k_id, {| keyId := k_id; keyUsage := ku; keyType := kt |}))
          = clean_keys honestk gks.
    Proof.
      intros; unfold clean_keys, filter; apply map_eq_Equal; unfold Equal; intros.
      rewrite fold_add; eauto.
      unfold honest_key_filter_fn; context_map_rewrites; trivial.
    Qed.

    Hint Resolve clean_keys_drops_added_dishonest_key.

    Lemma adv_step_implies_no_new_keys_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' froms' sents' cur_n' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk gks__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> honestk = findUserKeys usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)

          -> gks__s = clean_keys honestk gks
          -> forall cmd' honestk' gks__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> gks__s' = clean_keys honestk' gks'
              -> gks__s = gks__s'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; eauto;
        autorewrite with find_user_keys; eauto; clean_context;
          assert (~ In k_id gks) by (clean_map_lookups; auto);
          unfold keys_and_permissions_good in *; split_ands;
            assert (permission_heap_good gks (findUserKeys usrs')) as PHG by eauto;
            symmetry;
            cases (findUserKeys usrs' $? k_id); eauto;
              match goal with
              | [ H : findUserKeys _ $? _ = Some _ |- _ ] => specialize (PHG _ _ H); split_ex; contra_map_lookup; eauto
              end.
    Qed.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks' qmsgs' mycs' froms' sents' cur_n' bd bd' suid,
        step_user lbl suid bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
          bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), adv.(c_heap), adv.(from_nons), adv.(sent_nons), adv.(cur_nonce), cmd)
          -> suid = None
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> message_queues_ok cs usrs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> adv_cipher_queue_ok cs usrs adv.(c_heap)
          -> honest_nonces_ok cs usrs
          -> usrs__s = clean_users honestk cs usrs
          -> forall cmd' honestk' usrs__s',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' cs' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 9; intros; subst; eauto;
        autorewrite with find_user_keys;
        clean_context;
        try erewrite clean_users_addnl_cipher_idempotent; eauto.

      (* Send *)
      rewrite clean_users_add_pull; simpl.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.

      erewrite clean_users_cleans_user; eauto; f_equal.

      cases (msg_signed_addressed (findUserKeys usrs) cs' (Some rec_u_id) msg);
        eauto using clean_messages_drops_msg_signed_addressed_false.

      assert (msg_signed_addressed (findUserKeys usrs) cs' (Some rec_u_id) msg = true) as MSA by assumption.
      
      unfold msg_signed_addressed in Heq;
        rewrite andb_true_iff in Heq;
        split_ands.
      unfold msg_honestly_signed, msg_signing_key in H;
        destruct msg; try discriminate;
          cases (cs' $? c_id); try discriminate.

      unfold adv_cipher_queue_ok in H24; rewrite Forall_forall in H24.
      simpl in H1; assert (List.In c_id (c_heap adv)) as LIN by eauto.
      specialize (H24 _ LIN); split_ex; split_ands.
      clean_map_lookups; rewrite <- honest_key_honest_keyb in H; invert H.
      unfold msg_to_this_user in H4; simpl in H4; context_map_rewrites;
        cases (cipher_to_user c ==n rec_u_id); subst; try discriminate.

      unfold clean_messages at 1; unfold clean_messages'.
      rewrite fold_left_app; simpl.
      rewrite MSA; context_map_rewrites.
      rewrite !fold_clean_messages2', !fold_clean_messages.

      match goal with
      | [ |- context [match (match ?mtc with _ => _ end) with _ => _ end ] ] => cases mtc
      end; eauto; simpl.

      exfalso.
      
      split_ors; split_ex; split_ands.
      - unfold msg_signed_addressed in MSA; rewrite andb_true_iff in MSA; split_ands.
        unfold msg_honestly_signed, msg_signing_key, cipher_signing_key in H8; context_map_rewrites.
        unfold cipher_honestly_signed in H6; destruct c; simpl in H6; rewrite H6 in H8; discriminate.
      - clean_context.
        unfold honest_nonces_ok in H25.
        specialize (H25 _ _ _ _ H8 H6 H2).
        unfold honest_nonce_tracking_ok in H25; split_ands.
        specialize (H14 _ _ H5 H); split_ands.
        rewrite Forall_forall in H4; specialize (H4 _ H9).

        apply count_occ_eq_0_clean_msgs in Heq.

        split_ex; split_ands; clean_map_lookups.
        split_ors; try contradiction.
        rewrite Exists_exists in H10; split_ex; split_ands.
        rewrite Forall_forall in H17; specialize (H17 _ H10); destruct x2; split_ands; eauto.
        specialize (H17 H11).
        unfold msg_nonce_not_same in H17; unfold msg_nonce_same in H18.
        unfold msg_signed_addressed, msg_honestly_signed, msg_signing_key in H11;
          context_map_rewrites; destruct c0; try discriminate;
            cases (cs' $? c_id0); try discriminate.
        assert (cipher_nonce c <> cipher_nonce c0) by eauto.
        assert (cipher_nonce c = cipher_nonce c0) by eauto.
        congruence.
    Qed.
    
    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : simpl_universe A -> IdealWorld.universe A -> Prop)
        (cmd : user_cmd (Base B)) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs froms sents cur_n,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> R (strip_adversary U__r) U__i

        -> keys_and_permissions_good U__r.(all_keys) U__r.(users) U__r.(adversary).(key_heap)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))

        -> message_queues_ok U__r.(all_ciphers) U__r.(users) U__r.(all_keys)
        -> encrypted_ciphers_ok (findUserKeys (users U__r)) U__r.(all_ciphers) U__r.(all_keys)
        -> adv_cipher_queue_ok U__r.(all_ciphers) U__r.(users) U__r.(adversary).(c_heap)
        -> honest_nonces_ok U__r.(all_ciphers) U__r.(users)

                             
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := ks
                                                            ; protocol := cmd
                                                            ; msg_heap := qmsgs
                                                            ; c_heap   := mycs
                                                            ; from_nons := froms
                                                            ; sent_nons := sents
                                                            ; cur_nonce := cur_n |})) U__i.
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

    Lemma encrypted_ciphers_ok_new_honest_key_adv_univ :
      forall honestk honestk' cs k_id k gks gks',
        ~ In k_id gks
        -> permission_heap_good gks honestk
        -> k_id = keyId k
        -> gks' = gks $+ (k_id, k)
        -> honestk' = honestk $+ (k_id, true)
        -> encrypted_ciphers_ok honestk cs gks
        -> encrypted_ciphers_ok honestk' cs gks'.
    Proof.
      intros; subst; eapply encrypted_ciphers_ok_addnl_honest_key; eauto.
      cases (honestk $? keyId k); clean_map_lookups; eauto.
      specialize (H0 _ _ Heq); split_ex; contra_map_lookup.
    Qed.

    Hint Resolve encrypted_ciphers_ok_new_honest_key_adv_univ.
    Hint Resolve users_permission_heaps_good_merged_permission_heaps_good.
    
    Lemma honest_silent_step_adv_univ_enc_ciphers_ok :
      forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
            -> honestk = findUserKeys usrs
            -> encrypted_ciphers_ok honestk cs gks
            -> user_cipher_queues_ok cs honestk usrs
            -> keys_and_permissions_good gks usrs adv.(key_heap)
            -> next_cmd_safe honestk cs u_id froms sents cmd
            -> lbl = Silent
            -> forall cmd' usrs'',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
                -> forall cmdc cmdc' honestk',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> encrypted_ciphers_ok honestk' cs' gks'.
    Proof.
      induction 1; inversion 2; inversion 7; intros; subst;
        try discriminate;
        eauto 2;
        autorewrite with find_user_keys in *;
        keys_and_permissions_prop;
        clean_context;
        process_next_cmd_safe;
        eauto.

      - econstructor; eauto.
        eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto 2.
      - user_cipher_queues_prop; encrypted_ciphers_prop.
        rewrite merge_keys_addnl_honest; eauto.
      - econstructor; eauto.
        econstructor; eauto 2.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
      - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs')); simpl; eauto; simpl; eauto.
    Qed.

    Ltac new_key_not_in_honestk :=
      repeat
          match goal with
          | [ H : keys_and_permissions_good ?global_keys ?honusrs _ |- _ ] =>
            assert (permission_heap_good global_keys (findUserKeys honusrs))
              by (unfold keys_and_permissions_good in *; split_ands; eauto using users_permission_heaps_good_merged_permission_heaps_good);
            clear H
          | [ H1 : findUserKeys ?honusrs $? ?kid = Some _
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- _ ] =>
            specialize (H2 _ _ H1); split_ex; contra_map_lookup
          | [ H1 : ?global_keys $? ?kid = None
            , H2 : permission_heap_good ?global_keys (findUserKeys ?honusrs)
            |- ~ In ?kid (findUserKeys ?honusrs) ] =>
            cases (findUserKeys honusrs $? kid); clean_map_lookups; eauto 2
          end.

    Lemma action_adversary_safe_after_before_cleaning' :
      forall honestk honestk' cs a,
        (forall k_id, honestk' $? k_id = Some true -> honestk $? k_id = Some true)
        -> action_adversary_safe honestk' (clean_ciphers honestk cs) a
        -> action_adversary_safe honestk  cs a.
    Proof.
      intros * HONK AA.
      destruct a; unfold action_adversary_safe in *; split_ex; subst; eauto.

      - split; eauto 8.
        invert H; econstructor; eauto.
      - repeat (apply conj); eauto 8.
        + invert H.
          rewrite H4.
          rewrite <- find_mapsto_iff, clean_ciphers_mapsto_iff, find_mapsto_iff in H3;
            unfold honest_cipher_filter_fn in H3; split_ands.
          unfold msg_honestly_signed, msg_signing_key in *; context_map_rewrites.
          rewrite cipher_honestly_signed_honest_keyb_iff in H2; auto.

        + unfold msg_to_this_user in *; simpl in *; context_map_rewrites.
          match goal with
          | [ H : clean_ciphers _ _ $? _ = Some _ |- _ ] => apply clean_ciphers_inv in H
          end; simpl; context_map_rewrites; eauto.

        + unfold msgCiphersSignedOk in *; rewrite Forall_forall in *; intros; eauto.
          destruct x1; simpl in *.
          specialize (H1 _ H2); simpl in *; eauto.
          unfold msg_honestly_signed in *.
          unfold msg_signing_key in *; simpl in *; destruct c;
            try discriminate;
            context_map_rewrites.

          cases (clean_ciphers honestk cs $? c_id); try discriminate.
          repeat
          match goal with
          | [ H : clean_ciphers _ _ $? _ = Some _ |- _ ] => apply clean_ciphers_inv in H
          end; simpl; context_map_rewrites; eauto.
    Qed.

    Lemma action_adversary_safe_after_before_cleaning :
      forall {A} (usrs : honest_users A) cs a,
          action_adversary_safe (findUserKeys (clean_users (findUserKeys usrs) cs usrs)) (clean_ciphers (findUserKeys usrs) cs) a
        -> action_adversary_safe (findUserKeys usrs) cs a.
    Proof.
      intros; eapply action_adversary_safe_after_before_cleaning'; swap 1 2; eauto.
    Qed.

    Hint Resolve
         (* cipher_action_safe_after_before_cleaning *)
         action_adversary_safe_after_before_cleaning.

    Lemma honest_silent_new_cipher_implies_honest_step_origuniv' :
      forall {t A B} (msg : message t) (msg_c : crypto t) (usrs : honest_users A) (adv : user_data B) 
        cs cs' c_id c gks u_id honestk ks qmsgs mycs froms sents cur_n b k__signid msg_to enc_cmd kt,
        ~ In c_id cs
        -> honestk = findUserKeys usrs
        -> cs' = cs $+ (c_id,c)
        -> msg_c = SignedCiphertext c_id
        -> ks $? k__signid = Some true
        -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt)
        -> ( ( enc_cmd = Sign k__signid msg_to msg
            /\ c = SigCipher k__signid msg_to (Some u_id,cur_n) msg)
          \/ ( exists k__encid kp kt__e,
                  enc_cmd = SignEncrypt k__signid k__encid msg_to msg
                /\ ks $? k__encid = Some kp
                /\ gks $? k__encid = Some (MkCryptoKey k__encid Encryption kt__e)
                /\ keys_mine ks (findKeysMessage msg)
                /\ c = SigEncCipher k__signid k__encid msg_to (Some u_id,cur_n) msg)
          )
        -> message_queues_ok cs usrs gks
        -> next_cmd_safe honestk cs u_id froms sents enc_cmd
        -> forall cmd, usrs $? u_id =
          Some
            {|
              key_heap := ks;
              protocol := cmd;
              msg_heap := qmsgs;
              c_heap := mycs;
              from_nons := froms;
              sent_nons := sents;
              cur_nonce := cur_n |}
        -> step_user Silent (Some u_id)
                    (  clean_users honestk cs usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs (Some u_id) froms qmsgs
                     , mycs, froms, sents, cur_n, enc_cmd)
                    (  clean_users honestk cs' usrs
                     , clean_adv adv honestk cs b
                     , clean_ciphers honestk cs'
                     , clean_keys honestk gks
                     , clean_key_permissions honestk ks
                     , clean_messages honestk cs' (Some u_id) froms qmsgs
                     , (c_id :: mycs), froms, sents, 1+cur_n, @Return (Crypto t) msg_c ).
    Proof.
      intros; split_ex; subst.
      assert (findUserKeys usrs $? k__signid = Some true) by eauto 2.

      split_ors; subst;
        erewrite clean_messages_addnl_cipher_idempotent, clean_users_addnl_cipher_idempotent; eauto;
          process_next_cmd_safe;
          econstructor; eauto.

      unfold keys_mine in *; intros.
      repeat
        match goal with
        | [ H : (forall _ _, findKeysMessage ?msg $? _ = Some _ -> _), ARG : findKeysMessage ?msg $? _ = Some _ |- _ ] =>
          specialize (H _ _ ARG)
        end.
      split_ors; assert (findUserKeys usrs $? k_id = Some true) by eauto; eauto.
    Qed.

    Lemma msg_accepted_by_pattern_after_cleaning_honest_key :
      forall {t} (msg : crypto t) cs u_id froms pat k_id c_id honestk,
        msg = SignedCiphertext c_id
        -> msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> msg_signing_key cs msg = Some k_id
        -> honest_key honestk k_id
        -> msg_accepted_by_pattern (clean_ciphers honestk cs) (Some u_id) froms pat msg.
    Proof.
      intros.
      invert H0; econstructor; eauto; clean_context.
      - eapply clean_ciphers_keeps_honest_cipher; eauto.
        invert H2.
        unfold msg_signing_key in H1; context_map_rewrites; clean_context.
        unfold honest_cipher_filter_fn, cipher_honestly_signed.
        unfold honest_keyb; context_map_rewrites; eauto.
      - eapply clean_ciphers_keeps_honest_cipher; eauto.
        invert H2.
        unfold msg_signing_key in H1; context_map_rewrites; clean_context.
        unfold honest_cipher_filter_fn, cipher_honestly_signed.
        unfold honest_keyb; context_map_rewrites; eauto.
    Qed.

    Hint Resolve msg_accepted_by_pattern_after_cleaning_honest_key.

    Lemma honest_labeled_recv_implies_honest_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs: honest_users A) (adv : user_data B) usrs__s cs__s
        cs gks u_id honestk honestk' pat ks qmsgs mycs froms froms' sents cur_n pubk b,
          msg_accepted_by_pattern cs (Some u_id) froms pat msg
        -> honestk = findUserKeys usrs
        -> froms' = updateTrackedNonce (Some u_id) froms cs msg
        -> cs__s = clean_ciphers honestk cs
        -> usrs__s = clean_users honestk cs usrs
        -> pubk = findKeysCrypto cs msg
        -> honestk' = findUserKeys usrs $k++ pubk
        -> message_queue_ok honestk cs (existT _ _ msg :: qmsgs) gks
        -> next_cmd_safe honestk cs u_id froms sents (@Recv t pat)
        -> step_user (Action (Input msg pat froms)) (Some u_id)
                    (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms (existT _ _ msg :: qmsgs),
                     mycs, froms, sents, cur_n, @Recv t pat)
                    (clean_users honestk' cs usrs,
                     clean_adv adv honestk' cs b,
                     clean_ciphers honestk' cs,
                     clean_keys honestk' gks,
                     clean_key_permissions honestk' (ks $k++ pubk),
                     clean_messages honestk' cs (Some u_id) froms' qmsgs,
                     findCiphers msg ++ mycs,
                     updateTrackedNonce (Some u_id) froms cs msg, sents, cur_n, @Return (Crypto t) msg).
    Proof.
      intros; process_next_cmd_safe; subst.

      assert (msg_signed_addressed (findUserKeys usrs) cs (Some u_id) msg = true)
        as MSA by (unfold msg_signed_addressed; eauto using accepted_safe_msg_pattern_honestly_signed
                                                          , accepted_safe_msg_pattern_to_this_user).
      unfold clean_messages at 1.
      unfold clean_messages', msg_filter; simpl.
      rewrite !MSA.

      generalize MSA; intros MSA'; unfold msg_signed_addressed in MSA'; apply andb_true_iff in MSA'; split_ands.
      pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ H0); split_ands; split_ex.
      eapply msg_honestly_signed_signing_key_honest in H0; eauto.

      generalize (accepted_safe_msg_pattern_replay_safe H7 H); intros; split_ex;
        subst.
      unfold msg_nonce_ok at 2; context_map_rewrites.
      rewrite count_occ_not_In with (eq_dec := msg_seq_eq) in H8;
        rewrite H8.
      rewrite fold_clean_messages1' , clean_messages'_fst_pull, fold_clean_messages.
      invert H6; split_ands.

      specialize (H9 _ H2); split_ands.
      specialize (H10 H0); split_ands.
      unfold message_no_adv_private in H10.

      match goal with
      | [ |- context [ findUserKeys usrs $k++ ?pubk ]] => 
        assert (findUserKeys usrs $k++ pubk = findUserKeys usrs) as MKRW
      end.
      maps_equal; solve_perm_merges;
        repeat
          match goal with
          | [ H : (forall _ _, findKeysCrypto _ _ $? _ = Some _ -> _), ARG : findKeysCrypto _ _ $? _ = Some _ |- _ ] =>
            specialize (H _ _ ARG); split_ands; subst
          end; clean_map_lookups; eauto.

      rewrite MKRW.
      eapply StepRecv; eauto.

      * unfold updateTrackedNonce; context_map_rewrites.
        unfold msg_to_this_user, msg_destination_user in H1; context_map_rewrites.
        destruct (cipher_to_user x2 ==n u_id); subst; try discriminate.
        destruct (cipher_to_user x2 ==n cipher_to_user x2); try contradiction.
        rewrite H8 ; trivial.
      * rewrite clean_key_permissions_distributes_merge_key_permissions.
        match goal with
        | [ |- context [ ?same $k++ ?fst = ?same $k++ ?snd ]] => assert (fst = snd)
        end.
        maps_equal.
        cases (@findKeysCrypto t0 cs (SignedCiphertext x1) $? y).
        ** specialize (H10 _ _ Heq0); split_ands; subst.
           erewrite clean_key_permissions_keeps_honest_permission; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq0; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.
           unfold honest_cipher_filter_fn, cipher_honestly_signed;
             destruct x2; eauto.
           unfold msg_signing_key in H2; context_map_rewrites; clean_context.
           invert H0.
           unfold honest_keyb; context_map_rewrites; trivial.
        ** rewrite clean_key_permissions_adds_no_permissions; eauto; symmetry.
           unfold findKeysCrypto. unfold findKeysCrypto in Heq0; context_map_rewrites.
           erewrite clean_ciphers_keeps_honest_cipher; eauto.
           unfold msg_signing_key in H2; context_map_rewrites; clean_context.
           eapply honest_cipher_filter_fn_true_honest_signing_key; eauto.
        ** rewrite H13; trivial.
           
    Qed.

    Lemma keys_mine_after_cleaning :
      forall honestk ks chkkeys,
        keys_mine ks chkkeys
        -> (forall k_id kp, ks $? k_id = Some kp -> honestk $? k_id = Some true)
        -> keys_mine (clean_key_permissions honestk ks) chkkeys.
    Proof.
      unfold keys_mine; intros * KM KH * ARG.
      specialize (KM _ _ ARG); split_ors;
        match goal with
        | [ ARG : ?ks $? _ = Some _, H : (forall _ _, ?ks $? _ = Some _ -> _) |- _ ] => specialize (H _ _ ARG)
        end; erewrite clean_key_permissions_keeps_honest_permission; eauto.
    Qed.

    Hint Resolve keys_mine_after_cleaning.
    
    Lemma honest_labeled_send_implies_step_origuniv :
      forall {t A B} (msg : crypto t) (usrs: honest_users A) (adv : user_data B) rec_u
        cs gks u_id rec_u_id honestk ks qmsgs mycs froms sents cur_n b,
        keys_mine ks (findKeysCrypto cs msg)
        -> incl (findCiphers msg) mycs
        -> usrs $? rec_u_id = Some rec_u
        -> Some rec_u_id <> Some u_id
        -> honestk = findUserKeys usrs
        -> encrypted_ciphers_ok honestk cs gks
        -> user_cipher_queues_ok cs honestk usrs
        -> honest_nonces_ok cs usrs
        -> honest_users_only_honest_keys usrs
        -> next_cmd_safe honestk cs u_id froms sents (Send rec_u_id msg)
        -> forall cmdc,
            usrs $? u_id =
            Some
              {|
                key_heap := ks;
                protocol := cmdc;
                msg_heap := qmsgs;
                c_heap := mycs;
                from_nons := froms;
                sent_nons := sents;
                cur_nonce := cur_n |}
            -> step_user (Action (Output msg (Some u_id) (Some rec_u_id) sents))
                    (Some u_id)
                    (clean_users honestk cs usrs,
                     clean_adv adv honestk cs b,
                     clean_ciphers honestk cs,
                     clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms qmsgs, mycs,
                     froms, sents, cur_n, Send rec_u_id msg)
                    (clean_users honestk cs
                                 (usrs $+ (rec_u_id,
                                           {|
                                             key_heap := key_heap rec_u;
                                             protocol := protocol rec_u;
                                             msg_heap := msg_heap rec_u ++ [existT _ _ msg];
                                             c_heap := c_heap rec_u;
                                             from_nons := from_nons rec_u;
                                             sent_nons := sent_nons rec_u;
                                             cur_nonce := cur_nonce rec_u |})),
                     clean_adv
                       {| key_heap := key_heap adv $k++ findKeysCrypto cs msg;
                          protocol := protocol adv;
                          msg_heap := msg_heap adv ++ [existT _ _ msg];
                          c_heap := c_heap adv;
                          from_nons := from_nons adv;
                          sent_nons := sent_nons adv;
                          cur_nonce := cur_nonce adv |} honestk cs b,
                     clean_ciphers honestk cs,
                     clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs (Some u_id) froms qmsgs,
                     mycs, froms,
                     updateTrackedNonce (Some rec_u_id) sents cs msg, cur_n, ret tt).
    Proof.
      intros; subst; eauto.
      process_next_cmd_safe; subst.
      econstructor; eauto using clean_users_cleans_user; simpl.

      - simpl in *.
        assert (List.In x mycs) by eauto; user_cipher_queues_prop.
        erewrite clean_ciphers_keeps_honest_cipher; eauto 3.

      - rewrite clean_users_add_pull; simpl.
        erewrite clean_messages_keeps_hon_signed; eauto 8.
        unfold msg_signed_addressed; eauto.

      - unfold clean_adv; simpl.
        simpl in H0; assert (List.In x mycs) by eauto; 
          user_cipher_queues_prop.
        rewrite clean_adv_msgs_keeps_honest_msg; eauto.
        rewrite clean_key_permissions_distributes_merge_key_permissions.
        erewrite clean_ciphers_keeps_honest_cipher; eauto.

        unfold cipher_honestly_signed in H16; destruct x1; eauto.
        encrypted_ciphers_prop.

        assert(clean_key_permissions (findUserKeys usrs) (findKeysMessage msg) = findKeysMessage msg)
          as RW.
        maps_equal.
        cases (findKeysMessage msg $? y); eauto 12 using clean_key_permissions_adds_no_permissions.
        eapply clean_key_permissions_keeps_honest_permission; eauto.
        unfold honest_perm_filter_fn.
        specialize (H24 _ _ Heq); split_ands; context_map_rewrites; trivial.

        rewrite RW; trivial.
    Qed.

    Hint Resolve updateTrackedNonce_clean_ciphers_idempotent_honest_msg.

    Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv'' :
      forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' (b: <<Base B>>),
        step_user lbl suid bd bd'
        -> suid = Some u_id
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk cs usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> adv_message_queue_ok usrs cs gks adv.(msg_heap)
          -> honest_users_only_honest_keys usrs
          -> honest_nonces_ok cs usrs
          -> next_cmd_safe honestk cs u_id froms sents cmd
          -> forall cmd' cs__s' usrs__s' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_nons := froms
                                       ; sent_nons := sents
                                       ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_nons := froms'
                                              ; sent_nons := sents'
                                              ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> cs__s' = clean_ciphers honestk' cs'
                  -> usrs__s' = clean_users honestk' cs' usrs'
                  -> step_user lbl suid
                              (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                               clean_key_permissions honestk ks,
                               clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs__s', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                               clean_key_permissions honestk' ks',
                               clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd')
                  \/ (usrs__s, clean_adv adv honestk cs b, cs__s, clean_keys honestk gks,
                     clean_key_permissions honestk ks,
                     clean_messages honestk cs suid froms qmsgs, mycs, froms, sents, cur_n, cmd)
                    = (clean_users honestk' cs' usrs', clean_adv adv' honestk' cs b, cs__s', clean_keys honestk' gks',
                       clean_key_permissions honestk' ks',
                       clean_messages honestk' cs' suid froms' qmsgs', mycs', froms', sents', cur_n', cmd').
    Proof.
      induction 1; inversion 5; inversion 9; intros; subst; clean_context;
        autorewrite with find_user_keys in *;
        try solve [ left; econstructor; eauto;
                    user_cipher_queues_prop; eauto;
                    try solve_clean_keys_clean_key_permissions];
        eauto using honest_silent_recv_implies_honest_or_no_step_origuniv;
        try solve [ left; 
                    eauto 12 using honest_labeled_send_implies_step_origuniv
                    , honest_silent_new_cipher_implies_honest_step_origuniv'
                    , honest_silent_decrypt_implies_honest_step_origuniv
                    , honest_silent_new_key_implies_honest_step_origuniv].

      - apply next_action_next_cmd_safe_bind in H23.

        remember (findUserKeys usrs) as honestk.
        remember (usrs' $+ (u_id, {| key_heap := ks'
                                   ; protocol := cmdc'
                                   ; msg_heap := qmsgs'
                                   ; c_heap := mycs'
                                   ; from_nons := froms'
                                   ; sent_nons := sents'
                                   ; cur_nonce := cur_n' |})) as usrs''.
        remember (findUserKeys usrs'') as honestk'.

        specialize (IHstep_user _ _ _ _
                                b eq_refl
                                _ _ _ _
                                Heqhonestk
                                eq_refl
                                eq_refl
                                eq_refl
                                H5
                                H17
                                H18
                                H19
                                H20
                                H21
                                H22
                                H23
                                _ _ _ _
                                eq_refl
                                _ _ _
                                H25
                                Hequsrs''
                                Heqhonestk'
                                eq_refl
                                eq_refl

                 ); split_ors; clean_context.
        + left; econstructor; eauto.
        + right; unfold clean_adv; simpl.
          inversion H0; clear H0; subst.
          assert (clean_users (findUserKeys usrs) cs usrs
                  = clean_users
                      (findUserKeys
                         (usrs' $+ (u_id,
                                    {|
                                      key_heap := ks';
                                      protocol := cmdc';
                                      msg_heap := qmsgs';
                                      c_heap := mycs';
                                      from_nons := froms';
                                      sent_nons := sents';
                                      cur_nonce := cur_n' |}))) cs' usrs')
                 as USRSRW
                 by (unfold clean_users, mapi; eauto using map_eq_fields_eq).
          rewrite USRSRW; f_equal.

      - left; eapply honest_labeled_recv_implies_honest_step_origuniv; eauto 12.
        unfold message_queues_ok in H25; rewrite Forall_natmap_forall in H25.
        specialize (H25 _ _ H32); eauto.
    Qed.

    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b u_id userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
        universe_ok U
        -> adv_universe_ok U
        -> user_cipher_queues_ok U.(all_ciphers) (findUserKeys U.(users)) U.(users)
        -> U.(users) $? u_id = Some userData
        -> step_user Silent (Some u_id)
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
        -> honest_users_only_honest_keys U.(users)
        -> honest_cmds_safe U
        -> step_universe (strip_adversary_univ U b) Silent (strip_adversary_univ U' b)
        \/ strip_adversary_univ U b = strip_adversary_univ U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      remember H3 as RW. clear HeqRW.

      unfold adv_universe_ok, universe_ok in *; split_ands; simpl in *.
      unfold honest_cmds_safe in *; simpl in H.
      specialize (H6 _ _ _ eq_refl H2).
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv'' in RW; eauto.

      split_ors.
      - destruct adversary; unfold strip_adversary_univ; simpl in *.
        left.
        eapply StepUser; simpl; eauto.
        + eapply clean_users_cleans_user; eauto.
        + unfold build_data_step; simpl.
          unfold clean_adv; simpl.
          eauto.

        + unfold buildUniverse, clean_adv; simpl.
          f_equal.
          rewrite clean_users_add_pull; simpl.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          f_equal.

          assert (step_user Silent (Some u_id)
       (users,
       {|
       key_heap := key_heap0;
       protocol := protocol0;
       msg_heap := msg_heap0;
       c_heap := c_heap0;
       from_nons := from_nons0;
       sent_nons := sent_nons0;
       cur_nonce := cur_nonce0 |}, all_ciphers, all_keys, key_heap, msg_heap, c_heap, from_nons, sent_nons, cur_nonce, protocol)
       (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)) as STEP by assumption.
          eapply honest_silent_step_nochange_honestk_clean_ciphers_msgs_usrs in H3; eauto; split_ands.

          eapply honest_silent_step_nochange_clean_adv_messages.
          exact STEP.
          all: (reflexivity || eassumption).

      - right.
        unfold strip_adversary_univ, buildUniverse; simpl.
        inversion H13; subst.
        unfold clean_adv; simpl; f_equal.
        + rewrite clean_users_add_pull; simpl.
          assert (clean_users (findUserKeys users) all_ciphers users =
                  clean_users (findUserKeys (usrs $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}))) cs usrs).
          unfold clean_users, map; apply map_eq_elements_eq; simpl; auto.
          rewrite <- H14.
          apply map_eq_Equal; unfold Equal; intros.
          destruct (y ==n u_id); subst; clean_map_lookups; eauto.
          eapply clean_users_cleans_user; eauto.
          f_equal; eauto.
        + f_equal; eauto.
          rewrite H17.
          symmetry; eapply honest_silent_step_nochange_clean_adv_messages.
          exact H3.
          all : (reflexivity || eassumption).
          Unshelve. eauto.
    Qed.

    Lemma honest_cmd_safe_advuniv :
      forall {A} (cmd : RealWorld.user_cmd A) honestk honestk' cs u_id froms sents,
        next_cmd_safe honestk' (clean_ciphers honestk cs) u_id froms sents cmd
        -> (forall k_id, honestk' $? k_id = Some true -> honestk $? k_id = Some true)
        -> next_cmd_safe honestk cs u_id froms sents cmd.
    Proof.
      unfold next_cmd_safe; intros.
      specialize (H _ _ H1).

      cases cmd__n; split_ex; subst; intros; eauto;
        repeat simple apply conj; intros; eauto 8.

      - eapply msg_honestly_signed_after_without_cleaning; eauto.
        unfold RealWorld.msg_honestly_signed, RealWorld.msg_signing_key in *;
          context_map_rewrites;
          unfold RealWorld.honest_keyb in *.
        cases (honestk' $? RealWorld.cipher_signing_key x0); try discriminate;
          destruct b; try discriminate.
        specialize (H0 _ Heq); context_map_rewrites; eauto.

      - unfold RealWorld.msg_to_this_user, RealWorld.msg_destination_user in *;
          context_map_rewrites.
        erewrite clean_ciphers_inv; eauto.

      - eapply msgCiphersSigned_before_clean_ciphers; eauto.
        unfold RealWorld.msgCiphersSignedOk in *; simpl in *.
        invert H3; econstructor; eauto.
        unfold RealWorld.msg_honestly_signed, RealWorld.msg_signing_key in *;
          context_map_rewrites;
          unfold RealWorld.honest_keyb in *.
        cases (honestk' $? RealWorld.cipher_signing_key x0); try discriminate;
          destruct b; try discriminate.
        specialize (H0 _ Heq); context_map_rewrites; eauto.

      - invert H; econstructor; eauto.
      - specialize (H _ _ H2); split_ands; eauto.
    Qed.
  
    Lemma honest_cmds_safe_advuniv :
      forall {A B} (U__ra : RealWorld.universe A B) b,
        honest_cmds_safe (strip_adversary_univ U__ra b)
        -> honest_cmds_safe U__ra.
    Proof.
      unfold honest_cmds_safe; intros.
      eapply clean_users_cleans_user
        with (honestk := RealWorld.findUserKeys U__ra.(RealWorld.users))
             (cs := U__ra.(RealWorld.all_ciphers))
        in H1; eauto.
      
      specialize (H _ _ _ eq_refl H1); simpl in *.
      eapply honest_cmd_safe_advuniv; eauto.
    Qed.
    
    Hint Resolve honest_cmds_safe_advuniv.

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl,
        step_universe U lbl U'
        -> lbl = Silent
        -> adv_universe_ok U
        -> honest_cmds_safe U
        -> universe_ok U
        -> universe_ok U'.
     Proof.
       intros A B U U' lbl STEP e AUOK HCS UOK;
         rewrite e in *; clear e.

       unfold adv_universe_ok in AUOK; split_ands.
       invert STEP; eauto.

       - match goal with
         | [ H : users U $? _ = Some ?ud |- _ ] =>
           destruct U; destruct ud;
             unfold build_data_step, buildUniverse in *; simpl in *
         end.

         generalize (clean_users_cleans_user (findUserKeys users) all_ciphers users u_id H7 eq_refl);
           intros CLEAN_USER; simpl in CLEAN_USER.

         unfold honest_cmds_safe in HCS;
           specialize (HCS _ _ _ eq_refl H7); simpl in HCS.
         eapply honest_silent_step_adv_univ_enc_ciphers_ok; simpl; eauto.
       
       - destruct U.
         unfold build_data_step, buildUniverseAdv in *; simpl in *.
         eapply adv_step_encrypted_ciphers_ok; eauto.
         unfold keys_and_permissions_good in *; split_ands; eauto.
     Qed.
     
  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user.

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
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_silent_step (lameAdv b) R
      -> honest_actions_safe B R
      (* -> honest_users_only_honest_keys U__ra.(RealWorld.users) *)
      -> universe_ok U__ra
      -> adv_universe_ok U__ra
      -> R (RealWorld.peel_adv (strip_adversary_univ U__ra b)) U__i
      -> forall U__ra',
          RealWorld.step_universe U__ra Silent U__ra'
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

    remember (strip_adversary_univ U__ra b) as U__r.
    assert (honest_cmds_safe U__r) as HCS by eauto.

    match goal with
    | [ H : RealWorld.step_universe _ _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
        as U__ra'.

      apply honest_cmds_safe_advuniv in HCS.
      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H1 H2 H6 H13 H14 HeqU__ra' H12 HCS); split_ors.

      + assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
          as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).

        specialize (H _ _ H3 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ H4); split_ex; split_ands; eauto.

      + exists U__i; intuition idtac; eauto.
        destruct U__ra; destruct U__ra'; simpl in *.
        unfold strip_adversary_univ in *; unfold strip_adversary in *; simpl in *.
        invert H4; eauto.
        assert (clean_users (RealWorld.findUserKeys users) all_ciphers users = clean_users (RealWorld.findUserKeys users0) all_ciphers0 users0)
          as CLEAN_USERS by (unfold clean_users, mapi; auto).
        rewrite <- CLEAN_USERS; auto.

    (* Adversary step *)
    - exists U__i; intuition auto.
      eapply adv_step_stays_in_R; eauto.

  Qed.

  Lemma honest_key_is_honest_clean_key :
    forall {A} (us : RealWorld.honest_users A) k cs,
      RealWorld.honest_key (RealWorld.findUserKeys us) k
      -> RealWorld.honest_key (RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys us) cs us)) k.
  Proof.
    intros; invert H. pose proof @findUserKeys_clean_users_correct A us cs k; rewrite H0 in H; constructor. assumption.
  Qed.

  Lemma content_eq_strip_keys :
    forall t (m__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t) honestk gks,
      content_eq m__rw m__iw (clean_keys honestk gks)
      -> content_eq m__rw m__iw gks.
  Proof.
    induction m__rw; intros; eauto.
    - dependent destruction m__iw.
      unfold content_eq in *; simpl in *.
      destruct acc; destruct acc0.

      cases (clean_keys honestk gks $? k); try contradiction.
      apply clean_keys_inv in Heq; split_ands; context_map_rewrites; eauto.
      
    - dependent destruction m__iw.
      invert H.
      econstructor; eauto.
  Qed.

  Lemma key_perms_from_known_ciphers_clean_ciphers :
    forall cs mycs ks honestk,
      user_cipher_queue_ok cs honestk mycs
      -> key_perms_from_known_ciphers (clean_ciphers honestk cs) mycs ks
        = key_perms_from_known_ciphers cs mycs ks.
  Proof.
    unfold key_perms_from_known_ciphers.
    induction mycs; intros; eauto.
    invert H; split_ex; simpl.
    erewrite clean_ciphers_keeps_honest_cipher; eauto; context_map_rewrites.
    destruct x;
      eapply IHmycs with (ks := ks $k++ RealWorld.findKeysMessage msg) in H3; eauto.
  Qed.

  Lemma msg_not_honestly_signed_before_after_cleaning :
    forall {t} (msg : RealWorld.crypto t) honestk cs,
      RealWorld.msg_honestly_signed honestk cs msg = false
      -> RealWorld.msg_honestly_signed honestk (clean_ciphers honestk cs) msg = false.
  Proof.
    intros.
    unfold RealWorld.msg_honestly_signed in *.
    cases (RealWorld.msg_signing_key cs msg); 
      unfold RealWorld.msg_signing_key in *; destruct msg; try discriminate; eauto;
        cases (cs $? c_id); try discriminate.

    - invert Heq.
      erewrite clean_ciphers_eliminates_dishonest_cipher; eauto.
    - erewrite clean_ciphers_no_new_ciphers; eauto.
  Qed.

  Lemma findKeysCrypto_same_after_cipher_cleaning :
    forall t (msg : RealWorld.crypto t) cs honestk,
      RealWorld.msg_honestly_signed honestk cs msg = true
      -> RealWorld.findKeysCrypto (clean_ciphers honestk cs) msg = RealWorld.findKeysCrypto cs msg.
  Proof.
    destruct msg; intros; eauto.
    unfold RealWorld.findKeysCrypto.
    unfold RealWorld.msg_honestly_signed in H.
    cases (RealWorld.msg_signing_key cs (@RealWorld.SignedCiphertext t0 c_id)); try discriminate.
    unfold RealWorld.msg_signing_key in Heq; cases (cs $? c_id); try discriminate.
    invert Heq.
    erewrite clean_ciphers_keeps_honest_cipher; eauto.
    unfold honest_cipher_filter_fn, RealWorld.cipher_honestly_signed; destruct c; eauto.
  Qed.

  Lemma rewrite_clean_messages_cons :
    forall cs honestk uid froms msgs t (msg : RealWorld.crypto t) c n,
      not_replayed cs honestk uid froms msg = true
      -> match msg with
        | RealWorld.SignedCiphertext cid => cs $? cid = Some c /\ RealWorld.cipher_nonce c = n
        | _ => False
        end
      -> clean_messages honestk cs (Some uid) froms ((existT _ _ msg) :: msgs)
        = (existT _ _ msg) :: clean_messages honestk cs (Some uid) (n :: froms) msgs.
  Proof.
    intros; unfold clean_messages at 1, clean_messages'.
    simpl.
    unfold not_replayed in H; rewrite !andb_true_iff in H; split_ex.
    cases (msg_nonce_ok cs froms msg); try discriminate.
    unfold RealWorld.msg_signed_addressed.
    rewrite H, H2; simpl.
    destruct msg; try contradiction; split_ex; subst; trivial.
    rewrite fold_clean_messages2', clean_messages'_fst_pull, fold_clean_messages; simpl.
    unfold msg_nonce_ok in Heq; context_map_rewrites.
    cases (count_occ RealWorld.msg_seq_eq froms (RealWorld.cipher_nonce c)); try discriminate.
    invert Heq; trivial.
  Qed.

      


  (* Definition honest_cipher_nonces_unique (cs : RealWorld.ciphers) := *)
  (*   forall cid1 cid2 c1 c2, *)
  (*     cs $? cid1 = Some c1 *)
  (*     -> cs $? cid2 = Some c2 *)
  (*     -> RealWorld.cipher_nonce c1 = RealWorld.cipher_nonce c2 *)
  (*     -> c1 = c2. *)

  (* Lemma honest_step_honest_ciphers_unique_preservation : *)
  (*   forall {A B C} lbl suid bd bd', *)
  (*     RealWorld.step_user lbl suid bd bd' *)
  (*     -> forall cs cs' u_id (usrs usrs' : RealWorld.honest_users A) (adv adv' : RealWorld.user_data B) (cmd cmd' : RealWorld.user_cmd C) *)
  (*         gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n', *)

  (*       suid = Some u_id *)
  (*       -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
  (*       -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
  (*       -> honest_nonces_ok cs usrs *)
  (*       -> honest_cipher_nonces_unique cs *)
  (*       -> honest_cipher_nonces_unique cs'. *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 1; intros; subst; eauto. *)

  (*   all : clean_context. *)
  (*   - unfold honest_cipher_nonces_unique in *; intros. *)
  (*     destruct (c_id ==n cid1); destruct (c_id ==n cid2); clean_map_lookups; simpl in *; eauto. *)
  (*     + destruct c2; simpl in *; eauto. *)
      

  (* Lemma ok_to_not_update_froms : *)
  (*   forall cs msgs ks honestk uid froms t (msg : RealWorld.crypto t) cid c, *)
  (*     not_replayed cs honestk uid froms msg = true *)
  (*     -> msg = RealWorld.SignedCiphertext cid *)
  (*     -> cs $? cid = Some c *)
  (*     -> key_perms_from_message_queue cs honestk msgs uid froms (ks $k++ RealWorld.findKeysCrypto cs msg) *)
  (*       = key_perms_from_message_queue cs honestk msgs uid (RealWorld.cipher_nonce c :: froms) ( ks $k++ RealWorld.findKeysCrypto cs msg). *)
  (* Proof. *)
  (*   induction msgs; intros; eauto. *)
  (*   simpl; destruct a. *)
  (*   generalize H; intros NR. *)
  (*   unfold not_replayed in H; subst; rewrite !andb_true_iff in H; split_ex. *)
  (*   unfold msg_nonce_ok in H0; context_map_rewrites. *)
  (*   cases (count_occ RealWorld.msg_seq_eq froms (RealWorld.cipher_nonce c)); try discriminate. *)
  (*   cases (not_replayed cs honestk uid froms c0). *)
  (*   - admit. *)
  (*   - unfold not_replayed in Heq0 |- *. *)
  (*     rewrite !andb_false_iff in Heq0. *)
  (*     split_ors. *)
  (*     rewrite H3, andb_false_l; eapply IHmsgs; eauto. *)
  (*     rewrite H3, andb_false_r, andb_false_l; eapply IHmsgs; eauto. *)
  (*     unfold msg_nonce_ok in H3; destruct c0; try discriminate; simpl; context_map_rewrites. *)
  (*     cases (cs $? c_id); try discriminate; simpl. *)
  (*     cases (count_occ RealWorld.msg_seq_eq froms (RealWorld.cipher_nonce c0)); try discriminate. simpl. *)
  (*     cases (RealWorld.msg_seq_eq (RealWorld.cipher_nonce c) (RealWorld.cipher_nonce c0)); eauto. *)
  (*     rewrite <- e, Heq in Heq1; discriminate. *)
  (*     all : simpl in *; rewrite andb_false_r; eauto. *)
  (*     admit. *)
  (*     destruct c; simpl; eauto. *)
      
  Lemma key_perms_from_message_queue_clean_ciphers :
    forall cs msgs ks honestk uid froms A (usrs : RealWorld.honest_users A) kid kp,
      honestk = RealWorld.findUserKeys usrs
      -> key_perms_from_message_queue
          (clean_ciphers honestk cs)
          (RealWorld.findUserKeys (clean_users honestk cs usrs))
          (clean_messages honestk cs (Some uid) froms msgs)
          uid froms ks $? kid = Some kp
      -> key_perms_from_message_queue cs honestk msgs uid froms ks $? kid = Some kp.
  Proof.
    unfold key_perms_from_message_queue.
    induction msgs; intros; eauto.
    destruct a; simpl in *.
    pose proof (clean_messages_cons_split cs honestk uid froms msgs c eq_refl);
      split_ors; split_ex.

    - rewrite H1 in H0.
      apply IHmsgs in H0; eauto.
      rewrite H2; destruct msgs; eauto.
      destruct s.
      cases ( not_replayed cs honestk uid froms c0); eauto.




  (* Lemma key_perms_from_message_queue_clean_ciphers : *)
  (*   forall cs msgs ks honestk uid froms A (usrs : RealWorld.honest_users A), *)
  (*     honestk = RealWorld.findUserKeys usrs *)
  (*     -> key_perms_from_message_queue *)
  (*         (clean_ciphers honestk cs) *)
  (*         (RealWorld.findUserKeys (clean_users honestk cs usrs)) *)
  (*         (clean_messages honestk cs (Some uid) froms msgs) *)
  (*         uid froms ks *)
  (*       = key_perms_from_message_queue cs honestk msgs uid froms ks. *)
  (* Proof. *)
  (*   unfold key_perms_from_message_queue. *)
  (*   induction msgs; intros; eauto. *)
  (*   simpl; destruct a. *)
  (*   cases (not_replayed cs honestk uid froms c); eauto. *)
  (*   - erewrite rewrite_clean_messages_cons; eauto; simpl. *)

  (*     assert (HONK : honestk = RealWorld.findUserKeys usrs) by assumption. *)
  (*     eapply IHmsgs with (uid := uid) (ks := ks) (froms := froms) in HONK; eauto. *)
  (*     rewrite !key_perms_from_message_queue_notation in *. *)

  (*     assert (not_replayed (clean_ciphers honestk cs) (RealWorld.findUserKeys (clean_users honestk cs usrs)) uid froms c = true) by admit. *)
  (*     rewrite H0. *)
    
  (*   cases (RealWorld.msg_honestly_signed honestk cs c). *)
  (*   - unfold clean_messages, clean_messages'. simpl. *)

  (*     erewrite clean_messages_keeps_hon_signed; eauto. *)
  (*     rewrite msg_honestly_signed_before_after_cleaning'; eauto. *)
  (*     rewrite IHmsgs. *)
  (*     rewrite findKeysCrypto_same_after_cipher_cleaning; eauto. *)
      
  (*   - rewrite msg_not_honestly_signed_before_after_cleaning; eauto. *)
  (* Qed. *)

  (* MessageEq.key_perms_from_message_queue (clean_ciphers (RealWorld.findUserKeys users) all_ciphers) *)
  (*         (RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys users) all_ciphers users)) *)
  (*         (clean_messages (RealWorld.findUserKeys users) all_ciphers (Some u) (RealWorld.from_nons data__rw) *)
  (*            (RealWorld.msg_heap data__rw)) *)

  Lemma msg_matches_strip :
    forall {A B t} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (m__rw : RealWorld.crypto t) (m__iw : IdealWorld.message.message t)
      ch_id b,
      user_cipher_queues_ok  U__ra.(RealWorld.all_ciphers) (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.users)
      -> MessageEq.message_eq m__rw (strip_adversary_univ U__ra b) m__iw U__i ch_id
      -> MessageEq.message_eq m__rw U__ra m__iw U__i ch_id.
  Proof.
    intros.
    destruct U__ra; unfold strip_adversary_univ in *; simpl in *.
    invert H0; simpl in *.
      
    - generalize (clean_ciphers_inv _ _ _ H8); intros.
      econstructor 1; simpl; eauto using content_eq_strip_keys.

      intros.
      user_cipher_queues_prop.
      eapply clean_users_cleans_user with (cs := all_ciphers) (honestk := RealWorld.findUserKeys users) in H1; eauto.
      eapply H11 in H1; eauto using honest_key_is_honest_clean_key; simpl in *; clear H11.

      invert H1; clean_map_lookups; simpl in *.
      econstructor 1; eauto.

      rewrite key_perms_from_known_ciphers_clean_ciphers in H13; eauto.
      rewrite key_perms_from_message_queue_clean_ciphers in H13; eauto.





      ; split_ors; subst; eauto using clean_key_permissions_inv''.
      invert H; [ econstructor 1 | econstructor 2 ]; simpl in *; eauto.

        constructor; eauto.
        rewrite key_perms_from_known_ciphers_clean_ciphers in H11; eauto.
        


        apply findUserKeys_clean_users_correct in H1.
        
        autorewrite with find_user_keys in *.
        
        eapply honest_key_is_honest_clean_key; eauto.

        
        right; split; eauto.
        eapply clean_key_permissions_inv in H; split_ands; eauto.

      + eapply honest_key_is_honest_clean_key; eauto.

    - apply clean_ciphers_inv in H7.
      econstructor 2; simpl; eauto using content_eq_strip_keys.

      intros.
      eapply clean_users_cleans_user with (cs := all_ciphers) (honestk := RealWorld.findUserKeys users) in H; eauto.
      eapply H10 in H; eauto; simpl in *.

      + invert H1; invert H2.
        split_ors; eauto using clean_key_permissions_inv''.

        eapply clean_key_permissions_inv in H; split_ands; eauto.
        eapply clean_key_permissions_inv in H2; split_ands; eauto.

      + eapply honest_key_is_honest_clean_key; eauto.
      + eapply honest_key_is_honest_clean_key; eauto.
  Qed.
  
  Lemma action_matches_strip :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) a__r a__i b,
      action_matches (strip_action (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.all_ciphers) a__r) (strip_adversary_univ U__ra b) a__i U__i
      -> action_matches a__r U__ra a__i U__i.
  Proof.
    intros.
    invert H.

    - econstructor.
      2:reflexivity.
      2:eassumption.
      2:eapply msg_matches_strip; eauto.
      unfold strip_action in H2.
      destruct a__r; try discriminate.
      eauto.

    - eapply Out.
      2:reflexivity.
      2:eapply msg_matches_strip; eauto.
      unfold strip_action in H2.
      destruct a__r; try discriminate.
      eauto.
  Qed.
  
  Hint Resolve action_matches_strip.


  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
      simulates_labeled_step (lameAdv b) R
      -> honest_actions_safe B R
      (* -> simulates_labeled_step_safe R *)
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

    assert (lameAdv b (RealWorld.adversary (strip_adversary_univ U__ra b)))
      as LAME by (unfold lameAdv, strip_adversary_univ; simpl; trivial).
    
    assert (RealWorld.step_universe (strip_adversary_univ U__ra b)
                                    (Action (strip_action (RealWorld.findUserKeys U__ra.(RealWorld.users)) U__ra.(RealWorld.all_ciphers) a__r))
                                    (strip_adversary_univ U__ra' b))
      as UNIV_STEP.


    remember (strip_adversary_univ U__ra b) as U__r.
    assert (honest_cmds_safe U__r) as HCS by eauto.
    rewrite HeqU__r in HCS.
    apply honest_cmds_safe_advuniv in HCS.

    subst.
    eapply labeled_honest_step_advuniv_implies_stripped_univ_step; eauto using honest_cmds_implies_safe_actions.

    specialize (H _ _ H1 STRIP_UNIV_OK STRIP_ADV_UNIV_OK LAME _ _ UNIV_STEP); split_ex; split_ands.
    do 3 eexists; intuition idtac; eauto.
  Qed.

  Definition ciphers_honestly_signed (honestk : key_perms) (cs : RealWorld.ciphers) :=
    Forall_natmap (fun c => RealWorld.cipher_honestly_signed honestk c = true) cs.

  Definition keys_honest (honestk : key_perms) (ks : keys) :=
    Forall_natmap (fun k => RealWorld.honest_key honestk k.(keyId)) ks.

  Definition universe_starts_ok {A B} (U : RealWorld.universe A B) :=
    let honestk := RealWorld.findUserKeys U.(RealWorld.users)
    in  (forall u_id u,
            U.(RealWorld.users) $? u_id = Some u
            -> u.(RealWorld.msg_heap) = []
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
      /\ ciphers_honestly_signed honestk U.(RealWorld.all_ciphers)
      /\ keys_honest honestk U.(RealWorld.all_keys)
  .

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
            -> u.(RealWorld.msg_heap) = []
            /\ (forall k_id kp, u.(RealWorld.key_heap) $? k_id = Some kp -> honestk $? k_id = Some true))
      -> clean_users honestk cs usrs = usrs.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal, clean_users; intros; rewrite mapi_o; intros; subst; trivial.
    cases (usrs $? y); auto.
    specialize (H0 _ _ Heq); split_ands.
    destruct u; simpl in *; subst.
    f_equal; f_equal; eauto using universe_starts_ok_clean_key_permissions_idempotent.
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

  Lemma strip_adversary_same_as_peel_strip_simpl :
    forall {A B} (U : RealWorld.universe A B) b,
      strip_adversary U = RealWorld.peel_adv (strip_adversary_univ U b).
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
      (R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
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
    inversion H as [H__silent H__l].
    inversion H__l as [H__loud H__s]; clear H__l.
    inversion H__s as [H__honactsafe H__o]; clear H__s.
    inversion H__o as [R__start OK__start]; clear H__o.

    unfold simulates; rewrite H5.

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_start_ok_adding_adversary
    .

    unfold simulates_silent_step, simulates_labeled_step, honest_actions_safe.
    assert (R (strip_adversary U__ra) U__i /\ universe_ok U__ra /\ adv_universe_ok U__ra) by eauto.

    intuition idtac.
    - rewrite strip_adv_simpl_peel_same_as_strip_adv in *.
      eapply simulates_with_adversary_silent with (b0 := b); eauto.

    - eapply simulates_with_adversary_labeled; eauto.

    - subst.
      unfold honest_actions_safe; intros.

      apply honest_cmds_safe_advuniv with (b0:=b).
      eapply H__honactsafe;
        eauto using ok_universe_strip_adversary_still_ok
                  , ok_adv_universe_strip_adversary_still_ok.
  Qed.

  Theorem simulates_ok_with_adversary' :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : RealWorld.denote (RealWorld.Base B)),
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
    inversion H__s as [H__honactsafe H__o]; clear H__s.
    inversion H__o as [R__start OK__start]; clear H__o.

    unfold refines.

    exists (fun ur ui => R (strip_adversary_simpl ur) ui);
      eauto using simulates_ok_with_adversary.
  Qed.

End SingleAdversarySimulates.

Inductive rCouldGenerate : forall {A B},
    RealWorld.universe A B -> list RealWorld.action -> Prop :=
| RCgNothing : forall A B (U : RealWorld.universe A B),
    rCouldGenerate U []
| RCgSilent : forall A B (U U' : RealWorld.universe A B) acts,
      RealWorld.step_universe U Silent U'
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
     labeled_step_adv_univ_implies_adv_universe_ok
     action_adversary_safe_after_before_cleaning.

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
  forall A B (R R' : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop) (b : RealWorld.denote (RealWorld.Base B)),
    R' = (fun ur ui => R (strip_adversary_simpl ur) ui)
    -> simulates_silent_step (awesomeAdv (B:=B)) R'
    -> simulates_labeled_step (awesomeAdv (B:=B)) R'
    -> honest_actions_safe B R'
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
  induction 8; intros; subst; intuition eauto;
    assert (awesomeAdv (RealWorld.adversary U)) as AWE by (unfold awesomeAdv; trivial).

  - generalize (H0 _ _ H7 H3 H4 AWE _ H5); intro STEPPED;
      destruct STEPPED as [U__i' STEPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H8.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H8.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.
    assert (R' (RealWorld.peel_adv U') U__i') as INR' by (subst; eauto).

    assert (universe_ok U') as UOK.
    eapply silent_step_advuniv_implies_univ_ok; eauto.

    eapply H2; [rewrite HeqR' | ..]; eauto.
    
    assert (adv_universe_ok U') as AUOK.
    subst.
    unfold honest_actions_safe in *.
    eapply silent_step_adv_univ_implies_adv_universe_ok; eauto.
    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK AUOK _ INR'); split_ex; split_ands.

    eapply ideal_multi_silent_stays_could_generate with (acts__i:=x) in H; eauto.

  - generalize (H1 _ _ H7 H3 H4 AWE _ _ H5); intro STEPPED;
      destruct STEPPED as [a__i STEPPED];
      destruct STEPPED as [U__i' STEPPED];
      destruct STEPPED as [U__i'' STEPPPED]; split_ands.

    rewrite strip_adv_simpl_peel_same_as_strip_adv in H10.
    rewrite strip_adversary_same_as_peel_strip_simpl with (b0:=b) in H10.
    remember (fun (ur : RealWorld.simpl_universe A) (ui : IdealWorld.universe A) => R (strip_adversary_simpl ur) ui) as R'.

    assert (R' (RealWorld.peel_adv U') U__i'') as INR' by (subst; eauto).
    assert (R' (RealWorld.peel_adv (strip_adversary_univ U b)) U__i) as INR.
    rewrite HeqR'.
    rewrite <- strip_adversary_same_as_peel_strip_simpl
          , strip_adv_simpl_strip_adv_idempotent
          , strip_adversary_same_as_peel_strip_simpl with (b0:=b).
    rewrite strip_adv_simpl_peel_same_as_strip_adv in H7; assumption.

    assert (universe_ok (strip_adversary_univ U b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (adv_universe_ok (strip_adversary_univ U b))
      as STRIP_ADV_UNIV_OK
      by eauto using ok_adv_universe_strip_adversary_still_ok.

    generalize (H2 _ _ INR STRIP_UNIV_OK STRIP_ADV_UNIV_OK); simpl; intros ACT_SAFE.
    clear STRIP_UNIV_OK STRIP_ADV_UNIV_OK.

    apply honest_cmds_safe_advuniv in ACT_SAFE.

    assert (universe_ok U') as UOK.
    generalize H5; intros STEP.
    invert STEP; simpl in *.
    specialize (ACT_SAFE _ _ _ eq_refl H11).
    eapply honest_labeled_step_univ_ok;
      unfold adv_universe_ok in *;
      split_ands; eauto.

    destruct userData.
    eapply honest_cmd_implies_safe_action; eauto.
    reflexivity.

    assert (adv_universe_ok U') as AUOK by eauto.

    specialize (IHrCouldGenerate R _ b HeqR' H0 H1 H2 UOK AUOK _ INR'); split_ex; split_ands.

    exists (a__i :: x); split; eauto using ideal_multi_silent_stays_could_generate.
Qed.

Theorem refines_could_generate :
  forall A B (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : RealWorld.denote (RealWorld.Base B)),
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

Print Assumptions refines_could_generate.
