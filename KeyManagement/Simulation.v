From Coq Require Import
     List
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

Require Import MyPrelude Maps Common MapLtac.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Definition rstepSilent {A B : Type} (U1 U2 : RealWorld.universe A B) :=
  RealWorld.step_universe U1 Silent U2.

Definition istepSilent {A : Type} (U1 U2 : IdealWorld.universe A) :=
  IdealWorld.lstep_universe U1 Silent U2.

Inductive chan_key : Set :=
| Public (ch_id : IdealWorld.channel_id)
| Auth (ch_id : IdealWorld.channel_id): forall k,
    k.(RealWorld.keyUsage) = RealWorld.Signing -> chan_key
| Enc  (ch_id : IdealWorld.channel_id) : forall k,
    k.(RealWorld.keyUsage) = RealWorld.Encryption -> chan_key
| AuthEnc (ch_id : IdealWorld.channel_id) : forall k1 k2,
      k1.(RealWorld.keyUsage) = RealWorld.Signing
    -> k2.(RealWorld.keyUsage) = RealWorld.Encryption
    -> chan_key
.

Inductive msg_eq : forall t__r t__i,
    RealWorld.message t__r
    -> IdealWorld.message t__i * IdealWorld.channel_id * IdealWorld.channels * IdealWorld.permissions -> Prop :=

(* Still need to reason over visibility of channel -- plaintext really means everyone can see it *)
| PlaintextMessage' : forall content ch_id cs ps,
    ps $? ch_id = Some (IdealWorld.construct_permission true true) ->
    msg_eq (RealWorld.Plaintext content) (IdealWorld.Content content, ch_id, cs, ps)
.

Inductive action_matches :
    RealWorld.action -> IdealWorld.action -> Prop :=
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps p y,
      rw = (RealWorld.Input msg1 p y)
    -> iw = IdealWorld.Input msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
| Out : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps,
      rw = RealWorld.Output msg1
    -> iw = IdealWorld.Output msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
.

Definition simulates {A B : Type}
           (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop)
           (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) :=

(*  call spoofable *)

  (forall U__r U__i,
      R U__r U__i
      -> RealWorld.universe_ok U__r
      -> forall U__r',
          rstepSilent U__r U__r'
          -> exists U__i',
            istepSilent ^* U__i U__i'
            /\ RealWorld.universe_ok U__r'
            /\ R U__r' U__i')

/\ (forall U__r U__i,
      R U__r U__i
      -> RealWorld.universe_ok U__r
      -> forall a1 U__r',
          RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
          -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R U__r' U__i''
            (* /\ RealWorld.action_adversary_safe U__r.(RealWorld.all_keys) (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.all_ciphers) a1 *)
            /\ RealWorld.universe_ok U__r'
  )

/\ (forall U__r U__i,
      R U__r U__i
      -> forall a1 (U U__r' : RealWorld.universe A B),
        RealWorld.step_universe U (Action a1) U__r' (* excludes adversary steps *)
        -> RealWorld.findUserKeys U.(RealWorld.users) = RealWorld.findUserKeys U__r.(RealWorld.users)
        ->  RealWorld.action_adversary_safe
             (RealWorld.findUserKeys U__r.(RealWorld.users))
             a1
  (* and adversary couldn't have constructed message seen in a1 *)
  )

/\ R U__r U__i
/\ RealWorld.universe_ok U__r
.


Definition refines {A B : Type} (U1 : RealWorld.universe A B)(U2 : IdealWorld.universe A) :=
  exists R, simulates R U1 U2.

Infix "<|" := refines (no associativity, at level 70).


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

  Section AdversaryHelpers.
    Import RealWorld.

    Variable global_keys : keys.
    Variable honestk advk : key_perms.

    Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
      {| users       := U__r.(users)
       ; adversary   := {| key_heap := $0
                         ; msg_heap := []
                         ; protocol := advcode |}
       ; all_ciphers := U__r.(all_ciphers)
       ; all_keys    := U__r.(all_keys)
      |}.

    Definition msg_filter (sigM : { t & message t } ) : bool :=
      match sigM with
      (* | existT _ _ msg => msg_leaks_no_honest_keysb global_keys honestk cs msg *)
      | existT _ _ msg => msg_honestly_signedb honestk msg
      end.

    Definition clean_messages (msgs : queued_messages) :=
      List.filter msg_filter msgs.

    Definition clean_users {A} (usrs : honest_users A) :=
      (* usrs. *)
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages u_d.(msg_heap) |}) usrs.

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
                            ; protocol := Return b |}
          ; all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
          ; all_keys    := U__r.(all_keys)
         |}.

    Hint Resolve
         honest_cipher_filter_fn_proper
         honest_cipher_filter_fn_filter_proper
         honest_cipher_filter_fn_filter_transpose.

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
        -> honest_key honestk k
        -> k = cipher_signing_key c
        -> clean_ciphers honestk cs $? c_id = Some c.
    Proof.
      intros.
      eapply clean_ciphers_keeps_honest_cipher; auto.
      unfold honest_cipher_filter_fn, cipher_honestly_signed.
      cases c; subst; rewrite <- honest_key_honest_keyb; eauto.
    Qed.

    Hint Constructors msg_accepted_by_pattern msg_honestly_signed msg_contains_only_honest_public_keys.

    Lemma cipher_in_honest_ciphers_are_honestly_signed :
      forall cs c_id c honestk,
        cs $? c_id = Some c
        -> ciphers_honestly_signed honestk cs
        -> cipher_honestly_signed honestk c = true.
    Proof.
      induction 2; clean_map_lookups.
      cases (c_id0 ==n c_id); subst; clean_map_lookups; eauto.
    Qed.

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

    Lemma enc_message_has_honest_signing_key' :
      forall {t} k__signid k__encid allks honestk (msg : message t) cipherMsg,
          encryptMessage allks (k__signid,true) (k__encid,true) msg = Some cipherMsg
        -> honestk $? k__signid = Some true
        -> honest_key honestk k__signid
        /\ cipherMsg = SigEncCipher k__signid k__encid msg.
    Proof.
      intros.
      unfold encryptMessage in *.
      simpl in *.
      cases (allks $? k__signid); try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      cases (allks $? k__encid); try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      unfold sign_if_ok in *; simpl in *.
      clean_map_lookups; intuition eauto.
    Qed.

    Lemma enc_message_has_honest_signing_key :
      forall {t} k__signid k__encid kp__sign kp__enc allks honestk (msg : message t) cipherMsg,
          encryptMessage allks (k__signid,kp__sign) (k__encid,kp__enc) msg = Some cipherMsg
        -> honestk $? k__signid = Some kp__sign
        -> honest_key honestk k__signid
        /\ cipherMsg = SigEncCipher k__signid k__encid msg.
    Proof.
      intros.
      unfold encryptMessage in *.
      cases kp__sign; subst; simpl in *; eauto using enc_message_has_honest_signing_key'.
      exfalso.

      simpl in *; cases (allks $? k__signid);
        cases (allks $? k__encid); subst; clean_map_lookups; try discriminate.
      destruct k; destruct k0; cases keyUsage; cases keyUsage0; discriminate.
      destruct k; cases keyUsage; discriminate.
    Qed.

    Lemma enc_message_is_some_own_private_signing_key :
      forall {t} k__signid k__encid kp__sign kp__enc allks honestk (msg : message t) cipherMsg,
          encryptMessage allks (k__signid,kp__sign) (k__encid,kp__enc) msg = Some cipherMsg
        -> honestk $? k__signid = Some kp__sign
        -> kp__sign = true.
    Proof.
      intros.
      unfold encryptMessage in *.
      cases kp__sign; subst; eauto.
      exfalso.

      simpl in *; cases (allks $? k__signid);
        cases (allks $? k__encid); subst; clean_map_lookups; try discriminate.
      destruct k; destruct k0; cases keyUsage; cases keyUsage0; discriminate.
      destruct k; cases keyUsage; discriminate.
    Qed.

    Lemma sign_message_has_honest_signing_key' :
      forall {t} k_id allks honestk (msg : message t) cipherMsg,
          signMessage allks (k_id,true) msg = Some cipherMsg
        -> honestk $? k_id = Some true
        -> honest_key honestk k_id
        /\ cipherMsg = SigCipher k_id msg.
    Proof.
      intros.
      unfold signMessage in *; simpl in *.
      cases (allks $? k_id); subst; try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      unfold sign_if_ok in *; simpl in *.
      clean_map_lookups; eauto.
    Qed.

    Lemma sign_message_has_honest_signing_key :
      forall {t} k_id kp allks honestk (msg : message t) cipherMsg,
          signMessage allks (k_id,kp) msg = Some cipherMsg
        -> honestk $? k_id = Some kp
        -> honest_key honestk k_id
        /\ cipherMsg = SigCipher k_id msg.
    Proof.
      intros.
      unfold signMessage in *; simpl in *.
      cases kp; subst; eauto using sign_message_has_honest_signing_key'.
      exfalso.
      cases (allks $? k_id); subst; try discriminate.
      destruct k; unfold sign_if_ok in *;
        cases keyUsage; simpl in *; discriminate.
    Qed.

    Lemma sign_message_is_some_own_private_signing_key :
      forall {t} k_id kp allks honestk (msg : message t) cipherMsg,
          signMessage allks (k_id,kp) msg = Some cipherMsg
        -> honestk $? k_id = Some kp
        -> kp = true.
    Proof.
      intros.
      unfold signMessage in *; simpl in *.
      cases kp; subst; eauto.
      exfalso.
      cases (allks $? k_id); subst; try discriminate.
      destruct k; unfold sign_if_ok in *;
        cases keyUsage; simpl in *; discriminate.
    Qed.

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
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; Equal_eq; subst; eauto.
      unfold honest_cipher_filter_fn.
      assert (cipher_honestly_signed uks e = true) by eauto using ciphers_honestly_signed_mapsto.
      rewrite H2; trivial.
    Qed.



    Lemma clean_messages_keeps_honestly_signed :
      forall {t} (msg : message t) msgs honestk,
        msg_honestly_signed honestk msg
        -> clean_messages honestk (msgs ++ [existT _ _ msg])
          = clean_messages honestk msgs ++ [existT _ _ msg].
    Proof.
      intros; unfold clean_messages.
      rewrite message_honestly_signed_message_honestly_signedb in *.
      induction msgs; simpl; eauto.
      - rewrite H; trivial.
      - cases (msg_filter honestk a); subst; eauto.
        rewrite IHmsgs; trivial.
    Qed.

    Lemma accepted_safe_msg_pattern_honestly_signed :
      forall {t} (msg : message t) honestk pat,
        msg_pattern_safe honestk pat
        -> msg_accepted_by_pattern pat msg
        -> msg_honestly_signed honestk msg.
    Proof.
      induction 2;
        match goal with
        | [ H : msg_pattern_safe _ _ |- _] => invert H
        end; econstructor; eauto;
          match goal with
          | [ m1 : message ?t1 , m2 : message ?t2 |- message (Pair ?t1 ?t2) ] => exact (MsgPair m1 m2)
          end.
    Qed.

    Hint Resolve accepted_safe_msg_pattern_honestly_signed.

    Lemma clean_message_keeps_safely_patterned_message :
      forall {t} (msg : message t) honestk msgs pat,
        msg_pattern_safe honestk pat
        -> msg_accepted_by_pattern pat msg
        -> clean_messages honestk (existT _ _ msg :: msgs)
          = (existT _ _ msg) :: clean_messages honestk msgs.
    Proof.
      intros.
      assert (msg_honestly_signed honestk msg) by eauto.
      unfold clean_messages; simpl;
        match goal with
        | [ H : msg_honestly_signed _ _ |- _ ] => rewrite message_honestly_signed_message_honestly_signedb in H; rewrite H
        end; trivial.
    Qed.

    Lemma clean_users_idempotent_msg_queue_filter :
      forall msg_heap honestk,
          message_queue_safe honestk msg_heap
        -> clean_messages honestk msg_heap = msg_heap.
    Proof.
      induction msg_heap; auto; intros.
      destruct a; invert H.
      rewrite message_honestly_signed_message_honestly_signedb in H2.
      unfold clean_messages, msg_filter; simpl. rewrite H2. f_equal; eauto.
    Qed.

    Lemma clean_users_idempotent :
      forall {A} (usrs : honest_users A) honestk,
          (forall u_id u_d msgs,
              usrs $? u_id = Some u_d
              -> msgs = msg_heap u_d
              -> message_queue_safe honestk msgs)
        -> clean_users honestk usrs = usrs.
    Proof.
      induction usrs using P.map_induction_bis; intros; Equal_eq; simpl; auto;
        apply map_eq_Equal; unfold Equal; unfold clean_users; intros.
      - rewrite map_o, !empty_o; trivial.
      - cases ( x ==n y ); subst; clean_map_lookups.
        + rewrite map_o; clean_map_lookups. simpl.
          destruct e; simpl in *; f_equal; f_equal.

          assert ( usrs $+ (y, {| key_heap := key_heap; protocol := protocol; msg_heap := msg_heap |}) $? y = Some {| key_heap := key_heap; protocol := protocol; msg_heap := msg_heap |}) as YIN by (clean_map_lookups; trivial).

          apply clean_users_idempotent_msg_queue_filter; eauto.

        + rewrite map_o; clean_map_lookups. simpl.
          rewrite <- map_o.
          unfold clean_users in IHusrs; rewrite IHusrs; auto.
          intros.
          specialize (H0 u_id); cases (u_id ==n x); subst; clean_map_lookups; auto. eapply H0; clean_map_lookups; auto; auto.
    Qed.

    Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
         findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

    Lemma clean_users_cleans_user :
      forall {A} (usrs : honest_users A) honestk u_id u_d u_d',
        usrs $? u_id = Some u_d
        -> u_d' = {| key_heap := u_d.(key_heap)
                  ; protocol := u_d.(protocol)
                  ; msg_heap :=  clean_messages honestk u_d.(msg_heap) |}
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
                                       ; msg_heap := msgs |}
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
                                                ; msg_heap :=  clean_messages honestk u.(msg_heap) |}).
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
             ; msg_heap := clean_messages (findUserKeys U.(users)) user_data.(msg_heap) |}
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

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac.
      unfold message_queues_ok, message_queue_ok, user_queue in *; intros.
      cases (clean_users (findUserKeys users) users $? u_id); subst; clean_map_lookups.
      apply clean_users_cleans_user_inv in Heq; invert Heq; split_ands.
      specialize (H1 u_id x). rewrite H0 in H1.
      rewrite clean_users_no_change_findUserKeys; subst; simpl in *; rewrite H2; eauto.
    Qed.

    Lemma honest_enc_cipher_not_cleaned :
      forall {t} cs k__signid k__encid kp__enc allks honestk c_id (msg : message t) cipherMsg,
          encryptMessage allks (k__signid, true) (k__encid,kp__enc) msg = Some cipherMsg
        -> honestk $? k__signid = Some true
        -> clean_ciphers honestk (cs $+ (c_id, cipherMsg)) = clean_ciphers honestk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (enc_message_has_honest_signing_key _ _ _ _ _ _ H H0) as HONEST; split_ands.
      eapply clean_ciphers_added_honest_cipher_not_cleaned; subst; eauto.
    Qed.

    Lemma honest_sign_cipher_not_cleaned :
      forall {t} cs k_id allks honestk (msg : message t) c_id cipherMsg,
          signMessage allks (k_id,true) msg = Some cipherMsg
        -> honestk $? k_id = Some true
        -> clean_ciphers honestk (cs $+ (c_id, cipherMsg)) = clean_ciphers honestk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (sign_message_has_honest_signing_key _ _ _ _ H H0) as HONEST; split_ands.
      eapply clean_ciphers_added_honest_cipher_not_cleaned; subst; eauto.
    Qed.

    Hint Resolve
         honest_enc_cipher_not_cleaned
         honest_sign_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent.

    Hint Resolve
         enc_message_is_some_own_private_signing_key
         enc_message_has_honest_signing_key
         sign_message_is_some_own_private_signing_key
         sign_message_has_honest_signing_key
         message_queue_safe_after_msg_keys
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user
         (* adv_no_honest_keys_after_honestk_no_private_key_msg *)
    .

    Hint Constructors ciphers_honestly_signed.

    Lemma honest_silent_step_advuniv_implies_univ_ok :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> universe_ok
              {| users := usrs
               ; adversary := adv
               ; all_ciphers := cs
               ; all_keys := gks |}
        -> forall (cmd : user_cmd C),
            (exists cmdc, usrs $? u_id = Some {| key_heap := ks; protocol := cmdc; msg_heap := qmsgs |})
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Silent
              ->  exists cmdc', universe_ok
                  {| users := usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |})
                   ; adversary := adv'
                   ; all_ciphers := cs'
                   ; all_keys := gks' |}.
    Proof.

      Ltac fix_up_goals :=
        repeat match goal with
               | [ usrs : honest_users _
                    , H : _ $+ (?k1,_) $? ?k2 = Some _ 
                        |- message_queue_safe _ _ _ _ ] => cases (k1 ==n k2); subst; clean_map_lookups
               | [ |- context[ findUserKeys (_ $+ (_, {| key_heap := _ $k++ _ ; protocol := _ ; msg_heap := _ |})) ] ] =>
                 erewrite RealWorld.findUserKeys_readd_user_addnl_keys by eauto
               (* | [ H1 : encryptMessage _ (?kid, ?kp) _ _ _ = Some _ *)
               (*   , H2 : ?hon $? ?kid = Some _ |- _] => *)
               (*   assert (kp = true) by eauto; subst; eapply enc_message_has_honest_signing_key with (honestk := hon) in H1; eauto *)
               end.

      induction 1; inversion 3; inversion 1; unfold universe_ok in *; simpl in *; intros;
        subst; try discriminate; eauto;
          repeat match goal with
                 | [ H : exists _, _ |- _] => destruct H
                 | [ H : ?x = ?x |- _ ] => clear H
                 end; eexists;
            try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto;
            split_ands; intuition idtac; auto;
              fix_up_goals; eauto; simpl.
      simpl.

    Admitted.

    Lemma honest_silent_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' b,
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) cs__s honestk,
          honestk = findUserKeys usrs
          -> (exists cmdc, usrs $? u_id = Some {| key_heap := ks; protocol := cmdc; msg_heap := qmsgs |})
          -> adv_no_honest_keys honestk adv.(key_heap)
          -> ciphers_honestly_signed honestk cs
          (* -> key_heaps_compatible honestk adv.(key_heap) *)
          -> cs__s = clean_ciphers honestk cs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd' cs__s' pwless_adv,
              cs__s' = clean_ciphers honestk cs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Silent
              -> is_powerless pwless_adv b honestk
              -> step_user (B:=B) lbl u_id (usrs, pwless_adv, cs__s, gks, ks, qmsgs, cmd) (usrs', pwless_adv, cs__s', gks', ks', qmsgs', cmd').
    Proof.

      Ltac foo1 :=
        match goal with
        |  [ H : ?x = ?x |- _ ] => clear H
        | [ |- clean_ciphers _ _ _ $? _ = Some _ ] => eapply clean_ciphers_keeps_honest_cipher
        | [ |- honest_cipher_filter_fn _ _ _ _ = _ ] => unfold honest_cipher_filter_fn, cipher_honestly_signed
        | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H
        | [ |- context [match ?matchee with _ => _ end] ] => cases matchee; subst
        | [ |- ?hasp && _ = _ ] => cases hasp; simpl
        | [ |- false = true ] => exfalso; simpl in *
        | [ H : _ && _ = true |- _ ] => apply andb_prop in H; split_ands
        | [ H : match ?matchee with _ => _ end = _
         ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
        | [ H  : ciphers_honestly_signed ?gks ?ks ?cs
          , H1 : ?cs $? _ = Some ?c
            |- cipher_honestly_signed ?gks ?ks ?c = true] => econstructor; eauto
              (* unfold ciphers_honestly_signed in H; rewrite for_all_iff in H by auto; eapply H *)
        | [ |- MapsTo _ _ _ ] => apply find_mapsto_iff
        (* | [ H : cipher_honestly_signed _ _ _ = true |- _ ] => unfold cipher_honestly_signed,honest_signing_key, honest_key in H *)
        end.

      Ltac doit :=
        repeat foo1; auto;
        match goal with
        | [ H  : ciphers_honestly_signed ?gks ?ks ?cs
          , H1 : ?cs $? _ = Some ?c
               |- False ] => assert (cipher_honestly_signed gks ks c)
        end; repeat foo1; eauto.

      induction 1; inversion 6; inversion 2; intros; subst;
        repeat match goal with
               | [ H : Action _ = Silent |- _ ] => invert H
               end;
        econstructor;
        eauto using honest_enc_cipher_not_cleaned, honest_sign_cipher_not_cleaned;
        try solve [doit; discriminate].

      - assert (kp__sign = true) by eauto; subst.
        invert H8; eapply honest_enc_cipher_not_cleaned; eauto using findUserKeys_has_private_key_of_user.
      - assert (MapsTo c_id (SigEncCipher k__signid k__encid msg) cs') by (rewrite find_mapsto_iff; auto).
        assert (cipher_honestly_signed (findUserKeys usrs') (SigEncCipher k__signid k__encid msg) = true)
          by eauto using ciphers_honestly_signed_mapsto.
        eapply clean_ciphers_keeps_honest_cipher; eauto.

      - assert (kp = true) by eauto; subst.
        invert H4; eapply honest_sign_cipher_not_cleaned; eauto using findUserKeys_has_private_key_of_user.
      - assert (MapsTo c_id (SigCipher k_id msg) cs') by (rewrite find_mapsto_iff; auto).
        assert (cipher_honestly_signed (findUserKeys usrs') (SigCipher k_id msg) = true)
          by eauto using ciphers_honestly_signed_mapsto.
        eapply clean_ciphers_keeps_honest_cipher; eauto.
    Qed.

    Lemma honest_labeled_step_nochange_honestk :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          (* -> user_keys usrs u_id = Some ks *)
          -> action_adversary_safe (findUserKeys usrs) a
          -> message_queues_ok usrs (findUserKeys usrs)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc |}
              (* -> user_keys usrs' u_id = Some ks' *)
              (*   -> findUserKeys usrs' $k++ ks' *)
              (*     = findUserKeys usrs'. *)
                -> findUserKeys (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |}))
                  = findUserKeys usrs'.
    Proof.
      induction 1; inversion 1; inversion 4; try discriminate; subst; eauto;
        unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end;
          split_ands; intros.

      - erewrite findUserKeys_readd_user_addnl_keys; eauto.
        assert (msg_honestly_signed (findUserKeys usrs') msg) by eauto.
        unfold message_queues_ok in *.
        assert (user_queue usrs' u_id = Some (existT _ _ msg :: qmsgs'))
          as UQ
          by (unfold user_queue; context_map_rewrites; simpl; trivial).
        specialize (H13 _ _ UQ).
        invert H13.
        assert (msg_contains_only_honest_public_keys (findUserKeys usrs') msg) as HPK by auto.
        pose proof (safe_messages_have_only_honest_public_keys HPK).
        apply map_eq_Equal; unfold Equal; intros.
        specialize H5 with y.
        cases (findUserKeys usrs' $? y); subst; split_ors; split_ands; try contradiction.
        + erewrite merge_perms_adds_ks1; eauto.
        + erewrite merge_perms_chooses_greatest; unfold greatest_permission; eauto; rewrite orb_false_r; auto.
        + rewrite merge_perms_adds_no_new_perms; auto.
      - cases (rec_u_id ==n u_id); subst; clean_map_lookups; simpl; eauto.
        + rewrite map_add_eq.
          erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto.
        + erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto.
    Qed.

    (* Lemma honest_labeled_step_nochange_honestk : *)
    (*   forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd', *)
    (*     step_user lbl u_id bd bd' *)
    (*     -> forall (cmd : user_cmd C) a, *)
    (*       bd = (usrs, adv, cs, gks, ks, qmsgs, cmd) *)
    (*       -> user_keys usrs u_id = Some ks *)
    (*       -> lbl = Action a *)
    (*       -> forall cmd', *)
    (*           bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd') *)
    (*           (* -> forall cmdc', *) *)
    (*             (* usrs $? uid = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc |} *) *)
    (*           -> user_keys usrs' u_id = Some ks' *)
    (*             -> findUserKeys usrs' $k++ ks' *)
    (*               = findUserKeys usrs'. *)
    (*             (* -> findUserKeys (usrs' $+ (uid, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |})) *) *)
    (*             (*   = findUserKeys usrs'. *) *)
    (* Proof. *)
    (*   induction 1; inversion 1; inversion 3; try discriminate; subst; eauto. *)
    (* Qed. *)

    (*     Lemma honest_labeled_step_nochange_honestk : *)
    (*   forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd', *)
    (*     step_user lbl (Some u_id) bd bd' *)
    (*     -> forall (cmd : user_cmd C) a, *)
    (*       bd = (usrs, adv, cs, gks, ks, qmsgs, cmd) *)
    (*       -> action_adversary_safe (findUserKeys usrs) a *)
    (*       -> message_queues_ok usrs (findUserKeys usrs) *)
    (*       -> lbl = Action a *)
    (*       -> forall cmd', *)
    (*           bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd') *)
    (*           -> forall uid cmdc cmdc', *)
    (*             usrs $? uid = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc |} *)
    (*             -> findUserKeys (usrs' $+ (uid, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |})) *)
    (*               = findUserKeys usrs'. *)
    (* Proof. *)
    (*   induction 1; inversion 1; inversion 4; try discriminate; subst; eauto; *)
    (*     unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end; *)
    (*       split_ands; intros. *)

    (*   - specialize (H13 _ _ H1); simpl in *; invert H13. *)
    (*     assert (msg_contains_only_honest_public_keys (findUserKeys usrs') msg) by eauto. *)
    (*     erewrite findUserKeys_readd_user_addnl_keys; eauto. *)
    (*     specialize (safe_messages_have_only_honest_public_keys H2); intros. *)
    (*     apply map_eq_Equal; unfold Equal; intros. *)
    (*     specialize (H5 y); cases (findUserKeys usrs' $? y); split_ors; split_ands; try contradiction. *)
    (*     + erewrite merge_perms_adds_ks1; eauto. *)
    (*     + erewrite merge_perms_chooses_greatest; eauto; *)
    (*         unfold greatest_permission. rewrite orb_false_r; auto. *)
    (*     + rewrite merge_perms_adds_no_new_perms; auto. *)

    (*   - assert (uid <> rec_u_id) by admit. (* this should be true because of operational semantics, but fresh variable is being created *) *)
    (*     rewrite map_ne_swap; eauto. *)
    (*     erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto. *)

    (* Admitted. *)


    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a (b : B),
        step_user lbl u_id bd bd'
        -> action_adversary_safe (findUserKeys usrs) a
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Action a
              -> pwless_adv = {| key_heap := key_heap adv
                              ; protocol := Return b
                              ; msg_heap := adv.(msg_heap) |}
              -> pwless_adv' = {| key_heap := key_heap adv'
                               ; protocol := Return b
                               ; msg_heap := adv'.(msg_heap) |}
              -> step_user lbl u_id
                          (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, cmd)
                          (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', cmd').
    Proof.
      induction 1; inversion 5; inversion 4; intros;
        subst; try discriminate;
          try solve [ econstructor; eauto ];
          unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end;
            split_ands.

      - erewrite clean_message_keeps_safely_patterned_message; eauto.
        econstructor; eauto.

      - erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        econstructor; eauto.
        eapply clean_users_cleans_user; eauto.
        simpl.
        rewrite clean_users_add_pull; simpl.
        rewrite clean_messages_keeps_honestly_signed; simpl; trivial.
    Qed.


    (* Lemma no_honest_keys_in_msg_if_not_need_encryption : *)
    (*   forall {t} (msg : message t) honestk, *)
    (*     msg_leaks_no_honest_keys honestk msg *)
    (*     -> forall k_id kp kp', *)
    (*           findKeys msg $? k_id = Some kp *)
    (*         -> honestk $? k_id = Some kp' *)
    (*         -> kp' = false. *)
    (* Proof. *)
    (*   induction 1; intros; subst; simpl in *; clean_map_lookups; eauto. *)
    (*   - destruct kp; simpl in *. *)
    (*     cases (k_id ==n k0); cases (gks $? k0); subst; *)
    (*       clean_map_lookups; eauto. *)
    (*     cases kp'; eauto. *)
    (*     exfalso. *)
    (*     assert (honest_key gks honestk k0); eauto. *)
    (*   - assert ( findKeys gks msg1 $k++ findKeys gks msg2 $? k_id = Some kp ) as SPL by assumption. *)
    (*     apply merge_perms_split in SPL; split_ors; eauto. *)
    (* Qed. *)

    Lemma message_queue_safe_after_adding_dishonest_keys :
      forall honestk msgk msgs,
        message_queue_safe honestk msgs
        (* -> (forall k_id kp kp', msgk $? k_id = Some kp -> honestk $? k_id = Some kp' -> kp' = false) *)
        -> message_queue_safe (honestk $k++ msgk) msgs.
    Proof.
      unfold message_queue_safe; induction 1; intros; eauto.

      econstructor; eauto.
      destruct x.
      apply message_honestly_signed_after_new_msg_keys; auto.
    Qed.

    Lemma Forall_app :
      forall {A} (P : A -> Prop) (l : list A) a,
        Forall P (l ++ [a]) <-> Forall P (a :: l).
    Proof.
      split; intros;
        rewrite Forall_forall in *; intros;
          eapply H.
      - destruct H0; eauto; subst; apply in_or_app; eauto.
      - apply in_app_or in H0; split_ors; eauto.
        invert H0; eauto.
        invert H1.
    Qed.

    (* Lemma honest_labeled_step_advuniv_implies_univ_ok' : *)
    (*   forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a, *)
    (*     step_user lbl u_id bd bd' *)
    (*     -> universe_ok *)
    (*           {| users := usrs *)
    (*            ; adversary := adv *)
    (*            ; all_ciphers := cs *)
    (*            ; all_keys := gks |} *)
    (*     (* -> ciphers_honestly_signed gks honestk cs *) *)
    (*     -> forall (cmd : user_cmd C) honestk, *)
    (*         (exists cmdc, usrs $? u_id = Some {| key_heap := ks; protocol := cmdc; msg_heap := qmsgs |}) *)
    (*       -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd) *)
    (*       -> honestk = findUserKeys usrs *)
    (*       -> forall cmd', *)
    (*             bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd') *)
    (*           -> lbl = Action a *)
    (*           (* -> action_adversary_safe gks honestk cs a *) *)
    (*           ->  exists cmdc', universe_ok *)
    (*               {| users := usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |}) *)
    (*                ; adversary := adv' *)
    (*                ; all_ciphers := cs' *)
    (*                ; all_keys := gks' |}. *)
    (* Proof. *)
    (*   induction 1; inversion 3; inversion 2; unfold universe_ok in *; simpl in *; intros; *)
    (*     subst; try discriminate; eauto; *)
    (*       match goal with *)
    (*       | [ H : exists _, _ |- _ ] => destruct H *)
    (*       end; split_ands; eexists; intuition idtac. *)

    (*   - erewrite findUserKeys_readd_user_addnl_keys; eauto. *)


    (* Admitted. *)

    Lemma honest_labeled_step_advuniv_implies_univ_ok' :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a,
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> message_queues_ok usrs honestk
          -> user_queue usrs u_id = Some qmsgs
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Action a
              -> action_adversary_safe honestk a
              -> honestk' = findUserKeys usrs'
              -> keys_good gks'
              /\ message_queues_ok usrs' honestk'
              /\ message_queue_ok qmsgs' honestk'.
    Proof.
      induction 1; inversion 1; inversion 5; try discriminate; eauto; intros; subst; eauto;
        unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end; split_ands.

      - intuition idtac.
        assert (message_queue_ok (existT message t0 msg :: qmsgs') (findUserKeys usrs')).
        eapply H14; eauto.
        invert H1; eauto.
      - erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
        intuition idtac.
        unfold message_queues_ok, message_queue_ok; intros.
        unfold user_queue in *.
        cases (rec_u_id ==n u_id1); subst; clean_map_lookups; eauto; simpl in *.
        rewrite add_eq_o in H4; simpl in *; invert H4; eauto.
        apply Forall_app; constructor; eauto.
        eapply H15; eauto.
        unfold user_queue; rewrite H2; trivial.
        rewrite add_neq_o in H4; eauto.
        cases (usrs $? u_id1); subst; try discriminate.
        eapply H15; eauto.
        unfold user_queue. rewrite Heq; trivial.
        unfold message_queue_ok.
        eapply H15; eauto.
    Qed.

    Lemma honest_labeled_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl a,
        step_universe U lbl U'
        -> lbl = Action a
        -> action_adversary_safe (findUserKeys U.(users)) a
        -> universe_ok U
        -> universe_ok U'.
    Proof.
      intros.
      invert H; auto; try discriminate.
      destruct U; destruct userData; unfold build_data_step in *; simpl in *.

      unfold universe_ok in *; simpl in *; split_ands.

      (* eapply honest_labeled_step_advuniv_implies_univ_ok'. *)
      assert (  keys_good gks
              /\ message_queues_ok usrs (findUserKeys usrs)
              /\ message_queue_ok qmsgs (findUserKeys usrs) ).
      eapply honest_labeled_step_advuniv_implies_univ_ok'; eauto.
      unfold user_queue; rewrite H3; eauto.

      intuition idtac.
      erewrite honest_labeled_step_nochange_honestk; eauto.
      unfold message_queues_ok; intros.
      unfold user_queue in *.
      cases (u_id ==n u_id0); subst.
      + rewrite add_eq_o in H6; invert H6; eauto.
      + rewrite add_neq_o in H6; auto.
        cases (usrs $? u_id0); subst; try discriminate.
        assert (user_queue usrs u_id0 = Some msgs) as UQ by (unfold user_queue; context_map_rewrites; auto).
        specialize (H2 _ _ UQ); eauto.
    Qed.

    (* Lemma safe_actions_adv_univ_still_safe_strip_adv : *)
    (*   forall {A B} (U : universe A B) b cs a__r, *)
    (*     action_adversary_safe (all_keys (strip_adversary U b)) (findUserKeys (users (strip_adversary U b))) cs a__r *)
    (*     -> action_adversary_safe (RealWorld.all_keys U) (RealWorld.findUserKeys (RealWorld.users U)) cs a__r. *)
    (* Proof. *)
    (*   destruct U; simpl; intros. *)
    (*   rewrite clean_users_no_change_findUserKeys in H; auto. *)
    (* Qed. *)

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
      match goal with [H : Action _ = _ |- _] => invert H end.
    Qed.

    Lemma honest_labeled_step_nochange_adversary_protocol :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
            -> adv.(protocol) = adv'.(protocol).
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
    Qed.



    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
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
        -> exists (u_id : user_id) u_d u_d' usrs' adv' cs' gks' ks' qmsgs' cmd',
            usrs $? u_id = Some u_d
          /\ step_user (Action a) u_id (build_data_step U u_d)
                      (usrs', adv', cs', gks', ks', qmsgs', cmd')
          /\ U' = {| users        := usrs' $+ (u_id, u_d')
                  ; adversary    := adv'
                  ; all_ciphers  := cs'
                  ; all_keys     := gks'
                 |}
          /\ U'.(users) $? u_id = Some u_d'
          /\ u_d' = {| key_heap := ks'
                    ; protocol := cmd'
                    ; msg_heap := qmsgs'
                   |}.
    Proof.
      intros.
      invert H; eauto.
      invert H1.
      unfold build_data_step; simpl.
      repeat eexists; intuition eauto.
    Qed.

    Lemma labeled_honest_step_advuniv_implies_stripped_univ_step :
      forall {A B} (U U' : universe A B) act b,
        universe_ok U
        (* -> adv_no_honest_keys (findUserKeys (RealWorld.users U)) (U.(adversary).(key_heap)) *)
        -> action_adversary_safe (findUserKeys U.(users)) act
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

      rewrite HeqUU in H2; unfold build_data_step in H2; simpl in *.
      rewrite HeqUU; unfold strip_adversary; simpl; eapply StepUser with (u_id:=x).
      - simpl; eapply clean_users_cleans_user; eauto.
      - unfold build_data_step; simpl.
        eapply honest_labeled_step_advuniv_implies_honest_step_origuniv; subst; eauto.
        + simpl; reflexivity.
        + simpl; reflexivity.
        + simpl; repeat f_equal.
      - unfold buildUniverse; subst; simpl in *.
        destruct x0; subst; simpl in *.
        erewrite honest_labeled_step_nochange_honestk; eauto.

        repeat f_equal.
        apply map_eq_Equal; unfold Equal; intros.
        unfold clean_users at 1.
        cases (x ==n y); clean_map_lookups.
        + rewrite map_o; clean_map_lookups; simpl; trivial.
        + rewrite map_o; clean_map_lookups; simpl.
          rewrite <- map_o.
          unfold clean_users; trivial.
    Qed.

    Lemma adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks' qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> adv_no_honest_keys (findUserKeys usrs) adv.(key_heap)
          -> message_queue_safe honestk adv.(msg_heap)
          -> cs__s = clean_ciphers honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 6; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Send *)
      - erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.

      (* Encrypt *)
      - clear H7 H20.

        unfold encryptMessage in *; simpl in *.
        cases (gks' $? k__signid); try discriminate.
        destruct k; cases keyUsage; try discriminate.
        cases (gks' $? k__encid); try discriminate.
        destruct k; cases keyUsage; try discriminate.
        unfold sign_if_ok in H5; cases kp__sign; simpl in *; try discriminate; trivial.
        invert H5.

        specialize (H17 k__signid); split_ors; contra_map_lookup.
        destruct H; split_ands; contra_map_lookup.
        assert (honest_key (findUserKeys usrs') k__signid -> False).
        intros.
        invert H; contra_map_lookup. admit.
        (* invert H6; contra_map_lookup; simpl in *; split_ors; split_ands; contra_map_lookup; contradiction. *) admit.

        eapply clean_ciphers_eliminates_added_dishonest_cipher; clean_map_lookups; simpl; eauto. admit.
        (* eapply not_honest_signing_key_honest_signing_keyb; trivial. *) admit.

      - clear H3 H16.

        unfold signMessage in *; simpl in *.
        cases (gks' $? k_id); try discriminate.
        destruct k; cases keyUsage; try discriminate.
        unfold sign_if_ok in H1; cases kp; simpl in *; try discriminate; trivial.
        invert H1.

        specialize (H13 k_id); split_ors; contra_map_lookup.
        destruct H1; split_ands; contra_map_lookup.
        assert (honest_key (findUserKeys usrs') k_id -> False).
        intros.
        (* invert H3; contra_map_lookup. *)
        (* invert H4; contra_map_lookup; simpl in *; split_ors; split_ands; contra_map_lookup. contradiction. *)

        (* eapply clean_ciphers_eliminates_added_dishonest_cipher; clean_map_lookups; simpl; eauto. *)
        (* eapply not_honest_signing_key_honest_signing_keyb; trivial. *)
    Admitted.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks' qmsgs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          -> usrs__s = clean_users honestk usrs
          -> forall cmd' honestk' usrs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Send *)
      - erewrite <- findUserKeys_readd_user_same_keys_idempotent; eauto.
        admit.

    Admitted.


    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) (b : B)
        (cmd : user_cmd B) lbl u_id (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs,
        step_user lbl u_id
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, cmd)
        -> R (strip_adversary U__r b) U__i
        -> universe_ok U__r
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := adv.(key_heap) $k++ ks; protocol := cmd; msg_heap := qmsgs |}) b) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.
      unfold universe_ok in *; split_ands.

      (* some rewrites to get the goal matching the R assumption *)
      (* match goal with *)
      (* | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] => *)
      (*   assert ( cs = cs' ) as CS by (eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto); *)
      (*     assert ( us = us' ) as US by (eapply adv_step_implies_no_user_impact_after_cleaning; eauto) *)
      (* end; rewrite <- CS, <- US; clear CS US. *)

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
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i
          -> RealWorld.universe_ok U__r
          -> forall U__r' : RealWorld.universe A B,
              rstepSilent U__r U__r'
              -> exists U__i' : IdealWorld.universe A, (istepSilent) ^* U__i U__i' /\ RealWorld.universe_ok U__r' /\ R U__r' U__i')

      -> RealWorld.universe_ok U__ra
      -> R (strip_adversary U__ra b) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 /\ RealWorld.universe_ok U__ra'
                 /\ R (strip_adversary U__ra' b) U__i'.
  Proof.
    intros. 
    (* unfold RealWorld.universe_ok in H0; RealWorld.split_ands; simpl in *. *)

    assert (RealWorld.universe_ok U__ra) as UNIV_OK by assumption.
    rename H0 into for_split.
    unfold RealWorld.universe_ok in for_split; split_ands.

    assert (RealWorld.universe_ok (strip_adversary U__ra b)) as STRIP_UNIV_OK by (eauto using ok_universe_strip_adversary_still_ok).

    match goal with
    | [ H : rstepSilent _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - 
      assert (UNIV_STEP :
                rstepSilent
                  (strip_adversary U__ra b)
                  (strip_adversary (RealWorld.buildUniverse usrs adv cs gks u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |}) b) ).

      eapply RealWorld.StepUser;
        eauto using user_in_univ_user_in_stripped_univ.

      admit.

      unfold strip_adversary; simpl.

      unfold strip_adversary, RealWorld.buildUniverse;
        rewrite clean_users_idempotent; simpl; auto.
      intros; subst.
      erewrite RealWorld.findUserKeys_readd_user_same_keys_idempotent'; eauto.



      (* admit. *)
      (* eapply honest_silent_step_advuniv_implies_honest_step_origuniv; intros; *)
      (*   try rewrite clean_users_idempotent; eauto. *)
      (* admit. *)
      (* admit. *)
      (* admit. *)
      (* admit. *)
      (* eapply RealWorld.find_user_keys_universe_user; eauto. admit. *)
      (* eauto. *)
      (* unfold strip_adversary; simpl; smash_universe. *)

      (* unfold RealWorld.build_data_step in H5. *)
      (* eapply honest_silent_step_nochange_adversaries in H5; [| reflexivity..]; rewrite H5; trivial. *)

    (* eapply H; eauto. *)
      admit.
      admit.
      admit.
      admit.

    - exists U__i.
      split; [|split].
      + eapply TrcRefl.
      + admit. (* universe still ok *)
      + eapply adv_step_stays_in_R; eauto.

  Admitted.

  Lemma simulates_with_adversary_labeled :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      (forall U__r U__i,
          R U__r U__i
          -> RealWorld.universe_ok U__r
          -> forall a1 U__r',
              RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
              -> exists a2 U__i' U__i'',
                istepSilent^* U__i U__i'
              /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
              /\ action_matches a1 a2
              /\ R U__r' U__i''
              (* /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.users)) a1 *)
              /\ RealWorld.universe_ok U__r')
      -> (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
            R U__r U__i ->
            forall (a__r : RealWorld.action) (U__ra U__r' : RealWorld.universe A B),
              RealWorld.step_universe U__ra (Action a__r) U__r'
              -> RealWorld.findUserKeys (U__ra.(RealWorld.users)) = RealWorld.findUserKeys (U__r.(RealWorld.users))
              -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__r)) a__r)
      -> R (strip_adversary U__ra b) U__i
      -> RealWorld.universe_ok U__ra
      -> forall a__r U__ra',
          RealWorld.step_universe U__ra (Action a__r) U__ra'
          -> exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__r a__i
            /\ R (strip_adversary U__ra' b) U__i''
            (* /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__ra.(RealWorld.users)) a__r *)
            /\ RealWorld.universe_ok U__ra'.
  Proof.
    intros.

    assert (RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users (strip_adversary U__ra b))) a__r)
      as ADV_SAFE
        by eauto using findUserKeys_same_stripped_univ.
    rewrite <- findUserKeys_same_stripped_univ in ADV_SAFE.

    assert (RealWorld.universe_ok (strip_adversary U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (RealWorld.step_universe (strip_adversary U__ra b) (Action a__r) (strip_adversary U__ra' b))
      as UNIV_STEP.
    eapply labeled_honest_step_advuniv_implies_stripped_univ_step; eauto.

    specialize (H _ _ H1 STRIP_UNIV_OK _ _ UNIV_STEP).
    repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 3 eexists; intuition idtac; eauto.

    eapply honest_labeled_step_advuniv_implies_univ_ok; eauto.
  Qed.

  Lemma simulates_start_ok_adding_adversary :
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) b advcode,
        RealWorld.is_powerless U__r.(RealWorld.adversary) b (RealWorld.findUserKeys U__r.(RealWorld.users))
      -> U__ra = add_adversary U__r advcode
      -> R U__r U__i
      -> RealWorld.universe_ok U__r
      -> R (strip_adversary U__ra b) U__i
      /\ RealWorld.universe_ok U__ra.
  Proof.
    intros.
    unfold RealWorld.universe_ok, RealWorld.is_powerless in *; split_ands; subst; simpl in *.
    destruct U__r; destruct adversary; simpl in *.
    intuition idtac.
    unfold strip_adversary; simpl.
    erewrite real_univ_eq_fields_eq; eauto using clean_ciphers_idempotent, clean_users_idempotent.
    admit.
    (* Stripping doesn't set keys to zero *)
    admit.
    admit.
  Admitted.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) b,
      U__r <| U__i
      -> RealWorld.is_powerless U__r.(RealWorld.adversary) b (RealWorld.findUserKeys U__r.(RealWorld.users))
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

    split.
    admit.

    split; intros.
    eapply simulates_with_adversary_labeled; eauto.

    split. admit.

    eapply simulates_start_ok_adding_adversary; intuition eauto.

  Admitted.

End SingleAdversarySimulates.
