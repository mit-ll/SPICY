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
            /\ RealWorld.action_adversary_safe U__r.(RealWorld.all_keys) (RealWorld.findUserKeys U__r.(RealWorld.users)) a1 = true
            /\ RealWorld.universe_ok U__r'
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

    Fixpoint msg_filter (cs : ciphers) (sigM : { t & message t } ) : bool :=
      match sigM with
      | existT _ _ msg => msg_honestly_signed global_keys honestk cs msg
      end.

    Definition clean_messages (cs : ciphers) (msgs : queued_messages) :=
      List.filter (msg_filter cs) msgs.

    Definition clean_users {A} (cs : ciphers) (usrs : honest_users A) :=
      (* usrs. *)
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages cs u_d.(msg_heap) |}) usrs.

    Definition honest_cipher_filter_fn (c_id : cipher_id) (c : cipher) :=
      cipher_honestly_signed global_keys honestk c.

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
      unfold transpose_neqkey, Equal, honest_cipher_filter_fn; intros.
      cases e; cases e'; simpl.

      cases (honest_signing_key global_keys honestk k_id); cases (honest_signing_key global_keys honestk k_id0); eauto.
        cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; try contradiction; eauto.
      cases (honest_signing_key global_keys honestk k_id); cases (honest_signing_key global_keys honestk k__sign); eauto.
        cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; try contradiction; eauto.
      cases (honest_signing_key global_keys honestk k_id); cases (honest_signing_key global_keys honestk k__sign); eauto.
        cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; try contradiction; eauto.
      cases (honest_signing_key global_keys honestk k__sign); cases (honest_signing_key global_keys honestk k__sign0); eauto.
        cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; try contradiction; eauto.
    Qed.

    Definition clean_ciphers (cs : ciphers) :=
      filter honest_cipher_filter_fn cs.

  End AdversaryHelpers.

  Section RealWorldLemmas.
    Import RealWorld.

    Definition strip_adversary {A B} (U__r : universe A B) (b : B) : universe A B :=
      let honestk := findUserKeys U__r.(users)
      in {| users       := clean_users U__r.(all_keys) (findUserKeys U__r.(users)) U__r.(all_ciphers) U__r.(users)
          ; adversary   := {| key_heap := $0
                            ; msg_heap := []
                            ; protocol := Return b |}
          ; all_ciphers := clean_ciphers U__r.(all_keys) honestk U__r.(all_ciphers)
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

    Lemma clean_ciphers_mapsto_iff : forall allks honestk cs c_id c,
        MapsTo c_id c (clean_ciphers allks honestk cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn allks honestk c_id c = true.
    Proof.
      intros.
      apply filter_iff; eauto.
    Qed.
    
    Lemma clean_ciphers_keeps_honest_cipher :
      forall c_id c allks honestk cs,
        cs $? c_id = Some c
        -> honest_cipher_filter_fn allks honestk c_id c = true
        -> clean_ciphers allks honestk cs $? c_id = Some c.
    Proof.
      intros.
      rewrite <- find_mapsto_iff.
      rewrite <- find_mapsto_iff in H.
      apply clean_ciphers_mapsto_iff; intuition idtac.
    Qed.

    Lemma clean_ciphers_accepts :
      forall {t} allks honestk cs p (m : message t),
          msg_accepted_by_pattern (clean_ciphers allks honestk cs) p m
        -> msg_accepted_by_pattern cs p m.
    Proof.
      induction 1; intros; subst; eauto.
      - econstructor; auto.
      - eapply BothPairsAccepted; eauto.
      - eapply ProperlySigned; eauto.
        rewrite <- find_mapsto_iff in H1; rewrite clean_ciphers_mapsto_iff in H1.
        apply find_mapsto_iff; intuition.
      - eapply ProperlyEncrypted; eauto.
        rewrite <- find_mapsto_iff in H1; rewrite clean_ciphers_mapsto_iff in H1.
        apply find_mapsto_iff; intuition eassumption.
    Qed.

    Lemma honest_signing_key_not_cleaned :
      forall cs c_id c allks honestk k,
        cs $? c_id = Some c
        -> honest_signing_key allks honestk k = true
        -> k = cipher_signing_key c
        -> clean_ciphers allks honestk cs $? c_id = Some c.
    Proof.
      intros.
      eapply clean_ciphers_keeps_honest_cipher; auto.
      unfold honest_cipher_filter_fn.
      unfold cipher_signing_key in *.
      cases c; subst; eauto.
    Qed.

    Lemma clean_ciphers_accepts_non_spoofable :
      forall {t} allks honestk cs p (m : message t),
        msg_accepted_by_pattern cs p m
        -> forall p',
          p' = p
        -> msg_pattern_spoofable allks honestk p' = false
        -> msg_accepted_by_pattern (clean_ciphers allks honestk cs) p' m.
    Proof.
      induction 1; intros; subst; eauto.
      - econstructor; auto.
      - invert H4; apply orb_false_elim in H0; invert H0.
        eapply BothPairsAccepted; eauto.
      - eapply ProperlySigned; eauto.
        invert H3. rewrite negb_false_iff in H0.
        eapply honest_signing_key_not_cleaned; eauto.
      - eapply ProperlyEncrypted; eauto.
        invert H3. rewrite negb_false_iff in H0.
        eapply honest_signing_key_not_cleaned; eauto.
    Qed.

    Hint Constructors msg_accepted_by_pattern.

    Lemma clean_ciphers_doesn't_make_unaccepted_msg_accepted :
      forall {t} cs pat allks honestk (msg : message t),
          ~ msg_accepted_by_pattern cs pat msg
        -> ~ msg_accepted_by_pattern (clean_ciphers allks honestk cs) pat msg.
    Proof.
      unfold "~"; induction 2; subst;
        eauto;
        repeat match goal with
               | [ H : clean_ciphers _ _ _ $? _ = Some _ |- _] => rewrite <- find_mapsto_iff in H; rewrite clean_ciphers_mapsto_iff in H
               | [ H : _ /\ _ |- _ ] => invert H
               | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
               end; eauto.
    Qed.

    Hint Resolve clean_ciphers_doesn't_make_unaccepted_msg_accepted.
    Hint Extern 1 (_ $+ (?k, _) $? ?k = Some _) => rewrite add_eq_o.
    Hint Extern 1 (_ $+ (?k, _) $? ?v = _) => rewrite add_neq_o.

    Lemma clean_ciphers_eliminates_dishonest_cipher :
      forall c_id c allks honestk cs k,
        cs $? c_id = Some c
        -> honest_signing_key allks honestk k = false
        -> k = cipher_signing_key c
        -> clean_ciphers allks honestk cs $? c_id = None.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; eauto.
      cases (honest_cipher_filter_fn allks honestk k0 e); eauto.
      cases (c_id ==n k0); subst; eauto.
      exfalso.
      rewrite find_mapsto_iff in H2; rewrite H2 in H; invert H.
      unfold honest_cipher_filter_fn, cipher_honestly_signed, cipher_signing_key in *.
      cases c;
        rewrite Heq in H0; invert H0.
    Qed.

    Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher.

    Lemma clean_ciphers_reduces_or_keeps_same_ciphers :
      forall c_id c allks honestk cs,
        cs $? c_id = Some c
        -> ( clean_ciphers allks honestk  cs $? c_id = Some c
          /\ honest_signing_key allks honestk (cipher_signing_key c) = true)
        \/ ( clean_ciphers allks honestk cs $? c_id = None
          /\ honest_signing_key allks honestk (cipher_signing_key c) = false).
    Proof.
      intros.
      case_eq (honest_signing_key allks honestk (cipher_signing_key c)); intros; eauto.
      left; intuition idtac.
      eapply clean_ciphers_keeps_honest_cipher; eauto.
      unfold honest_cipher_filter_fn, cipher_signing_key in *.
      cases c; eauto.
    Qed.

    Lemma clean_ciphers_no_new_ciphers :
      forall c_id cs allks honestk,
        cs $? c_id = None
        -> clean_ciphers allks honestk cs $? c_id = None.
    Proof.
      intros.
      unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; eauto.
      cases (honest_cipher_filter_fn allks honestk k e); eauto.
      - case (c_id ==n k); intro; subst; unfold honest_cipher_filter_fn.
        + rewrite find_mapsto_iff in H0; rewrite H0 in H; invert H.
        + rewrite add_neq_o; eauto.
    Qed.

    Hint Resolve clean_ciphers_no_new_ciphers.

    Lemma clean_ciphers_eliminates_added_dishonest_cipher :
      forall c_id c allks honestk cs k,
        cs $? c_id = None
        -> honest_signing_key allks honestk k = false
        -> k = cipher_signing_key c
        -> clean_ciphers allks honestk cs = clean_ciphers allks honestk (cs $+ (c_id,c)).
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
      forall c_id cs allks honestk,
          ~ In c_id cs
        -> ~ In c_id (clean_ciphers allks honestk cs).
    Proof.
      intros.
      rewrite not_find_in_iff in H.
      apply not_find_in_iff; eauto.
    Qed.

    Hint Resolve not_in_ciphers_not_in_cleaned_ciphers.

    (* Ltac contra_map_lookup := *)
    (*   repeat *)
    (*     match goal with *)
    (*     | [ H1 : ?ks1 $? ?k = _, H2 : ?ks2 $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2 *)
    (*     | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction *)
    (*     end; try discriminate. *)

    Lemma enc_message_has_honest_signing_key :
      forall {t} k__signid kp__sign k__encid kp__enc allks honestk advk c_id (msg : message t) cipherMsg,
          encryptMessage allks (k__signid,kp__sign) (k__encid,kp__enc) msg c_id = Some cipherMsg
        -> honestk $? k__signid = Some kp__sign
        -> has_private_key allks (k__signid,kp__sign) = true
        -> adv_no_honest_keys allks honestk advk
        -> honest_signing_key allks honestk k__signid = true
        /\ cipherMsg = SigEncCipher c_id k__signid k__encid msg.
        (* /\ (k__sign.(keyType) = SymKey \/ k__sign.(keyType) = AsymKey true). *)
    Proof.
      intros.
      unfold encryptMessage in *.
      unfold honest_signing_key.
      simpl in *.
      cases (allks $? k__signid); try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      cases (allks $? k__encid); try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      unfold sign_if_ok in *.
      cases keyType; subst; try discriminate.
      - clean_map_lookups; intuition eauto.
        unfold honest_key. context_map_rewrites; auto.

      - cases kp__sign; try discriminate; clean_map_lookups; intuition idtac.
        unfold honest_key; context_map_rewrites; auto.
    Qed.

    Lemma sign_message_has_honest_signing_key :
      forall {t} k_id kp allks honestk advk c_id (msg : message t) cipherMsg,
          signMessage allks (k_id,kp) msg c_id = Some cipherMsg
        -> honestk $? k_id = Some kp
        -> has_private_key allks (k_id,kp) = true
        -> adv_no_honest_keys allks honestk advk
        -> honest_signing_key allks honestk k_id = true
        /\ cipherMsg = SigCipher c_id k_id msg.

    Proof.
      intros.
      unfold signMessage in *; simpl in *.
      unfold honest_signing_key.
      cases (allks $? k_id); subst; try discriminate.
      destruct k; simpl in *.
      cases keyUsage; subst; try discriminate.
      unfold sign_if_ok in *.
      cases keyType; subst; clean_map_lookups; unfold honest_key; context_map_rewrites; auto.
      cases kp; clean_map_lookups; auto.
    Qed.

    Lemma dishonest_cipher_cleaned :
      forall cs allks honestk c_id cipherMsg,
          honest_signing_key allks honestk (cipher_signing_key cipherMsg) = false
        -> ~ In c_id cs
        -> clean_ciphers allks honestk cs = clean_ciphers allks honestk (cs $+ (c_id, cipherMsg)).
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
      forall allks honestk cs c_id c k,
          honest_signing_key allks honestk k = true
        -> k = cipher_signing_key c
        -> clean_ciphers allks honestk (cs $+ (c_id,c)) = clean_ciphers allks honestk cs $+ (c_id,c).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      (* unfold honest_signing_key,honest_key in H. *)

      case (y ==n c_id); intros; subst; clean_map_lookups.
      - erewrite clean_ciphers_keeps_honest_cipher; auto.
      - case_eq (clean_ciphers allks honestk cs $? y); intros; subst.
        + case_eq (cs $? c_id); intros; subst; auto.
          * case_eq (cs $? y); intros; subst; auto.
            ** assert (cs $? y = Some c2) as HH by assumption;
                 eapply clean_ciphers_reduces_or_keeps_same_ciphers in HH; invert HH;
                   split_ands; subst; contra_map_lookup.

               apply clean_ciphers_keeps_honest_cipher; auto.

            ** exfalso. eapply clean_ciphers_no_new_ciphers in H2; contra_map_lookup.

          * unfold clean_ciphers, filter.
            rewrite fold_add; auto.
            unfold honest_cipher_filter_fn.
            cases c; simpl in *; rewrite H; auto.
        + case_eq (cs $? y); intros; subst; eauto.
          eapply clean_ciphers_eliminates_dishonest_cipher; eauto.
          case_eq (honest_signing_key allks honestk (cipher_signing_key c0)); intros; subst; auto.
          exfalso; eapply clean_ciphers_keeps_honest_cipher in H1; contra_map_lookup; auto.
    Qed.

    Lemma clean_ciphers_idempotent :
      forall gks uks cs,
        ciphers_honestly_signed gks uks cs = true
      -> clean_ciphers gks uks cs = cs.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; Equal_eq; subst; eauto.
      unfold honest_cipher_filter_fn, ciphers_honestly_signed in *.
      rewrite for_all_iff in H; auto.
      assert (cipher_honestly_signed gks uks e = true) by eauto.
      rewrite H2; trivial.
    Qed.

    Lemma clean_users_idempotent_msg_queue_filter :
      forall msg_heap ks honestk cs,
        message_queue_safe ks honestk cs msg_heap = true
        -> clean_messages ks honestk cs msg_heap = msg_heap.
    Proof.
      induction msg_heap; auto; intros.
      destruct a.

      assert ( message_queue_safe ks honestk cs (existT message x m :: msg_heap) = true ) as IND by assumption.
      assert ( existT message x m :: msg_heap = [existT message x m] ++ msg_heap ) as RW by auto.
      unfold message_queue_safe in IND; rewrite RW, forallb_app in IND.
      apply andb_prop in IND; split_ands.
      simpl in *.
      apply andb_prop in H; split_ands.
      apply andb_prop in H; split_ands.
      rewrite H3; auto.
      f_equal; auto.
    Qed.

    Lemma clean_users_idempotent :
      forall {A} (usrs : honest_users A) ks honestk cs,
          (forall u_id u_d msgs,
              usrs $? u_id = Some u_d
              -> msgs = msg_heap u_d
              -> message_queue_safe ks honestk cs msgs = true)
        -> clean_users ks honestk cs usrs = usrs.
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

  (*     Lemma findUserKeys_readd_user_same_keys_idempotent : *)
  (*   forall {A} (usrs : honest_users A) u_id u_d proto msgs, *)
  (*     usrs $? u_id = Some u_d *)
  (*     -> findUserKeys usrs = findUserKeys (usrs $+ (u_id, {| key_heap := key_heap u_d; protocol := proto; msg_heap := msgs |})). *)
  (* Proof. *)
  (*   intros. *)
  (*   induction usrs using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; auto. *)

  (*   cases (x ==n u_id); subst; clean_map_lookups. *)
  (*   - rewrite map_add_eq. *)
  (*     unfold findUserKeys. *)
  (*     rewrite !fold_add; auto. *)
  (*   - rewrite map_ne_swap; auto. *)
  (*     unfold findUserKeys. *)
  (*     rewrite fold_add; auto. *)
  (*     rewrite fold_add; auto; clean_map_lookups. *)
  (*     rewrite !findUserKeys_notation. *)
  (*     rewrite IHusrs at 1; auto. *)
  (*     rewrite not_find_in_iff; clean_map_lookups; trivial. *)
  (* Qed. *)

    Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
         findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

    Lemma clean_users_add_pull :
      forall {A} (usrs : honest_users A) aks honestk cs u_id u,
        ~ In u_id usrs
        -> clean_users aks honestk cs (usrs $+ (u_id,u))
          = clean_users aks honestk cs usrs $+ (u_id, {| key_heap := u.(key_heap)
                                                       ; protocol := u.(protocol)
                                                       ; msg_heap :=  clean_messages aks honestk cs u.(msg_heap) |}).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n u_id); subst; clean_map_lookups; eauto;
        unfold clean_users; rewrite !map_o; unfold option_map; clean_map_lookups; auto.
    Qed.

    Lemma clean_users_no_change_findUserKeys :
      forall {A} (usrs : honest_users A) aks honestk cs,
        findUserKeys (clean_users aks honestk cs usrs) = findUserKeys usrs.
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

    Lemma ok_universe_strip_adversary_ignores_users :
      forall {A B} (U__ra U__r: universe A B) (b : B) u_id u_d,
        U__ra.(users) $? u_id = Some u_d
        -> U__r = strip_adversary U__ra b
        -> universe_ok U__ra
        -> U__r.(users) $? u_id = Some u_d.
    Proof.
      unfold strip_adversary; intros; subst; simpl.
      unfold universe_ok in *; split_ands.
      rewrite clean_users_idempotent; auto.
    Qed.

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *.
      split_ands;
        try rewrite clean_users_idempotent, clean_ciphers_idempotent; eauto.
      intuition idtac.
      apply adv_no_honest_keys_empty.
    Qed.

    Lemma honest_enc_cipher_not_cleaned :
      forall {t} cs k__signid kp__sign k__encid kp__enc allks honestk advk c_id (msg : message t) cipherMsg,
          encryptMessage allks (k__signid, kp__sign) (k__encid,kp__enc) msg c_id = Some cipherMsg
        -> honestk $? k__signid = Some kp__sign
        -> has_private_key allks (k__signid, kp__sign) = true
        -> adv_no_honest_keys allks honestk advk
        -> clean_ciphers allks honestk (cs $+ (c_id, cipherMsg)) = clean_ciphers allks honestk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (enc_message_has_honest_signing_key _ _ _ _ _ H H0 H1 H2) as HONEST; split_ands.
      eapply clean_ciphers_added_honest_cipher_not_cleaned; subst; eauto.
    Qed.

    Lemma honest_sign_cipher_not_cleaned :
      forall {t} cs k_id kp allks honestk advk c_id (msg : message t) cipherMsg,
          signMessage allks (k_id,kp) msg c_id = Some cipherMsg
        -> honestk $? k_id = Some kp
        -> has_private_key allks (k_id,kp) = true
        -> adv_no_honest_keys allks honestk advk
        -> clean_ciphers allks honestk (cs $+ (c_id, cipherMsg)) = clean_ciphers allks honestk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (sign_message_has_honest_signing_key _ _ _ H H0 H1 H2) as HONEST; split_ands.
      eapply clean_ciphers_added_honest_cipher_not_cleaned; subst; eauto.
    Qed.

    Hint Resolve honest_enc_cipher_not_cleaned honest_sign_cipher_not_cleaned.

    Lemma honest_silent_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' b,
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s honestk,
          honestk = findUserKeys usrs
          -> adv_no_honest_keys gks honestk adv.(key_heap)
          -> ciphers_honestly_signed gks honestk cs = true
          (* -> key_heaps_compatible honestk adv.(key_heap) *)
          -> cs__s = clean_ciphers gks honestk cs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers gks' honestk cs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Silent
              -> step_user (B:=B) lbl (usrs, powerless_adv b, cs__s, gks, ks, qmsgs, cmd) (usrs', powerless_adv b, cs__s', gks', ks', qmsgs', cmd').
    Proof.

      Ltac foo1 :=
        match goal with
        |  [ H : ?x = ?x |- _ ] => clear H
        | [ |- clean_ciphers _ _ _ $? _ = Some _ ] => eapply clean_ciphers_keeps_honest_cipher
        | [ |- honest_cipher_filter_fn _ _ _ _ = _ ] => unfold honest_cipher_filter_fn, cipher_honestly_signed, honest_signing_key, honest_key
        | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H 
        | [ |- context [match ?matchee with _ => _ end] ] => cases matchee; subst
        | [ |- ?hasp && _ = _ ] => cases hasp; simpl
        | [ |- false = true ] => exfalso; simpl in *
        | [ H : _ && _ = true |- _ ] => apply andb_prop in H; split_ands
        | [ H : match ?matchee with _ => _ end = _
         ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
        | [ H  : ciphers_honestly_signed ?gks ?ks ?cs = true
          , H1 : ?cs $? _ = Some ?c
            |- cipher_honestly_signed ?gks ?ks ?c = true] =>
              unfold ciphers_honestly_signed in H; rewrite for_all_iff in H by auto; eapply H
        | [ |- MapsTo _ _ _ ] => apply find_mapsto_iff
        | [ H : cipher_honestly_signed _ _ _ = true |- _ ] => unfold cipher_honestly_signed,honest_signing_key, honest_key in H
        end.

      Ltac doit :=
        repeat foo1; auto;
        match goal with
        | [ H  : ciphers_honestly_signed ?gks ?ks ?cs = true
          , H1 : ?cs $? _ = Some ?c
               |- False ] => assert (cipher_honestly_signed gks ks c = true)
        end; repeat foo1; eauto.

      induction 1; inversion 5; inversion 2; intros; subst;
        repeat match goal with
               | [ H : Action _ = Silent |- _ ] => invert H
               end;
        econstructor;
        eauto using honest_enc_cipher_not_cleaned, honest_sign_cipher_not_cleaned;
        try solve [doit; discriminate].

      - eapply honest_enc_cipher_not_cleaned; eauto.
        admit. (* need link that the ks is in findUserKeys usrs *)

      - eapply honest_sign_cipher_not_cleaned; eauto.
        admit.

    Admitted.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a b,
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s honestk,
          honestk = findUserKeys usrs
          -> adv_no_honest_keys gks honestk adv.(key_heap)
          -> cs__s = clean_ciphers gks honestk cs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers gks honestk cs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Action a
              -> action_adversary_safe gks honestk a = true
              -> step_user (B:=B) lbl (usrs, powerless_adv b, cs__s, gks, ks, qmsgs, cmd) (usrs', powerless_adv b, cs__s', gks', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 4; inversion 2; intro; subst; econstructor; eauto; try discriminate.

      - invert H17. unfold action_adversary_safe in H.
        eapply clean_ciphers_accepts_non_spoofable; eauto.
        rewrite <- negb_true_iff; assumption.

      - unfold addUserKeys, powerless_adv; f_equal; simpl. admit. (* add constraint to operational semantics *)

    Admitted.


    Lemma honest_labeled_step_advuniv_implies_simulation :
      forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a b,
        step_user lbl bd bd'
        -> universe_ok
              {| users := usrs
               ; adversary := adv
               ; all_ciphers := cs
               ; all_keys := gks |}
        -> forall (cmd : user_cmd C) cs__s honestk,
            honestk = findUserKeys usrs
          -> (exists cmdc, usrs $? u_id = Some {| key_heap := ks; protocol := cmdc; msg_heap := qmsgs |})
          -> cs__s = clean_ciphers gks honestk cs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers gks honestk cs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> lbl = Action a
              -> step_user (B:=B) lbl (usrs, powerless_adv b, cs__s, gks, ks, qmsgs, cmd)
                          (usrs', powerless_adv b, cs__s', gks', ks', qmsgs', cmd')
              /\ exists cmdc', universe_ok
                  {| users := usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |})
                   ; adversary := adv'
                   ; all_ciphers := cs'
                   ; all_keys := gks' |}.
    Proof.
      induction 1; inversion 5; inversion 2; intro; subst; eauto; try discriminate.



    Admitted.

    Lemma no_honest_keys_in_msg_if_not_need_encryption :
      forall {t} (msg : message t) gks msgks honestk,
        msg_needs_encryption gks honestk msg = false
        -> msgks = findKeys gks msg
        -> forall k_id kp kp',
              msgks $? k_id = Some kp
            -> honestk $? k_id = Some kp'
            -> has_private_key gks (k_id,kp') = false.
    Proof.
      induction msg; intros; subst; simpl in *; clean_map_lookups; eauto.
      - destruct k; unfold has_private_key; simpl in *.
        cases (k ==n k_id); subst; eauto.
        + unfold honest_key in *;
            cases (gks $? k_id); subst; clean_map_lookups; auto.
          destruct k; simpl in *.
          cases keyType; clean_map_lookups; context_map_rewrites; try discriminate; auto.
        + unfold honest_key in *;
            cases (gks $? k_id); cases (gks $? k); subst; clean_map_lookups; auto.
      - apply orb_false_elim in H; split_ands; eauto.
        apply merge_perms_split in H1; split_ors; eauto.
    Qed.

    (* Lemma message_good : *)
    (*   forall {t} (msg : message t) gks honestk msgk, *)
    (*       msg_needs_encryption gks honestk msg = false *)
    (*     -> (forall k_id kp kp', *)
    (*           msgk $? k_id = Some kp -> honestk $? k_id = Some kp' -> has_private_key gks (k_id, kp') = false) *)
    (*     -> msg_needs_encryption gks (honestk $k++ msgk) msg = false. *)
    (* Proof. *)
    (*   induction msg; subst; simpl; intros; eauto. *)

    (*   - destruct k; simpl in *. *)
    (*     cases (gks $? k); auto. *)
    (*     unfold honest_key in *; rewrite Heq in *. *)
    (*     cases k0; eauto. *)
    (*     cases keyType; cases (honestk $? k); try discriminate; auto. *)
    (*     + cases (msgk $? k); [| assert (honestk $k++ msgk $? k = None) as N by auto using merge_perms_adds_no_new_perms; rewrite N]; auto. *)
    (*       admit. *)
    (*     + cases (msgk $? k). *)
    (*       assert (honestk $k++ msgk $? k = Some (greatest_permission b0 b1)) *)
    (*         as N by eauto using merge_perms_chooses_greatest; rewrite N; subst. *)
    (*       specialize (H0 _ _ _ Heq1 Heq0). *)
    (*       unfold has_private_key in H0; simpl in *. *)

    (*     + cases (msgk $? k); eauto. *)


    (*   - apply orb_false_intro. *)
    (*     specialize (IHmsg1 _ _ _ _ H H0 H1); split_ands; auto. *)
    (*     specialize (IHmsg2 _ _ _ _ H3 H2 H1); split_ands; auto. *)
    (*   - apply andb_true_intro. *)
    (*     specialize (IHmsg1 _ _ _ _ H H0 H1);  *)
    (*       specialize (IHmsg2 _ _ _ _ H3 H2 H1); split_ands; auto. *)
    (*   - cases (cs $? msg_id); auto. admit. *)
    (*   -  *)


    Lemma message_good :
      forall {t} (msg : message t) gks honestk msgk cs,
          msg_needs_encryption gks honestk msg = false
        -> msg_honestly_signed gks honestk cs msg = true
        -> (forall k_id kp kp',
              msgk $? k_id = Some kp -> honestk $? k_id = Some kp' -> has_private_key gks (k_id, kp') = false)
        -> msg_needs_encryption gks (honestk $k++ msgk) msg = false
        /\ msg_honestly_signed gks (honestk $k++ msgk) cs msg = true.
    Proof.
      induction msg; subst; simpl; intros;
        repeat match goal with
               | [ H : _ && _ = true |- _ ] => apply andb_prop in H; split_ands
               | [ H : _ || _ = false |- _ ] => apply orb_false_elim in H; split_ands
               | [ |- _ || _ = false ] => apply orb_false_intro
               end; try discriminate; intuition idtac.

      - apply orb_false_intro.
        specialize (IHmsg1 _ _ _ _ H H0 H1); split_ands; auto.
        specialize (IHmsg2 _ _ _ _ H3 H2 H1); split_ands; auto.
      - apply andb_true_intro.
        specialize (IHmsg1 _ _ _ _ H H0 H1); 
          specialize (IHmsg2 _ _ _ _ H3 H2 H1); split_ands; auto.
      - cases (cs $? msg_id); auto. admit.
      - 

    Admitted.



    Lemma message_queue_safe_after_adding_dishonest_keys :
      forall gks honestk msgk cs msgs,
        message_queue_safe gks honestk cs msgs = true
        -> (forall k_id kp kp', msgk $? k_id = Some kp -> honestk $? k_id = Some kp' -> has_private_key gks (k_id,kp') = false)
        -> message_queue_safe gks (honestk $k++ msgk) cs msgs = true.
    Proof.
      induction msgs; subst; intros; auto.
      unfold message_queue_safe; unfold message_queue_safe in H.
      assert (a :: msgs = [a] ++ msgs) as CONSAPP by auto.
      rewrite CONSAPP in *; clear CONSAPP.
      rewrite forallb_app in *.
      apply andb_prop in H; split_ands.
      apply andb_true_intro; split; auto.
      simpl in *. destruct a.
      clear IHmsgs H1.


    Admitted.




    Lemma honest_labeled_step_advuniv_implies_univ_ok :
      forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd' a,
        step_user lbl bd bd'
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
              -> lbl = Action a
              ->  exists cmdc', universe_ok
                  {| users := usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' |})
                   ; adversary := adv'
                   ; all_ciphers := cs'
                   ; all_keys := gks' |}.
    Proof.
      induction 1; inversion 3; inversion 1; unfold universe_ok in *; simpl in *; intros;
        subst; try discriminate; eauto;
          match goal with
          | [ H : exists _, _ |- _ ] => destruct H
          end; split_ands; eexists; intuition idtac;
            repeat match goal with
                   | [ H : ?x = ?x |- _ ] => clear H
                   end.

      Ltac findUserKeys_rewrites :=
        try rewrite map_add_eq; clean_map_lookups;
        try match goal with
            | [ H : ?m $? ?k2 = Some ?v |- context[ findUserKeys (?m $+ (?k1,?v1) $+ (?k2,?v2))] ] =>
              assert ( m $+ (k1,v1) $? k2 = Some v ) by (clean_map_lookups; auto)
            end; erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto.

      (* Recv *)
      - admit.
      - admit.
      - admit.
      - admit.

      (* Send *)

      - cases (u_id ==n u_id0); cases (u_id ==n rec_u_id); subst; clean_map_lookups; simpl;
          findUserKeys_rewrites.

        destruct u_d; clean_map_lookups; simpl.
        cases (u_id0 ==n rec_u_id); subst; clean_map_lookups; eauto.
        (* do sent messages have keys in them??? *)
        admit.

      - cases (u_id ==n rec_u_id); subst; clean_map_lookups; findUserKeys_rewrites.
      - cases (u_id ==n rec_u_id); subst; clean_map_lookups; findUserKeys_rewrites.
      - cases (u_id ==n rec_u_id); subst; clean_map_lookups; findUserKeys_rewrites.
        (* do sent messages have keys in them??? *)
        admit.

    Admitted.


    Lemma safe_actions_adv_univ_still_safe_strip_adv :
      forall {A B} (U : universe A B) b a__r,
        action_adversary_safe (all_keys (strip_adversary U b)) (findUserKeys (users (strip_adversary U b))) a__r = true
        -> action_adversary_safe (RealWorld.all_keys U) (RealWorld.findUserKeys (RealWorld.users U)) a__r = true.
    Proof.
      destruct U; simpl; intros.
      rewrite clean_users_no_change_findUserKeys in H; auto.
    Qed.

    (* Lemma clean_ciphers_idempotent : *)
    (*   forall gks uks cs, *)
    (*     ciphers_honestly_signed gks uks cs = true *)
    (*   -> clean_ciphers gks uks cs = cs. *)
    (* Proof. *)

    (* Lemma clean_users_no_change_findUserKeys : *)
    (*   forall {A} (usrs : honest_users A) aks honestk cs, *)
    (*     findUserKeys (clean_users aks honestk cs usrs) = findUserKeys usrs. *)
    (* Proof. *)


    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
      invert H4.
    Qed.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks ks' qmsgs qmsgs' bd bd',
        step_user lbl bd bd'
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

    (* Lemma user_step_adds_removes_no_adversaries : *)
    (*   forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks ks' qmsgs qmsgs' bd bd', *)
    (*     step_user lbl bd bd' *)
    (*     -> forall (cmd : user_cmd C), *)
    (*       bd = (usrs, adv, cs, ks, qmsgs, cmd) *)
    (*       -> forall cmd', *)
    (*         bd' = (usrs', adv', cs', ks', qmsgs', cmd') *)
    (*         -> (forall u_id', *)
    (*               adv' $? u_id' <> None *)
    (*               <-> adv $? u_id' <> None). *)
    (* Proof. *)
    (*   induction 1; inversion 1; inversion 1; intros; subst; eauto; *)
    (*     unfold iff; constructor; intro; eauto. *)

    (*   - unfold addUserKeys in H. rewrite <- in_find_iff in H. *)
    (*     rewrite map_in_iff in H. apply in_find_iff; eauto. *)

    (*   - unfold addUserKeys; apply in_find_iff. *)
    (*     rewrite <- in_find_iff in H. *)
    (*     rewrite map_in_iff; eauto. *)
    (* Qed. *)

    Ltac map_equal :=
      repeat match goal with
             | [ |- context[find ?k (add ?k _ _) ] ] => rewrite add_eq_o by (simple apply @eq_refl)
             | [ |- context[find ?k (add ?k' _ _) ] ] => rewrite add_neq_o by intuition
             | [ |- context[find ?k (empty _) ] ] => rewrite empty_o; trivial
             | [ |- context[$0 $++ _ ] ] => rewrite empty_add_idempotent
             | [ |- context[_ $++ $0 ] ] => rewrite add_empty_idempotent
             | [ |- (add ?k _ _) = _ ] => apply map_eq_Equal; unfold Equal; intros ?KEY; case (KEY ==n k); intro; subst
             | [ |- _ = (add ?k _ _) ] => apply map_eq_Equal; unfold Equal; intros ?KEY; case (KEY ==n k); intro; subst
             (* | [ |- (add _ _ _) = _ ] => normalize_set *)
             (* | [ |- (add _ _ _) = _ ] => unfold add, Raw.add; simpl *)
             | [ |- {| this := _ ; sorted := _ |} = _ ] => eapply map_eq_fields_eq
             | [ H : Empty ?m |- $0 = ?m ] => eapply Empty_eq_empty; exact H
             | [ H : Empty ?m |- ?m = $0 ] => symmetry
             | [ |- empty _ = _ ] => unfold empty, Raw.empty, remove, Raw.remove; simpl
             end.

    (* TODO tbraje: This statement really needs to be re-stated, if needed  *)
    (* Lemma adv_step_stays_in_R : *)
    (*   forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) *)
    (*           (cmd : user_cmd B) lbl u_id userData (usrs : honest_users A) (adv : user_data B) cs ks qmsgs, *)
    (*     U__r.(adversary) $? u_id = Some userData *)
    (*     -> (forall u_id', u_id' <> u_id -> U__r.(adversary) $? u_id' = None) (* single adversary *) *)
    (*     -> step_user lbl *)
    (*                 (build_data_step U__r userData) *)
    (*                 (usrs, adv, cs, ks, qmsgs, cmd) *)
    (*     -> R (strip_adversary U__r) U__i *)
    (*     -> R (strip_adversary (buildUniverseAdv usrs adv cs {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) U__i. *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold buildUniverseAdv, strip_adversary in *; simpl in *. *)

    (*   assert (U__r.(adversary) = $0 $+ (u_id,userData)) by (map_equal; eauto). *)

    (*   assert (findUserKeys U__r.(adversary) = userData.(key_heap)) as ADV_KEYS *)
    (*     by (rewrite H3; unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial). *)
    (*   rewrite ADV_KEYS in H2; clear ADV_KEYS. *)

    (*   assert (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |}) *)
    (*           = $0 $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) as ADV_RED; *)
    (*     map_equal; trivial. *)
    (*   pose proof H1 as NOADD; unfold build_data_step in NOADD; *)
    (*     eapply user_step_adds_removes_no_adversaries with (u_id' := KEY) in NOADD; eauto; *)
    (*       unfold iff in NOADD; invert NOADD. *)
    (*   case_eq (adv $? KEY); intros; eauto. exfalso. *)

    (*   assert (adv $? KEY <> None) as LK_KEY_NOT_NONE *)
    (*     by (unfold not; intros; *)
    (*         match goal with [ H1 : ?m $? ?k = Some _, H2 : ?m $? ?k = None |- _ ] => rewrite H1 in H2; invert H2 end). *)
    (*   specialize (H0 _ n); specialize (H4 LK_KEY_NOT_NONE); contradiction. *)

    (*   assert (findUserKeys (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) = ks); *)
    (*     rewrite ADV_RED; clear ADV_RED; *)
    (*     unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial. *)

    (*   match goal with *)
    (*   | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] => *)
    (*     assert ( cs = cs' ) as CS by (unfold build_data_step in *; eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto); *)
    (*       assert ( us = us' ) as US by (unfold build_data_step in *; eapply adv_step_implies_no_user_impact_after_cleaning; eauto) *)
    (*   end; rewrite <- CS; rewrite <- US; clear US CS; *)
    (*     assumption. *)

    (* Qed. *)


    Lemma adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks' qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> adv_no_honest_keys gks (findUserKeys usrs) adv.(key_heap)
          -> message_queue_safe gks honestk cs adv.(msg_heap) = true
          -> cs__s = clean_ciphers gks honestk cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers gks' honestk' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 6; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Send *)
      - erewrite findUserKeys_readd_user_same_keys_idempotent; eauto.

      (* Encrypt *)
      - assert (honest_signing_key gks' (findUserKeys usrs') (cipher_signing_key cipherMsg) = false).
        unfold encryptMessage, adv_no_honest_keys in *.
        unfold honest_signing_key. simpl in *.
        specialize (H17 k__signid).
        cases (gks' $? k__signid); try discriminate.
        destruct k; simpl in *. cases keyType; rewrite H1 in *; try contradiction.
          cases keyUsage; try discriminate.
          cases (gks' $? k__encid); try discriminate. destruct k; simpl in *. cases keyUsage; try discriminate.
          unfold sign_if_ok in *; cases kp__sign; clean_map_lookups; simpl. rewrite Heq, H17; auto.

        eapply clean_ciphers_eliminates_added_dishonest_cipher; clean_map_lookups; eauto.

      - assert (honest_signing_key gks' (findUserKeys usrs') (cipher_signing_key cipherMsg) = false).
        unfold signMessage, adv_no_honest_keys in *.
        unfold honest_signing_key.
        specialize (H14 k_id).
        cases (gks' $? k_id); try discriminate.
        destruct k; simpl in *. cases keyType; rewrite H in *; try contradiction.
          rewrite Heq in *; cases keyUsage; try discriminate.
          unfold sign_if_ok in *; cases kp; clean_map_lookups; simpl. rewrite Heq, H14; auto.
          simpl in *; rewrite Heq in *; discriminate.
        eapply clean_ciphers_eliminates_added_dishonest_cipher; clean_map_lookups; eauto.
    Qed.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) gks gks' ks' qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
            bd = (usrs, adv, cs, gks, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          -> usrs__s = clean_users gks honestk cs usrs
          -> forall cmd' honestk' usrs__s',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users gks' honestk' cs' usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Send *)
      - erewrite <- findUserKeys_readd_user_same_keys_idempotent; eauto.
        admit.

      (* Encrypt *)
      - (* using orig ciphers to clean would fix this ... *)
        admit.

      (* Sign *)
      - (* using orig ciphers to clean would fix this ... *)
        admit.

    Admitted.


    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) (b : B)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs,
        step_user lbl
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
      match goal with
      | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] =>
        assert ( cs = cs' ) as CS by (eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto);
          assert ( us = us' ) as US by (eapply adv_step_implies_no_user_impact_after_cleaning; eauto)
      end; rewrite <- CS, <- US; clear CS US.

      (* Remaining goal is to clean the keys *)
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

      (*   R U__r U__i *)
      (* -> RealWorld.keys_good U__r.(RealWorld.all_keys) *)
      (* -> RealWorld.adv_no_honest_keys U__r.(RealWorld.all_keys) U__r.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__r.(RealWorld.users)) *)
      (* -> forall U__r', *)
      (*     rstepSilent U__r U__r' *)
      (*     -> exists U__i', *)
      (*       istepSilent ^* U__i U__i' *)
      (*       /\ R U__r' U__i') *)


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

    match goal with
    | [ H : rstepSilent _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - simpl.
      (* assert (UNIV_STEP : *)
      (*           rstepSilent *)
      (*             (strip_adversary U__ra b) *)
      (*             (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id *)
      (*                                                       {| RealWorld.key_heap := ks *)
      (*                                                        ; RealWorld.protocol := cmd *)
      (*                                                        ; RealWorld.msg_heap := qmsgs |}) b) ). *)

      (* eapply RealWorld.StepUser; eauto. *)
      (* eapply honest_silent_step_advuniv_implies_honest_step_origuniv; intros; eauto. *)
      (* eapply RealWorld.find_user_keys_universe_user; eauto. admit. *)
      (* eauto. *)
      (* unfold strip_adversary; simpl; smash_universe. *)

      (* unfold RealWorld.build_data_step in H5. *)
      (* eapply honest_silent_step_nochange_adversaries in H5; [| reflexivity..]; rewrite H5; trivial. *)

    (* eapply H; eauto. *)
      admit.

    - exists U__i.
      split; [|split].
      + eapply TrcRefl.
      + admit. (* universe still ok *)
      + eapply adv_step_stays_in_R; eauto.

  Admitted.


  (* Lemma msg_pattern_spoofable_strengthen : *)
  (*   forall pat adv_keys honest_keys, *)
  (*     RealWorld.adv_no_honest_keys adv_keys honest_keys *)
  (*     -> negb (RealWorld.msg_pattern_spoofable $0 pat) = true *)
  (*     -> RealWorld.msg_pattern_spoofable adv_keys pat = RealWorld.msg_pattern_spoofable $0 pat. *)
  (* Proof. *)
  (*   induction pat; intros; auto. *)
  (*   - unfold RealWorld.msg_pattern_spoofable in *; simpl; fold RealWorld.msg_pattern_spoofable in *. *)
  (*     rewrite negb_orb in H0; invert H0. *)
  (*     rewrite andb_true_iff in H2; invert H2. *)
  (*     specialize (IHpat1 _ _ H H0). *)
  (*     specialize (IHpat2 _ _ H H1). *)
  (*     rewrite IHpat1. *)
  (*     rewrite IHpat2. *)
  (*     trivial. *)

  (*   - unfold RealWorld.msg_pattern_spoofable. simpl. *)
  (*     cases (adv_keys $? k); auto. admit. *)

  (*   - admit. *)
  (* Admitted. *)

  
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
              /\ RealWorld.action_adversary_safe U__r.(RealWorld.all_keys)
                                                     (RealWorld.findUserKeys U__r.(RealWorld.users))
                                                     a1 = true
              /\ RealWorld.universe_ok U__r')
      -> RealWorld.universe_ok U__ra
      -> R (strip_adversary U__ra b) U__i
      -> forall a__r U__ra',
          RealWorld.step_universe U__ra (Action a__r) U__ra'
          -> exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__r a__i
            /\ R (strip_adversary U__ra' b) U__i''
            /\ RealWorld.action_adversary_safe U__ra.(RealWorld.all_keys)
                                                    (RealWorld.findUserKeys U__ra.(RealWorld.users))
                                                    a__r = true
            /\ RealWorld.universe_ok U__ra'.
  Proof.
    intros.
    invert H2.

    assert (RealWorld.universe_ok U__ra) as UNIV_OK by assumption.
    rename H0 into for_split.
    unfold RealWorld.universe_ok in for_split; split_ands.

    (* destruct U__ra; destruct userData; *)
    (*   unfold RealWorld.build_data_step , RealWorld.buildUniverse, strip_adversary in *; simpl in *. *)

    (* eapply ok_universe_strip_adversary_still_ok; eauto. *)

    assert (UNIV_STEP :
              RealWorld.step_universe
                (strip_adversary U__ra b)
                (Action a__r)
                (strip_adversary (RealWorld.buildUniverse usrs adv cs gks u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |}) b) ).

    eapply RealWorld.StepUser; eauto using ok_universe_strip_adversary_ignores_users.
    eapply honest_labeled_step_advuniv_implies_honest_step_origuniv; simpl;
      intros; try rewrite clean_users_idempotent; eauto.

    (* unfold RealWorld.action_adversary_safe; simpl *)
    (* cases a__r; auto.  *)

    admit.
    unfold strip_adversary; simpl; smash_universe. simpl. admit.
    admit.

    assert (RealWorld.universe_ok (strip_adversary U__ra b)) as STRIP_U_OK by (eapply ok_universe_strip_adversary_still_ok; eauto).

    (* eapply RealWorld.find_user_keys_universe_user; eauto. admit. *)
  (*   admit. *)
  (*   unfold strip_adversary; simpl; smash_universe. *)
  (*   admit. (* Need evidence that the user didn't send keys -- strengthen notion of adversary safety *) *)

    specialize (H _ _ H1 STRIP_U_OK _ _ UNIV_STEP).
    repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 3 eexists; intuition idtac;
      eauto using safe_actions_adv_univ_still_safe_strip_adv.


    unfold RealWorld.buildUniverse, RealWorld.universe_ok; simpl.

  (*   invert H7. *)
  (*   unfold RealWorld.action_adversary_safe; destruct a1; auto. *)
  (*   f_equal; eapply msg_pattern_spoofable_strengthen; eauto. *)


  Admitted.

  (* Lemma simulates_with_adversary_loud : *)
  (*   forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop), *)
  (*     (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A), *)
  (*         R U__r U__i -> *)
  (*         forall (a1 : RealWorld.action) (U__r' : RealWorld.universe A B), *)
  (*           RealWorld.step_universe U__r (Action a1) U__r' -> *)
  (*           exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A), *)
  (*             (istepSilent) ^* U__i U__i' /\ *)
  (*             IdealWorld.lstep_universe U__i' (Action a__i) U__i'' /\ *)
  (*             action_matches a1 a__i /\ R U__r' U__i'' /\ *)
  (*             RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__r)) a1 = true) *)
  (*     -> RealWorld.adv_no_honest_keys (RealWorld.findUserKeys U__ra.(RealWorld.adversary)) (RealWorld.findUserKeys U__ra.(RealWorld.users)) *)
  (*     -> R (strip_adversary U__ra) U__i *)
  (*     -> forall a1 U__ra', *)
  (*         RealWorld.step_universe U__ra (Action a1) U__ra' *)
  (*         -> exists a__i U__i' U__i'', *)
  (*           (istepSilent) ^* U__i U__i' *)
  (*           /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i'' *)
  (*           /\ action_matches a1 a__i *)
  (*           /\ R (strip_adversary U__ra') U__i'' *)
  (*           /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__ra)) a1 = true. *)
  (* Proof. *)
  (*   simpl. *)
  (*   intros. *)
  (*   invert H2. *)

  (*   assert (UNIV_STEP : *)
  (*             RealWorld.step_universe *)
  (*               (strip_adversary U__ra) *)
  (*               (Action a1) *)
  (*               (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id *)
  (*                                                           {| RealWorld.key_heap := ks *)
  (*                                                            ; RealWorld.protocol := cmd *)
  (*                                                            ; RealWorld.msg_heap := qmsgs |})) ). *)

  (*   eapply RealWorld.StepUser; eauto. *)
  (*   eapply honest_loud_step_advuniv_implies_honest_step_origuniv; simpl; intros; eauto. *)
  (*   eapply RealWorld.find_user_keys_universe_user; eauto. admit. *)
  (*   admit. *)
  (*   unfold strip_adversary; simpl; smash_universe. *)
  (*   admit. (* Need evidence that the user didn't send keys -- strengthen notion of adversary safety *) *)

  (*   specialize (H _ _ H1 _ _ UNIV_STEP). *)
  (*   repeat match goal with *)
  (*          | [ H : exists _, _ |- _ ] => destruct H *)
  (*          | [ H : _ /\ _ |- _ ] => destruct H *)
  (*          end. *)
  (*   do 3 eexists; intuition idtac; eauto. *)

  (*   invert H7. *)
  (*   unfold RealWorld.action_adversary_safe; destruct a1; auto. *)
  (*   f_equal; eapply msg_pattern_spoofable_strengthen; eauto. *)

  (* Admitted. *)

  Lemma simulates_start_ok_adding_adversary :
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A)
      (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) b advcode,
        RealWorld.is_powerless U__r.(RealWorld.adversary) b
      -> U__ra = add_adversary U__r advcode
      -> R U__r U__i
      -> RealWorld.universe_ok U__r
      -> R (strip_adversary U__ra b) U__i
      /\ RealWorld.universe_ok U__ra.
  Proof.
    intros.
    unfold RealWorld.universe_ok, RealWorld.is_powerless in *; split_ands; subst; simpl in *.
    destruct U__r; destruct adversary; simpl in *.
    apply Empty_eq_empty in H; subst.
    intuition idtac.

    unfold strip_adversary; simpl.
    erewrite real_univ_eq_fields_eq; eauto using clean_ciphers_idempotent, clean_users_idempotent.

  Qed.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) b,
      U__r <| U__i
      -> RealWorld.is_powerless U__r.(RealWorld.adversary) b
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i.
  Proof.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud R__start]; clear H__l.

    unfold refines.
    exists (fun ur ui => R (strip_adversary ur b) ui); unfold simulates.

    split; [|split]; eauto using simulates_with_adversary_silent, simulates_with_adversary_labeled.
 
    eapply simulates_start_ok_adding_adversary; intuition eauto.

  Qed.

End SingleAdversarySimulates.
         