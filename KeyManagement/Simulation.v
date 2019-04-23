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
      -> RealWorld.key_heaps_compatible (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary).(RealWorld.key_heap)
      -> RealWorld.adv_no_honest_keys U__r.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__r.(RealWorld.users))
      -> forall U__r',
          rstepSilent U__r U__r'
          -> exists U__i',
            istepSilent ^* U__i U__i'
            /\ R U__r' U__i')

/\ (forall U__r U__i,
      R U__r U__i
      -> RealWorld.key_heaps_compatible (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary).(RealWorld.key_heap)
      -> RealWorld.adv_no_honest_keys U__r.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__r.(RealWorld.users))
      -> forall a1 U__r',
          RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
          -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R U__r' U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary).(RealWorld.key_heap) a1 = true
            /\ RealWorld.adv_no_honest_keys U__r'.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__r'.(RealWorld.users))
  (* and adversary couldn't have constructed message seen in a1 *)
  )

/\ R U__r U__i
/\ RealWorld.key_heaps_compatible (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.adversary).(RealWorld.key_heap)
/\ RealWorld.adv_no_honest_keys U__r.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__r.(RealWorld.users))
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

    Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
      {| users       := U__r.(users)
       ; adversary   := {| key_heap := $0
                         ; msg_heap := []
                         ; protocol := advcode |}
       ; all_ciphers := U__r.(all_ciphers)
      |}.

    Fixpoint msg_safe {t} (honestk advk : keys) (msg : message t) : bool :=
      match msg with
      | Plaintext _ => false
      | KeyMessage _ => false
      | MsgPair m1 m2 => msg_safe honestk advk m1 && msg_safe honestk advk m2
      | SignedCiphertext _ => true
      | Signature _ _ => true
      end.
    
    Fixpoint msg_filter (honestk advk : keys) (sigM : { t & message t } ) : bool :=
      match sigM with
      | existT _ _ msg => msg_safe honestk advk msg
      end.

    Definition clean_messages (honestk advk : keys) (msgs : queued_messages) :=
      List.filter (msg_filter honestk advk) msgs.

    Definition clean_users {A} (honestk advk : keys) (usrs : honest_users A) :=
      (* usrs. *)
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages honestk advk u_d.(msg_heap) |}) usrs.

    Definition honest_cipher_filter_fn (honestk advk : keys) (c_id : cipher_id) (c : cipher) :=
      match c with
      | SigCipher _ k_id _          => honest_signing_key honestk advk k_id
      | SigEncCipher _ k__sign k__enc _ => honest_signing_key honestk advk k__sign
      end.

    Lemma honest_cipher_filter_fn_proper :
      forall honestk advk,
        Proper (eq  ==>  eq  ==>  eq) (honest_cipher_filter_fn honestk advk).
    Proof.
      unfold Proper, Morphisms.respectful; intros; subst; reflexivity.
    Qed.

    Lemma honest_cipher_filter_fn_filter_proper :
      forall honestk advk,
        Proper
          ( eq  ==>  eq  ==>  Equal  ==>  Equal)
          (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk advk k e then m $+ (k, e) else m).
    Proof.
      unfold Proper, respectful;
      unfold Equal; intros; apply map_eq_Equal in H1; subst; auto.
    Qed.

    Lemma honest_cipher_filter_fn_filter_transpose :
      forall honestk advk,
        transpose_neqkey Equal
          (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn honestk advk k e then m $+ (k, e) else m).
    Proof.
      unfold transpose_neqkey, Equal, honest_cipher_filter_fn; intros.
      cases e; cases e'; simpl.

      Ltac clean_map_lookups1 :=
        match goal with
        | [ H : Some _ = None   |- _ ] => invert H
        | [ H : None = Some _   |- _ ] => invert H
        | [ H : Some _ = Some _ |- _ ] => invert H
        | [ H : $0 $? _ = Some _ |- _ ] => invert H
        | [ H : _ $+ (?k,_) $? ?k = _ |- _ ] => rewrite add_eq_o in H by trivial
        | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by auto
        | [ |- context[_ $+ (?k,_) $? ?k] ] => rewrite add_eq_o by trivial
        | [ |- context[_ $+ (?k1,_) $? ?k2] ] => rewrite add_neq_o by auto
        | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
        end.

      cases (honest_signing_key honestk advk k_id); cases (honest_signing_key honestk advk k_id0); eauto.
        cases (y ==n k); cases (y ==n k'); subst; repeat clean_map_lookups1; try contradiction; eauto.
      cases (honest_signing_key honestk advk k_id); cases (honest_signing_key honestk advk k__sign); eauto.
        cases (y ==n k); cases (y ==n k'); subst; repeat clean_map_lookups1; try contradiction; eauto.
      cases (honest_signing_key honestk advk k_id); cases (honest_signing_key honestk advk k__sign); eauto.
        cases (y ==n k); cases (y ==n k'); subst; repeat clean_map_lookups1; try contradiction; eauto.
      cases (honest_signing_key honestk advk k__sign); cases (honest_signing_key honestk advk k__sign0); eauto.
        cases (y ==n k); cases (y ==n k'); subst; repeat clean_map_lookups1; try contradiction; eauto.
    Qed.

    (* Lemma merge_maps_proper : *)
    (*   forall {B}, *)
    (*     Proper (eq  ==>  eq  ==>  eq  ==>  eq) *)
    (*       (fun (k: NatMap.key) (u : user_data B) (ks : t key) => ks $++ key_heap u). *)
    (* Proof. *)
    (*   unfold Proper, respectful; intros; subst; trivial. *)
    (* Qed. *)

    Definition clean_ciphers (honestk advk : keys) (cs : ciphers) :=
      filter (honest_cipher_filter_fn honestk advk) cs.

    Definition strip_adversary {A B} (U__r : universe A B) (b : B) : universe A B :=
      let honestk := findUserKeys U__r.(users)
      in {| users       := clean_users honestk U__r.(adversary).(key_heap) U__r.(users)
          ; adversary   := {| key_heap := $0
                            ; msg_heap := []
                            ; protocol := Return b |}
          ; all_ciphers := clean_ciphers honestk U__r.(adversary).(key_heap) U__r.(all_ciphers)
         |}.

  End AdversaryHelpers.

  Section RealWorldLemmas.
    Import RealWorld.

    Hint Resolve
         honest_cipher_filter_fn_proper
         honest_cipher_filter_fn_filter_proper
         honest_cipher_filter_fn_filter_transpose.

    Lemma univ_components :
      forall {A B} (U__r : universe A B),
        {| users       := users U__r
         ; adversary   := adversary U__r
         ; all_ciphers := all_ciphers U__r
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

    Lemma clean_ciphers_mapsto_iff : forall honestk advk cs c_id c,
        MapsTo c_id c (clean_ciphers honestk advk cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn honestk advk c_id c = true.
    Proof.
      intros.
      apply filter_iff; eauto.
      Qed.
    
    Lemma clean_ciphers_keeps_honest_cipher :
      forall c_id c honestk advk cs,
        cs $? c_id = Some c
        -> honest_cipher_filter_fn honestk advk c_id c = true
        -> clean_ciphers honestk advk cs $? c_id = Some c.
    Proof.
      intros.
      rewrite <- find_mapsto_iff.
      rewrite <- find_mapsto_iff in H.
      apply clean_ciphers_mapsto_iff; intuition idtac.
    Qed.

    Lemma clean_ciphers_accepts :
      forall {t} honestk advk cs p (m : message t),
          msg_accepted_by_pattern (clean_ciphers honestk advk cs) p m
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
      forall cs c_id c honestk advks k,
        cs $? c_id = Some c
        -> honest_signing_key honestk advks k = true
        -> k = cipher_signing_key c
        -> clean_ciphers honestk advks cs $? c_id = Some c.
    Proof.
      intros.
      eapply clean_ciphers_keeps_honest_cipher; auto.
      unfold honest_cipher_filter_fn.
      unfold cipher_signing_key in *.
      cases c; subst; eauto.
    Qed.

    Lemma clean_ciphers_accepts_non_spoofable :
      forall {t} honestk advks cs p (m : message t),
        msg_accepted_by_pattern cs p m
        -> forall p',
          p' = p
        -> msg_pattern_spoofable honestk advks p' = false
        -> msg_accepted_by_pattern (clean_ciphers honestk advks cs) p' m.
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
      forall {t} cs pat honestk advk (msg : message t),
          ~ msg_accepted_by_pattern cs pat msg
        -> ~ msg_accepted_by_pattern (clean_ciphers honestk advk cs) pat msg.
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
      forall c_id c honestk advk cs k,
        cs $? c_id = Some c
        -> honest_signing_key honestk advk k = false
        -> k = cipher_signing_key c
        -> clean_ciphers honestk advk cs $? c_id = None.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; eauto.
      cases (honest_cipher_filter_fn honestk advk k0 e); eauto.
      cases (c_id ==n k0); subst; eauto.
      exfalso.
      rewrite find_mapsto_iff in H2; rewrite H2 in H; invert H.
      unfold honest_cipher_filter_fn, cipher_signing_key in *.
      cases c;
        rewrite Heq in H0; invert H0.
    Qed.

    Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher.

    Lemma clean_ciphers_reduces_or_keeps_same_ciphers :
      forall c_id c honestk advk cs,
        cs $? c_id = Some c
        -> ( clean_ciphers honestk advk cs $? c_id = Some c
          /\ honest_signing_key honestk advk (cipher_signing_key c) = true)
        \/ ( clean_ciphers honestk advk cs $? c_id = None
          /\ honest_signing_key honestk advk (cipher_signing_key c) = false).
    Proof.
      intros.
      case_eq (honest_signing_key honestk advk (cipher_signing_key c)); intros; eauto.
      left; intuition idtac.
      eapply clean_ciphers_keeps_honest_cipher; eauto.
      unfold honest_cipher_filter_fn, cipher_signing_key in *.
      cases c; eauto.
    Qed.

    Lemma clean_ciphers_no_new_ciphers :
      forall c_id cs honestk advk,
        cs $? c_id = None
        -> clean_ciphers honestk advk cs $? c_id = None.
    Proof.
      intros.
      unfold clean_ciphers, filter.
      apply P.fold_rec_bis; intros; eauto.
      cases (honest_cipher_filter_fn honestk advk k e); eauto.
      - case (c_id ==n k); intro; subst; unfold honest_cipher_filter_fn.
        + rewrite find_mapsto_iff in H0; rewrite H0 in H; invert H.
        + rewrite add_neq_o; eauto.
    Qed.

    Hint Resolve clean_ciphers_no_new_ciphers.

    Lemma clean_ciphers_eliminates_added_dishonest_cipher :
      forall c_id c honestk advk cs k,
        cs $? c_id = None
        -> honest_signing_key honestk advk k = false
        -> k = cipher_signing_key c
        -> clean_ciphers honestk advk cs = clean_ciphers honestk advk (cs $+ (c_id,c)).
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
        rewrite not_find_in_iff; assumption.
    Qed.

    Lemma not_in_ciphers_not_in_cleaned_ciphers :
      forall c_id cs honestk advk,
          ~ In c_id cs
        -> ~ In c_id (clean_ciphers honestk advk cs).
    Proof.
      intros.
      rewrite not_find_in_iff in H.
      apply not_find_in_iff; eauto.
    Qed.

    Hint Resolve not_in_ciphers_not_in_cleaned_ciphers.

    Ltac contra_map_lookup :=
      repeat
        match goal with
        | [ H1 : ?ks1 $? ?k = _, H2 : ?ks2 $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2
        | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction
        end; try discriminate.

    Lemma enc_message_has_honest_signing_key :
      forall {t} k__sign k__enc honestk advk c_id (msg : message t) cipherMsg,
          encryptMessage k__sign k__enc msg c_id = Some cipherMsg
        -> honestk $? (keyId k__sign) = Some k__sign
        -> adv_no_honest_keys advk honestk
        -> key_heaps_compatible honestk advk
        -> honest_signing_key honestk advk (keyId k__sign) = true
        /\ cipherMsg = SigEncCipher c_id (keyId k__sign) (keyId k__enc) msg
        /\ (k__sign.(keyType) = SymKey \/ k__sign.(keyType) = AsymKey true).

    Proof.
      intros.
      unfold encryptMessage in *.
      destruct k__sign; destruct k__enc; simpl in *.
      unfold honest_signing_key.
      rewrite H0.
      cases keyUsage; eauto.
      invert H.
      unfold key_heaps_compatible, adv_no_honest_keys in *; split_ands.
      specialize (H1 keyId); simpl in *.
      cases keyType; eauto; cases (advk $? keyId); auto.
      - exfalso. specialize (H4 _ _ _ H0 Heq).
        destruct k; unfold keys_compatible in *; simpl in *.
        cases (keyId ==n keyId1); cases (keyType); subst; contra_map_lookup.
        cases (has_private_access); eauto; split_ors; contra_map_lookup.
      - cases keyUsage0; invert H; intuition idtac.
      - destruct k; cases has_private_access; subst.
        cases keyType; contra_map_lookup.
        cases has_private_access; split_ors; contra_map_lookup.
        contradiction.
        exfalso.
        cases keyType; contra_map_lookup.
        cases has_private_access; split_ors; contra_map_lookup.
        cases keyUsage0; discriminate.
        cases keyUsage0; discriminate.

      - cases keyUsage0.
        cases has_private_access; invert H; eauto.
        invert H.
    Qed.

    Lemma sign_message_has_honest_signing_key :
      forall {t} k honestk advk c_id (msg : message t) cipherMsg,
          signMessage k msg c_id = Some cipherMsg
        -> honestk $? (keyId k) = Some k
        -> adv_no_honest_keys advk honestk
        -> key_heaps_compatible honestk advk
        -> honest_signing_key honestk advk (keyId k) = true
        /\ cipherMsg = SigCipher c_id (keyId k) msg
        /\ (k.(keyType) = SymKey \/ k.(keyType) = AsymKey  true).

    Proof.
      intros.
      unfold signMessage in *.
      destruct k; simpl in *.
      unfold honest_signing_key.
      rewrite H0.
      cases keyUsage; contra_map_lookup; invert H.
      unfold key_heaps_compatible, adv_no_honest_keys in *; split_ands.
      specialize (H1 keyId); simpl in *.
      cases keyType; eauto; cases (advk $? keyId); auto.
      - exfalso. specialize (H3 _ _ _ H0 Heq).
        destruct k; unfold keys_compatible in *; simpl in *.
        cases (keyId ==n keyId0); cases (keyType); subst; contra_map_lookup.
        cases (has_private_access); eauto; split_ors; contra_map_lookup.
      - invert H4; intuition idtac.
      - destruct k; cases has_private_access; subst; invert H4.
        cases keyType; contra_map_lookup.
        cases has_private_access; split_ors; contra_map_lookup.
        contradiction.
      - cases has_private_access; invert H4; eauto.
    Qed.

    Lemma dishonest_cipher_cleaned :
      forall cs honestk advk c_id cipherMsg,
          honest_signing_key honestk advk (cipher_signing_key cipherMsg) = false
        -> ~ In c_id cs
        -> clean_ciphers honestk advk cs = clean_ciphers honestk advk (cs $+ (c_id, cipherMsg)).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.

      case_eq (cs $? y); intros.

      - apply clean_ciphers_reduces_or_keeps_same_ciphers with (honestk:=honestk) (advk:=advk) in H1.
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

    Lemma honest_enc_cipher_not_cleaned :
      forall {t} cs k__sign k__enc honestk advk c_id (msg : message t) cipherMsg,
          encryptMessage k__sign k__enc msg c_id = Some cipherMsg
        -> honestk $? (keyId k__sign) = Some k__sign
        -> adv_no_honest_keys advk honestk
        -> key_heaps_compatible honestk advk
        -> clean_ciphers honestk advk (cs $+ (c_id, cipherMsg)) = clean_ciphers honestk advk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (enc_message_has_honest_signing_key _ _ _ H H0 H1 H2) as HONEST; split_ands.

      apply map_eq_Equal; unfold Equal; intros.

      case (y ==n c_id); intros; subst.
      - m_equal.
        erewrite clean_ciphers_keeps_honest_cipher; eauto.
      - rewrite add_neq_o by auto.
        case_eq (clean_ciphers honestk advk cs $? y); intros; subst.
        + case_eq (cs $? c_id); intros; subst; eauto.
          * case_eq (cs $? y); intros; subst; eauto.
            ** assert (cs $? y = Some c1) as HH by assumption;
                 eapply clean_ciphers_reduces_or_keeps_same_ciphers in HH; invert HH; invert H4; subst;
                   split_ands; contra_map_lookup.

               rewrite H4. 
               apply clean_ciphers_keeps_honest_cipher; eauto.
               unfold honest_cipher_filter_fn; cases c; eauto.

            ** exfalso. eapply clean_ciphers_no_new_ciphers in H7; contra_map_lookup.

          * unfold clean_ciphers, filter.
            rewrite fold_add; auto.
            unfold honest_cipher_filter_fn.
            rewrite H3; simpl.
            rewrite add_neq_o; eauto.
            rewrite not_find_in_iff; assumption.
        + case_eq (cs $? y); intros; subst; eauto.
          eapply clean_ciphers_eliminates_dishonest_cipher; eauto.
          case_eq (honest_signing_key honestk advk (cipher_signing_key c)); intros; subst; eauto.
          exfalso.
          eapply clean_ciphers_keeps_honest_cipher in H6; contra_map_lookup.
          unfold honest_cipher_filter_fn; cases c; eauto.
    Qed.

    Lemma honest_sign_cipher_not_cleaned :
      forall {t} cs k honestk advk c_id (msg : message t) cipherMsg,
          signMessage k msg c_id = Some cipherMsg
        -> honestk $? (keyId k) = Some k
        -> adv_no_honest_keys advk honestk
        -> key_heaps_compatible honestk advk
        (* -> honest_signing_key honestk advk (keyId k) = true *)
        -> clean_ciphers honestk advk (cs $+ (c_id, cipherMsg)) = clean_ciphers honestk advk cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      pose proof (sign_message_has_honest_signing_key _ _ H H0 H1 H2) as HONEST; split_ands.

      apply map_eq_Equal; unfold Equal; intros.

      case (y ==n c_id); intros; subst.
      - m_equal.
        erewrite clean_ciphers_keeps_honest_cipher; eauto.
      - rewrite add_neq_o by auto.
        case_eq (clean_ciphers honestk advk cs $? y); intros; subst.
        + case_eq (cs $? c_id); intros; subst; eauto.
          * case_eq (cs $? y); intros; subst; eauto.
            ** assert (cs $? y = Some c1) as HH by assumption;
                 eapply clean_ciphers_reduces_or_keeps_same_ciphers in HH; invert HH; invert H4; subst;
                   split_ands; contra_map_lookup.

               rewrite H4.
               apply clean_ciphers_keeps_honest_cipher; eauto.
               unfold honest_cipher_filter_fn; cases c; eauto.

            ** exfalso. eapply clean_ciphers_no_new_ciphers in H7; contra_map_lookup.

          * unfold clean_ciphers, filter.
            rewrite fold_add; auto.
            unfold honest_cipher_filter_fn.
            rewrite H3; simpl.
            rewrite add_neq_o; eauto.
            rewrite not_find_in_iff; assumption.
        + case_eq (cs $? y); intros; subst; eauto.
          eapply clean_ciphers_eliminates_dishonest_cipher; eauto.
          case_eq (honest_signing_key honestk advk (cipher_signing_key c)); intros; subst; eauto.
          exfalso.
          eapply clean_ciphers_keeps_honest_cipher in H6; contra_map_lookup.
          unfold honest_cipher_filter_fn; cases c; eauto.
    Qed.

    Hint Resolve honest_enc_cipher_not_cleaned honest_sign_cipher_not_cleaned.

    Lemma honest_silent_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks ks' qmsgs qmsgs' bd bd' b,
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s honestk,
          honestk = findUserKeys usrs
          -> adv_no_honest_keys adv.(key_heap) honestk
          -> key_heaps_compatible honestk adv.(key_heap)
          -> cs__s = clean_ciphers honestk adv.(key_heap) cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers honestk adv.(key_heap) cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> lbl = Silent
              -> step_user (B:=B) lbl (usrs, powerless_adv b, cs__s, ks, qmsgs, cmd) (usrs', powerless_adv b, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 5; inversion 2; intro; subst;
        repeat match goal with
               | [ H : Action _ = Silent |- _ ] => invert H
               end;
        econstructor;
        eauto.

      - eapply honest_enc_cipher_not_cleaned; eauto.
        admit. (* need link that the ks is in findUserKeys usrs *)
      - eapply clean_ciphers_keeps_honest_cipher; eauto.
        unfold honest_cipher_filter_fn, honest_signing_key.
        unfold adv_no_honest_keys in H5. specialize (H5 (keyId k__sign)).
        assert (findUserKeys usrs' $? k__signid = Some k__sign) by admit.
        unfold key_heaps_compatible in *; split_ands.
        unfold keys_good in *.
        assert (keyId k__sign = k__signid) by auto.
        destruct k__sign; subst; simpl in *.

        cases (key_heap adv' $? keyId).
        + rewrite H2. assert (RealWorld.keyId k = keyId) by auto; destruct k; subst; simpl in *.
          cases keyUsage.
          * exfalso. admit.
          * cases keyType; cases keyType0; eauto; contra_map_lookup.
            ** exfalso. cases has_private_access; eauto; split_ors; contra_map_lookup.
            ** cases has_private_access0; eauto; split_ors; contra_map_lookup.

          (* TODO tbraje: this is where I left off before other refactorings *)
               admit. admit.

        + admit.

      - admit.
      - admit.
                                     
      (* - apply clean_ciphers_keeps_honest_cipher; unfold honest_cipher; eauto. *)
      (*   unfold adv_no_honest_keys in H5. specialize (H5 k__signid). *)
      (*   cases (findUserKeys adv' $? k__signid); auto. *)
      (*   destruct k; cases keyType; auto. *)
      (*   rewrite H1 in H5; invert H5. *)
      (*   cases has_private_access; auto. *)
      (*   rewrite H1 in H5; invert H5. *)

      (* - eapply honest_sign_cipher_not_cleaned; eauto. *)
      (*   unfold adv_no_honest_keys in H5. specialize (H5 (keyId k)). *)
      (*   cases (findUserKeys adv' $? keyId k); auto. *)
      (*     right; exists k0. destruct k0. cases keyType; simpl; eauto. *)
      (*     rewrite H5 in H0; invert H0. *)
      (*     cases has_private_access; eauto. *)
      (*     rewrite H5 in H0; invert H0. *)

      (* - apply clean_ciphers_keeps_honest_cipher; unfold honest_cipher; eauto. *)
      (*   unfold adv_no_honest_keys in H3. specialize (H3 (keyId k)). *)
      (*   cases (findUserKeys adv' $? keyId k); auto. *)
      (*   destruct k0; cases keyType; auto. *)
      (*   rewrite H3 in H0; invert H0. *)
      (*   cases has_private_access; auto. *)
      (*   rewrite H3 in H0; invert H0. *)

    Admitted.

    Lemma honest_loud_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks ks' qmsgs qmsgs' bd bd' a b,
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s honestk,
          honestk = findUserKeys usrs
          -> adv_no_honest_keys adv.(key_heap) ks
          -> cs__s = clean_ciphers honestk adv.(key_heap) cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers honestk adv.(key_heap) cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> lbl = Action a
              -> action_adversary_safe honestk adv.(key_heap) a = true
              -> step_user (B:=B) lbl (usrs, powerless_adv b, cs__s, ks, qmsgs, cmd) (usrs', powerless_adv b, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 4; inversion 2; intro; subst; econstructor; eauto; try discriminate.

      - invert H16. unfold action_adversary_safe in H.
        eapply clean_ciphers_accepts_non_spoofable; eauto.
        admit.
        (* unfold negb in H; cases (msg_pattern_spoofable (findUserKeys adv') pat); eauto. *)

      - unfold addUserKeys; m_equal; simpl. admit.
        
    Admitted.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks ks' qmsgs qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', ks', qmsgs', cmd')
            -> adv = adv'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.
      invert H4.
    Qed.



    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks ks' qmsgs qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', ks', qmsgs', cmd')
            -> forall u_id' u_d,
              usrs' $? u_id' = Some u_d
              -> usrs $? u_id' <> None.
    Proof.
      induction 1; inversion 1; inversion 1; intros; subst; eauto;
        repeat match goal with
               | [ H : ?us $? ?uid = Some _ |- ?us $? ?uid <> None ] => solve [ rewrite H; intro C; invert C ]
               end.

      case (u_id' ==n rec_u_id); intro.
      - subst. rewrite H1; intro C; invert C.
      - rewrite add_neq_o in H11 by auto.
        rewrite H11; intro C; invert C.
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
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks' qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) honestk cs__s,
            bd = (usrs, adv, cs, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          (* -> key_heaps_compatible (findUserKeys usrs) adv.(key_heap) *)
          -> adv_no_honest_keys adv.(key_heap) (findUserKeys usrs)
          -> message_queue_safe honestk adv.(msg_heap) = true
          -> cs__s = clean_ciphers honestk adv.(key_heap) cs
          -> forall cmd' honestk' cs__s',
                bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs
              -> cs__s' = clean_ciphers honestk' (adv'.(key_heap) $k++ ks') cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 5; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Recv *)
      - rewrite <- merge_keys_assoc, merge_keys_refl.
        admit. (* need small lemmas about safe message queues and finding keys in messages *)

      (* Send *)
      - simpl; rewrite merge_keys_symmetric, <- merge_keys_assoc, merge_keys_refl.
        admit. (* how can we prove that the adversary couldn't have created a message with any honest keys here? *)

      (* Encrypt *)
      - assert (honest_signing_key (findUserKeys usrs') (key_heap adv') (cipher_signing_key cipherMsg) = false).
        unfold encryptMessage, adv_no_honest_keys in *.
        unfold honest_signing_key.
        destruct k__sign; destruct k__enc; simpl in *.
        specialize (H14 keyId).
        cases keyUsage; cases keyUsage0; try discriminate.
        cases keyType; try discriminate.
        invert H4; simpl; rewrite H1 in H14; rewrite H14; trivial.
        cases has_private_access; invert H4; simpl; rewrite H1 in H14; split_ors; rewrite H; trivial.

        eapply clean_ciphers_eliminates_added_dishonest_cipher; eauto.
        rewrite <- not_find_in_iff; assumption.

      (* Decrypt *)
      - rewrite <- merge_keys_assoc, merge_keys_refl.
        admit.

      (* Sign *)
      - assert (honest_signing_key (findUserKeys usrs') (key_heap adv') (cipher_signing_key cipherMsg) = false).
        unfold signMessage, adv_no_honest_keys in *.
        unfold honest_signing_key.
        destruct k; simpl in *.
        specialize (H12 keyId).
        cases keyUsage; cases keyType; try discriminate.
        invert H2; simpl; rewrite H0 in H12; rewrite H12; trivial.
        cases has_private_access; invert H2; simpl; rewrite H0 in H12; split_ors; rewrite H; trivial.

        eapply clean_ciphers_eliminates_added_dishonest_cipher; eauto.
        rewrite <- not_find_in_iff; assumption.

    Admitted.

    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) ks' qmsgs' bd bd',
        step_user lbl bd bd'
        -> forall (cmd : user_cmd C) honestk usrs__s,
            bd = (usrs, adv, cs, adv.(key_heap), adv.(msg_heap), cmd)
          -> honestk = findUserKeys usrs
          -> usrs__s = clean_users honestk adv.(key_heap) usrs
          -> forall cmd' honestk' usrs__s',
                bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> honestk' = findUserKeys usrs'
              -> usrs__s' = clean_users honestk' (adv'.(key_heap) $k++ ks') usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst;
        try rewrite merge_keys_refl; eauto.

      (* Recv *)
      - rewrite <- merge_keys_assoc, merge_keys_refl. 
        admit.

      (* Send *)
      - simpl. rewrite merge_keys_symmetric, <- merge_keys_assoc, merge_keys_refl.
         admit.

      (* Decrypt *)
      - rewrite <- merge_keys_assoc, merge_keys_refl.
        admit.

    Admitted.


    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) (b : B)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs ks qmsgs,
        step_user lbl
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, ks, qmsgs, cmd)
        -> R (strip_adversary U__r b) U__i
        -> R (strip_adversary (buildUniverseAdv usrs cs {| key_heap := adv.(key_heap) $k++ ks; protocol := cmd; msg_heap := qmsgs |}) b) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.

      match goal with
      | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] =>
        idtac us; idtac us';
        idtac cs; idtac cs'
      end.

      assert ( (clean_users (findUserKeys (users U__r)) (key_heap (adversary U__r)) (users U__r)) = (clean_users (findUserKeys usrs) (key_heap adv $k++ ks) usrs) ).
      eapply adv_step_implies_no_user_impact_after_cleaning; eauto.

      assert ( (clean_ciphers (findUserKeys (users U__r)) (key_heap (adversary U__r)) (all_ciphers U__r)) = (clean_ciphers (findUserKeys usrs) (key_heap adv $k++ ks) cs) ).
      eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto.





      (* match goal with *)
      (* | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] => *)
      (*   idtac cs; idtac cs'. *)
      (*   assert ( cs = cs' ) as CS by (unfold build_data_step in *; eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto); *)
      (*     assert ( us = us' ) as US by (unfold build_data_step in *; eapply adv_step_implies_no_user_impact_after_cleaning; eauto) *)
      (* end; rewrite <- CS; rewrite <- US; clear US CS; *)
      (*   assumption. *)




      (* assert (U__r.(adversary) = $0 $+ (u_id,userData)) by (map_equal; eauto). *)

      (* assert (findUserKeys U__r.(adversary) = userData.(key_heap)) as ADV_KEYS *)
      (*   by (rewrite H3; unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial). *)
      (* rewrite ADV_KEYS in H2; clear ADV_KEYS. *)

      (* assert (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |}) *)
      (*         = $0 $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) as ADV_RED; *)
      (*   map_equal; trivial. *)
      (* pose proof H1 as NOADD; unfold build_data_step in NOADD; *)
      (*   eapply user_step_adds_removes_no_adversaries with (u_id' := KEY) in NOADD; eauto; *)
      (*     unfold iff in NOADD; invert NOADD. *)
      (* case_eq (adv $? KEY); intros; eauto. exfalso. *)

      (* assert (adv $? KEY <> None) as LK_KEY_NOT_NONE *)
      (*   by (unfold not; intros; *)
      (*       match goal with [ H1 : ?m $? ?k = Some _, H2 : ?m $? ?k = None |- _ ] => rewrite H1 in H2; invert H2 end). *)
      (* specialize (H0 _ n); specialize (H4 LK_KEY_NOT_NONE); contradiction. *)

      (* assert (findUserKeys (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) = ks); *)
      (*   rewrite ADV_RED; clear ADV_RED; *)
      (*   unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial. *)

      (* match goal with *)
      (* | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] => *)
      (*   assert ( cs = cs' ) as CS by (unfold build_data_step in *; eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto); *)
      (*     assert ( us = us' ) as US by (unfold build_data_step in *; eapply adv_step_implies_no_user_impact_after_cleaning; eauto) *)
      (* end; rewrite <- CS; rewrite <- US; clear US CS; *)
      (*   assumption. *)

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
          -> RealWorld.key_heaps_compatible (RealWorld.findUserKeys (RealWorld.users U__r)) (RealWorld.key_heap (RealWorld.adversary U__r))
          -> RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__r)) (RealWorld.findUserKeys (RealWorld.users U__r))
          -> forall U__r' : RealWorld.universe A B,
              rstepSilent U__r U__r'
              -> exists U__i' : IdealWorld.universe A, (istepSilent) ^* U__i U__i' /\ R U__r' U__i')

      -> RealWorld.key_heaps_compatible (RealWorld.findUserKeys (RealWorld.users U__ra)) (RealWorld.key_heap (RealWorld.adversary U__ra))
      -> RealWorld.adv_no_honest_keys U__ra.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__ra.(RealWorld.users))
      -> R (strip_adversary U__ra b) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 /\ R (strip_adversary U__ra' b) U__i'.
  Proof.
    intros.
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
      split.
      eapply TrcRefl.
      eapply adv_step_stays_in_R; eauto.

  Admitted.


  (* Lemma simulates_with_adversary_silent : *)
  (*   forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop), *)
  (*     (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A), *)
  (*         R U__r U__i *)
  (*         -> forall U__r' : RealWorld.universe A B, *)
  (*           rstepSilent U__r U__r' *)
  (*           -> exists U__i' : IdealWorld.universe A, (istepSilent) ^* U__i U__i' /\ R U__r' U__i') *)
  (*     -> RealWorld.adv_no_honest_keys U__ra.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__ra.(RealWorld.users)) *)
  (*     (* obviously single adv now *) *)
  (*     (* -> (forall a_id1 a_id2 a, a_id1 <> a_id2 -> U__ra.(RealWorld.adversary) $? a_id1 = Some a -> U__ra.(RealWorld.adversary) $? a_id2 = None) *) *)
  (*     -> R (strip_adversary U__ra) U__i *)
  (*     -> forall U__ra', *)
  (*         rstepSilent U__ra U__ra' *)
  (*         -> exists U__i', istepSilent ^* U__i U__i' *)
  (*                  /\ R (strip_adversary U__ra') U__i'. *)
  (* Proof. *)
  (*   simpl. *)
  (*   intros. *)
  (*   invert H3. *)

  (*   (* Honest step *) *)
  (*   - simpl. *)
  (*     assert (UNIV_STEP : *)
  (*               rstepSilent *)
  (*                 (strip_adversary U__ra) *)
  (*                 (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id *)
  (*                                                           {| RealWorld.key_heap := ks *)
  (*                                                            ; RealWorld.protocol := cmd *)
  (*                                                            ; RealWorld.msg_heap := qmsgs |})) ). *)

  (*     eapply RealWorld.StepUser; eauto. *)
  (*     eapply honest_silent_step_advuniv_implies_honest_step_origuniv; intros; eauto. *)
  (*     eapply RealWorld.find_user_keys_universe_user; eauto. admit. *)
  (*     eauto. *)
  (*     unfold strip_adversary; simpl; smash_universe. *)

  (*     unfold RealWorld.build_data_step in H5. *)
  (*     eapply honest_silent_step_nochange_adversaries in H5; [| reflexivity..]; rewrite H5; trivial. *)

  (*     eapply H; eauto. *)

  (*   - exists U__i. *)
  (*     split. *)
  (*     eapply TrcRefl. *)
  (*     eapply adv_step_stays_in_R; eauto. *)

  (* Admitted. *)

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
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i ->
          RealWorld.key_heaps_compatible (RealWorld.findUserKeys (RealWorld.users U__r)) (RealWorld.key_heap (RealWorld.adversary U__r)) ->
          RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__r)) (RealWorld.findUserKeys (RealWorld.users U__r)) ->
          forall (a1 : RealWorld.action) (U__r' : RealWorld.universe A B),
            RealWorld.step_universe U__r (Action a1) U__r' ->
            exists (a2 : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
              (istepSilent) ^* U__i U__i'
              /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
              /\ action_matches a1 a2
              /\ R U__r' U__i''
              /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__r)) (RealWorld.key_heap (RealWorld.adversary U__r)) a1 = true
              /\ RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__r')) (RealWorld.findUserKeys (RealWorld.users U__r')))
      -> RealWorld.adv_no_honest_keys U__ra.(RealWorld.adversary).(RealWorld.key_heap) (RealWorld.findUserKeys U__ra.(RealWorld.users))
      -> R (strip_adversary U__ra b) U__i
      -> forall a__r U__ra',
          RealWorld.step_universe U__ra (Action a__r) U__ra'
          -> exists (a__i : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__r a__i
            /\ R (strip_adversary U__ra' b) U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__ra)) (RealWorld.key_heap (RealWorld.adversary U__ra)) a__r = true
            /\ RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__ra')) (RealWorld.findUserKeys (RealWorld.users U__ra')).
  Proof.
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
    forall {A B} (U__r U__ra: RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B) advcode,
      RealWorld.is_powerless U__r.(RealWorld.adversary) = true
      -> U__ra = add_adversary U__r advcode
      -> RealWorld.key_heaps_compatible (RealWorld.findUserKeys (RealWorld.users U__r)) (RealWorld.key_heap (RealWorld.adversary U__r))
      -> RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__r)) (RealWorld.findUserKeys (RealWorld.users U__r))
      -> R (strip_adversary U__ra b) U__i
      /\ RealWorld.key_heaps_compatible (RealWorld.findUserKeys (RealWorld.users U__ra)) (RealWorld.key_heap (RealWorld.adversary U__ra))
      /\ RealWorld.adv_no_honest_keys (RealWorld.key_heap (RealWorld.adversary U__ra)) (RealWorld.findUserKeys (RealWorld.users U__ra)).
  Proof.

      (*   - rewrite H1; unfold strip_adversary, add_adversary; simpl. *)
      (* rewrite H0. rewrite empty_add_idempotent. *)
      (* unfold RealWorld.findUserKeys, fold; simpl. rewrite RealWorld.merge_keys_left_identity. *)

      (* rewrite clean_ciphers_nokeys_idempotent. *)
      (* unfold clean_users; simpl. *)
      (* rewrite <- H0; rewrite univ_components. auto. *)

  Admitted.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) (b : B),
      U__r <| U__i
      -> RealWorld.is_powerless U__r.(RealWorld.adversary) = true
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

    split; [|split];
      eauto using simulates_with_adversary_silent, simulates_with_adversary_labeled.

    eapply simulates_start_ok_adding_adversary; intuition eauto.

  Qed.

End SingleAdversarySimulates.
