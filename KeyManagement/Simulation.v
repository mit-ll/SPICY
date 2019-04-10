From Coq Require Import
     List
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
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps p x y,
      rw = (RealWorld.Input msg1 p x y)
    -> iw = IdealWorld.Input msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
| Out : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps x,
      rw = RealWorld.Output msg1 x
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
      -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
          /\ R U__r' U__i')

  /\ (forall U__r U__i,
        R U__r U__i
        -> forall a1 U__r',
          RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
          -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R U__r' U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.adversary)) a1 = true
    (* and adversary couldn't have constructed message seen in a1 *)
    )

  /\ R U__r U__i.

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

    Definition ADV := 10.

    Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
      addAdversaries U__r ($0 $+ (ADV, {| key_heap := $0
                                      ; msg_heap := []
                                      ; protocol := advcode |})).

    Fixpoint msg_safe {t} (msg : message t) : bool :=
      match msg with
      | Plaintext _ => false
      | KeyMessage _ => false
      | MsgPair m1 m2 => msg_safe m1 && msg_safe m2
      | SignedCiphertext _ => true
      | Signature _ _ => true
      end.

    Definition exm_safe (msg : exmsg) : bool :=
      match msg with
      | Exm m => true
      end.

    Definition clean_messages (msgs : queued_messages) :=
      List.filter exm_safe msgs.

    Definition clean_users {A} ( usrs : honest_users A ) :=
      usrs.
      (* map (fun u_d => {| key_heap := u_d.(key_heap) *)
      (*               ; protocol := u_d.(protocol) *)
      (*               ; msg_heap := clean_messages u_d.(msg_heap) |}) usrs. *)

    (* So called honest ciphers are those that :
     *  1. Are signed by an honest user
     *  2. HOW DO WE KNOW WHICH ENCRYPTED CIPHERS TO KEEP?
     *)
    Definition honest_cipher (adv_keys : keys) (c : cipher) :=
      match c with
      | SigCipher _ k_id _ =>
        match adv_keys $? k_id with
        | Some (MkCryptoKey _ _ SymKey)         => false
        | Some (MkCryptoKey _ _ (AsymKey true)) => false
        | _ => true
        end
      | SigEncCipher _ k__sign k__enc _ =>
        match adv_keys $? k__sign with
        | Some (MkCryptoKey _ _ SymKey)         => false
        | Some (MkCryptoKey _ _ (AsymKey true)) => false
        | _ => true
        end
      end.

    Definition honest_cipher_filter_fn (adv_keys : keys) (k : key_identifier) (v : cipher) :=
      honest_cipher adv_keys v.

    Lemma honest_cipher_proper_morphism :
      forall ks,
        Morphisms.Proper
          (Morphisms.respectful eq (Morphisms.respectful eq eq))
          (honest_cipher_filter_fn ks).
    Proof.
      unfold Morphisms.Proper, Morphisms.respectful; intros; subst; reflexivity.
    Qed.

    Lemma honest_cipher_filter_proper_morphism :
      forall adv_keys,
        Morphisms.Proper
          (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful Equal Equal)))
          (fun (k : NatMap.key) (e : cipher) (m : t cipher) => if honest_cipher_filter_fn adv_keys k e then m $+ (k, e) else m).
    Proof.
      unfold Morphisms.Proper, Morphisms.respectful; intros.
      apply map_eq_Equal in H1; subst; reflexivity.
    Qed.

    Lemma honest_cipher_filter_transpose_key :
      forall ks,
        transpose_neqkey Equal (fun k e m => if honest_cipher_filter_fn ks k e then m $+ (k, e) else m).
    Proof.
      unfold transpose_neqkey, Equal, honest_cipher_filter_fn; intros.
      case (honest_cipher ks e); eauto.
      case (honest_cipher ks e'); eauto.
      case (y ==n k); intro; subst.
      rewrite add_eq_o by auto. rewrite add_neq_o, add_eq_o by auto. trivial.
      rewrite add_neq_o by auto.
      case (y ==n k'); intros; subst.
      m_equal; trivial.
      do 3 rewrite add_neq_o by auto; trivial.
    Qed.

    Lemma merge_maps_proper_morphism :
      forall {B},
        Morphisms.Proper
          (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq)))
          (fun (k: NatMap.key) (u : user_data B) (ks : t key) => ks $++ key_heap u).
    Proof.
      unfold Morphisms.Proper, Morphisms.respectful; intros; subst; trivial.
    Qed.

    Definition clean_ciphers (adv_keys : keys) (cs : ciphers) :=
      filter (honest_cipher_filter_fn adv_keys) cs.

    Definition strip_adversary {A B} (U__r : universe A B) : universe A B :=
      {| users       := clean_users U__r.(users)
       ; adversary   := $0
       ; all_ciphers := clean_ciphers (findUserKeys U__r.(adversary)) U__r.(all_ciphers)
      |}.

    Lemma clean_ciphers_nokeys_idempotent :
      forall cs,
        clean_ciphers $0 cs = cs.
    Proof.
      intros.
      unfold clean_ciphers, filter.
      apply P.fold_rec; intros.

      m_equal.

      apply map_eq_Equal; unfold Equal, honest_cipher_filter_fn, honest_cipher; destruct e; subst; eauto.

    Qed.

  End AdversaryHelpers.

  Section RealWorldLemmas.
    Import RealWorld.

    Hint Resolve honest_cipher_proper_morphism honest_cipher_filter_proper_morphism honest_cipher_filter_transpose_key.

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
        -> exists ud', addUserKeys us ks $? uid = Some ud'.
    Proof.
      intros.
      (* eexists. *)
      unfold addUserKeys.
      apply find_mapsto_iff in H.
      eexists.
      rewrite <- find_mapsto_iff.
      rewrite map_mapsto_iff.
      eexists; intuition. eassumption.
    Qed.

    Lemma clean_ciphers_mapsto_iff : forall ks cs c_id c,
        MapsTo c_id c (clean_ciphers ks cs) <-> MapsTo c_id c cs /\ honest_cipher_filter_fn ks c_id c = true.
    Proof.
      intros.
      apply filter_iff; eauto.
    Qed.
    
    Lemma clean_ciphers_keeps_honest_cipher :
      forall c_id c adv_keys cs,
        cs $? c_id = Some c
        -> honest_cipher adv_keys c = true
        -> clean_ciphers adv_keys cs $? c_id = Some c.
    Proof.
      intros.
      rewrite <- find_mapsto_iff.
      rewrite <- find_mapsto_iff in H.
      apply clean_ciphers_mapsto_iff; intuition.
    Qed.

    Lemma clean_ciphers_accepts :
      forall {t} ks cs p (m : message t),
          msg_accepted_by_pattern (clean_ciphers ks cs) p m
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

    Lemma clean_ciphers_accepts_non_spoofable :
      forall {t} ks cs p (m : message t),
        msg_accepted_by_pattern cs p m
        -> forall p',
          p' = p
        -> msg_pattern_spoofable ks p' = false
        -> msg_accepted_by_pattern (clean_ciphers ks cs) p' m.
    Proof.
      induction 1; intros; subst; eauto.
      - econstructor; auto.
      - invert H4; apply orb_false_elim in H0; invert H0.
        eapply BothPairsAccepted; eauto.
      - eapply ProperlySigned; eauto.
        invert H3.
        case_eq (ks $? k); intros; rewrite H in H0; simpl.
        + invert H0.
        + eapply clean_ciphers_keeps_honest_cipher; eauto.
          unfold honest_cipher; rewrite H; trivial.
      - eapply ProperlyEncrypted; eauto.
        invert H3.
        case_eq (ks $? k__sign); intros; rewrite H in H0; simpl.
        + invert H0.
        + eapply clean_ciphers_keeps_honest_cipher; eauto.
          unfold honest_cipher; rewrite H; trivial.
    Qed.

    Hint Constructors msg_accepted_by_pattern.

    Lemma clean_ciphers_doesn't_make_unaccepted_msg_accepted :
      forall {t} cs pat ks (msg : message t),
          ~ msg_accepted_by_pattern cs pat msg
        -> ~ msg_accepted_by_pattern (clean_ciphers ks cs) pat msg.
    Proof.
      unfold "~"; induction 2; subst;
        eauto;
        repeat match goal with
               | [ H : clean_ciphers _ _ $? _ = Some _ |- _] => rewrite <- find_mapsto_iff in H; rewrite clean_ciphers_mapsto_iff in H
               | [ H : _ /\ _ |- _ ] => invert H
               | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
               end; eauto.
    Qed.

    Hint Resolve clean_ciphers_doesn't_make_unaccepted_msg_accepted.
    Hint Extern 1 (_ $+ (?k, _) $? ?k = Some _) => rewrite add_eq_o.
    Hint Extern 1 (_ $+ (?k, _) $? ?v = _) => rewrite add_neq_o.

    Lemma clean_ciphers_eliminates_dishonest_cipher :
      forall c_id c adv_keys cs,
        cs $? c_id = Some c
        -> honest_cipher adv_keys c = false
        -> clean_ciphers adv_keys cs $? c_id = None.
    Proof.
      intros; unfold clean_ciphers, filter.
      apply P.fold_rec; intros; eauto.
      unfold honest_cipher_filter_fn.
      case (c_id ==n k); intro; subst.
      - rewrite find_mapsto_iff in H1; rewrite H1 in H; invert H.
        rewrite H0; auto.
      - case (honest_cipher adv_keys e); eauto.
    Qed.

    Hint Resolve clean_ciphers_eliminates_dishonest_cipher clean_ciphers_keeps_honest_cipher.

    Lemma clean_ciphers_reduces_or_keeps_same_ciphers :
      forall c_id c adv_keys cs,
        cs $? c_id = Some c
        -> ( clean_ciphers adv_keys cs $? c_id = Some c
          /\ honest_cipher adv_keys c = true)
        \/ ( clean_ciphers adv_keys cs $? c_id = None
          /\ honest_cipher adv_keys c = false).
    Proof.
      intros.
      case_eq (honest_cipher adv_keys c); intro; eauto.
    Qed.

    Lemma clean_ciphers_no_new_ciphers :
      forall c_id cs adv_keys,
        cs $? c_id = None
        -> clean_ciphers adv_keys cs $? c_id = None.
    Proof.
      intros.
      unfold clean_ciphers, filter.
      apply P.fold_rec; intros.

      - eauto.

      - case (c_id ==n k); intro; subst; unfold honest_cipher_filter_fn.
        + rewrite find_mapsto_iff in H0; rewrite H0 in H; invert H.
        + case (honest_cipher adv_keys e); eauto.

    Qed.

    Hint Resolve clean_ciphers_no_new_ciphers.

    Lemma not_in_ciphers_not_in_cleaned_ciphers :
      forall c_id cs ks,
          ~ In c_id cs
        -> ~ In c_id (clean_ciphers ks cs).
    Proof.
      intros.
      rewrite not_find_in_iff in H.
      apply not_find_in_iff; eauto.
    Qed.

    Hint Resolve not_in_ciphers_not_in_cleaned_ciphers.

    Lemma enc_cipher_has_key :
      forall {t} k__sign k__enc (msg : message t) c_id cipherMsg,
        encryptMessage k__sign k__enc msg c_id = Some cipherMsg
        -> cipherMsg = SigEncCipher c_id (keyId k__sign) (keyId k__enc) msg
        /\ (k__sign.(keyType) = SymKey \/ k__sign.(keyType) = AsymKey true).
    Proof.
      intros.
      unfold encryptMessage in H.
      destruct k__sign; simpl in *.
      case_eq keyUsage; intro; subst; simpl in *; invert H; eauto.
      destruct k__enc; simpl in *.
      case_eq keyUsage; intro; subst; simpl in *; invert H1; eauto.
      case_eq keyType; intros; subst; simpl in *; invert H0; eauto.
      case_eq has_private_access; intros; subst; invert H1; eauto.
    Qed.

    Lemma sign_cipher_has_key :
      forall {t} k (msg : message t) c_id cipherMsg,
        signMessage k msg c_id = Some cipherMsg
        -> cipherMsg = SigCipher c_id (keyId k) msg
          /\ (k.(keyType) = SymKey \/ k.(keyType) = AsymKey  true).
    Proof.
      intros.
      unfold signMessage in H.

      case_eq k; intros; rewrite H0 in H.
      case_eq keyUsage; intro; subst; simpl in *; invert H;
        case_eq keyType; intros; subst; invert H1.
      - intuition.
      - case_eq has_private_access; intros; subst; invert H0; intuition.
      - intuition.
      - case_eq has_private_access; intros; subst; invert H0; intuition.
    Qed.

    Lemma dishonest_cipher_cleaned :
      forall cs adv_keys c_id cipherMsg,
          honest_cipher adv_keys cipherMsg = false
        -> ~ In c_id cs
        -> clean_ciphers adv_keys cs = clean_ciphers adv_keys (cs $+ (c_id, cipherMsg)).
    Proof.
      intros.
      apply map_eq_Equal; unfold Equal; intros.

      case_eq (cs $? y); intros.

      - apply clean_ciphers_reduces_or_keeps_same_ciphers with (adv_keys:=adv_keys) in H1.
        destruct H1; destruct H1;
          rewrite H1;
            unfold clean_ciphers, filter in H1;
            symmetry; unfold clean_ciphers, filter;
              rewrite fold_add by eauto;
              unfold honest_cipher_filter_fn; rewrite H; auto.

      - rewrite clean_ciphers_no_new_ciphers; auto.
        apply clean_ciphers_no_new_ciphers with (adv_keys:=adv_keys) in H1.
        unfold clean_ciphers, filter. rewrite fold_add; eauto.
        unfold honest_cipher_filter_fn; rewrite H.
        unfold clean_ciphers, filter in H1.
        symmetry; auto.
    Qed.

    Lemma honest_enc_cipher_not_cleaned :
      forall {t} cs k__sign k__enc ks c_id (msg : message t) cipherMsg,
          encryptMessage k__sign k__enc msg c_id = Some cipherMsg
        -> (ks $? (keyId k__sign) = None \/ exists k, ks $? (keyId k__sign) = Some k /\ keyType k = AsymKey false)
        -> clean_ciphers ks (cs $+ (c_id, cipherMsg)) = clean_ciphers ks cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      assert( honest_cipher ks cipherMsg = true ).
      apply enc_cipher_has_key in H; invert H.
      unfold honest_cipher.
      invert H0.
        rewrite H; auto.
        invert H. invert H0. rewrite H. destruct x. simpl in H1. rewrite H1; trivial.

      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n c_id); intros; subst.
      - rewrite clean_ciphers_keeps_honest_cipher with (c := cipherMsg); eauto.
        rewrite add_eq_o; auto.

      - case_eq (clean_ciphers ks cs $? y); intros.

        + rewrite -> clean_ciphers_keeps_honest_cipher with (c := c).
          rewrite add_neq_o by auto; auto.

          rewrite <- find_mapsto_iff in H2; apply clean_ciphers_mapsto_iff in H2; destruct H2.
          unfold honest_cipher_filter_fn in H3. auto.
          rewrite add_neq_o by auto; apply find_mapsto_iff; auto.

          rewrite <- find_mapsto_iff in H2; apply clean_ciphers_mapsto_iff in H2; destruct H2; auto.

        + rewrite add_neq_o by auto. rewrite H2.
          case_eq (cs $? y); intros.
          apply clean_ciphers_eliminates_dishonest_cipher with (c := c); eauto.
          case_eq (honest_cipher ks c); intros.
          apply clean_ciphers_keeps_honest_cipher with (adv_keys := ks) in H3. rewrite H3 in H2. invert H2. auto. auto.
          apply clean_ciphers_no_new_ciphers; auto.
    Qed.

    Lemma honest_sign_cipher_not_cleaned :
      forall {t} cs k ks c_id (msg : message t) cipherMsg,
        signMessage k msg c_id = Some cipherMsg
        -> (ks $? (keyId k) = None \/ exists k', ks $? (keyId k) = Some k' /\ keyType k' = AsymKey false)
        -> clean_ciphers ks (cs $+ (c_id, cipherMsg)) = clean_ciphers ks cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      assert( honest_cipher ks cipherMsg = true ).
      apply sign_cipher_has_key in H; invert H.
      unfold honest_cipher.
      invert H0.
        rewrite H; auto.
        invert H. invert H0. rewrite H. destruct x. simpl in H1. rewrite H1; trivial.

      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n c_id); intros; subst.
      - rewrite clean_ciphers_keeps_honest_cipher with (c := cipherMsg); eauto.
        rewrite add_eq_o; auto.

      - case_eq (clean_ciphers ks cs $? y); intros.

        + rewrite -> clean_ciphers_keeps_honest_cipher with (c := c).
          rewrite add_neq_o by auto; auto.

          rewrite <- find_mapsto_iff in H2; apply clean_ciphers_mapsto_iff in H2; destruct H2.
          unfold honest_cipher_filter_fn in H3. auto.
          rewrite add_neq_o by auto; apply find_mapsto_iff; auto.

          rewrite <- find_mapsto_iff in H2; apply clean_ciphers_mapsto_iff in H2; destruct H2; auto.

        + rewrite add_neq_o by auto. rewrite H2.
          case_eq (cs $? y); intros.
          apply clean_ciphers_eliminates_dishonest_cipher with (c := c); eauto.
          case_eq (honest_cipher ks c); intros.
          apply clean_ciphers_keeps_honest_cipher with (adv_keys := ks) in H3. rewrite H3 in H2. invert H2. auto. auto.
          apply clean_ciphers_no_new_ciphers; auto.
    Qed.

    Hint Resolve honest_enc_cipher_not_cleaned honest_sign_cipher_not_cleaned.

    Lemma honest_silent_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s adv_keys,
          adv_keys = findUserKeys adv
          -> adv_no_honest_keys adv_keys ks
          -> cs__s = clean_ciphers adv_keys cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers adv_keys cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> lbl = Silent
              -> step_user (B:=B) u_id lbl (usrs, $0, cs__s, ks, qmsgs, cmd) (usrs', $0, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 4; inversion 2; intro; subst;
        repeat match goal with
               | [ H : Action _ = Silent |- _ ] => invert H
               end;
        econstructor;
        eauto.

      - eapply honest_enc_cipher_not_cleaned; eauto.
        unfold adv_no_honest_keys in H7. specialize (H7 (keyId k__sign)).
        cases (findUserKeys adv' $? keyId k__sign); auto.
          right; exists k. destruct k. cases keyType; simpl; eauto.
          rewrite H7 in H1; invert H1.
          cases has_private_access; eauto.
          rewrite H7 in H1; invert H1.
                                     
      - apply clean_ciphers_keeps_honest_cipher; unfold honest_cipher; eauto.
        unfold adv_no_honest_keys in H5. specialize (H5 k__signid).
        cases (findUserKeys adv' $? k__signid); auto.
        destruct k; cases keyType; auto.
        rewrite H1 in H5; invert H5.
        cases has_private_access; auto.
        rewrite H1 in H5; invert H5.

      - eapply honest_sign_cipher_not_cleaned; eauto.
        unfold adv_no_honest_keys in H5. specialize (H5 (keyId k)).
        cases (findUserKeys adv' $? keyId k); auto.
          right; exists k0. destruct k0. cases keyType; simpl; eauto.
          rewrite H5 in H0; invert H0.
          cases has_private_access; eauto.
          rewrite H5 in H0; invert H0.

      - apply clean_ciphers_keeps_honest_cipher; unfold honest_cipher; eauto.
        unfold adv_no_honest_keys in H3. specialize (H3 (keyId k)).
        cases (findUserKeys adv' $? keyId k); auto.
        destruct k0; cases keyType; auto.
        rewrite H3 in H0; invert H0.
        cases has_private_access; auto.
        rewrite H3 in H0; invert H0.

    Qed.


    (* Lemma honest_loud_step_advuniv_implies_honest_step_origuniv : *)
    (*   forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd' a, *)
    (*     step_user u_id lbl bd bd' *)
    (*     -> forall (cmd : user_cmd C) cs__s adv_keys, *)
    (*       adv_keys = findUserKeys adv *)
    (*       -> adv_no_honest_keys adv_keys ks *)
    (*       -> cs__s = clean_ciphers adv_keys cs *)
    (*       -> bd = (usrs, adv, cs, ks, qmsgs, cmd) *)
    (*       -> forall cmd' cs__s', *)
    (*           cs__s' = clean_ciphers adv_keys cs' *)
    (*           -> bd' = (usrs', adv', cs', ks', qmsgs', cmd') *)
    (*           -> lbl = Action a *)
    (*           -> step_user (B:=B) u_id lbl (usrs, $0, cs__s, ks, qmsgs, cmd) (usrs', $0, cs__s', ks', qmsgs', cmd'). *)
    (* Proof. *)
    (*   induction 1; inversion 4; inversion 2; intro; subst; econstructor; eauto; try discriminate. *)

    (*   - invert H16. unfold action_adversary_safe in H. *)
    (*     eapply clean_ciphers_accepts_non_spoofable; eauto. *)
    (*     unfold negb in H; cases (msg_pattern_spoofable (findUserKeys adv') pat); eauto. *)

    (*   - unfold addUserKeys; m_equal; trivial. *)
        
    (* Qed. *)


    Lemma honest_loud_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd' a,
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s adv_keys,
          adv_keys = findUserKeys adv
          -> adv_no_honest_keys adv_keys ks
          -> cs__s = clean_ciphers adv_keys cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers adv_keys cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> lbl = Action a
              -> action_adversary_safe adv_keys a = true
              -> step_user (B:=B) u_id lbl (usrs, $0, cs__s, ks, qmsgs, cmd) (usrs', $0, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 4; inversion 2; intro; subst; econstructor; eauto; try discriminate.

      - invert H16. unfold action_adversary_safe in H.
        eapply clean_ciphers_accepts_non_spoofable; eauto.
        unfold negb in H; cases (msg_pattern_spoofable (findUserKeys adv') pat); eauto.

      - unfold addUserKeys; m_equal; trivial.
        
    Qed.

    Lemma honest_silent_step_nochange_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
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

    (* Specialize to single adversary.  This means that in the following proof, we assume
     * that, since we are stepping the adversary, then
     *   ks =  adv keys at beginning
     *   ks' = adv keys at the end
     *)
    Lemma adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s,
            bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> cs__s = clean_ciphers ks cs
          (* -> (forall k_id v, MapsTo k_id v ks -> MapsTo k_id v adv_keys) *)
          -> forall cmd' cs__s',
                bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> cs__s' = clean_ciphers ks' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 2; intros; subst; eauto.

      - (* Hrm.  Did the adversary receive any new keys in the received message.
         * We know not, since the message didn't come from an honest user, but
         * how can we show that?
         *)
        admit. 

      - apply dishonest_cipher_cleaned; eauto.
        apply enc_cipher_has_key in H4.
        invert H4.
        destruct k__sign; simpl in *.
        unfold honest_cipher; invert H0; simpl.
        rewrite H1; eauto.
        rewrite H1; eauto.

      - (* Adversary just decryped a message.  Did it have any keys?
         * Need to reason about what kinds of keys could be in there.
         *)
        admit.

      - apply dishonest_cipher_cleaned; eauto.
        apply sign_cipher_has_key in H2.
        invert H2; invert H3; 
          unfold honest_cipher; rewrite H0;
            destruct k; simpl in H; subst; eauto.

    Admitted.

    (* Specialize to single adversary.  This means that in the following proof, we assume
     * that, since we are stepping the adversary, then
     *   ks =  adv keys at beginning
     *   ks' = adv keys at the end
     *)
    Lemma adv_step_implies_no_user_impact_after_cleaning :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) usrs__s,
            bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> usrs__s = clean_users usrs
          (* -> (forall k_id v, MapsTo k_id v ks -> MapsTo k_id v adv_keys) *)
          -> forall cmd' usrs__s',
                bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> usrs__s' = clean_users usrs'
              -> usrs__s = usrs__s'.
    Proof.
      induction 1; inversion 1; inversion 2; intros; subst; eauto.

      (* only goal left is the adversary send case *)

      (* H1 : usrs $? rec_u_id = Some rec_u *)
      (* H3 : (usrs, adv, cs', ks', qmsgs', Send rec_u_id msg) = (usrs, adv, cs', ks', qmsgs', Send rec_u_id msg) *)
      (* H11 : (usrs $+ (rec_u_id, {| key_heap := key_heap rec_u; protocol := protocol rec_u; msg_heap := msg_heap rec_u ++ [Exm msg] |}), addUserKeys adv (findKeys msg), cs', ks', qmsgs', Return tt) = *)
      (*   (usrs $+ (rec_u_id, {| key_heap := key_heap rec_u; protocol := protocol rec_u; msg_heap := msg_heap rec_u ++ [Exm msg] |}), addUserKeys adv (findKeys msg), cs', ks', qmsgs', Return tt) *)
      (* ============================ *)
      (* clean_users usrs = clean_users (usrs $+ (rec_u_id, {| key_heap := key_heap rec_u; protocol := protocol rec_u; msg_heap := msg_heap rec_u ++ [Exm msg] |})) *)

      admit.

    Admitted.


    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
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

    Lemma user_step_adds_removes_no_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', ks', qmsgs', cmd')
            -> (forall u_id',
                  adv' $? u_id' <> None
                  <-> adv $? u_id' <> None).
    Proof.
      induction 1; inversion 1; inversion 1; intros; subst; eauto;
        unfold iff; constructor; intro; eauto.

      - unfold addUserKeys in H. rewrite <- in_find_iff in H.
        rewrite map_in_iff in H. apply in_find_iff; eauto.

      - unfold addUserKeys; apply in_find_iff.
        rewrite <- in_find_iff in H.
        rewrite map_in_iff; eauto.
    Qed.

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

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop)
              (cmd : user_cmd B) lbl u_id userData (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs,
        U__r.(adversary) $? u_id = Some userData
        -> (forall u_id', u_id' <> u_id -> U__r.(adversary) $? u_id' = None) (* single adversary *)
        -> step_user u_id lbl
                    (build_data_step U__r userData)
                    (usrs, adv, cs, ks, qmsgs, cmd)
        -> R (strip_adversary U__r) U__i
        -> R (strip_adversary (buildUniverseAdv usrs adv cs u_id {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary in *; simpl in *.

      assert (U__r.(adversary) = $0 $+ (u_id,userData)) by (map_equal; eauto).

      assert (findUserKeys U__r.(adversary) = userData.(key_heap)) as ADV_KEYS
        by (rewrite H3; unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial).
      rewrite ADV_KEYS in H2; clear ADV_KEYS.

      assert (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})
              = $0 $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) as ADV_RED;
        map_equal; trivial.
      pose proof H1 as NOADD; unfold build_data_step in NOADD;
        eapply user_step_adds_removes_no_adversaries with (u_id' := KEY) in NOADD; eauto;
          unfold iff in NOADD; invert NOADD.
      case_eq (adv $? KEY); intros; eauto. exfalso.

      assert (adv $? KEY <> None) as LK_KEY_NOT_NONE
        by (unfold not; intros;
            match goal with [ H1 : ?m $? ?k = Some _, H2 : ?m $? ?k = None |- _ ] => rewrite H1 in H2; invert H2 end).
      specialize (H0 _ n); specialize (H4 LK_KEY_NOT_NONE); contradiction.

      assert (findUserKeys (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) = ks);
        rewrite ADV_RED; clear ADV_RED;
        unfold findUserKeys, fold, Raw.fold; simpl; rewrite merge_keys_left_identity; trivial.

      match goal with
      | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs |} _ |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' |} _ ] =>
        assert ( cs = cs' ) as CS by (unfold build_data_step in *; eapply adv_step_implies_no_new_ciphers_after_cleaning; eauto);
          assert ( us = us' ) as US by (unfold build_data_step in *; eapply adv_step_implies_no_user_impact_after_cleaning; eauto)
      end; rewrite <- CS; rewrite <- US; clear US CS;
        assumption.

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
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i
          -> forall U__r' : RealWorld.universe A B,
            rstepSilent U__r U__r'
            -> exists U__i' : IdealWorld.universe A, (istepSilent) ^* U__i U__i' /\ R U__r' U__i')
      -> RealWorld.adv_no_honest_keys (RealWorld.findUserKeys U__ra.(RealWorld.adversary)) (RealWorld.findUserKeys U__ra.(RealWorld.users))
      -> (forall a_id1 a_id2 a, a_id1 <> a_id2 -> U__ra.(RealWorld.adversary) $? a_id1 = Some a -> U__ra.(RealWorld.adversary) $? a_id2 = None)
      -> R (strip_adversary U__ra) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                   /\ R (strip_adversary U__ra') U__i'.
  Proof.
    simpl.
    intros.
    invert H3.

    (* Honest step *)
    - simpl.
      assert (UNIV_STEP :
                rstepSilent
                  (strip_adversary U__ra)
                  (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).

      eapply RealWorld.StepUser; eauto.
      eapply honest_silent_step_advuniv_implies_honest_step_origuniv; intros; eauto.
      eapply RealWorld.find_user_keys_universe_user; eauto. admit.
      eauto.
      unfold strip_adversary; simpl; smash_universe.

      unfold RealWorld.build_data_step in H5.
      eapply honest_silent_step_nochange_adversaries in H5; [| reflexivity..]; rewrite H5; trivial.

      eapply H; eauto.

    - exists U__i.
      split.
      eapply TrcRefl.
      eapply adv_step_stays_in_R; eauto.

  Admitted.

  Lemma msg_pattern_spoofable_strengthen :
    forall pat adv_keys honest_keys,
      RealWorld.adv_no_honest_keys adv_keys honest_keys
      -> negb (RealWorld.msg_pattern_spoofable $0 pat) = true
      -> RealWorld.msg_pattern_spoofable adv_keys pat = RealWorld.msg_pattern_spoofable $0 pat.
  Proof.
    induction pat; intros; auto.
    - unfold RealWorld.msg_pattern_spoofable in *; simpl; fold RealWorld.msg_pattern_spoofable in *.
      rewrite negb_orb in H0; invert H0.
      rewrite andb_true_iff in H2; invert H2.
      specialize (IHpat1 _ _ H H0).
      specialize (IHpat2 _ _ H H1).
      rewrite IHpat1.
      rewrite IHpat2.
      trivial.

    - unfold RealWorld.msg_pattern_spoofable. simpl.
      cases (adv_keys $? k); auto. admit.

    - admit.
  Admitted.
    
  Lemma simulates_with_adversary_loud :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i ->
          forall (a1 : RealWorld.action) (U__r' : RealWorld.universe A B),
            RealWorld.step_universe U__r (Action a1) U__r' ->
            exists (a2 : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
              (istepSilent) ^* U__i U__i' /\
              IdealWorld.lstep_universe U__i' (Action a2) U__i'' /\
              action_matches a1 a2 /\ R U__r' U__i'' /\
              RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__r)) a1 = true)
      -> RealWorld.adv_no_honest_keys (RealWorld.findUserKeys U__ra.(RealWorld.adversary)) (RealWorld.findUserKeys U__ra.(RealWorld.users))
      -> R (strip_adversary U__ra) U__i
      -> forall a1 U__ra',
          RealWorld.step_universe U__ra (Action a1) U__ra'
          -> exists a2 U__i' U__i'',
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R (strip_adversary U__ra') U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__ra)) a1 = true.
  Proof.
    simpl.
    intros.
    invert H2.

    assert (UNIV_STEP :
              RealWorld.step_universe
                (strip_adversary U__ra)
                (Action a1)
                (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).

    eapply RealWorld.StepUser; eauto.
    eapply honest_loud_step_advuniv_implies_honest_step_origuniv; simpl; intros; eauto.
    eapply RealWorld.find_user_keys_universe_user; eauto. admit.
    admit.
    unfold strip_adversary; simpl; smash_universe.
    admit. (* Need evidence that the user didn't send keys -- strengthen notion of adversary safety *)

    specialize (H _ _ H1 _ _ UNIV_STEP).
    repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 3 eexists; intuition idtac; eauto.

    invert H7.
    unfold RealWorld.action_adversary_safe; destruct a1; auto.
    f_equal; eapply msg_pattern_spoofable_strengthen; eauto.

  Admitted.

  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
      U__r <| U__i
      -> U__r.(RealWorld.adversary) = $0
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i.
  Proof.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud R__start]; clear H__l.

    unfold refines. 
    exists (fun ur ui => R (strip_adversary ur) ui); unfold simulates.
    intuition idtac.
      (* eauto using simulates_with_adversary_silent, simulates_with_adversary_loud. *)

    - eapply simulates_with_adversary_silent; eauto.
      admit.
      admit.

    - eapply simulates_with_adversary_loud; eauto.
      admit.

    - rewrite H1; unfold strip_adversary, add_adversary; simpl.
      rewrite H0. rewrite empty_add_idempotent.
      unfold RealWorld.findUserKeys, fold; simpl. rewrite RealWorld.merge_keys_left_identity.

      rewrite clean_ciphers_nokeys_idempotent.
      unfold clean_users; simpl.
      rewrite <- H0; rewrite univ_components. auto.
  Admitted.

End SingleAdversarySimulates.
