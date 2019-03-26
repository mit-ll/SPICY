From Coq Require Import
     List
     Eqdep
     Program.Equality (* for dependent induction *)
.


Require Import MyPrelude Users Common MapLtac. 

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

Definition check_cipher (ch_id : IdealWorld.channel_id)
  :=
    forall A B ch_id k (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs (*do we need these??*) chans perms,
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end.
    
Definition chan_key_ok :=
  forall A B ch_id (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs chan_keys (*do we need these??*) chans perms,
    match chan_keys $? ch_id with
    | None => False
    | Some (Public _)   => msg_eq rm (im,ch_id,chans,perms)
    | Some (Auth _ k _) =>
      (* check_cipher ch_id k im rm cphrs chans perms *)
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end
    | Some (Enc  _ k _) => False
    | Some (AuthEnc _ k1 k2 _ _) => False
    end.


Inductive action_matches :
    RealWorld.action -> IdealWorld.action -> Prop :=
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps p x y z,
      rw = (RealWorld.Input msg1 p x y z)
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
      | Ciphertext _ => true
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
      | Cipher _ k_id _ =>
        match adv_keys $? k_id with
        | Some (SymKey _) => false
        | Some (AsymKey _ true) => false
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

    (* Lemma merge_maps_transpose_key : *)
    (*   forall {B}, *)
    (*     transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data B) (ks : t key) => ks $++ key_heap u). *)
    (* Proof. *)
    (*   unfold transpose_neqkey, Equal, honest_cipher_filter_fn; intros. *)



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


    Lemma clean_ciphers_doesn't_make_unaccepted_msg_accepted :
      forall {t} cs pat ks (msg : message t),
          msg_accepted_by_pattern_compute cs pat msg = false
        -> msg_accepted_by_pattern_compute (clean_ciphers ks cs) pat msg = false.
    Proof.
    (* need to induct on the combination of pat, msg
     * Looks like we need to convert msg_accepted_by_pattern to
     * inductive type to make this go through
     *)
    Admitted.

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
      forall {t} k (msg : message t) c_id cipherMsg,
        encryptMessage k msg c_id = Some cipherMsg
        -> cipherMsg = Cipher c_id (keyId k) msg
        /\ (exists cryp_key, k = SymKey cryp_key \/ k = AsymKey cryp_key false).
    Proof.
      intros.
      unfold encryptMessage in H.
      case_eq k; intros; rewrite H0 in H.
      - case_eq (usage k0); intro; rewrite H1 in H; invert H; eauto.
      - case_eq has_private_access; intro; rewrite H1 in H;
          case_eq (usage k0); intro; rewrite H2 in H || invert H; invert H; eauto.
    Qed.

    Lemma sign_cipher_has_key :
      forall {t} k (msg : message t) c_id cipherMsg,
        signMessage k msg c_id = Some cipherMsg
        -> cipherMsg = Cipher c_id (keyId k) msg
          /\ (exists cryp_key, k = SymKey cryp_key \/ k = AsymKey cryp_key true).
    Proof.
      intros.
      unfold signMessage in H.

      case_eq k; intros; rewrite H0 in H.
      - case_eq (usage k0); intro; rewrite H1 in H; invert H; eauto.
      - case_eq has_private_access; intro; rewrite H1 in H;
          case_eq (usage k0); intro; rewrite H2 in H || invert H; invert H; eauto.
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
      forall {t} cs k ks c_id (msg : message t) cipherMsg,
          encryptMessage k msg c_id = Some cipherMsg
        -> ks $? (keyId k) = None
        -> clean_ciphers ks (cs $+ (c_id, cipherMsg)) = clean_ciphers ks cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      assert( honest_cipher ks cipherMsg = true ).
      apply enc_cipher_has_key in H; invert H.
      unfold honest_cipher; rewrite H0; auto.

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
        -> ks $? (keyId k) = None
        -> clean_ciphers ks (cs $+ (c_id, cipherMsg)) = clean_ciphers ks cs $+ (c_id, cipherMsg).
    Proof.
      intros.
      assert( honest_cipher ks cipherMsg = true ).
      apply sign_cipher_has_key in H; invert H.
      unfold honest_cipher; rewrite H0; auto.

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

    Lemma honest_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s adv_keys,
          adv_keys = findUserKeys adv
          -> (forall uk_id uk, ks $? uk_id = Some uk -> adv_keys $? uk_id = None) (* better notion of disjoint to take care of public/private *)
          -> cs__s = clean_ciphers adv_keys cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers adv_keys cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> step_user (B:=B) u_id lbl (usrs, $0, cs__s, ks, qmsgs, cmd) (usrs', $0, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 4; inversion 2; subst.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      -
        (* eapply StepRecv. *)

        (* H3 : msg_accepted_by_pattern cs' pat msg = true *)
        (* ============================ *)
        (* step_user u_id (Action (Input msg pat u_id ks cs')) (usrs', $0, clean_ciphers (findUserKeys adv') cs', ks, Exm msg :: qmsgs', Recv pat) *)
        (*   (usrs', $0, clean_ciphers (findUserKeys adv') cs', ks $++ findKeys msg, qmsgs', Return msg) *)
        admit.

      - econstructor; eauto.
      - econstructor; eauto; unfold addUserKeys; m_equal; trivial.
      - econstructor; eauto.
      - econstructor; eauto.
        apply clean_ciphers_keeps_honest_cipher; unfold honest_cipher; eauto.
        invert H0; specialize (H5 _ _ H1); rewrite H5; eauto.

      - econstructor; eauto.
      - econstructor; eauto.

        (* Hrm. We have a problem here.  I should never get to this point if the ciphertext is sent from
         * an adversary, since the message would have been dropped at receive.  Not sure how to do this reasoning.
         *)

        (* H : ks' $? keyId k = Some k *)
        (* H0 : cs' $? c_id = Some (Cipher c_id k_id msg) *)
        (* ============================ *)
        (* clean_ciphers (findUserKeys adv') cs' $? c_id = Some (Cipher c_id k_id msg) *)
        admit.

    Admitted.

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

      -

        (* apply enc_cipher_has_key in H2; invert H2. *)

        (* Lemma dishonest_cipher_cleaned : *)
        (*   forall cs adv_keys c_id cipherMsg, *)
        (*     honest_cipher adv_keys cipherMsg = false *)
        (*     -> ~ In c_id cs *)
        (*     -> clean_ciphers adv_keys cs = clean_ciphers adv_keys (cs $+ (c_id, cipherMsg)). *)

        apply dishonest_cipher_cleaned; eauto.
        apply enc_cipher_has_key in H2. 
        invert H2; invert H3.
        unfold honest_cipher; invert H.
        rewrite H0; simpl; trivial.
        rewrite H0; simpl. (* stuck *)
        admit.

      - (* Adversary just decryped a message.  Did it have any keys?
         * Need to reason about what kinds of keys could be in there.
         *)
        admit.

      - apply dishonest_cipher_cleaned; eauto.
        apply sign_cipher_has_key in H2. 
        invert H2; invert H3.
        unfold honest_cipher; invert H;
          rewrite H0; simpl; trivial.

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

      pose proof H1 as CLEAN_CIPHERS.
      unfold build_data_step in CLEAN_CIPHERS.
      eapply adv_step_implies_no_new_ciphers_after_cleaning in CLEAN_CIPHERS; eauto.

      pose proof H1 as CLEAN_USERS.
      unfold build_data_step in CLEAN_USERS.
      eapply adv_step_implies_no_user_impact_after_cleaning in CLEAN_USERS; eauto.

      unfold buildUniverseAdv, strip_adversary, updateUserList in *; simpl in *.

      assert (U__r.(adversary) = $0 $+ (u_id,userData)).
      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n u_id); intro.
      subst. rewrite H. rewrite add_eq_o by trivial; trivial.
      specialize (H0 _ n). rewrite H0. rewrite add_neq_o by auto. eauto.

      assert (findUserKeys U__r.(adversary) = userData.(key_heap)).
      rewrite H3; unfold findUserKeys, fold, Raw.fold; simpl; rewrite empty_add_idempotent; trivial.

      rewrite H4 in H2; rewrite CLEAN_CIPHERS in H2.

      assert (findUserKeys (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) = ks).
      pose proof H1 as NOADD; unfold build_data_step in NOADD.

      assert (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |}) = $0 $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})).
      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n u_id); intros.
      subst; do 2 rewrite add_eq_o by trivial; trivial.
      do 2 rewrite add_neq_o by auto; simpl. specialize (H0 _ n).
      eapply user_step_adds_removes_no_adversaries with (u_id' := y) in NOADD; eauto.
      unfold iff in NOADD; invert NOADD.
      case_eq (adv $? y); intros.
      assert (adv $? y <> None). unfold not; intro. rewrite H7 in H8. invert H8.
      assert (adversary U__r $? u_id <> None); unfold not. intro. rewrite H9 in H; invert H.

      specialize (H5 H8); rewrite H3 in H5. rewrite add_neq_o in H5 by auto.
      assert ((empty cipher) $? y = None) by eauto. contradiction.

      rewrite empty_o; trivial.
      rewrite H5. unfold findUserKeys.
      unfold fold, Raw.fold; simpl. rewrite empty_add_idempotent; trivial.

      rewrite H5. rewrite <- CLEAN_USERS. eauto.

    Qed.

  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user.

  Hint Extern 1 (rstepSilent _ (strip_adversary _)) => 
    unfold RealWorld.buildUniverse, RealWorld.buildUniverseAdv, strip_adversary,
           updateUserList, RealWorld.findUserKeys;
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
    progress unfold RealWorld.build_data_step, RealWorld.buildUniverse, updateUserList; simpl.
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
      -> R (strip_adversary U__ra) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                   /\ R (strip_adversary U__ra') U__i'.
  Proof.
    simpl.
    intros.
    invert H1.

    (* Honest step *)
    - simpl.
      (* specialize (H _ _ H0). *)
      assert (UNIV_STEP :
                rstepSilent
                  (strip_adversary U__ra)
                  (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).
      eapply RealWorld.StepUser; eauto.
      eapply honest_step_advuniv_implies_honest_step_origuniv; intros; eauto. 
      admit. (* Disjoint keys assumption of last lemma *)
      eauto.
      unfold strip_adversary; simpl; smash_universe.

      unfold RealWorld.build_data_step in H3.
      eapply honest_silent_step_nochange_adversaries in H3; trivial. rewrite H3; trivial.

      eapply H; eauto.

    - exists U__i. constructor.
      eapply TrcRefl.
      eapply adv_step_stays_in_R; eauto.
      intros.
      admit. (* single adversary assumption *)

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
    invert H1. 

    assert (UNIV_STEP :
              RealWorld.step_universe
                (strip_adversary U__ra)
                (Action a1)
                (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).

    eapply RealWorld.StepUser; eauto.
    eapply honest_step_advuniv_implies_honest_step_origuniv; simpl; eauto.
    admit. (* Disjoint keys assumption of last lemma *)
    unfold strip_adversary; simpl; smash_universe.
    admit. (* Need evidence that the user didn't send keys *)

    specialize (H _ _ H0 _ _ UNIV_STEP).

    destruct H as [a2].
    destruct H as [U__i'].
    destruct H as [U__i''].
    destruct H. destruct H1. destruct H4. destruct H5.
    exists a2; exists U__i'; exists U__i''; intuition; eauto.

    unfold RealWorld.findUserKeys, strip_adversary, fold in H6; simpl in H6.
    unfold RealWorld.action_adversary_safe; destruct a1; auto.
    unfold RealWorld.msg_pattern_spoofable.
    admit.

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
    propositional;
      eauto using simulates_with_adversary_silent, simulates_with_adversary_loud.
    - rewrite H1; unfold strip_adversary, add_adversary; simpl.
      rewrite H0. rewrite empty_add_idempotent.
      unfold RealWorld.findUserKeys, fold; simpl. rewrite empty_add_idempotent.

      rewrite clean_ciphers_nokeys_idempotent.
      unfold clean_users; simpl.
      rewrite <- H0; rewrite univ_components. auto.
  Qed.

End SingleAdversarySimulates.
