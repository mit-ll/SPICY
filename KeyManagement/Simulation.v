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

Section Hygiene.
  Import RealWorld.

  (*       -> cs' = match msg with *)
  (*               | Plaintext _ => cs' *)
  (*               | KeyMessage _ => cs' *)
  (*               | MsgPair m1 m2 => cs' *)
  (*               | SignedCiphertext _ _ c_id => c_id :: cs *)
  (*               | Signature m _ c_id => c_id :: cs *)
  (*               end *)
  Definition ciphers_of {t} (msg : message t) : list cipher_id :=
    match msg with
    | SignedCiphertext _ _ c_id => [c_id]
    | Signature _ _ c_id        => [c_id]
    | _                         => []
    end.

  (* Fixpoint build_expr_value {A} (cmd : user_cmd A) : A := *)
  (*   match cmd with *)
  (*   | Return a => a *)
  (*   | Bind cmd1 cmd2 => build_expr_value (cmd2 (build_expr_value cmd1)) *)
  (*   | Gen => 1 *)
  (*   | Send _ _ => tt *)
  (*   | Recv _ => forall {t} (msg : message t), msg *)
  (*   | SignEncrypt _ _ _ => forall msg, msg *)
  (*   | Decrypt _ => forall msg, msg *)
  (*   | Sign _ _ => forall msg, msg *)
  (*   | Verify _ _ => true *)
  (*   | GenerateSymKey  _ => (1,true) *)
  (*   | GenerateAsymKey  _ => (1,true) *)
  (*   end. *)

  (* Fixpoint build_def_value {A} (cmd : user_cmd A) : option A := *)
  (*   match cmd with *)
  (*   | Return a => Some a *)
  (*   | Bind cmd1 cmd2 => build_expr_value (cmd2 (build_expr_value cmd1)) *)
  (*   | Gen => Some 1 *)
  (*   | Send _ _ => Some tt *)
  (*   | Recv _ => forall {t} (msg : message t), msg *)
  (*   | SignEncrypt _ _ _ => forall msg, msg *)
  (*   | Decrypt _ => forall msg, msg *)
  (*   | Sign _ _ => forall msg, msg *)
  (*   | Verify _ _ => Some true *)
  (*   | GenerateSymKey  _ => Some (1,true) *)
  (*   | GenerateAsymKey  _ => Some (1,true) *)
  (*   end. *)

  Inductive protocol_hygienic (cs : list cipher_id): forall {A}, user_cmd A -> Prop :=
  | BindRecvHygienic :
      forall {A t} (rec : user_cmd (message t)) (cmd : message t -> user_cmd A) pat,
        rec = Recv pat
        -> (forall cs' msg,
              cs' = ciphers_of msg ++ cs
              -> protocol_hygienic cs' (cmd msg)
          )
        -> protocol_hygienic cs (Bind rec cmd)
  | BindHygienic : forall {A B} (rec : user_cmd B) (cmd : B -> user_cmd A) b,
        protocol_hygienic cs (cmd b)
        -> protocol_hygienic cs (Bind rec cmd)
  | ReturnHygienic : forall {A} (a : A),
      protocol_hygienic cs (Return a)
  | GenHygienic :
      protocol_hygienic cs Gen
  | SendHygienic : forall {t} (uid : user_id) (msg : message t),
      protocol_hygienic cs (Send uid msg)
  | RecvHygienic : forall {t} pat,
      protocol_hygienic cs (@Recv t pat)
  | SignEncryptHygienic : forall {t} (msg : message t) k__s k__e,
      protocol_hygienic cs (SignEncrypt k__s k__e msg)
  | DecryptHygienic : forall {t} msg k__s k__e c_id,
      msg = SignedCiphertext k__s k__e c_id
      -> List.In c_id cs
      -> protocol_hygienic cs (@Decrypt t msg)
  | SignHygienic : forall {t} (msg : message t) k,
      protocol_hygienic cs (Sign k msg)
  | VerifyHygienic : forall {t} msg msg' k kp c_id,
      msg = Signature msg' k c_id
      -> List.In c_id cs
      -> protocol_hygienic cs (@Verify t kp msg).

  (* Inductive protocol_hygienic' (cs__in cs__out : list cipher_id): forall {A}, user_cmd A -> Prop := *)
  (* | BindHygienic' : *)
  (*     forall {B} (cmd : user_cmd B) (proc : B -> user_cmd A), *)
  (*       protocol_hygienic' cs__in cmd cs__out *)
  (*       -> protocol_hygienic' cs__out proc cs__in *)
  (* | ReturnHygienic' : forall {A} (a : A), *)
  (*     protocol_hygienic cs (Return a) cs *)
  (* | GenHygienic' : *)
  (*     protocol_hygienic' cs Gen cs *)
  (* | SendHygienic' : forall {t} (uid : user_id) (msg : message t), *)
  (*     protocol_hygienic' cs (Send uid msg) cs *)
  (* | RecvHygienic' : forall {t} pat, *)
  (*     protocol_hygienic cs (@Recv t pat) *)

  (* | SignEncryptHygienic : forall {t} (msg : message t) k__s k__e, *)
  (*     protocol_hygienic cs (SignEncrypt k__s k__e msg) *)
  (* | DecryptHygienic : forall {t} msg k__s k__e c_id, *)
  (*     msg = SignedCiphertext k__s k__e c_id *)
  (*     -> List.In c_id cs *)
  (*     -> protocol_hygienic cs (@Decrypt t msg) *)
  (* | SignHygienic : forall {t} (msg : message t) k, *)
  (*     protocol_hygienic cs (Sign k msg) *)
  (* | VerifyHygienic : forall {t} msg msg' k kp c_id, *)
  (*     msg = Signature msg' k c_id *)
  (*     -> List.In c_id cs *)
  (*     -> protocol_hygienic cs (@Verify t kp msg). *)



  Definition user_protocols_hygienic {A B} (U : universe A B) :=
    Forall_natmap (fun u => protocol_hygienic [] u.(protocol)) U.(users).

  Hint Constructors protocol_hygienic.
  Hint Extern 1 nat => exact 1.
  Hint Extern 1 key_identifier => exact 1.

  Definition testHygProto1 := Gen.

  Lemma testHygProto1_ok :
    protocol_hygienic [] testHygProto1.
  Proof.
    intros; eauto.
    Show Proof.
  Qed.

  Definition testHygProto2 := (_ <- Gen ; _ <- Gen ; n <- Gen ; Return n).

  Lemma testHygProto2_ok :
    protocol_hygienic [] testHygProto2.
    econstructor; eauto.
    Unshelve. auto.
    Show Proof.
  Qed.

  Definition testHygProto3 := (n <- Gen ; m <- Recv Accept ; match m with
                                                           | SignedCiphertext _ _ _ => @Decrypt Nat m
                                                           | _                      => Return (Plaintext 1)
                                                           end).

  Lemma testHygProto3_ok :
    protocol_hygienic [] testHygProto3.
    econstructor; auto.
    econstructor; auto.
    intros; eauto.
    dependent destruction msg; eauto.
    econstructor; simpl; auto. simpl in *; subst; eauto.
    Show Proof.
  Qed.

  Definition testHygProto4 := (n <- Gen ; m <- Return (SignedCiphertext 1 2 3) ; @Decrypt Nat m ).

  Lemma testHygProto4_ok :
    protocol_hygienic [] testHygProto4.
    econstructor; auto.
    eapply BindHygienic; auto.
    econstructor.
    trivial.
  Abort.

  Definition testHygProto5 := (n <- Gen ; m1 <- Return (SignedCiphertext 1 2 3) ; m2 <- @Recv CipherId Accept ; @Decrypt Nat m1 ).

  Lemma testHygProto5_ok :
    protocol_hygienic [] testHygProto5.
    econstructor; auto.
    eapply BindHygienic.
    econstructor.
    trivial.
    intros.
    dependent destruction msg; simpl in *.
    econstructor. trivial.
  Abort.

End Hygiene.

Definition simulates_silent_step {A B} (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) :=
  forall U__r U__i,
    R U__r U__i
    -> RealWorld.universe_ok U__r
    -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
            istepSilent ^* U__i U__i'
          /\ RealWorld.universe_ok U__r'
          /\ R U__r' U__i'.

Definition simulates_labeled_step {A B} (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) :=
  forall U__r U__i,
    R U__r U__i
    -> RealWorld.universe_ok U__r
    -> forall a1 U__r',
        RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
        -> exists a2 U__i' U__i'',
          istepSilent^* U__i U__i'
          /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
          /\ action_matches a1 a2
          /\ R U__r' U__i''
          /\ RealWorld.universe_ok U__r'.

Definition simulates_labeled_step_safe {A B} (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) :=
  forall U__r U__i,
    R U__r U__i
    -> forall a (U U__r' : RealWorld.universe A B),
      RealWorld.step_universe U (Action a) U__r' (* excludes adversary steps *)
      -> RealWorld.findUserKeys U.(RealWorld.users) = RealWorld.findUserKeys U__r.(RealWorld.users)
      ->  RealWorld.action_adversary_safe
           (RealWorld.findUserKeys U__r.(RealWorld.users))
           a.


Definition simulates {A B : Type}
           (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop)
           (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) :=

  (* conditions for simulation steps *)
  simulates_silent_step R
/\ simulates_labeled_step R
/\ simulates_labeled_step_safe R

  (* conditions for start *)
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
                         ; protocol := advcode
                         ; c_heap   := [] |}
       ; all_ciphers := U__r.(all_ciphers)
       ; all_keys    := U__r.(all_keys)
      |}.

    Definition msg_filter (sigM : { t & message t } ) : bool :=
      match sigM with
      | existT _ _ msg => msg_honestly_signed honestk msg
      end.

    Definition clean_messages (msgs : queued_messages) :=
      List.filter msg_filter msgs.

    Definition clean_users {A} (usrs : honest_users A) :=
      (* usrs. *)
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages u_d.(msg_heap)
                    ; c_heap   := u_d.(c_heap) |}) usrs.

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
                            ; protocol := Return b
                            ; c_heap   := U__r.(adversary).(c_heap) |}
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
        -> k = cipher_signing_key c
        -> honest_key honestk k
        -> clean_ciphers honestk cs $? c_id = Some c.
    Proof.
      intros.
      eapply clean_ciphers_keeps_honest_cipher; auto.
      unfold honest_cipher_filter_fn, cipher_honestly_signed.
      cases c; subst; rewrite <- honest_key_honest_keyb; eauto.
    Qed.

    Hint Constructors msg_accepted_by_pattern msg_contains_only_honest_public_keys.

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

    Hint Resolve dishonest_cipher_cleaned.

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
      unfold clean_ciphers, filter, ciphers_honestly_signed; intros.
      apply P.fold_rec_bis; intros; Equal_eq; subst; eauto.
      unfold honest_cipher_filter_fn.
      rewrite find_mapsto_iff in H0.
      assert (cipher_honestly_signed uks e = true).
        eapply Forall_natmap_in_prop with (P := fun c => cipher_honestly_signed uks c = true); eauto.
      rewrite H2; trivial.
    Qed.

    Lemma clean_messages_keeps_honestly_signed :
      forall {t} (msg : message t) msgs honestk,
        msg_honestly_signed honestk msg = true
        -> clean_messages honestk (msgs ++ [existT _ _ msg])
          = clean_messages honestk msgs ++ [existT _ _ msg].
    Proof.
      intros; unfold clean_messages.
      induction msgs; simpl; eauto.
      - rewrite H; trivial.
      - cases (msg_filter honestk a); subst; eauto.
        rewrite IHmsgs; trivial.
    Qed.

    Lemma clean_messages_drops_not_honestly_signed :
      forall {t} (msg : message t) msgs honestk,
        msg_honestly_signed honestk msg = false
        -> clean_messages honestk (msgs ++ [existT _ _ msg])
          = clean_messages honestk msgs.
    Proof.
      intros; unfold clean_messages.
      induction msgs; simpl; eauto.
      - rewrite H; trivial.
      - cases (msg_filter honestk a); subst; eauto.
        rewrite IHmsgs; trivial.
    Qed.

    Hint Extern 1 (honest_keyb _ _ = true) => rewrite <- honest_key_honest_keyb.
    Hint Extern 1 (_ && _ = true) => rewrite andb_true_iff.

    Lemma accepted_safe_msg_pattern_honestly_signed :
      forall {t} (msg : message t) honestk pat,
        msg_pattern_safe honestk pat
        -> msg_accepted_by_pattern pat msg
        -> msg_honestly_signed honestk msg = true.
    Proof.
      induction 2;
        match goal with
        | [ H : msg_pattern_safe _ _ |- _] => invert H
        end; simpl; eauto.
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
      assert (msg_honestly_signed honestk msg = true) by eauto.
      unfold clean_messages; simpl;
        match goal with
        | [ H : msg_honestly_signed _ _ = _ |- _ ] => rewrite H
        end; trivial.
    Qed.

    Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
         findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

    Lemma clean_users_cleans_user :
      forall {A} (usrs : honest_users A) honestk u_id u_d u_d',
        usrs $? u_id = Some u_d
        -> u_d' = {| key_heap := u_d.(key_heap)
                  ; protocol := u_d.(protocol)
                  ; msg_heap :=  clean_messages honestk u_d.(msg_heap)
                  ; c_heap   := u_d.(c_heap) |}
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
                                       ; msg_heap := msgs
                                       ; c_heap   := u_d.(c_heap) |}
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
                                                ; msg_heap :=  clean_messages honestk u.(msg_heap)
                                                ; c_heap   := u.(c_heap) |}).
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
             ; msg_heap := clean_messages (findUserKeys U.(users)) user_data.(msg_heap)
             ; c_heap   := user_data.(c_heap) |}
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

    Lemma user_cipher_queue_safe_after_cleaning :
      forall honestk cs mycs,
        user_cipher_queue_safe honestk cs mycs
        -> user_cipher_queue_safe honestk (clean_ciphers honestk cs) mycs.
    Proof.
      induction 1; econstructor; eauto.
    Qed.

    Lemma ok_universe_strip_adversary_still_ok :
      forall {A B} (U__ra U__r: universe A B) (b : B),
          U__r = strip_adversary U__ra b
        -> universe_ok U__ra
        -> universe_ok U__r.
    Proof.
      intros.
      subst; unfold universe_ok in *; destruct U__ra; simpl in *; intuition idtac;
        rewrite clean_users_no_change_findUserKeys; subst; simpl in *.
      - unfold message_queues_ok, message_queue_ok, user_queue in *; intros.
        cases (clean_users (findUserKeys users) users $? u_id); subst; clean_map_lookups.
        apply clean_users_cleans_user_inv in Heq; invert Heq; split_ands.
        specialize (H0 u_id x). rewrite H1 in H0.
        rewrite H3; eauto.
      - unfold user_cipher_queues_ok in *; intros.
        rewrite user_cipher_queue_cleaned_users_nochange in H1;
          assert ( user_cipher_queue_safe (findUserKeys users) all_ciphers mycs ); eauto.
        eapply user_cipher_queue_safe_after_cleaning; auto.
    Qed.

    Hint Resolve
         clean_ciphers_added_honest_cipher_not_cleaned
         findUserKeys_readd_user_same_key_heap_idempotent
         message_queue_safe_after_msg_keys
         ciphers_honestly_signed_after_msg_keys
         findUserKeys_has_private_key_of_user.

    Lemma message_queues_ok_readd_user_same_msgs :
      forall {A} (usrs : honest_users A) honestk u_id ks ks' cmd cmd' qmsgs mycs mycs',
        message_queues_ok usrs honestk
        -> usrs $? u_id = Some  {| key_heap := ks; protocol := cmd; msg_heap := qmsgs ; c_heap := mycs |}
        -> message_queues_ok (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs ; c_heap := mycs' |})) honestk.
    Proof.
      intros.
      unfold message_queues_ok in *; intros.
      unfold user_queue in *.
      specialize (H u_id0).
      cases (u_id0 ==n u_id); subst; eauto.
      - rewrite add_eq_o in H1; invert H1; auto.
        rewrite H0 in H; eauto.
      - rewrite add_neq_o in H1; invert H1; auto.
    Qed.

    Hint Resolve message_queues_ok_readd_user_same_msgs.

    Ltac clean_context :=
      try discriminate;
      repeat
        match goal with
        | [ H : ?X = ?X |- _ ] => clear H
        | [ H : Some _ = Some _ |- _ ] => invert H
        end.

    Lemma incl_end :
      forall {A} (l1 l2 l3 : list A) a,
        incl l1 l3
        -> incl l1 (l2 ++ a :: l3).
    Proof.
      intros.
      assert (incl l3 (l2 ++ a :: l3)). unfold incl in *; intros; eauto.
      eapply in_or_app. right; eauto.
      eapply incl_tran; eauto.
    Qed.

    Hint Constructors user_cipher_queue_safe.
    Hint Resolve incl_end.

    Lemma user_cipher_queue_safe_addnl_global_cipher :
      forall honestk cs mycs c_id c,
        user_cipher_queue_safe honestk cs mycs
        -> ~ In (elt:=cipher) c_id cs
        -> user_cipher_queue_safe honestk (cs $+ (c_id,c)) mycs.
    Proof.
      induction 1; intros; eauto.
      cases (c_id ==n cid); subst; clean_map_lookups; eauto.
    Qed.

    Lemma user_cipher_queue_safe_addnl_cipher :
      forall {t} (msg : message t) cs mycs c_id c k__s k__e honestk,
        user_cipher_queue_safe honestk cs mycs
        -> c = SigEncCipher k__s k__e msg
        -> cipher_honestly_signed honestk c = true
        -> keys_mine honestk (findKeys msg)
        -> incl (findCiphers msg) mycs
        -> ~ In c_id cs
        -> user_cipher_queue_safe honestk (cs $+ (c_id,c)) (c_id :: mycs).
    Proof.
      intros.
      econstructor; eauto using user_cipher_queue_safe_addnl_global_cipher.

      intros; subst;
        match goal with [H : SigEncCipher _ _ _ = SigEncCipher _ _ _ |- _] => invert H end;
        eauto.
    Qed.

    Lemma user_cipher_queues_ok_addnl_global_cipher :
      forall {A} (usrs : honest_users A) honestk cs c_id c,
        user_cipher_queues_ok usrs honestk cs
        -> ~ In (elt:=cipher) c_id cs
        -> user_cipher_queues_ok usrs honestk (cs $+ (c_id,c)).
    Proof.
      unfold user_cipher_queues_ok; intros.
      eapply user_cipher_queue_safe_addnl_global_cipher; eauto.
    Qed.

    Hint Resolve
         user_cipher_queue_safe_addnl_global_cipher
         user_cipher_queues_ok_addnl_global_cipher
         user_cipher_queue_safe_addnl_cipher.

    Lemma merge_keys_mine :
      forall ks1 ks2,
        keys_mine ks1 ks2
        -> ks1 $k++ ks2 = ks1.
    Proof.
      unfold keys_mine; intros.
      apply map_eq_Equal; unfold Equal; intros.
      specialize (H y).
      cases (ks1 $? y); cases (ks2 $? y); subst.
      - specialize (H b0).
        erewrite merge_perms_chooses_greatest; unfold greatest_permission;
          intuition idtac; subst; eauto.
        + invert H; rewrite orb_diag; trivial.
        + rewrite orb_false_r; trivial.
      - erewrite merge_perms_adds_ks1; eauto.
      - specialize (H b); intuition idtac; discriminate.
      - rewrite merge_perms_adds_no_new_perms; auto.
    Qed.

    Lemma cipher_message_keys_already_in_honest :
      forall {A t} (msg : message t) (usrs : honest_users A) honestk cs c_id u_id k__s k__e mycs,
        honestk = findUserKeys usrs
        -> cs $? c_id = Some (SigEncCipher k__s k__e msg)
        -> List.In c_id mycs
        -> user_cipher_queue usrs u_id = Some mycs
        -> user_cipher_queues_ok usrs honestk cs
        -> honestk $k++ findKeys msg = honestk.
    Proof.
      intros.
      eapply cipher_id_in_user_cipher_queue_prop in H1; eauto.
      destruct H1 as [c H1]; split_ands.
      destruct H5 as [l1 H5]; destruct H5 as [l2 H5]; split_ands; clean_map_lookups.
      assert (keys_mine (findUserKeys usrs) (findKeys msg) /\ incl (findCiphers msg) l2) by eauto;
        split_ands.

      unfold keys_mine in H.

      apply map_eq_Equal; unfold Equal; intros.
      cases (findUserKeys usrs $? y); cases (findKeys msg $? y); subst.
      - specialize (H _ _ Heq0).
        erewrite merge_perms_chooses_greatest; unfold greatest_permission; simpl; eauto.
        split_ors; split_ands; subst; clean_map_lookups; auto.
        rewrite orb_diag; trivial.
      - erewrite merge_perms_adds_ks1; eauto.
      - specialize (H _ _ Heq0); split_ors; split_ands; clean_map_lookups.
      - rewrite merge_perms_adds_no_new_perms; trivial.
    Qed.

    Lemma user_cipher_queue_safe_readd_ciphers :
      forall honestk cs mycs newcs,
        user_cipher_queue_safe honestk cs mycs
        -> incl newcs mycs
        -> user_cipher_queue_safe honestk cs (newcs ++ mycs).
    Proof.
      induction newcs; intros; eauto.
      unfold incl in H0.
      assert (List.In a mycs) by eauto.
      eapply cipher_id_in_user_cipher_queue_prop in H1; eauto.
      invert H1; split_ands.
      simpl.
      econstructor; eauto.
      eapply IHnewcs; eauto.
      assert (incl newcs (a :: newcs)). unfold incl; eauto.
      eapply incl_tran; eauto.
      destruct H3 as [l1 H3]; destruct H3 as [l2 H3]; split_ands; eauto.
      intros; subst; eauto.
      assert (keys_mine honestk (findKeys msg) /\ incl (findCiphers msg) l2) by eauto; split_ands.
      intuition idtac.
      rewrite app_assoc; eauto.
    Qed.

    Lemma user_cipher_queue_safe_add_pub_keys :
      forall honestk pubk cs mycs,
        user_cipher_queue_safe honestk cs mycs
        -> (forall k kp, pubk $? k = Some kp -> kp = false)
        -> user_cipher_queue_safe (honestk $k++ pubk) cs mycs.
    Proof.
      induction 1; eauto; intros.
      econstructor; eauto.
      - apply cipher_honestly_signed_after_msg_keys; auto.
      - intros.
        assert (keys_mine honestk (findKeys msg) /\ incl (findCiphers msg) cids) by eauto;
          intuition idtac.
        unfold keys_mine in *; intros; eauto.
        specialize (H6 _ _ H8).
        cases (pubk $? k_id).
        + specialize (H3 _ _ Heq); subst.
          split_ors; split_ands; erewrite merge_perms_chooses_greatest;
            unfold greatest_permission; simpl; eauto.
          * rewrite orb_false_r; auto.
          * rewrite orb_true_l; auto.
        + split_ors; split_ands; subst;
            erewrite merge_perms_adds_ks1; auto; auto.
    Qed.

    Hint Resolve user_cipher_queue_safe_add_pub_keys.

    Lemma user_ciphers_honestly_signed_after_silent_honest_step :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> user_cipher_queue_safe (findUserKeys usrs) cs mycs
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> user_cipher_queue_safe (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'
                                                                         ; protocol := cmdc'
                                                                         ; msg_heap := qmsgs'
                                                                         ; c_heap := mycs'|} )))
                                         cs' mycs'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst; clean_context;
        try
          erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      - eapply user_cipher_queue_safe_addnl_cipher; simpl; eauto.
        unfold keys_mine in *; intros; eauto.
        specialize (H4 _ _ H6);
          split_ors; cases kp; subst; split_ands; try discriminate; eauto.

        cases (findUserKeys usrs' $? k_id); subst; split_ands; try discriminate.
        cases b; subst; eauto.
        assert ( findUserKeys usrs' $? k_id <> None ) by eauto using findUserKeys_has_key_of_user; contradiction.

      - erewrite findUserKeys_readd_user_addnl_keys; eauto.
        eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands.
        destruct H6 as [l1 H6]; destruct H6 as [l2 H6]; split_ands.
        clean_map_lookups.
        assert ( keys_mine (findUserKeys usrs') (findKeys msg) /\ incl (findCiphers msg) l2 ) by eauto;
          split_ands.

        rewrite merge_keys_mine; eauto.
        eapply user_cipher_queue_safe_readd_ciphers; eauto.

      - econstructor; eauto; simpl; eauto.
        intros.
        invert H2.
    Qed.

    Lemma user_cipher_queues_ok_readd_user :
      forall {A} (usrs : honest_users A) u_id ks ks' cmd cmd' qmsgs qmsgs' cs mycs,
        usrs $? u_id = Some {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}
        -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
        -> user_cipher_queues_ok
            (usrs $+ (u_id, {| key_heap := ks'; protocol := cmd'; msg_heap := qmsgs'; c_heap := mycs |}))
            (findUserKeys usrs) cs.
    Proof.
      unfold user_cipher_queues_ok; intros.
      unfold user_cipher_queue in *.
      cases (u_id ==n u_id0); subst; specialize (H0 u_id0 mycs0).
      - rewrite add_eq_o in H1; invert H1; eauto.
        rewrite H in H0; eauto.
      - rewrite add_neq_o in H1; invert H1; eauto.
    Qed.

    Hint Resolve user_cipher_queues_ok_readd_user.

    Lemma user_cipher_queues_ok_after_silent_honest_step :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> user_cipher_queues_ok
                    (usrs' $+ (u_id, {| key_heap := ks'
                                      ; protocol := cmdc'
                                      ; msg_heap := qmsgs'
                                      ; c_heap := mycs'|} ))
                    (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'
                                                    ; protocol := cmdc'
                                                    ; msg_heap := qmsgs'
                                                    ; c_heap := mycs'|} )))
                    cs'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst; clean_context;
        try
          erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto;
          unfold user_cipher_queues_ok; intros;
              unfold user_cipher_queue in *.

      - cases (u_id ==n u_id1); subst; [rewrite add_eq_o in H6 | rewrite add_neq_o in H6];
          eauto; invert H6.

        eapply user_cipher_queue_safe_addnl_cipher; simpl; eauto.
        + assert (user_cipher_queue usrs' u_id1 = Some mycs) by (unfold user_cipher_queue; context_map_rewrites; auto).
          specialize (H10 _ _ H6); eauto.
        + unfold keys_mine in *; intros; eauto.
          specialize (H4 _ _ H6);
            split_ors; cases kp; subst; split_ands; try discriminate; eauto.

          cases (findUserKeys usrs' $? k_id); subst; split_ands; try discriminate.
          cases b; subst; eauto.
          assert ( findUserKeys usrs' $? k_id <> None ) by eauto using findUserKeys_has_key_of_user; contradiction.

      - cases (u_id ==n u_id1); subst; [rewrite add_eq_o in H4 | rewrite add_neq_o in H4];
          eauto; invert H4;
            erewrite findUserKeys_readd_user_addnl_keys; eauto.

        + assert ( user_cipher_queue usrs' u_id1 = Some mycs ) by (unfold user_cipher_queue; context_map_rewrites; auto).
          specialize (H10 _ _ H4).
          eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands.
          destruct H7 as [l1 H7]; destruct H7 as [l2 H7]; split_ands.
          clean_map_lookups.
          assert ( keys_mine (findUserKeys usrs') (findKeys msg) /\ incl (findCiphers msg) l2 ) by eauto;
            split_ands.

          rewrite merge_keys_mine; eauto.
          eapply user_cipher_queue_safe_readd_ciphers; eauto.

        + cases (usrs' $? u_id1); subst; try discriminate; invert H6.
          assert ( user_cipher_queue usrs' u_id = Some mycs ) by (unfold user_cipher_queue; context_map_rewrites; auto).
          assert ( user_cipher_queue usrs' u_id1 = Some u.(c_heap) ) by (unfold user_cipher_queue; context_map_rewrites; auto).
          assert (user_cipher_queue_safe (findUserKeys usrs') cs' mycs) by eauto.
          assert (user_cipher_queue_safe (findUserKeys usrs') cs' u.(c_heap)) by eauto.
          eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands; eauto.
          destruct H12 as [l1 H12]; destruct H12 as [l2 H12]; split_ands.
          clean_map_lookups.
          assert ( keys_mine (findUserKeys usrs') (findKeys msg) /\ incl (findCiphers msg) l2 ) by eauto;
            split_ands.

          rewrite merge_keys_mine; eauto.

      - cases (u_id ==n u_id1); subst; [rewrite add_eq_o in H2 | rewrite add_neq_o in H2 ];
          eauto; invert H2.

        assert ( user_cipher_queue usrs' u_id1 = Some mycs ) by (unfold user_cipher_queue; context_map_rewrites; auto).
        assert (user_cipher_queue_safe (findUserKeys usrs') cs mycs) by eauto.
        econstructor; eauto; simpl; eauto.
        intros.
        invert H4.
    Qed.

    Lemma honest_silent_step_advuniv_implies_uq_ok :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> user_cipher_queues_ok usrs honestk cs
          -> user_queue usrs u_id = Some qmsgs
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> honestk' = findUserKeys usrs'
              -> user_cipher_queues_ok usrs' honestk' cs'.
    Proof.
      induction 1; inversion 1; inversion 5; try discriminate; eauto;
        intros; subst; eauto;
          unfold user_cipher_queues_ok; intros; eauto.
    Qed.

    Lemma message_queues_ok_after_silent_honest_step :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> message_queues_ok usrs (findUserKeys usrs)
          -> user_cipher_queue_safe (findUserKeys usrs) cs mycs
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> message_queues_ok (usrs' $+ (u_id, {| key_heap := ks'
                                                      ; protocol := cmdc'
                                                      ; msg_heap := qmsgs'
                                                      ; c_heap := mycs' |}))
                                    (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'
                                                                    ; protocol := cmdc'
                                                                    ; msg_heap := qmsgs'
                                                                    ; c_heap := mycs'|} ))).
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; clean_context;
        try
          erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      - assert (user_queue usrs' u_id = Some (existT _ _ msg :: qmsgs'))
          as UQ by (unfold user_queue; context_map_rewrites; eauto).
        pose proof (H3 _ _ UQ).
        invert H.
        unfold message_queues_ok; intros.
        unfold user_queue in H; cases (u_id ==n u_id1); subst.
        + rewrite add_eq_o in H; eauto; invert H; eauto.
        + rewrite add_neq_o in H; eauto.

      - eapply message_queues_ok_readd_user_same_msgs; eauto.
        erewrite findUserKeys_readd_user_addnl_keys; eauto.

        unfold message_queues_ok in *; intros.
        pose proof (H10 _ _ H4).
        eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands.
        destruct H8 as [l1 H8]; destruct H8 as [l2 H8]; split_ands; subst; clean_map_lookups.
        assert ( keys_mine (findUserKeys usrs') (findKeys msg) /\ incl (findCiphers msg) l2 ) by eauto;
          split_ands.
        rewrite merge_keys_mine; eauto.
    Qed.

    Hint Resolve
         user_cipher_queues_ok_after_silent_honest_step
         message_queues_ok_after_silent_honest_step.

    Lemma honest_silent_step_advuniv_implies_univ_ok' :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> message_queues_ok usrs honestk
          -> user_queue usrs u_id = Some qmsgs
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> honestk' = findUserKeys usrs'
              -> keys_good gks'
              /\ message_queues_ok usrs' honestk'
              /\ message_queue_ok qmsgs' honestk'.
    Proof.
      induction 1; inversion 1; inversion 5; try discriminate; eauto; intros; subst; eauto.

      intuition idtac.
      specialize (H13 _ _ H14); invert H13; eauto.
    Qed.

    Inductive encrypted_cipher_ok (honestk : key_perms) : cipher -> Prop :=
    | SigCipherOk : forall {t} (msg : message t) k,
        encrypted_cipher_ok honestk (SigCipher k msg)
    | SigEncCipherEncKeyNotHonestOk : forall {t} (msg : message t) k__e k__s,
        honestk $? k__e <> Some true
        -> (forall k, findKeys msg $? k = Some true
                -> honestk $? k <> Some true)
        -> encrypted_cipher_ok honestk (SigEncCipher k__s k__e msg)
    | SigEncCipherEncKeyHonestOk : forall {t} (msg : message t) k__e k__s,
        honestk $? k__e = Some true
        -> encrypted_cipher_ok honestk (SigEncCipher k__s k__e msg)
    .

    Hint Constructors encrypted_cipher_ok.

    Definition encrypted_ciphers_ok (honestk : key_perms) :=
      Forall_natmap (encrypted_cipher_ok honestk).

    (* Definition encrypted_ciphers_ok (cs : ciphers) (honestk : key_perms) := *)
    (*   forall {t} (msg : message t) c_id k__s k__e, *)
    (*     cs $? c_id = Some (SigEncCipher k__s k__e msg) *)
    (*     (* -> honestk $? k__s = Some true *) *)
    (*     -> (honestk $? k__e = None \/ honestk $? k__e = Some false) *)
    (*     -> forall k, *)
    (*         findKeys msg $? k = Some true *)
    (*         -> honestk $? k = None *)
    (*         \/ honestk $? k = Some false. *)


    Definition message_no_adv_private {t} (msg : message t) (honestk : key_perms) :=
      forall k, findKeys msg $? k = Some true
           (* -> advk $? k = Some true *)
           -> (honestk $? k = None \/ honestk $? k = Some false).

    (*   (* forall k, honestk $? k = None -> findKeys msg $? k = None \/ findKeys msg $? k = Some false. *) *)

    (* Definition message_no_adv_private {t} (msg : message t) (advk : key_perms) := *)
    (*   forall k, findKeys msg $? k = Some true -> advk $? k = None \/ advk $? k = Some false. *)

    Hint Unfold message_no_adv_private.

    Definition message_queue_ok' (msgs : queued_messages) (honestk : key_perms) :=
      Forall (fun sigm => match sigm with
                       | (existT _ _ m) =>
                         msg_honestly_signed honestk m = true -> message_no_adv_private m honestk
                       end) msgs.

    Definition message_queues_ok' {A} (usrs : honest_users A) (honestk : key_perms) :=
      forall u_id msgs,
        user_queue usrs u_id = Some msgs
        -> message_queue_ok' msgs honestk.

    Lemma adv_step_advuniv_implies_univ_ok' :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
        gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> message_queues_ok' usrs honestk
          -> user_cipher_queues_ok usrs honestk cs
          -> adv_no_honest_keys honestk ks
          -> ks = adv.(key_heap)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> honestk' = findUserKeys usrs'
              -> keys_good gks'
              /\ message_queues_ok' usrs' honestk'
              /\ user_cipher_queues_ok usrs' honestk' cs'.
    Proof.
      induction 1; inversion 1; inversion 7; try discriminate; eauto; intros; subst; eauto.

      destruct rec_u; simpl in *;
        intuition idtac;
        erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      unfold message_queues_ok'; intros.
      cases (rec_u_id ==n u_id0); subst; eauto; unfold user_queue in H.
      - rewrite add_eq_o in H; simpl in *; invert H; auto.
        assert (user_queue usrs u_id0 = Some msg_heap) as UQ by (unfold user_queue; context_map_rewrites; trivial).
        specialize (H16 _ _ UQ); auto.
        unfold message_queue_ok'.
        apply Forall_app; constructor; auto; intros.
        unfold message_no_adv_private; intros.

        cases (findUserKeys usrs $? k); subst; auto.
        cases b; auto.

        exfalso.
        unfold keys_mine, adv_no_honest_keys in *.
        specialize (H0 _ _ H1); split_ors; split_ands; try discriminate.
        specialize (H18 k); split_ors; split_ands; clean_map_lookups. contradiction.

      - rewrite add_neq_o in H; simpl in *; auto.
        cases (usrs $? u_id0); subst; try discriminate; invert H.
        destruct u. assert (user_queue usrs u_id0 = Some msg_heap0) as UQ by (unfold user_queue; context_map_rewrites; auto).
        specialize (H16 _ _ UQ); auto.
    Qed.


    Lemma findUserKeys_multi_add_same_keys_idempotent :
      forall {A} (usrs : honest_users A) u_id1 u_id2 u_d1 u_d2 u_d1' u_d2',
        usrs $? u_id1 = Some u_d1
        -> usrs $? u_id2 = Some u_d2
        -> key_heap u_d1 = key_heap u_d1'
        -> key_heap u_d2 = key_heap u_d2'
        -> findUserKeys (usrs $+ (u_id1,u_d1') $+ (u_id2,u_d2')) = findUserKeys usrs.
    Proof.
      intros.

      cases (u_id1 ==n u_id2); subst; clean_map_lookups.
      - rewrite map_add_eq; eauto.
        destruct u_d2'; simpl in *; erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.

      - remember (usrs $+ (u_id1,u_d1')) as usrs'.
        assert ( usrs' $? u_id2 = Some u_d2 )
          by (subst; clean_map_lookups; auto).

        destruct u_d1'; destruct u_d2'; simpl in *.

        assert (findUserKeys usrs' = findUserKeys usrs)
          by (subst; eauto; eapply findUserKeys_readd_user_same_keys_idempotent'; eauto).

        erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.
    Qed.


    Lemma honest_labeled_step_encrypted_ciphers_ok :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> encrypted_ciphers_ok honestk cs
          -> message_queues_ok usrs honestk
          (* -> user_cipher_queues_ok usrs honestk cs *)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Action a
              -> action_adversary_safe honestk a
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> encrypted_ciphers_ok honestk' cs'.
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; try discriminate; eauto.

      - erewrite findUserKeys_readd_user_addnl_keys; eauto.
        invert H19; simpl in *; split_ands.
        assert (user_queue usrs' u_id = Some (existT _ _ msg :: qmsgs')) by (unfold user_queue; context_map_rewrites; auto).
        specialize (H17 _ _ H1). invert H17.
        assert (msg_contains_only_honest_public_keys (findUserKeys usrs') msg) by eauto.
        rewrite safe_messages_perm_merge_honestk_idempotent; eauto.

      - erewrite findUserKeys_multi_add_same_keys_idempotent; eauto.

    Qed.

    Lemma honest_silent_step_encrypted_ciphers_ok :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          (* -> adv_no_honest_keys honestk adv.(key_heap) *)
          (* -> user_cipher_queues_ok usrs honestk cs *)
          -> encrypted_ciphers_ok honestk cs
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> encrypted_ciphers_ok honestk' cs'.
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst; try discriminate;
        try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      - econstructor; eauto.
        admit. (* no way to tell where message is going *)
      - erewrite findUserKeys_readd_user_addnl_keys by eauto; eauto.
        eapply Forall_natmap_in_prop in H19; eauto.
        assert (findUserKeys usrs' $? k__encid = Some true) by eauto.
        invert H19; try contradiction.

        admit.
      - econstructor; eauto.

    Admitted.

    Lemma adv_step_encrypted_ciphers_ok :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys honestk ks
          -> encrypted_ciphers_ok honestk cs
          -> ks = adv.(key_heap)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> honestk' = findUserKeys usrs'
              -> encrypted_ciphers_ok honestk' cs'.
    Proof.
      induction 1; inversion 1; inversion 5; intros; subst; try discriminate; eauto.

      - econstructor; eauto.
        (* specialize (H19 k__encid); split_ors; split_ands; subst; eauto. *)

        + cases kp__enc; subst; eauto.
          * eapply SigEncCipherEncKeyNotHonestOk.
            specialize (H19 k__encid).
            unfold not; intros; split_ors; split_ands; clean_map_lookups; eauto.
            intros.
            specialize (H4 _ _ H6); split_ors; split_ands; unfold not; intros; eauto;
              specialize (H19 k); split_ors; split_ands; clean_map_lookups; eauto.
          * cases (findUserKeys usrs' $? k__encid).
            cases b; eauto.

            ** eapply SigEncCipherEncKeyNotHonestOk; eauto.
               unfold not; intros; clean_map_lookups.
               intros; unfold not; intros.
               specialize (H19 k); split_ors; split_ands; clean_map_lookups; eauto.
               specialize (H4 _ _ H6); split_ors; split_ands; eauto.

            ** eapply SigEncCipherEncKeyNotHonestOk; eauto.
               unfold not; intros; clean_map_lookups.
               unfold not; intros.
               specialize (H19 k); split_ors; split_ands; clean_map_lookups; eauto.
               specialize (H4 _ _ H6); split_ors; split_ands; eauto.

      - econstructor; eauto.

    Qed.


    Lemma honest_labeled_step_adv_no_honest_keys :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys honestk adv.(key_heap)
          (* -> message_queues_ok usrs honestk *)
          (* -> user_cipher_queues_ok usrs honestk cs *)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Action a
              -> action_adversary_safe honestk a
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> adv_no_honest_keys honestk' adv'.(key_heap).
    Proof.
      induction 1; inversion 1; inversion 3; intros; subst; try discriminate; eauto.

      - erewrite findUserKeys_readd_user_addnl_keys; eauto.
        admit.

      - erewrite findUserKeys_multi_add_same_keys_idempotent; eauto.
        simpl.
        invert H17. simpl  in *; split_ands.
        admit.
    Admitted.

    Lemma honest_silent_step_adv_no_honest_keys :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys honestk adv.(key_heap)
          -> user_cipher_queues_ok usrs honestk cs
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> adv_no_honest_keys honestk' adv'.(key_heap).
    Proof.
      induction 1; inversion 1; inversion 4; intros; subst; try discriminate;
        try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      erewrite findUserKeys_readd_user_addnl_keys by eauto; eauto.
      rewrite merge_keys_mine; eauto.
      assert (user_cipher_queue usrs' u_id = Some mycs) by (unfold user_cipher_queue; context_map_rewrites; auto).
      specialize (H20 _ _ H4).
      eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands; clean_map_lookups.
      destruct H7 as [l1 H7]; destruct H7 as [l2 H7]; split_ands.
      assert (keys_mine (findUserKeys usrs') (findKeys msg) /\ incl (findCiphers msg) l2) by eauto; split_ands; auto.
    Qed.

    Lemma adv_step_adv_no_honest_keys :
      forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl None bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> adv_no_honest_keys honestk ks
          -> encrypted_ciphers_ok honestk cs
          -> ks = adv.(key_heap)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> honestk' = findUserKeys usrs'
              -> adv_no_honest_keys honestk' ks'.
    Proof.
      induction 1; inversion 1; inversion 5; intros; subst; try discriminate; eauto.

      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) by auto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      unfold adv_no_honest_keys in *.

      intros.
      specialize (H19 k_id); intuition idtac.
      specialize (H4 k_id); split_ors; split_ands; clean_map_lookups.

      right; right; split; eauto; intros.

      cases (key_heap adv' $? k_id);
        cases (findKeys msg $? k_id); subst; clean_map_lookups.
      - erewrite merge_perms_chooses_greatest in H5; unfold greatest_permission in *; eauto; invert H5.
        rewrite orb_true_iff in H11; split_ors; subst; eauto.

        eapply Forall_natmap_in_prop in H20; eauto; intuition idtac.
        invert H20; eauto.
        + specialize (H14 _ Heq0); contradiction.
        + specialize (ADV k__encid); split_ors; split_ands; clean_map_lookups; contradiction.

      - erewrite merge_perms_adds_ks1 in H5; eauto.
      - erewrite merge_perms_adds_ks2 with (ks2:=findKeys msg)in H5; eauto.
        invert H5.
        eapply Forall_natmap_in_prop in H20; eauto; invert H20.
        + specialize (H14 _ Heq0); contradiction.
        + specialize (ADV k__encid); split_ors; split_ands; clean_map_lookups. contradiction.
      - rewrite merge_perms_adds_no_new_perms in H5; auto.
    Qed.


    (* Lemma adv_step_advuniv_implies_univ_ok' : *)
    (*   forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
    (*     gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd', *)
    (*     step_user lbl None bd bd' *)
    (*     -> forall (cmd : user_cmd C) honestk, *)
    (*         bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd) *)
    (*       -> honestk = findUserKeys usrs *)
    (*       -> keys_good gks *)
    (*       -> message_queues_ok usrs honestk *)
    (*       -> user_cipher_queues_ok usrs honestk cs *)
    (*       -> ks = adv.(key_heap) *)
    (*       -> forall cmd' honestk', *)
    (*             bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd') *)
    (*           -> honestk' = findUserKeys usrs' *)
    (*           -> keys_good gks' *)
    (*           /\ message_queues_ok usrs' honestk' *)
    (*           /\ user_cipher_queues_ok usrs' honestk' cs'. *)
    (* Proof. *)
    (*   induction 1; inversion 1; inversion 6; try discriminate; eauto; intros; subst; eauto. *)

    (*   destruct rec_u; simpl in *; *)
    (*     intuition idtac; *)
    (*     erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto. *)

    (*   unfold message_queues_ok; intros. *)
    (*   cases (rec_u_id ==n u_id0); subst; eauto; unfold user_queue in H. *)
    (*   - rewrite add_eq_o in H; simpl in *; invert H; auto. *)
    (*     assert (user_queue usrs u_id0 = Some msg_heap) as UQ by (unfold user_queue; context_map_rewrites; trivial). *)
    (*     specialize (H16 _ _ UQ); auto. *)
    (*     unfold message_queue_ok. *)
    (*     apply Forall_app; constructor; auto; intros. *)

    (*     (* how do I know this message wasn't honestly signed? *) *)
    (*     admit. *)

    (*   - rewrite add_neq_o in H; simpl in *; auto. *)
    (*     cases (usrs $? u_id0); subst; try discriminate; invert H. *)
    (*     destruct u. assert (user_queue usrs u_id0 = Some msg_heap0) as UQ by (unfold user_queue; context_map_rewrites; auto). *)
    (*     specialize (H16 _ _ UQ); auto. *)
    (* Admitted. *)

    Lemma silent_step_advuniv_implies_univ_ok :
      forall {A B} (U U' : universe A B) lbl,
        step_universe U lbl U'
        -> lbl = Silent
        -> universe_ok U
        -> universe_ok U'.
    Proof.
      intros.
      invert H; auto; try discriminate.

      (* Honest step *)
      - destruct U; destruct userData; unfold build_data_step in *; simpl in *.
        unfold universe_ok in *; simpl in *; split_ands.

        assert (  keys_good gks
                /\ message_queues_ok usrs (findUserKeys usrs)
                /\ message_queue_ok qmsgs (findUserKeys usrs) ).
        eapply honest_silent_step_advuniv_implies_univ_ok'; eauto.
        unfold user_queue; rewrite H2; eauto.

        intuition idtac.
        + unfold user_cipher_queues_ok in *.
          assert (user_cipher_queue users u_id = Some c_heap ) by (unfold user_cipher_queue; context_map_rewrites; auto).
          eapply message_queues_ok_after_silent_honest_step; eauto.
        + eapply user_cipher_queues_ok_after_silent_honest_step; eauto.

      (* adv step *)
      - destruct U; unfold build_data_step in *; simpl in *.
        unfold universe_ok in *; simpl in *; split_ands;
          eauto using adv_step_advuniv_implies_univ_ok'.
    Admitted. (* upd univ ok *)

    Lemma honest_silent_step_advuniv_implies_honest_or_no_step_origuniv :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' (b: B),
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) cs__s usrs__s honestk,
          honestk = findUserKeys usrs
          -> cs__s = clean_ciphers honestk cs
          -> usrs__s = clean_users honestk usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> user_keys usrs u_id = Some ks
          -> user_cipher_queue usrs u_id = Some mycs
          -> user_cipher_queue_safe honestk cs mycs
          -> forall cmd' cs__s' usrs__s' pwless_adv pwless_adv' honestk',
              honestk' = findUserKeys usrs'
              -> cs__s' = clean_ciphers honestk' cs'
              -> usrs__s' = clean_users honestk' usrs'
              -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Silent
              -> pwless_adv = {| key_heap := key_heap adv
                              ; protocol := Return b
                              ; msg_heap := adv.(msg_heap)
                              ; c_heap   := adv.(c_heap) |}
              -> pwless_adv' = {| key_heap := key_heap adv'
                               ; protocol := Return b
                               ; msg_heap := adv'.(msg_heap)
                               ; c_heap   := adv'.(c_heap) |}
              -> step_user lbl u_id
                          (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                          (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd')
              \/ (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                = (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd')
    .

    Proof.
      induction 1; inversion 4; inversion 7; intros; subst; clean_context;
        try solve [ left; econstructor; eauto ].

      - remember (findUserKeys usrs) as honestk.
        remember (findUserKeys usrs') as honestk'.
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

        specialize (IHstep_user _ _ _ _ _ _ _ _ _
                                Heqhonestk
                                Heqcs__s
                                Hequsrs__s
                                bd1
                                H4
                                H13
                                H14
                                _ _ _ _ _ _
                                Heqhonestk'
                                Heqcs__s'
                                Hequsrs__s'
                                bd1'
                                SIL
                                Heqpwless_adv
                                Heqpwless_adv'
                   ); split_ors.
        + left; econstructor; eauto.
        + right; invert H0; eauto.

      - cases (msg_honestly_signed (findUserKeys usrs') msg).
        + left. econstructor; eauto.
          unfold clean_messages, msg_filter; simpl; rewrite Heq; eauto.
        + right. simpl. rewrite Heq. trivial.

      - left.
        eapply cipher_id_in_user_cipher_queue_prop in H8; eauto; invert H8; split_ands.
        destruct H6 as [l1 H6]; destruct H6 as [l2 H6]; split_ands; clean_map_lookups.
        econstructor; eauto.
        apply in_or_app; eauto.

      - eapply cipher_id_in_user_cipher_queue_prop in H2; eauto; invert H2; split_ands.
        destruct H4 as [l1 H4]; destruct H4 as [l2 H4]; split_ands; clean_map_lookups.
        left; econstructor; eauto.
        apply in_or_app; eauto.
    Qed.


    (* Lemma honestly_signed_messages_add_no_private_adv_keys : *)
    (*   forall {A t} (msg : message t) (usrs : honest_users A) honestk cs (* u_id ks cmd msgs mycs *),  *)
    (*     honestk = findUserKeys usrs *)
    (*     -> msg_honestly_signed honestk msg = true *)
    (*     -> message_no_adv_private msg honestk *)
    (*     -> user_cipher_queues_ok usrs honestk cs *)
    (*     -> honestk $k++ findKeys msg = honestk. *)
    (* Proof. *)
    (*   unfold msg_honestly_signed; intros. *)
    (*   destruct msg; eauto; try discriminate. *)
    (*   - admit.  (* Let's eliminate this case upstream! *) *)
    (*   - simpl. *)
    (*     apply map_eq_Equal; unfold Equal; intros. *)
    (*     specialize (H1 y); simpl in *. *)
    (*     cases (findKeys msg $? y); eauto. *)
    (*     + cases b; subst; eauto. *)
    (*       * assert (findUserKeys usrs $? y = None \/ findUserKeys usrs $? y = Some false) by auto; *)
    (*           split_ors; context_map_rewrites; eauto. *)


    (*     (forall k, honestk $? k = None -> findKeys msg $? k = None \/ findKeys msg $? k = Some false) *)



    Lemma honest_labeled_step_nochange_honestk :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) a,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> action_adversary_safe (findUserKeys usrs) a
          (* -> message_queues_ok usrs (findUserKeys usrs) *)
          -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> findUserKeys (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}))
                  = findUserKeys usrs'.
    Proof.
      induction 1; inversion 1; inversion 4; try discriminate; subst; eauto;
        unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end;
          split_ands; intros.

      - erewrite findUserKeys_readd_user_addnl_keys; eauto.
        assert (msg_honestly_signed (findUserKeys usrs') msg = true) by eauto.

        assert (keys_mine (findUserKeys usrs') (findKeys msg) ) by admit.

        (* MSGQ -- need honstk $k++ findKeys msg = honestk (on RECV) *)
        admit.
        (* unfold message_queues_ok in *. *)
        (* assert (user_queue usrs' u_id = Some (existT _ _ msg :: qmsgs')) *)
        (*   as UQ *)
        (*   by (unfold user_queue; context_map_rewrites; simpl; trivial). *)
        (* specialize (H16 _ _ UQ). *)
        (* invert H16. *)
        (* assert (msg_contains_only_honest_public_keys (findUserKeys usrs') msg) as HPK by auto. *)
        (* pose proof (safe_messages_have_only_honest_public_keys HPK). *)
        (* apply map_eq_Equal; unfold Equal; intros. *)
        (* specialize H3 with y. *)
        (* cases (findUserKeys usrs' $? y); subst; split_ors; split_ands; try contradiction. *)
        (* + erewrite merge_perms_adds_ks1; eauto. *)
        (* + erewrite merge_perms_chooses_greatest; unfold greatest_permission; eauto; rewrite orb_false_r; auto. *)
        (* + rewrite merge_perms_adds_no_new_perms; auto. *)
      - cases (rec_u_id ==n u_id); subst; clean_map_lookups; simpl; eauto.
        + rewrite map_add_eq.
          erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto.
        + erewrite !findUserKeys_readd_user_same_keys_idempotent'; eauto.
    Admitted.

    Lemma honest_labeled_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a (b : B),
        step_user lbl u_id bd bd'
        -> action_adversary_safe (findUserKeys usrs) a
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
              -> step_user lbl u_id
                          (usrs__s, pwless_adv, cs__s, gks, ks, clean_messages honestk qmsgs, mycs, cmd)
                          (usrs__s', pwless_adv', cs__s', gks', ks', clean_messages honestk' qmsgs', mycs', cmd').
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

    Lemma message_queue_ok_adding_public_keys :
      forall msgs honestk pubk,
        message_queue_ok msgs honestk
        -> (forall k kp, pubk $? k = Some kp -> kp = false)
        -> message_queue_ok msgs (honestk $k++ pubk).
    Proof.
      unfold message_queue_ok; induction 1; eauto; intros;
        econstructor; eauto.

      destruct x; simpl in *; intros.
      apply message_contains_only_honest_public_keys_after_new_keys.
      apply H.
      eapply message_honestly_signed_after_remove_pub_keys; eauto.
    Qed.

    Hint Resolve message_queue_ok_adding_public_keys.

    Lemma honest_labeled_step_advuniv_implies_univ_ok' :
      forall {A B C} (u_id : user_id) cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd' a,
        step_user lbl u_id bd bd'
        -> forall (cmd : user_cmd C) honestk,
            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> honestk = findUserKeys usrs
          -> keys_good gks
          -> message_queues_ok usrs honestk
          -> user_cipher_queues_ok usrs honestk cs
          (* -> user_queue usrs u_id = Some qmsgs *)
          (* -> user_cipher_queue usrs u_id = Some mycs *)
          -> forall cmd' honestk',
                bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> lbl = Action a
              -> action_adversary_safe honestk a
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' |})
                  -> honestk' = findUserKeys usrs''
                  -> keys_good gks'
                  /\ message_queues_ok usrs'' honestk'
                  /\ user_cipher_queues_ok usrs'' honestk' cs'.
              (* /\ message_queue_ok qmsgs' honestk' *)
    Proof.
      induction 1; inversion 1; inversion 5; try discriminate; eauto; intros; subst; eauto;
        unfold action_adversary_safe in *; match goal with [ H : Action _ = Action _ |- _] => invert H end; split_ands.

      assert (user_cipher_queue usrs' u_id = Some mycs) by (unfold user_cipher_queue; context_map_rewrites; auto).

      - erewrite findUserKeys_readd_user_addnl_keys by eauto.
        intuition idtac.

        + unfold message_queues_ok in *; intros.

          assert (user_queue usrs' u_id = Some (existT _ _ msg :: qmsgs'))
            as UQ by (unfold user_queue; context_map_rewrites; auto).
          assert (  message_queue_ok (existT message t0 msg :: qmsgs') (findUserKeys usrs') ) as MQOK by eauto.
          invert MQOK.

          cases (u_id ==n u_id1); subst; unfold user_queue in H2.
          * rewrite add_eq_o in H2; invert H2; eauto.
          * rewrite add_neq_o in H2; auto. cases (usrs' $? u_id1); subst; invert H2.
            assert ( message_queue_ok (msg_heap u) (findUserKeys usrs') )
              by (apply H17 with (u_id:=u_id1); unfold user_queue; context_map_rewrites; auto); eauto.

        + unfold user_cipher_queues_ok; intros; eauto.
          unfold user_cipher_queue in H2; cases (u_id ==n u_id1); subst; eauto.
          * rewrite add_eq_o in H2; invert H2; eauto.
            (* Need to add condition on ciphers contained in messages
             * Hrm public key condition here (on RECV) concerns me.  How can I know?
             *)
            admit.
          * rewrite add_neq_o in H2; auto.
            cases (usrs' $? u_id1); subst; invert H2.
            assert (user_cipher_queue usrs' u_id1 = Some u.(c_heap))
              by (unfold user_cipher_queue; context_map_rewrites; auto).
            eapply user_cipher_queue_safe_add_pub_keys; eauto.

      - cases (u_id ==n rec_u_id); subst; eauto.
        + (* This case should be ruled out by operational semantics *)
          rewrite map_add_eq.
          erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto.
          intuition eauto.

        + erewrite !findUserKeys_readd_user_same_keys_idempotent' by eauto.
          intuition idtac.

          * unfold message_queues_ok; intros.
            unfold user_queue in H4.
            cases (u_id1 ==n rec_u_id); subst.
            ** rewrite add_neq_o, add_eq_o in H4; auto; invert H4.
               apply Forall_app; constructor; eauto.
               eapply H16; eauto.
               unfold user_queue; rewrite H2; trivial.
            ** cases (u_id1 ==n u_id); subst; eauto.
               *** rewrite add_eq_o in H4; auto; invert H4; eauto.
                   eapply H16 with (u_id := u_id); eauto. unfold user_queue; context_map_rewrites; auto.
               *** rewrite !add_neq_o in H4; auto.
                   cases (usrs $? u_id1); subst; invert H4.
                   eapply H16 with (u_id := u_id1); eauto. unfold user_queue; context_map_rewrites; auto.

          * remember (usrs $+ (rec_u_id,
                              {| key_heap := key_heap rec_u; protocol := protocol rec_u; msg_heap := msg_heap rec_u ++ [existT message t0 msg]; c_heap := c_heap rec_u |})) as us.

            assert ( us $? u_id = Some {| key_heap := ks'; protocol := cmdc; msg_heap := qmsgs'; c_heap := mycs' |}) by
                (subst; clean_map_lookups; auto).

            assert (findUserKeys us = findUserKeys usrs)
              by (subst; eauto; eapply findUserKeys_readd_user_same_keys_idempotent'; eauto).

            rewrite <- H6;
              eapply user_cipher_queues_ok_readd_user; eauto.
            rewrite H6; subst.
            destruct rec_u; eapply user_cipher_queues_ok_readd_user; eauto.

    Admitted.

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
      eapply honest_labeled_step_advuniv_implies_univ_ok'; eauto.
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
      induction 1; inversion 1; inversion 2; subst; eauto.
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
          /\ step_user (Action a) u_id (build_data_step U u_d)
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

    Lemma honest_silent_step_nochange_clean_ciphers :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> clean_ciphers (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}))) cs'
                  = clean_ciphers (findUserKeys usrs') cs'.
    Proof.
      induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto;
        try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      erewrite findUserKeys_readd_user_addnl_keys by eauto.
      erewrite cipher_message_keys_already_in_honest; eauto.
      unfold user_cipher_queue; rewrite H21; auto.
    Qed.

    Lemma honest_silent_step_nochange_clean_messages :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> clean_messages (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}))) qmsgs'
                  = clean_messages (findUserKeys usrs') qmsgs'.
    Proof.
      induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto;
        try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      erewrite findUserKeys_readd_user_addnl_keys; eauto.
      erewrite cipher_message_keys_already_in_honest; eauto.
      unfold user_cipher_queue; rewrite H21; auto.
    Qed.

    Lemma honest_silent_step_nochange_clean_users :
      forall {A B C} cs cs' (u_id : user_id) lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
                gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
        step_user lbl u_id bd bd'
        -> user_cipher_queues_ok usrs (findUserKeys usrs) cs
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
          -> lbl = Silent
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
              -> forall cmdc cmdc',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs |}
                -> clean_users (findUserKeys (usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' |}))) usrs'
                  = clean_users (findUserKeys usrs') usrs'.
    Proof.
      induction 1; inversion 2; inversion 2; intros; subst; try discriminate; eauto;
        try erewrite findUserKeys_readd_user_same_keys_idempotent' by eauto; eauto.

      erewrite findUserKeys_readd_user_addnl_keys; eauto.
      erewrite cipher_message_keys_already_in_honest; eauto.
      unfold user_cipher_queue; rewrite H21; auto.

    Qed.

    Hint Extern 1 (user_keys _ _ = Some _ ) => unfold user_keys; context_map_rewrites.

    Lemma silent_honest_step_advuniv_implies_stripped_univ_step_or_none :
      forall {A B} (U U' : universe A B) b (u_id : user_id) userData usrs adv cs gks ks qmsgs mycs cmd,
        universe_ok U
        (* -> step_universe U Silent U' *)
        -> U.(users) $? u_id = Some userData
        -> step_user Silent u_id
                    (build_data_step U userData)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd ; c_heap := mycs |}
        -> step_universe (strip_adversary U b) Silent (strip_adversary U' b)
        \/ strip_adversary U b = strip_adversary U' b.
    Proof.
      intros.
      subst; simpl.
      destruct U; unfold build_data_step in *; simpl in *.

      remember H1 as RW. clear HeqRW.

      assert (user_cipher_queue users u_id = Some (c_heap userData)); unfold user_cipher_queue; context_map_rewrites; eauto.
      unfold universe_ok in *; split_ands.
      eapply honest_silent_step_advuniv_implies_honest_or_no_step_origuniv in RW; eauto.

      split_ors.
      - left.
        eapply StepUser; eauto.
        unfold build_data_step; simpl.
        + exact H5.
        + unfold strip_adversary, buildUniverse; simpl.
          rewrite clean_users_add_pull; simpl.
          clear H5.

          (* In order to resolve this, we will need to state that cleaning users and ciphers is the
           * same in the presence of honest silent steps.  At first this is troubling, since silent
           * steps can create keys (not implemented right now).  However, this will not be a problem,
           * since there shouldn't be any ciphers signed by keys which have just been created.
           *)
          destruct userData.
          erewrite honest_silent_step_nochange_clean_ciphers; eauto; simpl in *.
          erewrite honest_silent_step_nochange_clean_messages; eauto.
          erewrite honest_silent_step_nochange_clean_users; eauto.
      - right.
        unfold strip_adversary, buildUniverse; simpl.
        destruct userData; invert H5.
        assert (clean_users (findUserKeys users) users = clean_users (findUserKeys usrs) usrs)
          by (apply map_eq_elements_eq; simpl; auto).
        f_equal.
        + rewrite clean_users_add_pull; simpl.
          erewrite honest_silent_step_nochange_clean_users; eauto.
          rewrite H5.
          erewrite honest_silent_step_nochange_clean_messages; eauto.
          rewrite <- !H5.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n u_id); subst; clean_map_lookups; trivial.
          eapply clean_users_cleans_user; eauto.
          simpl. rewrite H14; trivial.
        + erewrite honest_silent_step_nochange_clean_ciphers; eauto.

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

        f_equal.
        apply map_eq_Equal; unfold Equal; intros.
        unfold clean_users at 1.
        cases (x ==n y); clean_map_lookups.
        + rewrite map_o; clean_map_lookups; simpl; trivial.
        + rewrite map_o; clean_map_lookups; simpl.
          rewrite <- map_o.
          unfold clean_users; trivial.
    Qed.

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
      erewrite findUserKeys_readd_user_same_keys_idempotent'; eauto.

      rewrite clean_users_add_pull; simpl.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n rec_u_id); subst; clean_map_lookups; eauto.
      clear H5 H17.

      (* This is just not true *)
      assert (msg_honestly_signed (findUserKeys usrs) msg = false) by admit.

      rewrite clean_messages_drops_not_honestly_signed; auto.
      erewrite clean_users_cleans_user; eauto.

    Admitted.

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop) (b : B)
        (cmd : user_cmd B) lbl (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs mycs,
        step_user lbl None
                  (build_data_step U__r U__r.(adversary))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> R (strip_adversary U__r b) U__i
        (* -> universe_ok U__r *)
        -> adv_no_honest_keys (findUserKeys (users U__r)) (key_heap (adversary U__r))
        -> R (strip_adversary (buildUniverseAdv usrs cs gks {| key_heap := adv.(key_heap) $k++ ks
                                                            ; protocol := cmd
                                                            ; msg_heap := qmsgs
                                                            ; c_heap   := mycs |}) b) U__i.
    Proof.
      intros.
      unfold buildUniverseAdv, strip_adversary, build_data_step in *; subst; simpl.
      (* unfold universe_ok in *; split_ands. *)

      Hint Resolve
           adv_step_implies_no_user_impact_after_cleaning
           adv_step_implies_no_new_ciphers_after_cleaning.

      (* some rewrites to get the goal matching the R assumption *)
      match goal with
      | [ H : R {| users := ?us ; adversary := _ ; all_ciphers := ?cs ; all_keys := _ |} _
          |- R {| users := ?us' ; adversary := _ ; all_ciphers := ?cs' ; all_keys := _ |} _ ] =>
        assert (cs = cs') as CS by eauto;
          assert (us = us') as US by eauto
      end; rewrite <- CS, <- US.

      (* need to match up the adversaries *)
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

  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i
          -> RealWorld.universe_ok U__r
          -> forall U__r',
              rstepSilent U__r U__r'
              -> exists U__i', (istepSilent) ^* U__i U__i' /\ RealWorld.universe_ok U__r' /\ R U__r' U__i')
      -> RealWorld.universe_ok U__ra
      -> R (strip_adversary U__ra b) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                 /\ RealWorld.universe_ok U__ra'
                 /\ R (strip_adversary U__ra' b) U__i'.
  Proof.
    intros.

    assert (RealWorld.universe_ok (strip_adversary U__ra b))
      as STRIP_UNIV_OK
        by (eauto using ok_universe_strip_adversary_still_ok).

    assert (RealWorld.universe_ok U__ra')
      by eauto using silent_step_advuniv_implies_univ_ok.

    match goal with
    | [ H : rstepSilent _ _ |- _ ] => invert H
    end.

    (* Honest step *)
    - remember (RealWorld.buildUniverse usrs adv cs gks u_id
                                        {| RealWorld.key_heap := ks ; RealWorld.msg_heap := qmsgs ; RealWorld.protocol := cmd |})
               as U__ra'.

      pose proof (silent_honest_step_advuniv_implies_stripped_univ_step_or_none b H0 H4 H5 HeqU__ra'); split_ors.

      + specialize (H _ _ H1 STRIP_UNIV_OK _ H2).
        repeat match goal with
               | [ H : exists _, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
               end.
        unfold RealWorld.universe_ok in *.
        eexists; eauto.

      + exists U__i; intuition idtac; eauto.
        rewrite <- H2; trivial.

    (* Adversary step *)
    - exists U__i; intuition idtac.
      + eapply TrcRefl.
      + eapply adv_step_stays_in_R; eauto.
        (* need to start with adv has no honest keys *)
        admit.

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

  Lemma simulates_labeled_step_adversary_safe :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A)
            (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) (b : B),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i ->
          forall (a__r : RealWorld.action) (U__ra U__r' : RealWorld.universe A B),
            RealWorld.step_universe U__ra (Action a__r) U__r'
          -> RealWorld.findUserKeys (U__ra.(RealWorld.users)) = RealWorld.findUserKeys (U__r.(RealWorld.users))
          -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__r)) a__r)
      -> R (strip_adversary U__ra b) U__i
      -> forall a__r (U U__ra' : RealWorld.universe A B),
          RealWorld.step_universe U (Action a__r) U__ra'
          -> RealWorld.findUserKeys (RealWorld.users U) = RealWorld.findUserKeys (RealWorld.users U__ra)
          -> RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users U__ra)) a__r.
  Proof.
    intros.

    assert (RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.users (strip_adversary U__ra b))) a__r)
      as ADV_SAFE.
    eapply H; eauto.
    erewrite <- findUserKeys_same_stripped_univ; eauto.

    erewrite findUserKeys_same_stripped_univ; eauto.
  Qed.

  Print Assumptions simulates_with_adversary_labeled.

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

    (* Will need to add additional constraints on starting universe, like what kinds of messages
     * can be in the queues and what ciphers can be in the cipher heap.  *)

    erewrite real_univ_eq_fields_eq;
      eauto using clean_ciphers_idempotent. (* clean_users_idempotent *)
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

    Hint Resolve
         simulates_with_adversary_silent
         simulates_with_adversary_labeled
         simulates_labeled_step_adversary_safe
         simulates_start_ok_adding_adversary.

    unfold simulates_silent_step, simulates_labeled_step, simulates_labeled_step_safe.

    split; eauto.
    split; eauto.

  Qed.

  Print Assumptions simulates_ok_with_adversary.

End SingleAdversarySimulates.
