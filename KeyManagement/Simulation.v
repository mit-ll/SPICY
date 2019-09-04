From Coq Require Import
     List
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

Require Import
        MyPrelude
        AdversaryUniverse
        Maps
        MessageEq
        Common
        MapLtac
        Keys
        Tactics.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Hint Resolve in_eq in_cons.
Remove Hints absurd_eq_true trans_eq_bool.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Definition rstepSilent {A B : Type} (U1 U2 : RealWorld.universe A B) :=
  RealWorld.step_universe U1 Messages.Silent U2.

Definition istepSilent {A : Type} (U1 U2 : IdealWorld.universe A) :=
  IdealWorld.lstep_universe U1 Messages.Silent U2.

Inductive chan_key : Set :=
| Public (ch_id : IdealWorld.channel_id)
| Auth (ch_id : IdealWorld.channel_id): forall k,
    k.(keyUsage) = Signing -> chan_key
| Enc  (ch_id : IdealWorld.channel_id) : forall k,
    k.(keyUsage) = Encryption -> chan_key
| AuthEnc (ch_id : IdealWorld.channel_id) : forall k1 k2,
      k1.(keyUsage) = Signing
    -> k2.(keyUsage) = Encryption
    -> chan_key
.

(* Inductive msg_eq : forall t__r t__i, *)
(*     RealWorld.crypto t__r *)
(*     -> IdealWorld.message.message t__i * IdealWorld.channel_id * IdealWorld.channels * IdealWorld.permissions -> Prop := *)

(* (* Still need to reason over visibility of channel -- plaintext really means everyone can see it *) *)
(* | PlaintextMessage' : forall content ch_id cs ps, *)
(*     ps $? ch_id = Some (IdealWorld.construct_permission true true) -> *)
(*     msg_eq (RealWorld.Content content) (IdealWorld.message.Content content, ch_id, cs, ps) *)
(* . *)

Inductive action_matches : forall {A B : Type},
                           RealWorld.action -> RealWorld.universe A B ->
                           IdealWorld.action -> IdealWorld.universe A -> Prop :=
| Inp : forall A B t__r t__i (m__rw : RealWorld.crypto t__r) (m__iw m__expected : IdealWorld.message.message t__i)
               ms (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A) rw iw ch_id cs ps p y,
      rw = (RealWorld.Input m__rw p y)
      -> iw = IdealWorld.Input m__iw ch_id cs ps
      -> U__iw.(IdealWorld.channel_vector) $? ch_id = Some ((existT _ _ m__expected) :: ms)
      -> MessageEq.message_eq m__rw U__rw m__iw U__iw m__expected ch_id {} {}
      -> action_matches rw U__rw iw U__iw
| Out : forall A B t__r t__i (m__rw : RealWorld.crypto t__r) (m__iw m__expected : IdealWorld.message.message t__i) ms (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A) rw iw ch_id cs ps,
    rw = RealWorld.Output m__rw
    -> iw = IdealWorld.Output m__iw ch_id cs ps
    -> U__iw.(IdealWorld.channel_vector) $? ch_id = Some (ms ++ [existT _ _ m__expected])
    -> MessageEq.message_eq m__rw U__rw m__iw U__iw m__expected ch_id {} {}
    -> action_matches rw U__rw iw U__iw
.

Section RealWorldUniverseProperties.
  Import RealWorld.

  Variable honestk : key_perms.

  Definition permission_heap_honest (perms : key_perms) :=
    forall k_id p,
      perms $? k_id = Some p
      -> honestk $? k_id = Some true.

  Definition permission_heap_good (ks : keys) (perms : key_perms) :=
    forall k_id p,
      perms $? k_id = Some p
      -> exists k, ks $? k_id = Some k.

  (* Syntactic Predicates *)
  Definition keys_and_permissions_good {A} (ks : keys) (usrs : honest_users A) (adv_heap : key_perms): Prop :=
    (forall k_id k,
          ks $? k_id = Some k
        -> keyId k = k_id)
    /\ Forall_natmap (fun u => permission_heap_good ks u.(key_heap)) usrs
    /\ permission_heap_good ks adv_heap.

  (* Definition msgCiphers_ok {t} (cs : ciphers) (msg : crypto t) := *)
  (*   Forall (fun sigm => match sigm with *)
  (*                    | (existT _ _ m) => *)
  (*                      match m with *)
  (*                      | SignedCiphertext k__sign k__enc msg_id *)
  (*                        => exists t (m' : crypto t), cs $? msg_id = Some (SigEncCipher k__sign k__enc m') *)
  (*                      | Signature m' k sig *)
  (*                        => cs $? sig = Some (SigCipher k m') *)
  (*                      | _ => False *)
  (*                      end *)
  (*                    end) (findMsgCiphers msg). *)

  (* Definition ciphers_good (cs : ciphers) : Prop := *)
  (*   Forall_natmap (fun c => *)
  (*                    match c with *)
  (*                    | SigEncCipher k__sign k__enc m => msgCiphers_ok cs m *)
  (*                    | SigCipher k m => msgCiphers_ok cs m *)
  (*                    end *)
  (*                 ) cs. *)

  Definition user_cipher_queue_ok (cs : ciphers) (honestk : key_perms) :=
    Forall (fun cid => exists c, cs $? cid = Some c
                       /\ cipher_honestly_signed honestk c = true).

  Definition user_cipher_queues_ok {A} (cs : ciphers) (honestk : key_perms) (usrs : honest_users A) :=
    Forall_natmap
      (fun u => user_cipher_queue_ok cs honestk u.(c_heap)) usrs.

  Definition adv_cipher_queue_ok (cs : ciphers) :=
    Forall (fun cid => exists c, cs $? cid = Some c).

  Inductive encrypted_cipher_ok (cs : ciphers) (gks : keys): cipher -> Prop :=
  | SigCipherHonestOk : forall {t} (msg : crypto t) k k_data,
      honestk $? k = Some true
      -> gks $? k = Some k_data
      -> (forall k_id, findKeysCrypto msg $? k_id = Some true -> False)
      -> (forall k_id, findKeysCrypto msg $? k_id = Some false -> honestk $? k_id = Some true)
      -> msgCiphersSignedOk honestk cs msg
      -> encrypted_cipher_ok cs gks (SigCipher k msg)
  | SigCipherNotHonestOk : forall {t} (msg : crypto t) k k_data,
      honestk $? k <> Some true
      -> gks $? k = Some k_data
      (* -> msgCiphersOk cs msg *)
      -> encrypted_cipher_ok cs gks (SigCipher k msg)
  | SigEncCipherAdvSignedOk :  forall {t} (msg : crypto t) k__s k__e k_data__s k_data__e,
      honestk $? k__s <> Some true
      -> gks $? k__s = Some k_data__s
      -> gks $? k__e = Some k_data__e
      -> (forall k kp, findKeysCrypto msg $? k = Some kp
                 -> exists v, gks $? k = Some v
                      /\ (kp = true -> honestk $? k <> Some true))
      -> (forall cid, List.In cid (findCiphers msg) -> exists c, cs $? cid = Some c)
      (* -> msgCiphersOk cs msg *)
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg)
  | SigEncCipherHonestSignedEncKeyHonestOk : forall {t} (msg : crypto t) k__s k__e k_data__s k_data__e,
      honestk $? k__s = Some true
      -> honestk $? k__e = Some true
      -> gks $? k__s = Some k_data__s
      -> gks $? k__e = Some k_data__e
      -> (forall k_id kp, findKeysCrypto msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> msgCiphersSignedOk honestk cs msg
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg).

  Definition encrypted_ciphers_ok (cs : ciphers) (gks : keys) :=
    Forall_natmap (encrypted_cipher_ok cs gks) cs.

  Definition message_no_adv_private {t} (msg : crypto t) :=
    forall k p, findKeysCrypto msg $? k = Some p -> honestk $? k = Some true /\ p = false.
    (* forall k, findKeys msg $? k = Some true -> False. *)

  Hint Unfold message_no_adv_private.

  Definition adv_message_queue_ok (honestk : key_perms) (cs : ciphers) (gks : keys) (msgs : queued_messages) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall k kp,
                         findKeysCrypto m $? k = Some kp
                         -> gks $? k <> None /\ (kp = true /\ honestk $? k <> Some true))
                     /\ (forall c_id, List.In c_id (findCiphers m) -> exists c, cs $? c_id = Some c)
                     end
           ) msgs.

  Definition message_queue_ok (cs : ciphers) (msgs : queued_messages) (gks : keys) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall k kp, findKeysCrypto m $? k = Some kp -> gks $? k <> None)
                     (* /\ (forall cid, msg_cipher_id m = Some cid -> cs $? cid <> None) *)
                     /\ (forall k cid,
                           msg_signing_key cs m = Some k
                           -> msg_cipher_id m = Some cid
                           -> honest_key honestk k
                           (* -> msgCipherOk cs m *)
                           -> gks $? k <> None
                           /\ message_no_adv_private m
                           /\ msgCiphersSignedOk honestk cs m
                           /\ cs $? cid <> None)
                           (* /\ msgCipherOk cs m) *)
                     (* /\ (forall cid, msg_cipher_id m = Some cid *)
                     (*         -> cs $? cid <> None *)
                     (*         /\ msgCipherOk cs m) *)
                       (* -> msgCipherOk cs m  *)
                     end) msgs.
  (* Definition message_queue_ok (cs : ciphers) (msgs : queued_messages) (gks : keys) := *)
  (*   Forall (fun sigm => match sigm with *)
  (*                    | (existT _ _ m) => *)
  (*                      (forall k kp, findKeysCrypto m $? k = Some kp -> gks $? k <> None) *)
  (*                    /\ (forall k, msg_signing_key m = Some k *)
  (*                            -> gks $? k <> None *)
  (*                            /\ (honest_key honestk k *)
  (*                               -> message_no_adv_private m *)
  (*                               /\ msgCiphersSignedOk honestk cs m *)
  (*                               /\ (forall cid, msg_cipher_id m = Some cid *)
  (*                                         -> cs $? cid <> None *)
  (*                                         /\ msgCipherOk cs m))) *)
  (*                    end) msgs. *)

  Definition adv_no_honest_keys (advk : key_perms) : Prop :=
    forall k_id,
      (  honestk $? k_id = None
      \/  honestk $? k_id = Some false
      \/ (honestk $? k_id = Some true /\ advk $? k_id <> Some true)
      ).

  Lemma adv_no_honest_keys_empty :
    adv_no_honest_keys $0.
    unfold adv_no_honest_keys; intros; simpl.
    cases (honestk $? k_id); subst; intuition idtac.
    cases b; subst; intuition idtac.
    right; right; intuition idtac.
    invert H.
  Qed.

End RealWorldUniverseProperties.

Definition message_queues_ok {A} (cs : RealWorld.ciphers) (usrs : RealWorld.honest_users A) (gks : keys) :=
  Forall_natmap (fun u => message_queue_ok (RealWorld.findUserKeys usrs) cs u.(RealWorld.msg_heap) gks) usrs.

Definition universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  encrypted_ciphers_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.all_keys)
.

Definition adv_universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  keys_and_permissions_good U.(RealWorld.all_keys) U.(RealWorld.users) U.(RealWorld.adversary).(RealWorld.key_heap)
    /\ user_cipher_queues_ok U.(RealWorld.all_ciphers) honestk U.(RealWorld.users)
    /\ message_queues_ok U.(RealWorld.all_ciphers) U.(RealWorld.users) U.(RealWorld.all_keys)
    /\ adv_cipher_queue_ok U.(RealWorld.all_ciphers) U.(RealWorld.adversary).(RealWorld.c_heap)
    /\ adv_message_queue_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.all_keys) U.(RealWorld.adversary).(RealWorld.msg_heap)
    /\ adv_no_honest_keys honestk U.(RealWorld.adversary).(RealWorld.key_heap).

Section Simulation.
  Variable A B : Type.
  Variable advP : RealWorld.user_data B -> Prop.
  Variable R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop.

  Definition simulates_silent_step :=
    forall (U__r : RealWorld.universe A B) U__i,
      R (RealWorld.peel_adv U__r) U__i
    -> universe_ok U__r
    -> adv_universe_ok U__r
    -> advP U__r.(RealWorld.adversary)
    -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
        /\ R (RealWorld.peel_adv U__r') U__i'.

  Definition simulates_labeled_step :=
    forall (U__r : RealWorld.universe A B) U__i,
      R (RealWorld.peel_adv U__r) U__i
    -> universe_ok U__r
    -> adv_universe_ok U__r
    -> advP U__r.(RealWorld.adversary)
    -> forall a1 U__r',
        RealWorld.step_universe U__r (Messages.Action a1) U__r' (* excludes adversary steps *)
        -> exists a2 U__i' U__i'',
          istepSilent^* U__i U__i'
        /\ IdealWorld.lstep_universe U__i' (Messages.Action a2) U__i''
        /\ action_matches a1 U__r a2 U__i'
        /\ R (RealWorld.peel_adv U__r') U__i''.

  Definition simulates_universe_ok :=
    forall B (U__r : RealWorld.universe A B) U__i,
        R (strip_adversary U__r) U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> forall U__r' lbl,
        RealWorld.step_universe U__r lbl U__r'
        -> universe_ok U__r'.

  Definition simulates_labeled_step_safe :=
    forall B (U__r : RealWorld.universe A B) U__i,
      R (strip_adversary U__r) U__i
      -> forall U__r' a,
        RealWorld.step_universe U__r (Messages.Action a) U__r' (* excludes adversary steps *)
        -> RealWorld.action_adversary_safe
            (RealWorld.findUserKeys U__r.(RealWorld.users))
            U__r.(RealWorld.all_ciphers)
            a.

  Definition simulates (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) :=

    (* conditions for simulation steps *)
    simulates_silent_step
  /\ simulates_labeled_step
  /\ simulates_universe_ok
  /\ simulates_labeled_step_safe

  (* conditions for start *)
  /\ R (RealWorld.peel_adv U__r) U__i
  /\ universe_ok U__r
  /\ adv_universe_ok U__r.

End Simulation.

Definition refines {A B : Type} (advP : RealWorld.user_data B -> Prop) (U1 : RealWorld.universe A B) (U2 : IdealWorld.universe A) :=
  exists R, simulates advP R U1 U2.

Notation "u1 <| u2 \ p " := (refines p u1 u2) (no associativity, at level 70).

Definition lameAdv {B} (b : B) :=
  fun adv => adv.(RealWorld.protocol) = RealWorld.Return b.

Definition awesomeAdv : forall B, RealWorld.user_data B -> Prop :=
  fun _ _ => True.

Section RealWorldLemmas.

  Import RealWorld.

  (* Lemma msgCipherOk_addnl_cipher : *)
  (*   forall {t} (msg : crypto t) cs c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> msgCipherOk cs msg *)
  (*     -> msgCipherOk (cs $+ (c_id,c)) msg. *)
  (* Proof. *)
  (*   destruct msg; intros; eauto; *)
  (*     unfold msgCipherOk in *; split_ex. *)
  (*   - destruct (c_id ==n msg_id); subst; clean_map_lookups; eauto. *)
  (*   - destruct (c_id ==n sig); subst; clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Hint Resolve msgCipherOk_addnl_cipher. *)

  (* Lemma msgCiphersOk_addnl_cipher' : *)
  (*   forall cs (msgs : list (sigT crypto)) c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> Forall (fun sigm => match sigm with (existT _ _ m) => msgCipherOk cs m end) msgs *)
  (*     -> Forall (fun sigm => match sigm with (existT _ _ m) => msgCipherOk (cs $+ (c_id,c)) m end) msgs. *)
  (* Proof. *)
  (*   induction msgs; intros; eauto. *)
  (*   invert H0; *)
  (*     econstructor; eauto. *)
  (*   destruct a; eauto. *)
  (* Qed. *)

  Lemma msg_honestly_signed_addnl_cipher :
    forall {t} (msg : crypto t) honestk cs c_id c,
      ~ In c_id cs
      -> msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed honestk (cs $+ (c_id,c)) msg = true.
  Proof.
    destruct msg; intros; eauto;
      unfold msg_honestly_signed, msg_signing_key in *;
      repeat
        match goal with
        | [ |- context [ ?cs $+ (?cid1,_) $? ?cid2 ] ] => destruct (cid1 ==n cid2); subst; clean_map_lookups
        | [ H1 : ?cs $? ?cid = _ |- _ ] =>
          match goal with
          | [ H2 : ?P |- _] =>
            match P with
            | context [ match cs $? cid with _ => _ end ] => rewrite H1 in H2
            end
          end
        end; clean_map_lookups; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_addnl_cipher.

  Lemma msg_honestly_signed_addnl_honest_key :
    forall {t} (msg : crypto t) honestk cs k_id,
      ~ In k_id honestk
      -> msg_honestly_signed honestk cs msg = true
      -> msg_honestly_signed (honestk $+ (k_id,true)) cs msg = true.
  Proof.
    destruct msg; intros; eauto;
      unfold msg_honestly_signed, msg_signing_key in *;
      repeat
        match goal with
        | [ |- context [ ?cs $? ?cid ] ] => cases (cs $? cid)
        | [ |- context [ match ?c with _ => _ end ]] => is_var c; destruct c
        | [ |- context [ honest_keyb _ _ = _ ] ] => unfold honest_keyb in *
        | [ H : ?honk $+ (?kid1,_) $? ?kid2 = _ |- _ ] => destruct (kid1 ==n kid2); subst; clean_map_lookups
        | [ H : ?honk $? ?kid = _, M : match ?honk $? ?kid with _ => _ end = _ |- _ ] => rewrite H in M
        end; eauto.
  Qed.

  Hint Resolve msg_honestly_signed_addnl_honest_key.

  Lemma msgCiphersSignedOk_addnl_cipher' :
    forall cs (msgs : queued_messages) honestk c_id c,
      ~ In c_id cs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk (cs $+ (c_id,c)) m = true end) msgs.
  Proof.
    induction msgs; intros; eauto.
    invert H0;
      econstructor; eauto.
    destruct a; intuition eauto.
  Qed.

  (* Lemma msgCiphersOk_addnl_cipher : *)
  (*   forall {t} (msg : crypto t) cs c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> msgCiphersOk cs msg *)
  (*     -> msgCiphersOk (cs $+ (c_id,c)) msg. *)
  (* Proof. unfold msgCiphersOk; intros; eapply msgCiphersOk_addnl_cipher'; eauto. Qed. *)

  Lemma msgCiphersSignedOk_addnl_cipher :
    forall {t} (msg : crypto t) honestk cs c_id c,
      ~ In c_id cs
      -> msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk honestk (cs $+ (c_id,c)) msg.
  Proof. unfold msgCiphersSignedOk; intros; eapply msgCiphersSignedOk_addnl_cipher'; eauto. Qed.

  Hint Resolve
       msgCiphersSignedOk_addnl_cipher.
  
  Lemma msgCiphersSignedOk_new_honest_key' :
    forall (msgCphrs : queued_messages) honestk cs k,
      honestk $? keyId k = None
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgCphrs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed (honestk $+ (keyId k,true)) cs m = true end) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H0; eauto; clean_map_lookups.
    destruct a; intuition eauto.
  Qed.

  Lemma msgCiphersSignedOk_new_honest_key :
    forall {t} (msg : crypto t) honestk cs k,
      msgCiphersSignedOk honestk cs msg
      -> honestk $? keyId k = None
      -> msgCiphersSignedOk (honestk $+ (keyId k, true)) cs msg.
  Proof.
    intros; eapply msgCiphersSignedOk_new_honest_key'; eauto.
  Qed.

  Hint Resolve msgCiphersSignedOk_new_honest_key.

  Lemma msg_signing_key_in_ciphers :
    forall {t} (c : crypto t) cs k,
      msg_signing_key cs c = Some k
      -> exists cid cphr,
        msg_cipher_id c = Some cid
      /\ cs  $? cid = Some cphr
      /\ cipher_signing_key cphr = k.
  Proof.
    intros.
    unfold msg_signing_key in *; destruct c; try discriminate;
      unfold msg_cipher_id, cipher_signing_key.
    - cases (cs $? msg_id); try discriminate; destruct c; try discriminate;
        invert H; eauto.
    - cases (cs $? sig); try discriminate; destruct c0; try discriminate;
        invert H; eauto.
  Qed.

  Lemma msgCiphersSignedOk_cleaned_honestk' :
    forall (msgCphrs : queued_messages) honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk cs m = true end) msgCphrs
      -> Forall (fun sigm => match sigm with (existT _ _ m) => msg_honestly_signed honestk' (clean_ciphers honestk cs) m = true end) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H0; eauto; clean_map_lookups.
    destruct a; intuition eauto;
      unfold msg_honestly_signed in *;
      cases (msg_signing_key cs c); try discriminate.

    assert (msg_signing_key (clean_ciphers honestk cs) c = Some k).
    unfold msg_signing_key; unfold msg_signing_key in Heq;
      destruct c; try discriminate.
    cases (cs $? msg_id); try discriminate; destruct c; try discriminate; invert Heq;
      erewrite clean_ciphers_keeps_honest_cipher; eauto; simpl; eauto.
    cases (cs $? sig); try discriminate; destruct c0; try discriminate; invert Heq;
      erewrite clean_ciphers_keeps_honest_cipher; eauto; simpl; eauto.
    
    rewrite H0; unfold honest_keyb in *.
    cases (honestk $? k); try discriminate; destruct b; try discriminate.
    assert (honestk' $? k = Some true) as RW by eauto; rewrite RW; eauto.
  Qed.

  Lemma msgCiphersSigned_cleaned_honestk :
    forall {t} (msg : crypto t) honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> msgCiphersSignedOk honestk cs msg
      -> msgCiphersSignedOk honestk' (clean_ciphers honestk cs) msg.
  Proof. unfold msgCiphersSignedOk; intros; eapply msgCiphersSignedOk_cleaned_honestk'; auto. Qed.

  Hint Resolve msgCiphersSigned_cleaned_honestk.

  Hint Constructors encrypted_cipher_ok.
  
  Lemma encrypted_cipher_ok_addnl_cipher :
    forall honestk cs ks c_id c1 c2,
      encrypted_cipher_ok honestk cs ks c1
      -> ~ In c_id cs
      -> encrypted_cipher_ok honestk (cs $+ (c_id,c2)) ks c1.
  Proof.
    inversion 1; intros; eauto.
    econstructor; intros; eauto.
    destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_cipher :
    forall honestk cs ks c_id c,
      Forall_natmap (encrypted_cipher_ok honestk cs ks) cs
      -> ~ In c_id cs
      -> Forall_natmap (encrypted_cipher_ok honestk (cs $+ (c_id, c)) ks) cs.
  Proof.
    intros.
    rewrite Forall_natmap_forall in *.
    intros.
    specialize (H _ _ H1); eauto using encrypted_cipher_ok_addnl_cipher.
  Qed.

  Lemma encrypted_cipher_ok_addnl_key :
    forall honestk cs ks k c,
      encrypted_cipher_ok honestk cs ks c
      -> ~ In (keyId k) ks
      -> encrypted_cipher_ok honestk cs (ks $+ (keyId k, k)) c.
  Proof.
    inversion 1; intros; subst; invert H;
      try solve [
            econstructor; try assumption;
            try
              match goal with
              | [ |- _ $+ (?kid1,_) $? ?kid2 = _] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              end; eauto
          ].

    - clean_map_lookups.
      eapply SigEncCipherAdvSignedOk; eauto.
      cases (keyId k ==n k__s); subst; clean_map_lookups; eauto.
      cases (keyId k ==n k__e); subst; clean_map_lookups; eauto.
      intros.
      cases (keyId k ==n k0); subst; clean_map_lookups; eauto.
      exists k; eauto.
      specialize (H13 _ _ H); split_ex; split_ands; auto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_key :
    forall honestk cs ks k_id k,
      encrypted_ciphers_ok honestk cs ks
      -> ~ In (keyId k) ks
      -> k_id = keyId k
      -> encrypted_ciphers_ok honestk cs (ks $+ (k_id, k)).
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *.
    intros; subst.
    specialize (H _ _ H2); eauto using encrypted_cipher_ok_addnl_key.
  Qed.

  Lemma keys_mine_addnl_honest_key :
    forall honestk k_id ks,
      keys_mine honestk ks
      -> keys_mine (honestk $+ (k_id,true)) ks.
  Proof.
    intros; unfold keys_mine; intros.
    destruct (k_id ==n k_id0); subst; clean_map_lookups;
      destruct kp; eauto.
  Qed.

  Hint Resolve keys_mine_addnl_honest_key.

  Lemma encrypted_cipher_ok_addnl_honest_key :
    forall honestk cs ks k c,
      encrypted_cipher_ok honestk cs ks c
      -> ~ In (keyId k) honestk
      -> ~ In (keyId k) ks
      -> encrypted_cipher_ok (honestk $+ (keyId k, true)) cs (ks $+ (keyId k, k)) c.
  Proof.
    inversion 1; intros; subst; invert H; clean_map_lookups;
      try solve [
            econstructor; try assumption;
            repeat
              match goal with
              | [ H : (forall k kp, findKeysCrypto _ $? k = Some kp -> _) |- (forall k kp, findKeysCrypto _ $? k = Some kp -> _ ) ] => intros
              | [ H : (forall k, findKeysCrypto _ $? k = _ -> _) |- (forall k, findKeysCrypto _ $? k = _ -> _ ) ] => intros
              | [ H : (forall k, findKeysCrypto ?msg $? k = ?opt -> _), FK : findKeysCrypto ?msg $? _ = ?opt |- _ ] =>
                specialize (H _ FK); split_ex; split_ands
              | [ H : ?m $? _ = Some _, H1 : (forall k_id kp, ?m $? k_id = Some kp -> _) |- _ /\ _ ] => specialize (H1 _ _ H)
              | [ |- context [_ $+ (?kid1,_) $? ?kid2 = _] ] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              | [ |- context [_ $+ (?kid1,_) $? ?kid2 <> _] ] => cases (kid1 ==n kid2); subst; clean_map_lookups; eauto
              end; intuition eauto
          ].

    eapply SigEncCipherAdvSignedOk; eauto.
    - destruct (keyId k ==n k__s); subst; clean_map_lookups; eauto.
    - destruct (keyId k ==n k__s); subst; clean_map_lookups; eauto.
    - destruct (keyId k ==n k__e); subst; clean_map_lookups; eauto.
    - intros.
      specialize (H14 _ _ H); split_ex; split_ands.
      eexists; destruct (keyId k ==n k0); subst; clean_map_lookups; eauto.
  Qed.

  Lemma encrypted_ciphers_ok_addnl_honest_key :
    forall honestk cs ks k_id k,
      encrypted_ciphers_ok honestk cs ks
      -> ~ In (keyId k) ks
      -> ~ In (keyId k) honestk
      -> k_id = keyId k
      -> encrypted_ciphers_ok (honestk $+ (k_id,true)) cs (ks $+ (k_id, k)).
  Proof.
    unfold encrypted_ciphers_ok; intros.
    rewrite Forall_natmap_forall in *.
    intros; subst; eauto using encrypted_cipher_ok_addnl_honest_key.
  Qed.

  Hint Resolve
       encrypted_ciphers_ok_addnl_cipher
       encrypted_ciphers_ok_addnl_key.

  Lemma adv_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
              gks gks' ks ks' qmsgs qmsgs' mycs mycs' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs ks
        -> adv_cipher_queue_ok cs mycs
        -> encrypted_ciphers_ok honestk cs gks
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
            -> honestk' = findUserKeys usrs'
            -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 1; inversion 7; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto.

    - econstructor; auto.
      assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (H20 k__signid).
      econstructor; eauto.
      + unfold not; intros; split_ors; split_ands; contra_map_lookup; contradiction.
      + intros.
        specialize (H4 _ _ H6).
        specialize (ADV k); unfold not; split_ors; split_ands; contra_map_lookup; try contradiction;
          unfold keys_and_permissions_good, permission_heap_good in *; split_ands;
            try specialize (H12 _ _ H4); try specialize (H13 _ _ H4);  split_ex; eexists;
              intuition (intros; eauto); contra_map_lookup;
                contradiction.
      + intros.
        destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
        unfold adv_cipher_queue_ok in H22.
        rewrite Forall_forall in H22.
        specialize (H5 _ H6).
        specialize (H22 _ H5); eauto.
    - econstructor; eauto.
      specialize (H16 k_id).
      eapply SigCipherNotHonestOk; unfold not; intros; split_ors; split_ands; contra_map_lookup; try contradiction; eauto.
  Qed.

  Lemma universe_ok_adv_step :
    forall {A B} (U__r : universe A B) lbl usrs adv cs gks ks qmsgs mycs cmd,
      universe_ok U__r
      -> adv_universe_ok U__r
      -> step_user lbl None
                  (users U__r, adversary U__r, all_ciphers U__r, all_keys U__r,
                   key_heap (adversary U__r), msg_heap (adversary U__r),
                   c_heap (adversary U__r), protocol (adversary U__r)) (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
      -> universe_ok
          (buildUniverseAdv
             usrs cs gks
             {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}).
  Proof.
    unfold universe_ok, adv_universe_ok; destruct U__r; simpl; intros; split_ands; eauto using adv_step_encrypted_ciphers_ok.
  Qed.

End RealWorldLemmas.
