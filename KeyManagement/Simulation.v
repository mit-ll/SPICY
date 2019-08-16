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

Definition rstepSilent {A B : Type} (U1 U2 : RealWorld.universe A B) :=
  RealWorld.step_universe U1 Silent U2.

Definition istepSilent {A : Type} (U1 U2 : IdealWorld.universe A) :=
  IdealWorld.lstep_universe U1 Silent U2.

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

  Definition msgCiphers_ok {t} (cs : ciphers) (msg : message t) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       match m with
                       | SignedCiphertext k__sign k__enc msg_id
                         => exists t (m' : message t), cs $? msg_id = Some (SigEncCipher k__sign k__enc m')
                       | Signature m' k sig
                         => cs $? sig = Some (SigCipher k m')
                       | _ => False
                       end
                     end) (findMsgCiphers msg).

  Definition ciphers_good (cs : ciphers) : Prop :=
    Forall_natmap (fun c =>
                     match c with
                     | SigEncCipher k__sign k__enc m => msgCiphers_ok cs m
                     | SigCipher k m => msgCiphers_ok cs m
                     end
                  ) cs.

  Definition user_cipher_queue_ok (cs : ciphers) (honestk : key_perms) :=
    Forall (fun cid => exists c, cs $? cid = Some c
                       /\ cipher_honestly_signed honestk c = true).

  Definition user_cipher_queues_ok {A} (cs : ciphers) (honestk : key_perms) (usrs : honest_users A) :=
    Forall_natmap
      (fun u => user_cipher_queue_ok cs honestk u.(c_heap)) usrs.

  Definition adv_cipher_queue_ok (cs : ciphers) :=
    Forall (fun cid => exists c, cs $? cid = Some c).

  Inductive encrypted_cipher_ok (cs : ciphers) (gks : keys): cipher -> Prop :=
  | SigCipherHonestOk : forall {t} (msg : message t) k k_data,
      honestk $? k = Some true
      -> gks $? k = Some k_data
      -> (forall k_id, findKeys msg $? k_id = Some true -> False)
      -> (forall k_id, findKeys msg $? k_id = Some false -> honestk $? k_id = Some true)
      -> msgCiphersSigned honestk cs msg
      -> encrypted_cipher_ok cs gks (SigCipher k msg)
  | SigCipherNotHonestOk : forall {t} (msg : message t) k k_data,
      honestk $? k <> Some true
      -> gks $? k = Some k_data
      -> encrypted_cipher_ok cs gks (SigCipher k msg)
  | SigEncCipherAdvSignedOk :  forall {t} (msg : message t) k__s k__e k_data__s k_data__e,
      honestk $? k__s <> Some true
      -> gks $? k__s = Some k_data__s
      -> gks $? k__e = Some k_data__e
      -> (forall k kp, findKeys msg $? k = Some kp
                 -> exists v, gks $? k = Some v
                      /\ (kp = true -> honestk $? k <> Some true))
      -> (forall cid, List.In cid (findCiphers msg) -> exists c, cs $? cid = Some c)
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg)
  | SigEncCipherHonestSignedEncKeyHonestOk : forall {t} (msg : message t) k__s k__e k_data__s k_data__e,
      honestk $? k__s = Some true
      -> honestk $? k__e = Some true
      -> gks $? k__s = Some k_data__s
      -> gks $? k__e = Some k_data__e
      -> (forall k_id kp, findKeys msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      (* -> keys_mine honestk (findKeys msg) *)
      -> msgCiphersSigned honestk cs msg
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg).

  Definition encrypted_ciphers_ok (cs : ciphers) (gks : keys) :=
    Forall_natmap (encrypted_cipher_ok cs gks) cs.

  Definition message_no_adv_private {t} (msg : message t) :=
    forall k p, findKeys msg $? k = Some p -> honestk $? k = Some true /\ p = false.
    (* forall k, findKeys msg $? k = Some true -> False. *)
  (* -> (honestk $? k = None \/ honestk $? k = Some false). *)

  Hint Unfold message_no_adv_private.

  Definition adv_message_queue_ok (honestk : key_perms) (cs : ciphers) (gks : keys) (msgs : queued_messages) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall k kp,
                         findKeys m $? k = Some kp
                         -> gks $? k <> None /\ (kp = true /\ honestk $? k <> Some true))
                     /\ (forall c_id, List.In c_id (findCiphers m) -> exists c, cs $? c_id = Some c)
                     end
           ) msgs.

  Definition message_queue_ok (cs : ciphers) (msgs : queued_messages) (gks : keys) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall k kp, findKeys m $? k = Some kp -> gks $? k <> None)
                       /\ ( match m with
                           | SignedCiphertext k__sign _ _ =>
                               gks $? k__sign <> None
                             /\ if honest_keyb honestk k__sign
                               then message_no_adv_private m /\ msgCiphersSigned honestk cs m
                               else True
                           | Signature _ k__sign _ =>
                               gks $? k__sign <> None
                             /\ if honest_keyb honestk k__sign
                               then message_no_adv_private m /\ msgCiphersSigned honestk cs m
                               else True
                           | _ => True
                           end
                         )
                       (* /\ (msg_honestly_signed honestk m = true *)
                       (*    -> message_no_adv_private m *)
                       (*    /\ msgCiphersSigned honestk cs m) *)
                     end
           ) msgs.

  Definition message_queues_ok {A} (cs : ciphers) (usrs : honest_users A) (gks : keys) :=
    Forall_natmap (fun u => message_queue_ok cs u.(msg_heap) gks) usrs.

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

Definition universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  encrypted_ciphers_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.all_keys)
.

Definition adv_universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  keys_and_permissions_good U.(RealWorld.all_keys) U.(RealWorld.users) U.(RealWorld.adversary).(RealWorld.key_heap)
    /\ user_cipher_queues_ok U.(RealWorld.all_ciphers) honestk U.(RealWorld.users)
    /\ message_queues_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.users) U.(RealWorld.all_keys)
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
        RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
        -> exists a2 U__i' U__i'',
          istepSilent^* U__i U__i'
        /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
        /\ action_matches a1 a2
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
        RealWorld.step_universe U__r (Action a) U__r' (* excludes adversary steps *)
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

  Lemma msgCiphersSigned_addnl_cipher :
    forall cs msgs honestk c_id c,
      Forall (RealWorld.msgCipherOk honestk cs) msgs
      -> ~ In c_id cs
      -> Forall (RealWorld.msgCipherOk honestk (cs $+ (c_id,c))) msgs.
  Proof.
    induction msgs; intros; econstructor; invert H; eauto; clean_map_lookups.
    unfold RealWorld.msgCipherOk in H3. unfold RealWorld.msgCipherOk.
    destruct a; intuition idtac.
    destruct m; eauto.
    - invert H1; invert H2; repeat eexists.
      destruct (c_id ==n msg_id); subst; clean_map_lookups; eauto.
    - destruct (c_id ==n sig); subst; clean_map_lookups; eauto.
  Qed.

  Lemma msgCiphersSigned_new_honest_key' :
    forall msgCphrs honestk cs k,
      Forall (msgCipherOk honestk cs) msgCphrs
      -> honestk $? keyId k = None
      -> Forall (RealWorld.msgCipherOk (honestk $+ (keyId k, true)) cs) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H; eauto; clean_map_lookups.
    unfold msgCipherOk in H3. unfold msgCipherOk.
    destruct a; intuition idtac.
    destruct m; eauto.
    - simpl in *; unfold honest_keyb in *; simpl;
        cases (honestk $? k__sign); try discriminate;
          destruct (keyId k ==n k__sign); subst; clean_map_lookups; context_map_rewrites;
            cases b; try discriminate; trivial.
    - simpl in *; unfold honest_keyb in *; simpl;
        cases (honestk $? k0); try discriminate;
          destruct (keyId k ==n k0); subst; clean_map_lookups; context_map_rewrites;
            cases b; try discriminate; trivial.
  Qed.

  Lemma msgCiphersSigned_new_honest_key :
    forall {t} (msg : message t) honestk cs k,
      msgCiphersSigned honestk cs msg
      -> honestk $? keyId k = None
      -> msgCiphersSigned (honestk $+ (keyId k, true)) cs msg.
  Proof.
    intros; eapply msgCiphersSigned_new_honest_key'; eauto.
  Qed.

  Hint Resolve msgCiphersSigned_new_honest_key.

  Lemma msgCiphersSigned_cleaned_honestk' :
    forall msgCphrs honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> Forall (msgCipherOk honestk cs) msgCphrs
      -> Forall (msgCipherOk honestk' (clean_ciphers honestk cs)) msgCphrs.
  Proof.
    induction msgCphrs; intros; econstructor; invert H0; eauto; clean_map_lookups.
    unfold msgCipherOk in H3; unfold msgCipherOk.
    destruct a; destruct m; intuition eauto.
    - unfold msg_honestly_signed, honest_keyb in *.
      cases (honestk $? k__sign); try discriminate;
        destruct b;
        try discriminate.
        match goal with
        | [ H : honestk $? k__sign = Some true, H2 : (forall k_id, honestk $? _ = _ -> _ ) |- _ ] => specialize (H2 _ H); rewrite H2
        end; trivial.
    - split_ex; repeat eexists; apply clean_ciphers_keeps_honest_cipher; eauto.
    - unfold msg_honestly_signed, honest_keyb in *.
      cases (honestk $? k); try discriminate;
        destruct b; try discriminate;
        match goal with
        | [ H : honestk $? k = Some true, H2 : (forall k_id, honestk $? _ = _ -> _ ) |- _ ] => specialize (H2 _ H); rewrite H2
        end; trivial.
    - split_ex; repeat eexists; apply clean_ciphers_keeps_honest_cipher; eauto.
  Qed.

  Lemma msgCiphersSigned_cleaned_honestk :
    forall {t} (msg : message t) honestk honestk' cs,
      (forall k_id, honestk $? k_id = Some true -> honestk' $? k_id = Some true)
      -> msgCiphersSigned honestk cs msg
      -> msgCiphersSigned honestk' (clean_ciphers honestk cs) msg.
  Proof. unfold msgCiphersSigned; intros; eapply msgCiphersSigned_cleaned_honestk'; auto. Qed.

  Hint Resolve msgCiphersSigned_cleaned_honestk.

  Lemma encrypted_cipher_ok_addnl_cipher :
    forall honestk cs ks c_id c1 c2,
      encrypted_cipher_ok honestk cs ks c1
      -> ~ In c_id cs
      -> encrypted_cipher_ok honestk (cs $+ (c_id,c2)) ks c1.
  Proof.
    inversion 1; intros; try solve [ econstructor; eauto ].
    - econstructor; eauto.
      eapply msgCiphersSigned_addnl_cipher; auto.
    - eapply SigEncCipherAdvSignedOk; eauto.
      intros.
      destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
    - eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      eapply msgCiphersSigned_addnl_cipher; auto.
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

    clean_map_lookups.
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
              | [ H : (forall k kp, findKeys _ $? k = Some kp -> _) |- (forall k kp, findKeys _ $? k = Some kp -> _ ) ] => intros
              | [ H : (forall k, findKeys _ $? k = _ -> _) |- (forall k, findKeys _ $? k = _ -> _ ) ] => intros
              | [ H : (forall k, findKeys ?msg $? k = ?opt -> _), FK : findKeys ?msg $? _ = ?opt |- _ ] =>
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
