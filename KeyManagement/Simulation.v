From Coq Require Import
     List
     Morphisms
     Eqdep
     Program.Equality (* for dependent induction *)
.

Require Import
        MyPrelude
        Maps
        Common
        MapLtac
        Keys
        Tactics
        Messages.

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
Definition message_matches (n : nat) := if n then True else False.
  
Inductive action_matches {A B} :
    RealWorld.action * RealWorld.universe A B -> IdealWorld.action * IdealWorld.universe A -> Prop :=
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) a__rw a__iw ch_id cs ps p y U__iw U__rw,
      a__rw = (RealWorld.Input msg1 p y)
    -> a__iw = IdealWorld.Input msg2 ch_id cs ps
    -> MessageEq.message_matches  (msg1, U__rw) (msg2, U__iw)
    -> action_matches (a__rw, U__rw)
                     (a__iw, U__iw)
| Out : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) a__rw a__iw ch_id cs ps U__iw U__rw,
      a__rw = RealWorld.Output msg1
    -> a__iw = IdealWorld.Output msg2 ch_id cs ps
    -> MessageEq.message_matches (msg1, U__rw) (msg2, U__iw)
    -> action_matches (a__rw, U__rw)
                     (a__iw, U__iw)
.

Section RealWorldUniverseProperties.
  Import RealWorld.

Section RealWorldUniverseProperties.
  Import RealWorld.

  Definition testHygProto1 := Gen.

  Lemma testHygProto1_ok :
    protocol_hygienic [] testHygProto1.
||||||| merged common ancestors
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
=======
  Variable honestk : key_perms.

  Definition keys_good (ks : keys) : Prop :=
    forall k_id k,
        ks $? k_id = Some k
      -> keyId k = k_id.

  Definition user_cipher_queue_ok (cs : ciphers) (honestk : key_perms) :=
    Forall (fun cid => exists c, cs $? cid = Some c
                       /\ cipher_honestly_signed honestk c = true).

  Definition user_cipher_queues_ok {A} (cs : ciphers) (honestk : key_perms) (usrs : honest_users A) :=
    Forall_natmap
      (fun u => user_cipher_queue_ok cs honestk u.(c_heap)) usrs.

  Lemma cons_app_split :
    forall {A} (l l1 l2 : list A) a,
      a :: l = l1 ++ l2
      -> (l1 = [] /\ l2 = a :: l)
      \/ (exists l1', l1 = a :: l1' /\ l = l1' ++ l2).
>>>>>>> message_type_refactor
  Proof.
    destruct l1; eauto; intros.

    right. invert H.
    eexists; eauto.
  Qed.

  Definition msgCiphersSigned {t} (msg : message t) :=
    (* Forall (fun m => let m := (existT _ _ msg) in msg_honestly_signed honestk msg = true) (findMsgCiphers msg). *)
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) => msg_honestly_signed honestk m = true
                     end) (findMsgCiphers msg).

  Inductive encrypted_cipher_ok : cipher -> Prop :=
  | SigCipherHonestOk : forall {t} (msg : message t) k,
      honestk $? k = Some true
      -> (forall k, findKeys msg $? k = Some true -> False)
      -> msgCiphersSigned msg
      -> encrypted_cipher_ok (SigCipher k msg)
  | SigCipherNotHonestOk : forall {t} (msg : message t) k,
      honestk $? k <> Some true
      -> encrypted_cipher_ok (SigCipher k msg)
  | SigEncCipherAdvSignedOk :  forall {t} (msg : message t) k__e k__s,
      honestk $? k__s <> Some true
      -> (forall k, findKeys msg $? k = Some true
              -> honestk $? k <> Some true)
      -> encrypted_cipher_ok (SigEncCipher k__s k__e msg)
  (* | SigEncCipherHonestSignedEncKeyNotHonestOk : forall {t} (msg : message t) k__e k__s, *)
  (*     honestk $? k__s = Some true *)
  (*     -> honestk $? k__e <> Some true *)
  (*     -> (forall k, findKeys msg $? k = Some true *)
  (*             -> honestk $? k <> Some true) *)
  (*     -> encrypted_cipher_ok (SigEncCipher k__s k__e msg) *)
  | SigEncCipherHonestSignedEncKeyHonestOk : forall {t} (msg : message t) k__e k__s,
      honestk $? k__s = Some true
      -> honestk $? k__e = Some true
      -> keys_mine honestk (findKeys msg)
      -> msgCiphersSigned msg
      -> encrypted_cipher_ok (SigEncCipher k__s k__e msg).

  Definition encrypted_ciphers_ok :=
    Forall_natmap encrypted_cipher_ok.

  Definition message_no_adv_private {t} (msg : message t) :=
    forall k, findKeys msg $? k = Some true -> False.
  (* -> (honestk $? k = None \/ honestk $? k = Some false). *)

  Hint Unfold message_no_adv_private.

  Definition message_queue_ok (msgs : queued_messages) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                         msg_honestly_signed honestk m = true
                       -> message_no_adv_private m
                       /\ msgCiphersSigned m
                     end
           ) msgs.

  Definition message_queues_ok {A} (usrs : honest_users A) :=
    Forall_natmap (fun u => message_queue_ok u.(msg_heap)) usrs.

  Definition adv_no_honest_keys (advk : key_perms) : Prop :=
    forall k_id,
      (  honestk $? k_id = None
      \/  honestk $? k_id = Some false
      \/ (honestk $? k_id = Some true /\ advk $? k_id <> Some true)
      ).

  Definition is_powerless {B} (usr : user_data B) (b: B): Prop :=
    adv_no_honest_keys usr.(key_heap)
  /\ usr.(protocol) = Return b.

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
  in  encrypted_ciphers_ok honestk U.(RealWorld.all_ciphers)
.

Definition adv_universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  keys_good U.(RealWorld.all_keys)
    /\ user_cipher_queues_ok U.(RealWorld.all_ciphers) honestk U.(RealWorld.users)
    /\ message_queues_ok honestk U.(RealWorld.users)
    /\ adv_no_honest_keys honestk U.(RealWorld.adversary).(RealWorld.key_heap).

Definition simulates_silent_step {A B} (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) :=
  forall U__r U__i,
    R U__r U__i
    -> universe_ok U__r
    -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
            istepSilent ^* U__i U__i'
          /\ universe_ok U__r'
          /\ R U__r' U__i'.

Definition simulates_labeled_step {A B} (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop) :=
  forall U__r U__i,
    R U__r U__i
    -> universe_ok U__r
    -> forall a1 U__r',
        RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
        -> exists a2 U__i' U__i'',
          istepSilent^* U__i U__i'
          /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
          /\ action_matches (a1, U__r) (a2, U__i)
          /\ R U__r' U__i''
          /\ universe_ok U__r'.

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
/\ universe_ok U__r
.

Definition refines {A B : Type} (U1 : RealWorld.universe A B)(U2 : IdealWorld.universe A) :=
  exists R, simulates R U1 U2.

Infix "<|" := refines (no associativity, at level 70).
