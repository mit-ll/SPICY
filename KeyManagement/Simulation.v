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
          /\ action_matches a1 a2
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
