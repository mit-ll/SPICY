(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     List
     Morphisms
     Eqdep
.

Require Import
        MyPrelude
        Maps
        Messages
        MessageEq
        Common
        Keys
        AdversaryUniverse
.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Definition istepSilent {A} (U1 U2 : IdealWorld.universe A) :=
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

Inductive action_matches : forall {A B : type},
                           RealWorld.action -> RealWorld.universe A B ->
                           IdealWorld.action -> IdealWorld.universe A -> Prop :=
| Inp : forall A B t (m__rw : RealWorld.crypto t) (m__iw m__expected : IdealWorld.message.message t)
               ms (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A) rw iw ch_id cs ps p froms,
      rw = (RealWorld.Input m__rw p froms)
      -> iw = IdealWorld.Input m__iw ch_id cs ps
      -> U__iw.(IdealWorld.channel_vector) $? ch_id = Some ((existT _ _ m__expected) :: ms)
      -> MessageEq.message_eq m__rw U__rw m__iw U__iw ch_id
      -> action_matches rw U__rw iw U__iw
| Out : forall A B t (m__rw : RealWorld.crypto t) (m__iw : IdealWorld.message.message t)
          (U__rw : RealWorld.universe A B) (U__iw : IdealWorld.universe A) rw iw ch_id cs ps suid_to suid_from sents,
    rw = RealWorld.Output m__rw suid_to suid_from sents
    -> iw = IdealWorld.Output m__iw ch_id cs ps
    (* -> U__iw.(IdealWorld.channel_vector) $? ch_id = Some (ms ++ [existT _ _ m__expected]) *)
    -> MessageEq.message_eq m__rw U__rw m__iw U__iw ch_id
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

  Definition user_cipher_queue_ok (cs : ciphers) (honestk : key_perms) :=
    Forall (fun cid => exists c, cs $? cid = Some c
                       /\ cipher_honestly_signed honestk c = true).

  Definition user_cipher_queues_ok {A} (cs : ciphers) (honestk : key_perms) (usrs : honest_users A) :=
    Forall_natmap
      (fun u => user_cipher_queue_ok cs honestk u.(c_heap)) usrs.

  Definition adv_cipher_queue_ok {A} (cs : ciphers) (usrs : honest_users A) :=
    Forall (fun cid => exists new_cipher,
                cs $? cid = Some new_cipher
                /\ ( (fst (cipher_nonce new_cipher) = None /\ cipher_honestly_signed (findUserKeys usrs) new_cipher = false)
                  \/ exists u_id u rec_u,
                      fst (cipher_nonce new_cipher) = Some u_id
                      /\ usrs $? u_id = Some u
                      /\ u_id <> cipher_to_user new_cipher
                      /\ List.In (cipher_nonce new_cipher) u.(sent_nons)
                      /\ usrs $? cipher_to_user new_cipher = Some rec_u
                      /\ ( List.In (cipher_nonce new_cipher) rec_u.(from_nons)
                        \/ Exists (fun sigM => match sigM with
                                           | existT _ _ m =>
                                             msg_signed_addressed (findUserKeys usrs) cs (Some (cipher_to_user new_cipher)) m = true
                                           /\ msg_nonce_same new_cipher cs m
                                           end) rec_u.(msg_heap)))
           ).

  Inductive encrypted_cipher_ok (cs : ciphers) (gks : keys): cipher -> Prop :=
  | SigCipherHonestOk : forall {t} (msg : message t) msg_to nonce k kt,
      honestk $? k = Some true
      -> gks $? k = Some {| keyId := k; keyUsage := Signing; keyType := kt |}
      (* only send honest public keys *)
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> encrypted_cipher_ok cs gks (SigCipher k msg_to nonce msg)
  | SigCipherNotHonestOk : forall {t} (msg : message t) msg_to nonce k kt,
      honestk $? k <> Some true
      -> gks $? k = Some {| keyId := k; keyUsage := Signing; keyType := kt |}
      -> encrypted_cipher_ok cs gks (SigCipher k msg_to nonce msg)
  | SigEncCipherAdvSignedOk :  forall {t} (msg : message t) msg_to nonce k__s k__e kt__s kt__e,
      honestk $? k__s <> Some true
      -> gks $? k__s = Some {| keyId := k__s; keyUsage := Signing; keyType := kt__s |}
      -> gks $? k__e = Some {| keyId := k__e; keyUsage := Encryption; keyType := kt__e |}
      -> (forall k kp, findKeysMessage msg $? k = Some kp
                 -> exists v, gks $? k = Some v
                      /\ (kp = true -> honestk $? k <> Some true))
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg_to nonce msg)
  | SigEncCipherHonestSignedEncKeyHonestOk : forall {t} (msg : message t) msg_to nonce k__s k__e kt__s kt__e,
      honestk $? k__s = Some true
      -> honestk $? k__e = Some true
      -> gks $? k__s = Some {| keyId := k__s; keyUsage := Signing; keyType := kt__s |}
      -> gks $? k__e = Some {| keyId := k__e; keyUsage := Encryption; keyType := kt__e |}
      (* only send honest keys *)
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> encrypted_cipher_ok cs gks (SigEncCipher k__s k__e msg_to nonce msg).

  Definition encrypted_ciphers_ok (cs : ciphers) (gks : keys) :=
    Forall_natmap (encrypted_cipher_ok cs gks) cs.

  Definition message_no_adv_private {t} (cs : ciphers) (msg : crypto t) :=
    forall k p, findKeysCrypto cs msg $? k = Some p -> honestk $? k = Some true /\ p = false.

  Definition adv_message_queue_ok {A} (usrs : honest_users A)
             (cs : ciphers) (gks : keys) (msgs : queued_messages) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall cid, msg_cipher_id m = Some cid -> cs $? cid <> None)
                     /\ (forall k kp,
                           findKeysCrypto cs m $? k = Some kp
                           -> gks $? k <> None /\ (kp = true -> (findUserKeys usrs) $? k <> Some true))
                     /\ (forall k,
                           msg_signing_key cs m = Some k
                           -> gks $? k <> None)
                     /\ (forall c_id, List.In c_id (findCiphers m)
                                -> exists c, cs $? c_id = Some c
                                     /\ ( ( fst (cipher_nonce c) = None /\ cipher_honestly_signed (findUserKeys usrs) c = false )
                                       \/ exists uid u rec_u,
                                           fst (cipher_nonce c) = Some uid
                                           /\ usrs $? uid = Some u
                                           /\ uid <> cipher_to_user c
                                           /\ List.In (cipher_nonce c) u.(sent_nons)
                                           /\ usrs $? cipher_to_user c = Some rec_u
                                           /\ ( List.In (cipher_nonce c) rec_u.(from_nons)
                                             \/ Exists (fun sigM =>
                                                         match sigM with
                                                         | existT _ _ m =>
                                                           msg_signed_addressed (findUserKeys usrs) cs (Some (cipher_to_user c)) m = true
                                                           /\ msg_nonce_same c cs m
                                                         end) rec_u.(msg_heap))))
                     end
           ) msgs.

  Definition message_queue_ok (cs : ciphers) (msgs : queued_messages) (gks : keys) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (forall k kp, findKeysCrypto cs m $? k = Some kp -> gks $? k <> None)
                     /\ (forall cid,
                           msg_cipher_id m = Some cid
                           -> cs $? cid <> None)
                     /\ (forall k,
                           msg_signing_key cs m = Some k
                           -> gks $? k <> None
                           /\ ( honest_key honestk k
                             -> message_no_adv_private cs m
                             /\ msgCiphersSignedOk honestk cs m)
                       )
                     end) msgs.

  Definition adv_no_honest_keys (advk : key_perms) : Prop :=
    forall k_id,
      (  honestk $? k_id = None
      \/  honestk $? k_id = Some false
      \/ (honestk $? k_id = Some true /\ advk $? k_id <> Some true)
      ).

  Definition honest_users_only_honest_keys {A} (usrs : honest_users A) :=
    forall u_id u,
      usrs $? u_id = Some u
      -> forall k_id kp,
        u.(key_heap) $? k_id = Some kp
        -> findUserKeys usrs $? k_id = Some true.

  Definition honest_nonce_tracking_ok (cs : ciphers)
             (me : option user_id) (my_sents : sent_nonces) (my_cur_n : nat)
             (to_usr : user_id) (to_froms : recv_nonces) (to_msgs : queued_messages) :=

      Forall (fun non => snd non < my_cur_n) my_sents
    /\ Forall (fun non => fst non = me -> snd non < my_cur_n) to_froms
    /\ Forall (fun sigM => match sigM with
                       | existT _ _ msg =>
                         forall c_id c,
                           msg = SignedCiphertext c_id
                           -> cs $? c_id = Some c
                           -> cipher_to_user c = to_usr
                           -> fst (cipher_nonce c) = me
                           -> snd (cipher_nonce c) < my_cur_n
                       end) to_msgs
    /\ forall c_id c,
        cs $? c_id = Some c
      -> fst (cipher_nonce c) = me (* if cipher created by me *) 
      -> snd (cipher_nonce c) < my_cur_n
      /\ ( cipher_to_user c = to_usr
          -> ~ List.In (cipher_nonce c) my_sents (* and hasn't yet been sent *)
          -> ~ List.In (cipher_nonce c) to_froms (* then it hasn't been read by destination user *)
            /\ Forall (fun sigM => match sigM with (* and isn't in destination user's message queue *)
                               | (existT _ _ msg) => msg_to_this_user cs (Some to_usr) msg = false
                                                    \/ msg_nonce_not_same c cs msg end) to_msgs).

  Definition action_adversary_safe (honestk : key_perms) (cs : ciphers) (a : action) : Prop :=
    match a with
    | Input  msg pat froms    => msg_pattern_safe honestk pat
                              /\ exists c_id c, msg = SignedCiphertext c_id
                                        /\ cs $? c_id = Some c
                                        /\ ~ List.In (cipher_nonce c) froms
    | Output msg msg_from msg_to sents => msg_honestly_signed honestk cs msg = true
                                       /\ msg_to_this_user cs msg_to msg = true
                                       /\ msgCiphersSignedOk honestk cs msg
                                       /\ exists c_id c, msg = SignedCiphertext c_id
                                                 /\ cs $? c_id = Some c
                                                 /\ fst (cipher_nonce c) = msg_from  (* only send my messages *)
                                                 /\ ~ List.In (cipher_nonce c) sents
    end.

  Inductive next_cmd_safe (honestk : key_perms) (cs : ciphers) (u_id : user_id) (froms : recv_nonces) (sents : sent_nonces) :
    forall {A}, user_cmd A -> Prop :=

  | SafeBind : forall {r A} (cmd1 : user_cmd r) (cmd2 : <<r>> -> user_cmd A),
      next_cmd_safe honestk cs u_id froms sents cmd1
      -> next_cmd_safe honestk cs u_id froms sents (Bind cmd1 cmd2)
  | SafeEncrypt : forall {t} (msg : message t) k__sign k__enc msg_to,
      honestk $? k__enc = Some true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> next_cmd_safe honestk cs u_id froms sents (SignEncrypt k__sign k__enc msg_to msg)
  | SafeSign : forall {t} (msg : message t) k msg_to,
      (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> next_cmd_safe honestk cs u_id froms sents (Sign k msg_to msg)
  | SafeRecv : forall t pat,
      msg_pattern_safe honestk pat
      -> next_cmd_safe honestk cs u_id froms sents (@Recv t pat)
  | SafeSend : forall {t} (msg : crypto t) msg_to,
        msg_honestly_signed honestk cs msg = true
      -> msg_to_this_user cs (Some msg_to) msg = true
      -> msgCiphersSignedOk honestk cs msg
      -> (exists c_id c, msg = SignedCiphertext c_id
                /\ cs $? c_id = Some c
                /\ fst (cipher_nonce c) = (Some u_id)  (* only send my messages *)
                /\ ~ List.In (cipher_nonce c) sents)
      -> next_cmd_safe honestk cs u_id froms sents (Send msg_to msg)

  (* Boring Commands *)
  | SafeReturn : forall {A} (a : <<A>>), next_cmd_safe honestk cs u_id froms sents (Return a)
  | SafeGen : next_cmd_safe honestk cs u_id froms sents Gen
  | SafeDecrypt : forall {t} (c : crypto t), next_cmd_safe honestk cs u_id froms sents (Decrypt c)
  | SafeVerify : forall {t} k (c : crypto t), next_cmd_safe honestk cs u_id froms sents (Verify k c)
  | SafeGenerateSymKey : forall usage, next_cmd_safe honestk cs u_id froms sents (GenerateSymKey usage)
  | SafeGenerateAsymKey : forall usage, next_cmd_safe honestk cs u_id froms sents (GenerateAsymKey usage)
  .

  Definition honest_cmds_safe {A B} (U : universe A B) : Prop :=
    forall u_id u honestk,
      honestk = findUserKeys U.(users)
      -> U.(users) $? u_id = Some u
      -> next_cmd_safe (findUserKeys U.(users)) U.(all_ciphers) u_id u.(from_nons) u.(sent_nons) u.(protocol).

  Definition label_safe (honestk : key_perms) (cs : ciphers) (lbl : label) : Prop :=
    match lbl with
    | Silent   => True
    | Action a => action_adversary_safe honestk cs a
    end.
  
End RealWorldUniverseProperties.

Definition message_queues_ok {A} (cs : RealWorld.ciphers) (usrs : RealWorld.honest_users A) (gks : keys) :=
  Forall_natmap (fun u => message_queue_ok (RealWorld.findUserKeys usrs) cs u.(RealWorld.msg_heap) gks) usrs.

Definition honest_nonces_ok {A} (cs : RealWorld.ciphers) (usrs : RealWorld.honest_users A) :=
  forall u_id u rec_u_id rec_u,
    u_id <> rec_u_id
    -> usrs $? u_id = Some u
    -> usrs $? rec_u_id = Some rec_u
    -> honest_nonce_tracking_ok cs
                        (Some u_id) u.(RealWorld.sent_nons) u.(RealWorld.cur_nonce)
                        rec_u_id rec_u.(RealWorld.from_nons) rec_u.(RealWorld.msg_heap).

Definition universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  encrypted_ciphers_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.all_keys)
.

Definition adv_universe_ok {A B} (U : RealWorld.universe A B) : Prop :=
  let honestk := RealWorld.findUserKeys U.(RealWorld.users)
  in  keys_and_permissions_good U.(RealWorld.all_keys) U.(RealWorld.users) U.(RealWorld.adversary).(RealWorld.key_heap)
    /\ user_cipher_queues_ok U.(RealWorld.all_ciphers) honestk U.(RealWorld.users)
    /\ message_queues_ok U.(RealWorld.all_ciphers) U.(RealWorld.users) U.(RealWorld.all_keys)
    /\ adv_cipher_queue_ok U.(RealWorld.all_ciphers) U.(RealWorld.users) U.(RealWorld.adversary).(RealWorld.c_heap)
    /\ adv_message_queue_ok U.(RealWorld.users) U.(RealWorld.all_ciphers) U.(RealWorld.all_keys) U.(RealWorld.adversary).(RealWorld.msg_heap)
    /\ adv_no_honest_keys honestk U.(RealWorld.adversary).(RealWorld.key_heap)
    /\ honest_nonces_ok U.(RealWorld.all_ciphers) U.(RealWorld.users)
    /\ honest_users_only_honest_keys U.(RealWorld.users).

Section Simulation.
  Variable A B : type.
  Variable advP : RealWorld.user_data B -> Prop.
  Variable R : RealWorld.simpl_universe A -> IdealWorld.universe A -> Prop.

  Definition simulates_silent_step :=
    forall (U__r : RealWorld.universe A B) U__i,
      R (RealWorld.peel_adv U__r) U__i
    -> universe_ok U__r
    -> adv_universe_ok U__r
    -> advP U__r.(RealWorld.adversary)
    -> forall U__r',
        RealWorld.step_universe U__r Silent U__r'
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

  Definition honest_actions_safe :=
    forall (U__r : RealWorld.universe A B) U__i,
        R (RealWorld.peel_adv U__r) U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> honest_cmds_safe U__r.

  Definition simulates (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) :=

    (* conditions for simulation steps *)
    simulates_silent_step
  /\ simulates_labeled_step
  /\ honest_actions_safe

  (* conditions for start *)
  /\ R (RealWorld.peel_adv U__r) U__i
  /\ universe_ok U__r
  /\ adv_universe_ok U__r.

End Simulation.

Definition refines {A B} (advP : RealWorld.user_data B -> Prop) (U1 : RealWorld.universe A B) (U2 : IdealWorld.universe A) :=
  exists R, simulates advP R U1 U2.

Notation "u1 <| u2 \ p " := (refines p u1 u2) (no associativity, at level 70).

Definition lameAdv {B} (b : RealWorld.denote (RealWorld.Base B)) :=
  fun adv => adv.(RealWorld.protocol) = @RealWorld.Return (RealWorld.Base B) b.

Definition awesomeAdv : forall B, RealWorld.user_data B -> Prop :=
  fun _ _ => True.
