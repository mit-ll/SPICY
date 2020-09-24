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
        ChMaps
        Messages
        MessageEq
        Common
        Keys
        AdversaryUniverse
.

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       .

Set Implicit Arguments.


Section IdealDefiniions.

  Import IdealWorld.

  Definition istepSilent {A} (U1 U2 : universe A) :=
    lstep_universe U1 Silent U2.

  Inductive indexedIdealStep {A} (uid : user_id) (lbl : label) (U1 U2 : universe A) : Prop :=
  | IndexedIdealStep : forall u proto chans prms,
      U1.(users) $? uid = Some u
      -> lstep_user uid lbl (U1.(channel_vector), u.(protocol), u.(perms)) (chans, proto, prms)
      -> U2 = construct_universe
               chans
               (U1.(users) $+ (uid, {| protocol := proto ; perms := prms |}))
      -> indexedIdealStep uid lbl U1 U2.

  Lemma indexedIdealStep_ideal_step :
    forall A uid lbl U1 U2,
      @indexedIdealStep A uid lbl U1 U2
      -> lstep_universe U1 lbl U2.
  Proof. intros * IND; invert IND; econstructor; eauto. Qed.

End IdealDefiniions.

Section RealDefinitions.
  Import RealWorld.

  Inductive indexedRealStep {A B} (uid : user_id) (lbl : label) (U1 U2 : universe A B) : Prop :=
  | IndexedRealStep : forall userData usrs adv cs gks ks qmsgs mycs froms sents cur_n (cmd : user_cmd (Base A)),
      U1.(users) $? uid = Some userData
      -> step_user lbl (Some uid)
                  (build_data_step U1 userData)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> U2 = buildUniverse usrs adv cs gks uid {| key_heap  := ks
                                                   ; msg_heap  := qmsgs
                                                   ; protocol  := cmd
                                                   ; c_heap    := mycs
                                                   ; from_nons := froms
                                                   ; sent_nons := sents
                                                   ; cur_nonce := cur_n |}
      -> indexedRealStep uid lbl U1 U2.

  Lemma indexedRealStep_real_step :
    forall A B uid lbl U1 U2,
      @indexedRealStep A B uid lbl U1 U2
      -> step_universe (Some uid) U1 (mkULbl lbl uid) U2.
  Proof. intros * IND; invert IND; econstructor; eauto. Qed.

End RealDefinitions.

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

Inductive action_matches (cs : RealWorld.ciphers) (gks : keys) :
  RealWorld.uaction -> IdealWorld.action -> Prop :=

| InpSig : forall t (m__rw : RealWorld.crypto t) (msg__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t)
          kid uid seq froms p cid ch_id chans ps,
    m__rw = RealWorld.SignedCiphertext cid
    -> cs $? cid = Some (RealWorld.SigCipher kid uid seq msg__rw)
    -> content_eq msg__rw m__iw gks
    -> action_matches cs gks (uid, RealWorld.Input m__rw p froms) (IdealWorld.Input m__iw uid ch_id chans ps)
| InpEnc : forall t (m__rw : RealWorld.crypto t) (msg__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t)
          kid1 kid2 uid seq froms p cid ch_id chans ps,
    m__rw = RealWorld.SignedCiphertext cid
    -> cs $? cid = Some (RealWorld.SigEncCipher kid1 kid2 uid seq msg__rw)
    -> content_eq msg__rw m__iw gks
    -> action_matches cs gks (uid, RealWorld.Input m__rw p froms) (IdealWorld.Input m__iw uid ch_id chans ps)
| OutSig : forall t (m__rw : RealWorld.crypto t) (msg__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t)
          kid seq to from sents cid ch_id chans ps,
    m__rw = RealWorld.SignedCiphertext cid
    -> cs $? cid = Some (RealWorld.SigCipher kid to seq msg__rw)
    -> content_eq msg__rw m__iw gks
    -> action_matches cs gks (from, RealWorld.Output m__rw (Some from) (Some to) sents) (IdealWorld.Output m__iw from ch_id chans ps)
| OutEnc : forall t (m__rw : RealWorld.crypto t) (msg__rw : RealWorld.message.message t) (m__iw : IdealWorld.message.message t)
          kid1 kid2 seq to from sents cid ch_id chans ps,
    m__rw = RealWorld.SignedCiphertext cid
    -> cs $? cid = Some (RealWorld.SigEncCipher kid1 kid2 to seq msg__rw)
    -> content_eq msg__rw m__iw gks
    -> action_matches cs gks (from, RealWorld.Output m__rw (Some from) (Some to) sents) (IdealWorld.Output m__iw from ch_id chans ps)
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

End RealWorldUniverseProperties.

Section SafeActions.
  Import RealWorld.
  
  Inductive nextAction : forall {A B}, user_cmd A -> user_cmd B -> Prop :=
  | NaReturn : forall A (a : << A >>),
      nextAction (Return a) (Return a)
  | NaGen :
      nextAction Gen Gen
  | NaSend : forall t uid (msg : crypto t),
      nextAction (Send uid msg) (Send uid msg)
  | NaRecv : forall t pat,
      nextAction (@Recv t pat) (@Recv t pat)
  | NaSignEncrypt : forall t k__s k__e u_id (msg : message t),
      nextAction (SignEncrypt k__s k__e u_id msg) (SignEncrypt k__s k__e u_id msg)
  | NaDecrypt : forall t (msg : crypto t),
      nextAction (Decrypt msg) (Decrypt msg)
  | NaSign : forall t k u_id (msg : message t),
      nextAction (Sign k u_id msg) (Sign k u_id msg)
  | NaVerify : forall t k (msg : crypto t),
      nextAction (Verify k msg) (Verify k msg)
  | NaGenSymKey : forall usg,
      nextAction (GenerateSymKey usg) (GenerateSymKey usg)
  | NaGenAsymKey : forall usg,
      nextAction (GenerateAsymKey usg) (GenerateAsymKey usg)
  | NaBind : forall A B r (c : user_cmd B) (c1 : user_cmd r) (c2 : << r >> -> user_cmd A),
      nextAction c1 c
      -> nextAction (Bind c1 c2) c
  .

  Lemma nextAction_couldBe :
    forall {A B} (c1 : user_cmd A) (c2 : user_cmd B),
      nextAction c1 c2
      -> match c2 with
        | Return _ => True
        | Gen => True
        | Send _ _ => True
        | Recv _ => True
        | SignEncrypt _ _ _ _ => True
        | Decrypt _ => True
        | Sign _ _ _ => True
        | Verify _ _ => True
        | GenerateAsymKey _ => True
        | GenerateSymKey _ => True
        | Bind _ _ => False
        end.
  Proof.
    induction 1; eauto.
  Qed.

  Definition next_cmd_safe (honestk : key_perms) (cs : ciphers) (u_id : user_id)
             (froms : recv_nonces) (sents : sent_nonces) {A} (cmd : user_cmd A) :=
    forall {B} (cmd__n : user_cmd B),
      nextAction cmd cmd__n
      -> match cmd__n with
        | Return _ => True
        | Gen => True
        | Send msg_to msg =>
          msg_honestly_signed honestk cs msg = true
          /\ msg_to_this_user cs (Some msg_to) msg = true
          /\ msgCiphersSignedOk honestk cs msg
          /\ (exists c_id c, msg = SignedCiphertext c_id
                       /\ cs $? c_id = Some c
                       /\ fst (cipher_nonce c) = (Some u_id)  (* only send my messages *)
                       /\ ~ List.In (cipher_nonce c) sents)
        | Recv pat =>
          msg_pattern_safe honestk pat
        | SignEncrypt k__sign k__enc msg_to msg =>
          honestk $? k__enc = Some true
          /\ (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
        | Decrypt _ => True
        | Sign _ _ msg =>
          (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
        | Verify _ _ => True
        | GenerateAsymKey _ => True
        | GenerateSymKey _ => True
        | Bind _ _ => False
        end.

  Definition honest_cmds_safe {A B} (U : universe A B) : Prop :=
    forall u_id u honestk,
      honestk = findUserKeys U.(users)
      -> U.(users) $? u_id = Some u
      (* -> forall lbl bd, step_user lbl (Some u_id) (build_data_step U u) bd *)
      -> next_cmd_safe (findUserKeys U.(users)) U.(all_ciphers) u_id u.(from_nons) u.(sent_nons) u.(protocol).

  Definition label_safe (honestk : key_perms) (cs : ciphers) (lbl : label) : Prop :=
    match lbl with
    | Silent   => True
    | Action a => action_adversary_safe honestk cs a
    end.

End SafeActions.

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
    -> forall suid U__r',
        RealWorld.step_universe suid U__r Silent U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
        /\ R (RealWorld.peel_adv U__r') U__i'.

  Definition simulates_labeled_step :=
    forall (U__r : RealWorld.universe A B) U__i,
      R (RealWorld.peel_adv U__r) U__i
    -> universe_ok U__r
    -> adv_universe_ok U__r
    -> advP U__r.(RealWorld.adversary)
    -> forall uid U__r' ra,
        indexedRealStep uid (Action ra) U__r U__r'
        -> exists ia U__i' U__i'',
            (indexedIdealStep uid Silent) ^* U__i U__i'
            /\ indexedIdealStep uid (Action ia) U__i' U__i''
            /\ action_matches U__r.(RealWorld.all_ciphers) U__r.(RealWorld.all_keys) (uid,ra) ia
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
