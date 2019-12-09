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

Inductive action_matches : forall {A B : Type},
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
    /\ honest_nonces_ok U.(RealWorld.all_ciphers) U.(RealWorld.users).

Section OperationalSemanticsPredicates.
  Import RealWorld.

  Inductive honest_party_step : forall A B C, rlabel -> option user_id -> data_step0 A B C -> data_step0 A B C -> Prop :=

  (* Plumbing *)
  | HonestBindRecur : forall {B r r'} (usrs usrs' : honest_users r') (adv adv' : user_data B)
                      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' sents sents' cur_n cur_n'
                      (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      honest_party_step lbl u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd1)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd1')
      -> honest_party_step lbl u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Bind cmd1 cmd2)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', Bind cmd1' cmd2)
  | HonestBindProceed : forall {B r r'} (usrs : honest_users r) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n
                        (v : r') (cmd : r' -> user_cmd r),
      honest_party_step Silent u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Bind (Return v) cmd)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd v)

  | HonestGen : forall {A B} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n n,
      honest_party_step Silent u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Gen)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Return n)

  (* Comms  *)
  | HonestRecv : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs qmsgs' mycs mycs' froms froms'
                 sents cur_n (msg : crypto t) msgs pat newkeys newcs,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
      -> qmsgs' = msgs
      -> findKeysCrypto cs msg = newkeys
      -> newcs = findCiphers msg
      -> ks' = ks $k++ newkeys
      -> mycs' = newcs ++ mycs
      -> froms' = updateTrackedNonce u_id froms cs msg
      -> msg_accepted_by_pattern cs u_id pat msg
      -> honest_party_step (Action (Input msg pat froms)) u_id
                  (usrs, adv, cs, gks, ks , qmsgs , mycs, froms, sents, cur_n,  Recv pat)
                  (usrs, adv, cs, gks, ks', qmsgs', mycs', froms', sents, cur_n, Return msg)

  | HonestRecvDrop : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs suid gks ks qmsgs qmsgs'
                     mycs froms froms' sents cur_n (msg : crypto t) pat msgs,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
      -> qmsgs' = msgs
      -> froms' = (if msg_signed_addressed (findUserKeys usrs) cs suid msg
                  then updateTrackedNonce suid froms cs msg
                  else froms)
      -> ~ msg_accepted_by_pattern cs suid pat msg
      -> honest_party_step Silent suid (* Error label ... *)
                  (usrs, adv, cs, gks, ks, qmsgs , mycs, froms,  sents, cur_n, Recv pat)
                  (usrs, adv, cs, gks, ks, qmsgs', mycs, froms', sents, cur_n, @Recv t pat)

  (* Augment attacker's keys with those available through messages sent, *)
  (*  * including traversing through ciphers already known by attacker, etc. *)
  (*  *)
  | HonestSend : forall {A B} {t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
                 cs suid gks ks qmsgs mycs froms sents sents' cur_n rec_u_id rec_u newkeys (msg : crypto t),
      findKeysCrypto cs msg = newkeys
      -> keys_mine ks newkeys
      -> incl (findCiphers msg) mycs
      -> usrs $? rec_u_id = Some rec_u
      -> Some rec_u_id <> suid
      -> sents' = updateTrackedNonce (Some rec_u_id) sents cs msg
      -> usrs' = usrs $+ (rec_u_id, {| key_heap  := rec_u.(key_heap)
                                      ; protocol  := rec_u.(protocol)
                                      ; msg_heap  := rec_u.(msg_heap) ++ [existT _ _ msg]
                                      ; c_heap    := rec_u.(c_heap)
                                      ; from_nons := rec_u.(from_nons)
                                      ; sent_nons := rec_u.(sent_nons)
                                      ; cur_nonce := rec_u.(cur_nonce) |})
      -> adv' = 
        {| key_heap  := adv.(key_heap) $k++ newkeys
           ; protocol  := adv.(protocol)
           ; msg_heap  := adv.(msg_heap) ++ [existT _ _ msg]
           ; c_heap    := adv.(c_heap)
           ; from_nons := adv.(from_nons)
           ; sent_nons := adv.(sent_nons)
           ; cur_nonce := adv.(cur_nonce) |}
      -> honest_party_step (Action (Output msg suid (Some rec_u_id) sents)) suid
                  (usrs , adv , cs, gks, ks, qmsgs, mycs, froms, sents,  cur_n, Send rec_u_id msg)
                  (usrs', adv', cs, gks, ks, qmsgs, mycs, froms, sents', cur_n, Return tt)

  (* Encryption / Decryption *)
  | HonestEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs' froms sents
                    cur_n cur_n' (msg : message t) k__signid k__encid kp__enc kt__enc kt__sign c_id cipherMsg msg_to,
      gks $? k__encid  = Some (MkCryptoKey k__encid Encryption kt__enc)
      -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt__sign)
      -> ks $? k__encid   = Some kp__enc
      -> ks $? k__signid  = Some true
      -> ~ In c_id cs
      -> keys_mine ks (findKeysMessage msg)
      -> cur_n' = 1 + cur_n
      -> cipherMsg = SigEncCipher k__signid k__encid msg_to (u_id, cur_n) msg
      -> cs' = cs $+ (c_id, cipherMsg)
      -> mycs' = c_id :: mycs
      (* Extra condition *)
      -> findUserKeys usrs $? k__encid = Some true
      -> honest_party_step Silent u_id
                  (usrs, adv, cs , gks, ks, qmsgs, mycs,  froms, sents, cur_n,  SignEncrypt k__signid k__encid msg_to msg)
                  (usrs, adv, cs', gks, ks, qmsgs, mycs', froms, sents, cur_n', Return (SignedCiphertext c_id))

  | HonestDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs mycs mycs'
                    (msg : message t) k__signid kp__sign k__encid c_id nonce newkeys kt__sign kt__enc msg_to froms sents cur_n,
      cs $? c_id     = Some (SigEncCipher k__signid k__encid msg_to nonce msg)
      -> gks $? k__encid  = Some (MkCryptoKey k__encid Encryption kt__enc)
      -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt__sign)
      -> ks  $? k__encid  = Some true
      -> ks  $? k__signid = Some kp__sign
      -> findKeysMessage msg = newkeys
      -> ks' = ks $k++ newkeys
      -> mycs' = (* newcs ++  *)mycs
      -> List.In c_id mycs
      -> honest_party_step Silent u_id
                  (usrs, adv, cs, gks, ks , qmsgs, mycs,  froms, sents, cur_n, Decrypt (SignedCiphertext c_id))
                  (usrs, adv, cs, gks, ks', qmsgs, mycs', froms, sents, cur_n, Return msg)

  (* Signing / Verification *)
  | HonestSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs' froms sents cur_n cur_n'
                 (msg : message t) k_id kt c_id cipherMsg msg_to,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
      -> ks  $? k_id = Some true
      -> ~ In c_id cs
      -> cur_n' = 1 + cur_n
      -> cipherMsg = SigCipher k_id msg_to (u_id, cur_n) msg
      -> cs' = cs $+ (c_id, cipherMsg)
      -> mycs' = c_id :: mycs
      -> honest_party_step Silent u_id
                  (usrs, adv, cs , gks, ks, qmsgs, mycs,  froms, sents, cur_n,  Sign k_id msg_to msg)
                  (usrs, adv, cs', gks, ks, qmsgs, mycs', froms, sents, cur_n', Return (SignedCiphertext c_id))

  | HonestVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n
                   (msg : message t) k_id kp kt c_id nonce msg_to,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
      -> ks  $? k_id = Some kp
      -> cs $? c_id = Some (SigCipher k_id msg_to nonce msg)
      -> List.In c_id mycs
      -> honest_party_step Silent u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Verify k_id (SignedCiphertext c_id))
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Return (true, msg))
  | HonestGenerateSymKey: forall {A B} (usrs : honest_users A) (adv : user_data B)
                          cs u_id gks gks' ks ks' qmsgs mycs froms sents cur_n
                          (k_id : key_identifier) k usage,
      gks $? k_id = None
      -> k = MkCryptoKey k_id usage SymKey
      -> gks' = gks $+ (k_id, k)
      -> ks' = add_key_perm k_id true ks
      -> honest_party_step Silent u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, GenerateSymKey usage)
                  (usrs, adv, cs, gks', ks', qmsgs, mycs, froms, sents, cur_n, Return (k_id, true))
  | HonestGenerateAsymKey: forall {A B} (usrs : honest_users A) (adv : user_data B)
                           cs u_id gks gks' ks ks' qmsgs mycs froms sents cur_n
                           (k_id : key_identifier) k usage,
      gks $? k_id = None
      -> k = MkCryptoKey k_id usage AsymKey
      -> gks' = gks $+ (k_id, k)
      -> ks' = add_key_perm k_id true ks
      -> honest_party_step Silent u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, GenerateAsymKey usage)
                  (usrs, adv, cs, gks', ks', qmsgs, mycs, froms, sents, cur_n, Return (k_id, true))
  .

  Inductive honest_party_universe_step {A B} : universe A B -> rlabel -> universe A B -> Prop :=
  | HonestUser  : forall U U' (u_id : user_id) userData usrs adv
                    cs gks ks qmsgs mycs froms sents cur_n lbl (cmd : user_cmd A),
      U.(users) $? u_id = Some userData
      -> honest_party_step
          lbl (Some u_id)
          (build_data_step U userData)
          (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> U' = buildUniverse usrs adv cs gks u_id {| key_heap  := ks
                                                 ; msg_heap  := qmsgs
                                                 ; protocol  := cmd
                                                 ; c_heap    := mycs
                                                 ; from_nons := froms
                                                 ; sent_nons := sents
                                                 ; cur_nonce := cur_n |}
      -> honest_party_universe_step U lbl U'.


End OperationalSemanticsPredicates.

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

  Definition simulates_universe_ok' :=
    forall (U__r : RealWorld.universe A B) U__i,
        R (RealWorld.peel_adv U__r) U__i
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> advP U__r.(RealWorld.adversary)
      -> forall U__r' lbl,
            RealWorld.step_universe U__r lbl U__r'
          -> honest_party_universe_step U__r lbl U__r'.
          (* \/ U__r.(RealWorld.all_ciphers) = U__r'.(RealWorld.all_ciphers). *)

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
