(* 
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     String
     Sumbool
     Morphisms.

From SPICY Require Import
     MyPrelude
     Common
     Maps
     Keys
     Messages.

Set Implicit Arguments.

Module RW_message <: GRANT_ACCESS.
  Definition access := key_permission.
End RW_message.

Module message := Messages(RW_message).
Import message.
Export message.

Definition cipher_id := nat.

Inductive crypto : type -> Type :=
| Content {t} (c : message t) : crypto t
| SignedCiphertext {t} (c_id : cipher_id) : crypto t
.

(* We need to handle non-deterministic message  -- external choice on ordering *)
Inductive msg_pat :=
| Accept
| Signed (k : key_identifier) (chk_replay : bool)
| SignedEncrypted (k__sign k__enc : key_identifier) (chk_replay : bool)
.

Definition msg_seq : Set := (option user_id) * nat.

Definition msg_seq_eq (s1 s2 : msg_seq) : {s1 = s2} + {s1 <> s2}.
  repeat (decide equality).
Defined.

Inductive cipher : Type :=
| SigCipher {t} (k__sign : key_identifier) (msg_to : user_id) (c_nonce : msg_seq) (msg : message t) : cipher
| SigEncCipher {t} (k__sign k__enc : key_identifier) (msg_to : user_id) (c_nonce : msg_seq) (msg : message t) : cipher
.

Definition cipher_signing_key (c : cipher) :=
  match c with
  | SigCipher k _ _ _      => k
  | SigEncCipher k _ _ _ _ => k
  end.

Definition cipher_to_user (c : cipher) :=
  match c with
  | SigCipher _ to _ _      => to
  | SigEncCipher _ _ to _ _ => to
  end.

Definition cipher_nonce (c : cipher) :=
  match c with
  | SigCipher _ _ n _      => n
  | SigEncCipher _ _ _ n _ => n
  end.

Definition queued_messages := list (sigT crypto).
Definition ciphers         := NatMap.t cipher.
Definition my_ciphers      := list cipher_id.
Definition recv_nonces     := list msg_seq.
Definition sent_nonces     := list msg_seq.

Inductive msg_accepted_by_pattern (cs : ciphers) (opt_uid_to : option user_id) (froms : recv_nonces)
  : forall {t : type}, msg_pat -> crypto t -> Prop :=
| MsgAccept : forall {t} (m : crypto t),
    msg_accepted_by_pattern cs opt_uid_to froms Accept m
| ProperlySigned : forall {t t'} c_id k (m : message t) msg_to nonce (chk : bool),
    cs $? c_id = Some (SigCipher k msg_to nonce m)
    -> (if chk then (count_occ msg_seq_eq froms nonce = 0) else True)
    -> opt_uid_to = Some msg_to
    -> msg_accepted_by_pattern cs opt_uid_to froms (Signed k chk) (@SignedCiphertext t' c_id)
| ProperlyEncrypted : forall {t t'} c_id k__sign k__enc (m : message t) msg_to nonce (chk : bool),
    cs $? c_id = Some (SigEncCipher k__sign k__enc msg_to nonce m)
    -> (if chk then (count_occ msg_seq_eq froms nonce = 0) else True)
    -> opt_uid_to = Some msg_to
    -> msg_accepted_by_pattern cs opt_uid_to froms (SignedEncrypted k__sign k__enc chk) (@SignedCiphertext t' c_id).

Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff : core.

Notation honest_key honk kid := (honk $? kid = Some true).

Section SafeMessages.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  (* Inductive honest_key (k_id : key_identifier) : Prop := *)
  (* | HonestKey : *)
  (*       honestk $? k_id = Some true *)
  (*     -> honest_key k_id. *)

  Definition honest_keyb (k_id : key_identifier) : bool :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Definition msg_cipher_id {t} (msg : crypto t) : option cipher_id :=
    match msg with
    | SignedCiphertext c_id => Some c_id
    | _ => None
    end.

  Definition msg_signing_key {t} (cs : ciphers) (msg : crypto t) : option key_identifier :=
    match msg with
    | Content _ => None
    | SignedCiphertext c_id =>
      match cs $? c_id with
      | Some c => Some (cipher_signing_key c)
      | None   => None
      end
    end.

  Definition msg_destination_user {t} (cs : ciphers) (msg : crypto t) : option user_id :=
    match msg with
    | Content _ => None
    | SignedCiphertext c_id =>
      match cs $? c_id with
      | Some c => Some (cipher_to_user c)
      | None   => None
      end
    end.

  Definition msg_honestly_signed {t} (cs : ciphers) (msg : crypto t) : bool :=
    match msg_signing_key cs msg with
    | Some k => honest_keyb k
    | _ => false
    end.

  Definition msg_to_this_user {t} (cs : ciphers) (to_usr : option user_id) (msg : crypto t) : bool :=
    match msg_destination_user cs msg with
    | Some to_usr' => match to_usr with
                     | None => true
                     | Some to_hon_user => if to_usr' ==n to_hon_user then true else false
                     end
    | _ => false
    end.

  Definition msg_signed_addressed (cs : ciphers) (to_user_id : option user_id) {t} (msg : crypto t) :=
    msg_honestly_signed cs msg && msg_to_this_user cs to_user_id msg.

  Definition keys_mine (my_perms key_perms: key_perms) : Prop :=
    forall k_id kp,
      key_perms $? k_id = Some kp
    ->  my_perms $? k_id = Some kp
    \/ (my_perms $? k_id = Some true /\ kp = false).

  Definition cipher_honestly_signed (c : cipher) : bool :=
    match c with
    | SigCipher k_id _ _ _              => honest_keyb k_id
    | SigEncCipher k__signid k__encid _ _ _ => honest_keyb k__signid
    end.

  Definition ciphers_honestly_signed :=
    Forall_natmap (fun c => cipher_honestly_signed c = true).

  Inductive msg_pattern_safe : msg_pat -> Prop :=
  | HonestlySignedSafe : forall k,
        honest_key honestk k
      -> msg_pattern_safe (Signed k true)
  | HonestlySignedEncryptedSafe : forall k__sign k__enc,
        honest_key honestk k__sign
      -> msg_pattern_safe (SignedEncrypted k__sign k__enc true)
  .

End SafeMessages.

Inductive user_cmd_type :=
| Base (t : type)
| Message (t : type)
| Crypto (t : type)
| UPair (t1 t2 : user_cmd_type)
.

Fixpoint denote (t : user_cmd_type) :=
  match t with
  | Base t' => message.typeDenote t'
  | Message t' => message t'
  | Crypto t' => crypto t'
  | UPair t1 t2 => (denote t1 * denote t2)%type
  end
.

Declare Scope realworld_scope.
Notation "<< t >>" := (denote t) (at level 75) : realworld_scope.
Delimit Scope realworld_scope with realworld.
Open Scope realworld_scope.

Inductive user_cmd : user_cmd_type -> Type :=
(* Plumbing *)
| Return {A} (res : <<A>>%realworld) : user_cmd A
| Bind {A A'} (cmd1 : user_cmd A') (cmd2 : <<A'>>%realworld -> user_cmd A) : user_cmd A

| Gen : user_cmd (Base Nat)

(* Messaging *)
| Send {t} (uid : user_id) (msg : crypto t) : user_cmd (Base Unit)
| Recv {t} (pat : msg_pat) : user_cmd (Crypto t)

(* Crypto!! *)
| SignEncrypt {t} (k__sign k__enc : key_identifier) (msg_to : user_id) (msg : message t) : user_cmd (Crypto t)
| Decrypt {t} (c : crypto t) : user_cmd (Message t)

| Sign    {t} (k : key_identifier) (msg_to : user_id) (msg : message t) : user_cmd (Crypto t)
| Verify  {t} (k : key_identifier) (c : crypto t) : user_cmd (UPair (Base Bool) (Message t))

| GenerateKey (kt : key_type) (usage : key_usage) : user_cmd (Base Access)
.

Module RealWorldNotations.
  Ltac denoteInvert T :=
    match T with
      | key_permission => exact (Base Access)
      | bool => exact (Base Bool)
      | nat => exact (Base Nat)
      | unit => exact (Base Unit)
      | (?T1 * ?T2)%type =>
        exact (UPair ltac:(denoteInvert T1) ltac:(denoteInvert T2))
      end
  .
  Ltac typeOf x :=
    match type of x with
    | ?T => denoteInvert T
    end
  .
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75) : realworld_scope.
  Notation "'ret' x" := (@Return ltac:(typeOf x) x) (at level 75, only parsing) : realworld_scope.
End RealWorldNotations.
Import  RealWorldNotations.

Record user_data (A : type) :=
  mkUserData {
      key_heap  : key_perms
    ; protocol  : user_cmd (Base A)
    ; msg_heap  : queued_messages
    ; c_heap    : my_ciphers
    ; from_nons : recv_nonces
    ; sent_nons : sent_nonces
    ; cur_nonce : nat
    }.

Definition honest_users A := user_list (user_data A).

Record simpl_universe A :=
  mkSimplUniverse {
      s_users       : honest_users A
    ; s_all_ciphers : ciphers
    ; s_all_keys    : keys
    }.

Record universe A B :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : user_data B
    ; all_ciphers : ciphers
    ; all_keys    : keys
    }.

Definition peel_adv {A B} (U : universe A B) : simpl_universe A :=
   {| s_users       := U.(users)
    ; s_all_ciphers := U.(all_ciphers)
    ; s_all_keys    := U.(all_keys) |}.

Definition findUserKeys {A} (us : user_list (user_data A)) : key_perms :=
  fold (fun u_id u ks => ks $k++ u.(key_heap)) us $0.

Definition addUserKeys {A} (ks : key_perms) (u : user_data A) : user_data A :=
  {| key_heap  := u.(key_heap) $k++ ks
   ; protocol  := u.(protocol)
   ; msg_heap  := u.(msg_heap)
   ; c_heap    := u.(c_heap)
   ; from_nons := u.(from_nons)
   ; sent_nons := u.(sent_nons)
   ; cur_nonce := u.(cur_nonce)
  |}.

Definition addUsersKeys {A} (us : user_list (user_data A)) (ks : key_perms) : user_list (user_data A) :=
  map (addUserKeys ks) us.

Fixpoint findKeysMessage {t} (msg : message t) : key_perms :=
  match msg with
  | message.Permission k => $0 $+ (fst k, snd k) 
  | message.Content _ => $0
  | message.MsgPair m1 m2 => findKeysMessage m1 $k++ findKeysMessage m2
  end.

Definition findKeysCrypto {t} (cs : ciphers) (msg : crypto t) : key_perms :=
  match msg with
  | Content  m          => findKeysMessage m
  | SignedCiphertext c_id  =>
    match cs $? c_id with
    | Some (SigCipher _ _ _ m) => findKeysMessage m
    | _ => $0
    end
  end.

Definition findCiphers {t} (msg : crypto t) : my_ciphers :=
  match msg with
  | Content _          => []
  | SignedCiphertext c => [c]
  end.

Definition findMsgCiphers {t} (msg : crypto t) : queued_messages :=
  match msg with
  | Content _          => []
  | SignedCiphertext _ => [existT _ _ msg]
  end.

Definition user_keys {A} (usrs : honest_users A) (u_id : user_id) : option key_perms :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(key_heap)
  | None     => None
  end.

Definition user_queue {A} (usrs : honest_users A) (u_id : user_id) : option queued_messages :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(msg_heap)
  | None     => None
  end.

Definition user_cipher_queue {A} (usrs : honest_users A) (u_id : user_id) : option my_ciphers :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(c_heap)
  | None     => None
  end.

Definition buildUniverse {A B}
           (usrs : honest_users A) (adv : user_data B) (cs : ciphers) (ks : keys)
           (u_id : user_id) (userData : user_data A) : universe A B :=
  {| users        := usrs $+ (u_id, userData)
   ; adversary    := adv
   ; all_ciphers  := cs
   ; all_keys     := ks
   |}.

Definition buildUniverseAdv {A B}
           (usrs : honest_users A) (cs : ciphers) (ks : keys)
           (userData : user_data B) : universe A B :=
  {| users        := usrs
   ; adversary    := userData
   ; all_ciphers  := cs
   ; all_keys     := ks
   |}.

Definition updateTrackedNonce {t} (to_usr : option user_id) (froms : recv_nonces) (cs : ciphers) (msg : crypto t) :=
  match msg with
  | Content _ => froms
  | SignedCiphertext c_id =>
    match cs $? c_id with
    | None => froms
    | Some c =>
      match to_usr with
      | None => froms
      | Some to_uid =>
        if to_uid ==n cipher_to_user c
        then match count_occ msg_seq_eq froms (cipher_nonce c) with
             | 0 => cipher_nonce c :: froms
             | _ => froms
             end
        else froms
      end                
    end
  end.

Definition updateSentNonce {t} (to_usr : option user_id) (sents : sent_nonces) (cs : ciphers) (msg : crypto t) :=
  match msg with
  | Content _ => sents
  | SignedCiphertext c_id =>
    match cs $? c_id with
    | None => sents
    | Some c =>
      match to_usr with
      | None => sents
      | Some to_uid =>
        if to_uid ==n cipher_to_user c
        then cipher_nonce c :: sents
        else sents
      end                
    end
  end.


Definition msg_nonce_not_same (new_cipher : cipher) (cs : ciphers) {t} (msg : crypto t) : Prop :=
  forall c_id c,
    msg = SignedCiphertext c_id
    -> cs $? c_id = Some c
    -> cipher_nonce new_cipher <> cipher_nonce c.

Definition msg_nonce_same (new_cipher : cipher) (cs : ciphers) {t} (msg : crypto t) : Prop :=
  forall c_id c,
      msg = SignedCiphertext c_id
    -> cs $? c_id = Some c
    -> cipher_nonce new_cipher = cipher_nonce c.

Definition msg_not_replayed {t} (to_usr : option user_id) (cs : ciphers) (froms : recv_nonces) (msg : crypto t) (msgs : queued_messages) : Prop :=
  exists c_id c,
      msg = SignedCiphertext c_id
    /\ cs $? c_id = Some c
    /\ ~ List.In (cipher_nonce c) froms
    /\ Forall (fun sigM => match sigM with
                       | (existT _ _ m) => msg_to_this_user cs to_usr m = true
                                        -> msg_nonce_not_same c cs m
                       end) msgs.

Inductive action : Type :=
| Input  t (msg : crypto t) (pat : msg_pat) (froms : recv_nonces)
| Output t (msg : crypto t) (from_user : option user_id) (to_user : option user_id) (sents : sent_nonces)
.

Definition rlabel := @label action.
Definition uaction := (user_id * action)%type.
Definition ulabel := @label uaction.
Definition mkULbl (lbl : rlabel) (uid : user_id) : ulabel :=
  match lbl with
  | Silent => Silent
  | Action a => Action (uid, a)
  end.

Definition data_step0 A B C : Type :=
  honest_users A * user_data B * ciphers * keys * key_perms * queued_messages * my_ciphers * recv_nonces * sent_nonces * nat * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B (Base C) :=
  (U.(users), U.(adversary), U.(all_ciphers), U.(all_keys),
   u_data.(key_heap), u_data.(msg_heap), u_data.(c_heap), u_data.(from_nons), u_data.(sent_nons), u_data.(cur_nonce), u_data.(protocol)).

Inductive step_user : forall A B C, rlabel -> option user_id -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {A B r r'} (usrs usrs' : honest_users A) (adv adv' : user_data B)
                    lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' sents sents' cur_n cur_n'
                    (cmd1 cmd1' : user_cmd r) (cmd2 : <<r>> -> user_cmd r'),
    step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd1)
                       (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd1')
    -> step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Bind cmd1 cmd2)
                         (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', Bind cmd1' cmd2)
| StepBindProceed : forall {A B r r'} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n
                      (v : <<r'>>) (cmd : <<r'>> -> user_cmd r),
    step_user Silent u_id
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Bind (@Return r' v) cmd)
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd v)

| StepGen : forall {A B} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n n,
    step_user Silent u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Gen)
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs qmsgs' mycs mycs' froms froms'
               sents cur_n (msg : crypto t) msgs__front msgs__back pat newkeys newcs,
      qmsgs = msgs__front ++ (existT _ _ msg) :: msgs__back (* we have a message waiting for us! *)
    -> qmsgs' = msgs__front ++ msgs__back
    -> findKeysCrypto cs msg = newkeys
    -> newcs = findCiphers msg
    -> ks' = ks $k++ newkeys
    -> mycs' = newcs ++ mycs
    -> froms' = updateTrackedNonce u_id froms cs msg
    -> msg_accepted_by_pattern cs u_id froms pat msg
    -> Forall (fun '(existT _ _ msg')  => ~ msg_accepted_by_pattern cs u_id froms pat msg') msgs__front
    -> step_user (Action (Input msg pat froms)) u_id
                (usrs, adv, cs, gks, ks , qmsgs , mycs, froms, sents, cur_n,  Recv pat)
                (usrs, adv, cs, gks, ks', qmsgs', mycs', froms', sents, cur_n, @Return (Crypto t) msg)


(* Augment attacker's keys with those available through messages sent, *)
(*  * including traversing through ciphers already known by attacker, etc. *)
(*  *)
| StepSend : forall {A B} {t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
               cs suid gks ks qmsgs mycs froms sents sents' cur_n rec_u_id rec_u newkeys (msg : crypto t),
    findKeysCrypto cs msg = newkeys
    -> keys_mine ks newkeys
    -> incl (findCiphers msg) mycs
    -> usrs $? rec_u_id = Some rec_u
    -> Some rec_u_id <> suid
    -> sents' = updateSentNonce (Some rec_u_id) sents cs msg
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
    -> step_user (Action (Output msg suid (Some rec_u_id) sents)) suid
                (usrs , adv , cs, gks, ks, qmsgs, mycs, froms, sents,  cur_n, Send rec_u_id msg)
                (usrs', adv', cs, gks, ks, qmsgs, mycs, froms, sents', cur_n, @Return (Base Unit) tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs' froms sents
                  cur_n cur_n' (msg : message t) k__signid k__encid kp__enc kt__enc kt__sign c_id cipherMsg msg_to msg_nonce,
      gks $? k__encid  = Some (MkCryptoKey k__encid Encryption kt__enc)
    -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt__sign)
    -> ks $? k__encid   = Some kp__enc
    -> ks $? k__signid  = Some true
    -> ~ In c_id cs
    -> keys_mine ks (findKeysMessage msg)
    -> cur_n' = 1 + cur_n
    -> (u_id <> None -> msg_nonce = (u_id, cur_n))
    -> cipherMsg = SigEncCipher k__signid k__encid msg_to msg_nonce msg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> mycs' = c_id :: mycs
    -> step_user Silent u_id
                (usrs, adv, cs , gks, ks, qmsgs, mycs,  froms, sents, cur_n,  SignEncrypt k__signid k__encid msg_to msg)
                (usrs, adv, cs', gks, ks, qmsgs, mycs', froms, sents, cur_n', @Return (Crypto t) (SignedCiphertext c_id))

| StepDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs mycs mycs'
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
    -> step_user Silent u_id
                (usrs, adv, cs, gks, ks , qmsgs, mycs,  froms, sents, cur_n, Decrypt (SignedCiphertext c_id))
                (usrs, adv, cs, gks, ks', qmsgs, mycs', froms, sents, cur_n, @Return (Message t) msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs'
               froms sents cur_n cur_n' msg_nonce (msg : message t) k_id kt c_id cipherMsg msg_to,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
    -> ks  $? k_id = Some true
    -> ~ In c_id cs
    -> keys_mine ks (findKeysMessage msg)
    -> cur_n' = 1 + cur_n
    -> (u_id <> None -> msg_nonce = (u_id, cur_n))
    -> cipherMsg = SigCipher k_id msg_to msg_nonce msg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> mycs' = c_id :: mycs
    -> step_user Silent u_id
                (usrs, adv, cs , gks, ks, qmsgs, mycs,  froms, sents, cur_n,  Sign k_id msg_to msg)
                (usrs, adv, cs', gks, ks, qmsgs, mycs', froms, sents, cur_n', @Return (Crypto t) (SignedCiphertext c_id))

| StepVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs froms sents cur_n
                 (msg : message t) k_id kp kt c_id nonce msg_to,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
    -> ks  $? k_id = Some kp
    -> cs $? c_id = Some (SigCipher k_id msg_to nonce msg)
    -> List.In c_id mycs
    -> step_user Silent u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, Verify k_id (SignedCiphertext c_id))
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, @Return (UPair (Base Bool) (Message t))(true, msg))

| StepGenerateKey: forall {A B} (usrs : honest_users A) (adv : user_data B)
                     cs u_id gks gks' ks ks' qmsgs mycs froms sents cur_n
                     (k_id : key_identifier) k kt usage,
    gks $? k_id = None
    -> k = MkCryptoKey k_id usage kt
    -> gks' = gks $+ (k_id, k)
    -> ks' = add_key_perm k_id true ks
    -> step_user Silent u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, GenerateKey kt usage)
                (usrs, adv, cs, gks', ks', qmsgs, mycs, froms, sents, cur_n, @Return (Base Access) (k_id, true))

.

Inductive step_universe {A B} : option user_id -> universe A B -> ulabel -> universe A B -> Prop :=
| StepUser : forall U U' (u_id : user_id) userData usrs adv cs gks ks qmsgs mycs froms sents cur_n lbl lbl' (cmd : user_cmd (Base A)),
    U.(users) $? u_id = Some userData
    -> step_user lbl (Some u_id)
                (build_data_step U userData)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
    -> U' = buildUniverse usrs adv cs gks u_id {| key_heap  := ks
                                               ; msg_heap  := qmsgs
                                               ; protocol  := cmd
                                               ; c_heap    := mycs
                                               ; from_nons := froms
                                               ; sent_nons := sents
                                               ; cur_nonce := cur_n |}
    -> lbl' = mkULbl lbl u_id
    -> step_universe (Some u_id) U lbl' U'
| StepAdversary : forall U U' usrs adv cs gks ks qmsgs mycs froms sents cur_n lbl (cmd : user_cmd (Base B)),
    step_user lbl None
              (build_data_step U U.(adversary))
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
    -> U' = buildUniverseAdv usrs cs gks {| key_heap  := ks
                                         ; msg_heap  := qmsgs
                                         ; protocol  := cmd
                                         ; c_heap    := mycs
                                         ; from_nons := froms
                                         ; sent_nons := sents
                                         ; cur_nonce := cur_n |}
    -> step_universe None U Silent U'
.
