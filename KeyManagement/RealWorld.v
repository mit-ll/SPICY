From Coq Require Import String.
Require Import Frap.
Require Import Common.

Set Implicit Arguments.

Definition key_identifier := nat.
Definition cipher_id      := nat.

Inductive key_usage :=
| Encryption
| Signing
.

Record cryptographic_key := MkCryptoKey {
                                key_id : key_identifier ;
                                usage  : key_usage
                              }.

(* A master key type *)
Inductive key :=
| SymKey   (k : cryptographic_key)
| AsymKey  (k : cryptographic_key) (has_private_access : bool)
.

(** How are we going to model encryption / decryption in this framework?  Each key has
    associated with it either:
    - a key id (in the case of a symmetric key)
    - a public/privite key pair (in the case of an asymmetric key)

    In order for us to share a secret, we need to appropriately hide that secret so that
    it cannot be viewed by eavesdroppers.  At the same time, for the purposes of this model
    we are creating, we need to be able to detect very simply whether a decryption has been
    successful.  The way we are going to do this, conceptually, is to include the key_id as
    part of the message, and have the decryption step relation check whether that key_id
    exists in the user's key heap.  Let's work out more precisely what happens in the two
    cases:  symmetric and asymmetric keys.
   
    * Symmetric Key encryption / decryption

    If I want to encrypt something and share it with someone else using a symmetric key, we
    first have to generate the key and securely share it.  Ignoring things like usage and
    the actual sharing process, the steps are:
    - Generate symmetric key: private_key : symmetric_key := k (system adds to user's key heap)
    - Securely share k (via Sym_Key_Msg, system adds to user's key heap)
    - Sending user encrypts with k
    - Sending user sends encrypted message to receiving user
    - Receiving user decrypts with k (system verifies k is in decrypting user's key heap)

    * Asymmetric Key encryption / decryption

    Sharing a secret via asymmetric keys has a few more steps, but no 'magical' ones.  Each
    user generates public/private key pairs, exchange the public parts, and encrypts with
    a combination of own private key / destination user's public key.  The steps in more
    detail:
    - UserA generates key:
        (pub_key_id, priv_key_id) : (nat,nat) := (pubIdA,privIdA)
    - UserB generates key:
        (pub_key_id, priv_key_id) : (nat,nat) := (pubIdB,privIdB)
    - UserA publicly sends to UserB pubIdA
    - UserB publicly sends to UserA pubIdB
    - UserA encrypts message with pubIdB, sends to UserB
    - UserB decrypts reeived message with privIdB
 *)

(* Messages ultimately wrap either a string or a key 
   Messages can be encrypted, signed, or HMACed in a nested fashion any number of times 
   Note: the key_pair_message constructor is temporary and will be removed *)
Inductive message : Set -> Type :=
(* Base Message Types *)
| Plaintext {A : Set} (txt : A) : message A
| KeyMessage  (k : key) : message key

| MsgPair {A B : Set} (msg1 : message A) (msg2 : message B) : message (A*B)

(* TODO tbraje: is there a way to collapse these two?? *)
| Ciphertext (msg_id : cipher_id) : message cipher_id
| Signature  (sig_id : cipher_id) : message cipher_id
.

Inductive user_cmd : Type -> Type :=
(* Plumbing *)
| Return {A : Type} (res : A) : user_cmd A
| Bind {A A' : Type} (cmd1 : user_cmd A') (cmd2 : A' -> user_cmd A) : user_cmd A

(* Messaging *)
| Send {A : Set} (uid : user_id) (msg : message A) : user_cmd unit
| Recv {A : Set}: user_cmd (message A)

(* Crypto!! *)
| Encrypt {A : Set} (k : key) (msg : message A) : user_cmd (message cipher_id)
| Decrypt {A : Set} (msg : message cipher_id) : user_cmd (message A)

| Sign    {A : Set} (k : key) (msg : message A) : user_cmd (message cipher_id)
| Verify  (msg : message cipher_id) : user_cmd bool

| GenerateSymKey  (usage : key_usage) : user_cmd key
| GenerateAsymKey (usage : key_usage) : user_cmd key

(* Allow administrator to make some global change to the universe -- revoke keys, etc. *)
(* This may be a universe level step -- Administrator forces all users to stop *)
(* | Barrier {result : Set} : user_cmd result *)
.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

(* Exisistential wrapper for message, so we can put it in collections *)
(* This feels overly complicated to me... *) 
Inductive exmsg : Type :=
| Exm {A : Set} (msg : message A) : exmsg.

Check ($0 $+ (1, Exm (Plaintext "foo")) $+ (2, Exm (Plaintext 1))).

Record user_data (A : Type) :=
  mkUserData {
      usrid    : user_id ;
      key_heap : fmap nat key ;
      protocol : user_cmd A ;
      (* msg_heap : user_msg_heap ; *)
      (* is_admin : bool *)
    }.

Inductive cipher : Type :=
| Cipher {A: Set} (c_id : cipher_id) (k_id : key_identifier) (msg : message A) : cipher
.

Definition queued_messages := fmap user_id (list exmsg).
Definition keys            := fmap key_identifier key.
Definition ciphers         := fmap cipher_id cipher.

Record universe (A : Type) :=
  mkUniverse {
      users            : user_list (user_data A) ;
      users_msg_buffer : queued_messages ;
      all_keys         : keys ;
      all_ciphers      : ciphers
    }.

(* This is horribly inefficient, but I want the list to act like a queue.  We want
 * first in - first out semantics to keep message order preserved *)
Local Definition multiMapAdd {K V} (k : K)(v : V)(m : fmap K (list V)) : fmap K (list V) :=
  match m $? k with
  | None => m $+ (k, [v])
  | Some vs => m $+ (k, vs ++ [v]) (* add new element to end, to preserve order *)
  end.

(* When we are finding keys, we need to check whether they are asymmetric.  If
   so, we mark them as not having access to the private key, since the intent is to
   send only the public part of the key *)
Local Fixpoint findKeys {A} (msg : message A) : list key :=
  match msg with
  | Plaintext pt       => []

  | KeyMessage (AsymKey k' _) => [AsymKey k' false] (* Only sending public keys *)
  | KeyMessage k       => [k]
  | MsgPair msg1 msg2  => findKeys msg1 ++ findKeys msg2
  | Ciphertext _       => []
  | Signature _        => []
  end.

Local Definition updateKeyHeap (ks : list key) (key_heap : keys) : keys :=
  let addKey (m : keys) (k : key) :=
      match k with
      | SymKey k'     => m $+ (k'.(key_id), k)
      | AsymKey k' b  => m $+ (k'.(key_id), k)
      end
  in  fold_left addKey ks key_heap.

Local Definition updateUserKeyHeap {A : Set} (ks : list key) (ud : user_data A) : user_data A :=
  {| usrid    := ud.(usrid)
     ; key_heap := updateKeyHeap ks ud.(key_heap)
     ; protocol := ud.(protocol)
  |}.

Definition encryptMessage {A} (k : key) (m : message A) (c_id : cipher_id) : option cipher :=
  match k with
  | SymKey k'  =>
    match (usage k') with
    | Encryption => Some (Cipher c_id k'.(key_id) m)
    | _          => None
    end
  | AsymKey k' _ => (* Encryption always uses the public part of an asymmetric key *)
    match (usage k') with
    | Encryption => Some (Cipher c_id k'.(key_id) m)
    | _          => None
    end
  end.

Definition signMessage {A} (k : key) (m : message A) (c_id : cipher_id) : option cipher :=
  match k with
  | SymKey k'  =>
    match (usage k') with
    | Signing => Some (Cipher c_id k'.(key_id) m)
    | _       => None
    end
  | AsymKey k' true => (* Signing requires private key, so check we have access *)
    match (usage k') with
    | Signing => Some (Cipher c_id k'.(key_id) m)
    | _       => None
    end
  | _ => None
  end.

Definition canVerifySignature {A} (ciphers : fmap cipher_id cipher)(usrDat : user_data A)(c_id : cipher_id) : Prop :=
  forall {A} (m : message A) k_id k ,
    ciphers $? c_id = Some (Cipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Definition data_step0 (A : Type) : Type := 
  ciphers * keys * queued_messages * fmap nat key * user_cmd A.

Inductive step_user : forall A, user_id -> data_step0 A -> data_step0 A -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {r r'} u_id cs cs' ks ks' msgs msgs' uks uks' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
    step_user u_id (cs, ks, msgs, uks, cmd1) (cs', ks', msgs', uks', cmd1')
    -> step_user u_id (cs, ks, msgs, uks, Bind cmd1 cmd2) (cs', ks', msgs', uks', Bind cmd1' cmd2)
| StepBindProceed : forall {r r'} u_id cs ks msgs uks (v : r') (cmd : r' -> user_cmd r),
    step_user u_id (cs, ks, msgs, uks, Bind (Return v) cmd) (cs, ks, msgs, uks, cmd v)

(* Comms *)
| StepRecv : forall {A} u_id cs ks qmsgs uks (msg : message A) msgs newkeys,
    qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> findKeys msg = newkeys
    -> step_user u_id (cs, ks, qmsgs, uks, Recv)
                     (cs, ks, qmsgs $+ (u_id, msgs), updateKeyHeap newkeys uks, Return msg)
| StepSend : forall {A} u_id cs ks qmsgs rec_u_id uks (msg : message A),
    step_user u_id (cs, ks, qmsgs, uks, Send rec_u_id msg)
                   (cs, ks, multiMapAdd rec_u_id (Exm msg) qmsgs, uks, Return tt)

(* Encryption / Decryption *)
(* | StepEncrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k k_id c_id cipherMsg, *)
(*     usrDat.(key_heap) $? k_id = Some k *)
(*     -> ~(c_id \in (dom cs)) *)
(*     -> encryptMessage k msg c_id = Some cipherMsg *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Encrypt k msg) *)
(*                 (cs $+ (c_id, cipherMsg), ks, qmsgs, usrDat, Return (Ciphertext c_id)) *)

(* | StepSymmetricDecrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k_id k c_id newkeys, *)
(*     cs $? c_id = Some (Cipher c_id k_id msg) *)
(*     -> usrDat.(key_heap) $? k_id = Some (SymKey k) *)
(*     -> findKeys msg = newkeys (* find keys in new key heap *) *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Decrypt (Ciphertext c_id)) *)
(*                 (cs, ks, qmsgs, updateUserKeyHeap newkeys usrDat, Return msg) *)

(* | StepAsymmetricDecrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k_id k c_id newkeys, *)
(*     cs $? c_id = Some (Cipher c_id k_id msg) *)
(*     -> usrDat.(key_heap) $? k_id = Some (AsymKey k true) (* check we have access to private key *) *)
(*     -> findKeys msg = newkeys *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Decrypt (Ciphertext c_id)) *)
(*                 (cs, ks, qmsgs, updateUserKeyHeap newkeys usrDat, Return msg) *)

(* Signing / Verification *)
(* | StepSign : forall {A} cs ks qmsgs usrDat k_id k (msg : message A) c_id cipherMsg, *)
(*     usrDat.(key_heap) $? k_id = Some k *)
(*     -> ~(c_id \in (dom cs)) *)
(*     -> signMessage k msg c_id = Some cipherMsg *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Sign k msg) *)
(*                 (cs $+ (c_id, cipherMsg), ks, qmsgs, usrDat, Return (Signature c_id)) *)
(* | StepVerify : forall cs ks qmsgs usrDat c_id, *)
(*     canVerifySignature cs usrDat c_id *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Verify (Signature c_id)) *)
(*                 (cs, ks, qmsgs, usrDat, Return true) *)
(* | StepFailVerify : forall cs ks qmsgs usrDat c_id, *)
(*     ~ canVerifySignature cs usrDat c_id *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Verify (Signature c_id)) *)
(*                 (cs, ks, qmsgs, usrDat, Return false) *)
(* | StepFailVerifyNotSig : forall cs ks qmsgs usrDat c_id msg, *)
(*     ~ msg <> Signature c_id *)
(*     -> step_user (cs, ks, qmsgs, usrDat, Verify msg) *)
(*                 (cs, ks, qmsgs, usrDat, Return false) *)

(* Key creation *)
(* | StepGenerateSymKey: forall A cs ks qmsgs (usrDat : user_data A) usage k kid, *)
(*     ~(kid \in (dom ks)) *)
(*     -> k = SymKey (MkCryptoKey kid usage) *)
(*     -> step_user (cs, ks, qmsgs, usrDat, GenerateSymKey usage) *)
(*                 (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k) *)
(* | StepGenerateAsymKey: forall {a : Set} cs ks qmsgs (usrDat : user_data a) usage k kid, *)
(*     ~(kid \in (dom ks)) *)
(*     -> k = AsymKey (MkCryptoKey kid usage) true *)
(*     -> step_user (cs, ks, qmsgs, usrDat, GenerateAsymKey usage) *)
(*                 (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k) *)
                
(* | Barrier {result : Set} : user_cmd result. *)
.

Definition updateUniverse {A} (U : universe A) (cs : ciphers) (ks : keys) (qmsgs : queued_messages)
                          (u_id : user_id) (userKeys : keys) (cmd : user_cmd A): universe A :=
  {|
    users            := updateUserList U.(users) u_id ( mkUserData u_id userKeys cmd )
  ; users_msg_buffer := qmsgs
  ; all_keys         := ks
  ; all_ciphers      := cs
  |}.

Inductive step_universe {A} : universe A -> universe A -> Prop :=
| StepUser : forall U u_id userData uks cs ks qmsgs (cmd cmd' : user_cmd A),
    In (u_id,userData) U.(users)
    (* U.(users) $? u_id = Some userData *)
    -> step_user u_id (U.(all_ciphers), U.(all_keys), U.(users_msg_buffer), userData.(key_heap), cmd)
                     (cs, ks, qmsgs, uks, cmd')
    -> step_universe U (updateUniverse U cs ks qmsgs u_id uks cmd')
.

Definition extractPlainText {A} (msg : message A) : option A :=
  match msg with
  | Plaintext t => Some t
  | _           => None
  end.



Section PingProtocol.

  Example ping : list (user_data nat) :=
    {| usrid    := 0
     ; key_heap := $0
     ; protocol := (  _ <- Send 1 (Plaintext 1)
                    ; rec <- Recv (A := nat)
                    ; Return (match extractPlainText rec with
                              | (Some msg) => msg
                              | None       => 99
                              end))
    |}
      ::
    {| usrid    := 1
     ; key_heap := $0
     ; protocol := (  rec <- Recv (A := nat)
                    ; _ <- Send 0 (Plaintext 0)
                    ; Return (match extractPlainText rec with
                              | Some msg => msg
                              | None     => 98
                              end))
    |}
      :: [].

  Example ping_universe : universe nat :=
    {|
      users            := map (fun u_d => (u_d.(usrid), u_d)) ping
    ; users_msg_buffer := $0
    ; all_keys         := $0
    ; all_ciphers      := $0
    |}.

  Check ping_universe.

End PingProtocol.

(* Additional functionality to implement:
   1. Administration
   2. CA
*) 
