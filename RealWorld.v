From Coq Require Import String.
Require Import Frap.
Set Implicit Arguments.

Definition user_id        := nat.
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
| Return {result : Type} (r : result) : user_cmd result
| Bind {result result' : Type} (c1 : user_cmd result') (c2 : result' -> user_cmd result) : user_cmd result

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

Record user_data := mkUserData {
  usrid    : user_id ;
  key_heap : fmap nat key ;
  protocol : user_cmd unit ;
  (* msg_heap : user_msg_heap ; *)
  (* is_admin : bool *)
}.

Inductive cipher : Type :=
| Cipher {A: Set} (c_id : cipher_id) (k_id : key_identifier) (msg : message A) : cipher
.

Definition queued_messages := fmap user_id (list exmsg).
Definition keys            := fmap key_identifier key.
Definition ciphers         := fmap cipher_id cipher.

Record universe := mkUniverse {
  users            : fmap user_id user_data ;
  users_msg_buffer : queued_messages ;
  all_keys         : keys ;
  all_ciphers      : ciphers
}.

(* This is horribly inefficient, but I want the list to act like a queue.  We want
 * first in - first out semantics to keep message order preserved *)
Definition multiMapAdd {K V} (k : K)(v : V)(m : fmap K (list V)) : fmap K (list V) :=
  match m $? k with
  | None => m $+ (k, [v])
  | Some vs => m $+ (k, vs ++ [v]) (* add new element to end, to preserve order *)
  end.

(* When we are finding keys, we need to check whether they are asymmetric.  If
   so, we mark them as not having access to the private key, since the intent is to
   send only the public part of the key *)
Fixpoint findKeys {A} (msg : message A) : list key :=
  match msg with
  | Plaintext pt       => []

  | KeyMessage (AsymKey k' _) => [AsymKey k' false] (* Only sending public keys *)
  | KeyMessage k       => [k]
  | MsgPair msg1 msg2  => findKeys msg1 ++ findKeys msg2
  | Ciphertext _       => []
  | Signature _        => []
  end.

Definition updateKeyHeap (ks : list key) (key_heap : keys) : keys :=
  let addKey (m : keys) (k : key) :=
      match k with
      | SymKey k'     => m $+ (k'.(key_id), k)
      | AsymKey k' b  => m $+ (k'.(key_id), k)
      end
  in  fold_left addKey ks key_heap.

Definition updateUserKeyHeap (ks : list key) (ud : user_data) : user_data :=
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

Definition canVerifySignature (ciphers : fmap cipher_id cipher)(usrDat : user_data)(c_id : cipher_id) : Prop :=
  forall {A} (m : message A) k_id k ,
    ciphers $? c_id = Some (Cipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Inductive step_user :
  forall A, ciphers * keys * queued_messages * user_data * user_cmd A
       -> ciphers * keys * queued_messages * user_data * user_cmd A -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {r r'} cs cs' ks ks' msgs msgs' usrDat usrDat' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
    step_user (cs, ks, msgs, usrDat, cmd1) (cs', ks', msgs', usrDat', cmd1')
    -> step_user (cs, ks, msgs, usrDat, Bind cmd1 cmd2) (cs', ks', msgs', usrDat', Bind cmd1' cmd2)
| StepBindProceed : forall {r r'} cs ks msgs usrDat usrDat' (v : r') (cmd : r' -> user_cmd r),
    step_user (cs, ks, msgs, usrDat, Bind (Return v) cmd) (cs, ks, msgs, usrDat', cmd v)

(* Comms *)
| StepRecv : forall {A} cs ks qmsgs usrDat (msg : message A) msgs newkeys,
    qmsgs $? usrDat.(usrid) = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> findKeys msg = newkeys
    -> step_user (cs, ks, qmsgs, usrDat, Recv)
                (cs, ks, qmsgs $+ (usrDat.(usrid), msgs), updateUserKeyHeap newkeys usrDat, Return msg)
| StepSend : forall {A} cs ks qmsgs usrDat u_id (msg : message A),
    step_user (cs, ks, qmsgs, usrDat, Send u_id msg) (cs, ks, multiMapAdd u_id (Exm msg) qmsgs, usrDat, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k k_id c_id cipherMsg,
    usrDat.(key_heap) $? k_id = Some k
    -> ~(c_id \in (dom cs))
    -> encryptMessage k msg c_id = Some cipherMsg
    -> step_user (cs, ks, qmsgs, usrDat, Encrypt k msg)
                (cs $+ (c_id, cipherMsg), ks, qmsgs, usrDat, Return (Ciphertext c_id))

| StepSymmetricDecrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k_id k c_id newkeys,
    cs $? c_id = Some (Cipher c_id k_id msg)
    -> usrDat.(key_heap) $? k_id = Some (SymKey k)
    -> findKeys msg = newkeys (* find keys in new key heap *)
    -> step_user (cs, ks, qmsgs, usrDat, Decrypt (Ciphertext c_id))
                (cs, ks, qmsgs, updateUserKeyHeap newkeys usrDat, Return msg)

| StepAsymmetricDecrypt : forall {A} cs ks qmsgs usrDat (msg : message A) k_id k c_id newkeys,
    cs $? c_id = Some (Cipher c_id k_id msg)
    -> usrDat.(key_heap) $? k_id = Some (AsymKey k true) (* check we have access to private key *)
    -> findKeys msg = newkeys
    -> step_user (cs, ks, qmsgs, usrDat, Decrypt (Ciphertext c_id))
                (cs, ks, qmsgs, updateUserKeyHeap newkeys usrDat, Return msg)

(* Signing / Verification *)
| StepSign : forall {A} cs ks qmsgs usrDat k_id k (msg : message A) c_id cipherMsg,
    usrDat.(key_heap) $? k_id = Some k
    -> ~(c_id \in (dom cs))
    -> signMessage k msg c_id = Some cipherMsg
    -> step_user (cs, ks, qmsgs, usrDat, Sign k msg)
                (cs $+ (c_id, cipherMsg), ks, qmsgs, usrDat, Return (Signature c_id))
| StepVerify : forall cs ks qmsgs usrDat c_id,
    canVerifySignature cs usrDat c_id
    -> step_user (cs, ks, qmsgs, usrDat, Verify (Signature c_id)) (cs, ks, qmsgs, usrDat, Return true)
| StepFailVerify : forall cs ks qmsgs usrDat c_id,
    ~ canVerifySignature cs usrDat c_id
    -> step_user (cs, ks, qmsgs, usrDat, Verify (Signature c_id)) (cs, ks, qmsgs, usrDat, Return false)
| StepFailVerifyNotSig : forall cs ks qmsgs usrDat c_id msg,
    ~ msg <> Signature c_id
    -> step_user (cs, ks, qmsgs, usrDat, Verify msg) (cs, ks, qmsgs, usrDat, Return false)

(* Key creation *)
| StepGenerateSymKey: forall cs ks qmsgs usrDat usage k kid,
    ~(kid \in (dom ks))
    -> k = SymKey (MkCryptoKey kid usage)
    -> step_user (cs, ks, qmsgs, usrDat, GenerateSymKey usage) (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k)
| StepGenerateAsymKey: forall cs ks qmsgs usrDat usage k kid,
    ~(kid \in (dom ks))
    -> k = AsymKey (MkCryptoKey kid usage) true
    -> step_user (cs, ks, qmsgs, usrDat, GenerateAsymKey usage) (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k)
 
(* | Barrier {result : Set} : user_cmd result. *)
.

Definition updateUniverse (U : universe) (cs : ciphers) (ks : keys) (qmsgs : queued_messages) (user : user_data) : universe :=
  {|
     users            := U.(users) $+ (user.(usrid), user)
   ; users_msg_buffer := qmsgs
   ; all_keys         := ks
   ; all_ciphers      := cs
  |}.

Inductive step_universe : universe -> universe -> Prop :=
| StepUser : forall {A} U u_id userData userData' cs ks qmsgs (cmd cmd' : user_cmd A),
    U.(users) $? u_id = Some userData
    -> step_user (U.(all_ciphers), U.(all_keys), U.(users_msg_buffer), userData, cmd) (cs, ks, qmsgs, userData', cmd')
    -> step_universe U (updateUniverse U cs ks qmsgs userData')
.


(* Additional functionality to implement:
   1. Administration
   2. CA
*) 
