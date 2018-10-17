From Coq Require Import String.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := nat.

Definition key_id              := nat.
Definition symmetric_key_id    := nat.
Definition asymmetric_key_id   := nat.
Definition asym_public_key_id  := nat.
Definition asym_private_key_id := nat.

Definition signed_message_id    := nat.
Definition encrypted_message_id := nat.
Definition hmac_message_id      := nat.

(* Possible usages for symmetric keys *)
Inductive symmetric_usage :=
| AES_GCM
| AES_CTR
| AES_KW
| HMAC.

(* Possible usages for asymmetric keys *)
Inductive asymmetric_usage :=
| RSA_Encryption
| ECDSA_Signature
.

(* Keys track identifiers, the user_id of the generating user, and a usage *) 
Record symmetric_key := MkSymmetricKey {
  sym_key_id : symmetric_key_id ;
  sym_generating_user_id : user_id ;
  sym_usage : symmetric_usage
  }.

Record asymmetric_public_key := MkAsymmetricPublicKey {
  asym_public_key         : asym_public_key_id;
  asym_key_ref            : asymmetric_key_id;
  asym_generating_user_id : user_id ;
  asym_usage              : asymmetric_usage;
  }.

(* Asymmetric keys track the above but have two parts, public and private *)
Record asymmetric_key := MkAsymmetricKey {
  asym_key_id        : asymmetric_key_id ;
  public_key         : asymmetric_public_key ;
  private_key        : asym_private_key_id
  }.

(* A master key type *)
Inductive key :=
| SymKey     (k : symmetric_key)
| AsymKey    (k : asymmetric_key)
| AsymPubKey (k : asymmetric_public_key).

Definition buildSymmetricKey (k_id : symmetric_key_id) (usage : symmetric_usage) (u_id : user_id) :=
  {|
     sym_key_id             := k_id
   ; sym_generating_user_id := u_id
   ; sym_usage              := usage
  |}.

Definition buildAsymmetricKey (kid1 kid2 kid3 : asym_private_key_id) (usage : asymmetric_usage) (u_id : user_id) :=
  {|
     asym_key_id             := kid1
   ; public_key              := {| asym_key_ref    := kid1
                                 ; asym_public_key := kid2
                                 ; asym_generating_user_id := u_id
                                 ; asym_usage := usage |}
   ; private_key             := kid3
  |}.

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
| Sym_Key_Msg  (k : symmetric_key)   : message symmetric_key
| Asym_Key_Msg (k : asymmetric_key)  : message asymmetric_key

| MsgPair {A B : Set} (msg1 : message A) (msg2 : message B) : message (A*B)

| Ciphertext   (msg_id : encrypted_message_id) : message encrypted_message_id
| Signature    {A : Set} (msg : message A)(sig_id : signed_message_id) : message A
| HMAC_Message {A : Set} (msg : message A)(hmac_id : hmac_message_id) : message A
.
 
Inductive user_cmd : Type -> Type :=
(* Plumbing *)
| Return {result : Type} (r : result) : user_cmd result
| Bind {result result' : Type} (c1 : user_cmd result') (c2 : result' -> user_cmd result) : user_cmd result

(* Messaging *)
| Send {A : Set} (uid : user_id) (msg : message A) : user_cmd unit
| Recv {A : Set}: user_cmd (message A)

(* Crypto!! *)
| Encrypt {A : Set} (k : key) (msg : message A)  : user_cmd (message encrypted_message_id)
| Decrypt {A : Set} (msg : message encrypted_message_id) : user_cmd (message A)

| Sign    {A : Set} (k : key) (msg : message A) : user_cmd (message A)
| Verify  {A : Set} (msg : message A) : user_cmd bool

| ProduceHMAC {A : Set} (k : key) (msg : message A) : user_cmd (message A)
| VerifyHMAC  {A : Set} (msg : message A) : user_cmd bool

| GenerateSymKey (usage : symmetric_usage) : user_cmd symmetric_key
| GenerateAsymKeys (usage : asymmetric_usage) : user_cmd asymmetric_key

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

Definition queued_messages := fmap user_id (list exmsg).
Definition user_msg_heap   := list (user_id * exmsg).

Record user_data := mkUserData {
   usrid    : user_id ;
   key_heap : fmap nat key ;
   protocol : user_cmd unit ;
   (* msg_heap : user_msg_heap ; *)
   (* is_admin : bool *)
   }.

(* The network stores message buffers for each user. Any messages sent to a user are stored here until
   the user calls Recv, at which point they are removed from the buffer and added to the user's msg_heap *)
(* Record network := mkNetwork { *)
(*   users_msg_buffer : queued_messages ; *)
(*   trace            : list (user_id * user_id * message) (* sender / receiver / message *) *)
(* }. *)

Inductive encrypted_message : Type :=
| Enc {A: Set} (key_id : nat) (msg : message A) : encrypted_message
| Sig (key_id  : nat)                   : encrypted_message
| Hmac (key_id : nat)                   : encrypted_message
.

(* The universe consists of some number of users and a network.
   The key_counter is a temporary hack to keep track of key_ids and make sure two users don't generate
   keys with the same id. *)
Record universe := mkUniverse {
    users            : fmap user_id user_data ;
    users_msg_buffer : queued_messages ;
    all_keys         : fmap nat key ;
    encryptions      : fmap nat encrypted_message ; (* used for sigs and hmacs as well *)
}.

(* This is horribly inefficient, but I want the list to act like a queue.  We want
 * first in - first out semantics to keep message order preserved *)
Definition multiMapAdd {K V} (k : K)(v : V)(m : fmap K (list V)) : fmap K (list V) :=
  match m $? k with
  | None => m $+ (k, [v])
  | Some vs => m $+ (k, vs ++ [v]) (* add new element to end, to preserve order *)
  end.

Fixpoint findKeys {A} (msg : message A) : list key :=
  match msg with
  | Plaintext pt       => []

  | Sym_Key_Msg k      => [SymKey k]
  | Asym_Key_Msg k     => [AsymPubKey k.(public_key)]
  | MsgPair msg1 msg2  => findKeys msg1 ++ findKeys msg2
  | Ciphertext _       => []
  | Signature msg _    => findKeys msg
  | HMAC_Message msg _ => findKeys msg
  end.

Definition updateUserKeyHeap (keys : list key) (ud : user_data) : user_data :=
  let addKey (m : fmap nat key) (k : key) :=
        match k with
        | SymKey k'     => m $+ (k'.(sym_key_id),   k)
        (* Add public and private parts of key to user heap *)
        | AsymKey k'    => m $+ (k'.(private_key), k) $+ (k'.(public_key).(asym_public_key), AsymPubKey k'.(public_key))
        | AsymPubKey k' => m $+ (k'.(asym_public_key), k)
        end
  in
    {| usrid    := ud.(usrid)
     ; key_heap := fold_left addKey keys ud.(key_heap)
     ; protocol := ud.(protocol)
    |}.


Definition updateUniverseDeliverMsg {A} (U : universe) (user : user_data) (msg : message A) (msgs : (list exmsg) ) :=
  {|
     users            := U.(users) $+ (user.(usrid), updateUserKeyHeap (findKeys msg) user) (* add sent keys to user's heap *)
   ; users_msg_buffer := U.(users_msg_buffer) $+ (user.(usrid), msgs)
   ; all_keys         := U.(all_keys)
   ; encryptions      := U.(encryptions)
  |}.

Definition updateUniverseCipherMsg (U : universe) (uid : user_id) (cipher_id : nat) (msg: encrypted_message) :=
  {|
     users            := U.(users)
   ; users_msg_buffer := U.(users_msg_buffer)
   ; all_keys         := U.(all_keys)
   ; encryptions      := U.(encryptions) $+ ( cipher_id , msg )
  |}.

Definition updateUniverseSendMsg {A} (U : universe) (uid : user_id) (msg : message A) :=
  {|
     users            := U.(users)
   ; users_msg_buffer := multiMapAdd uid (Exm msg) U.(users_msg_buffer)
   ; all_keys         := U.(all_keys)
   ; encryptions      := U.(encryptions)
  |}.

Definition encryptMessage {A} (k : key) (m : message A) : option encrypted_message :=
  match k with
  | SymKey k'  => match (sym_usage k') with
                 | AES_GCM => Some (Enc k'.(sym_key_id) m)
                 | AES_CTR => Some (Enc k'.(sym_key_id) m)
                 | AES_KW  => Some (Enc k'.(sym_key_id) m)
                 | _       => None
                 end
  | AsymKey k' => None
  | AsymPubKey k' => match (asym_usage k') with
                    | RSA_Encryption => Some (Enc k'.(asym_key_ref) m) (* Need private key to decrypt! *)
                    | _              => None
                    end
  end.

Definition signMessage {A} (k : key) (m : message A) : option encrypted_message :=
  match k with
  | SymKey k'  => None
  | AsymKey k' =>
    let pk := k'.(public_key)
    in  match (asym_usage pk) with
        | ECDSA_Signature => Some (Sig pk.(asym_key_ref))
        | _               => None
        end
  | AsymPubKey k' => None
  end.

Definition hmacMessage {A} (k : key) (m : message A) : option encrypted_message :=
  match k with
  | SymKey k'  => match (sym_usage k') with
                 | HMAC => Some (Hmac k'.(sym_key_id))
                 | _    => None
                 end
  | AsymKey k' => None
  | AsymPubKey k' => None
  end.

Definition updateUniverseNewKey (U : universe) (user : user_data) (k : key) :=
  let addKey (k : key) (m : fmap nat key) :=
      match k with
      | SymKey k'     => m $+ (k'.(sym_key_id),  k)
      | AsymKey k'    => m $+ (k'.(asym_key_id), k)
      | AsymPubKey k' => m
      end
  in
    {|
       users            := U.(users) $+ (user.(usrid), updateUserKeyHeap [k] user)
     ; users_msg_buffer := U.(users_msg_buffer)
     ; all_keys         := addKey k U.(all_keys)
     ; encryptions      := U.(encryptions)
    |}.

Definition canVerifySignature (U : universe)(usrDat : user_data)(sig_id : signed_message_id)(k_id : nat) : Prop :=
  forall k k',
    U.(encryptions) $? sig_id = Some (Sig k_id)
    (* Look up asymmetric key by its global universe identifier *)
    /\ U.(all_keys) $? k_id = Some (AsymKey k)
    (*  Make sure that the user has the public part of the looked up key *)
    /\ usrDat.(key_heap) $? k.(public_key).(asym_public_key) = Some (AsymPubKey k').

Definition canVerifyHMAC (u: universe) (usrDat : user_data) (hmac_id : hmac_message_id) (k_id : nat) : Prop :=
  forall k,
    u.(encryptions) $? hmac_id = Some (Hmac k_id)
    /\ usrDat.(key_heap) $? k_id = Some (SymKey k).

Inductive step_user : forall A, universe * user_data * user_cmd A -> universe * user_cmd A -> Prop :=
(* Plumbing *)
| StepBindRecur : forall result result' U U' usrDat (cmd1 cmd1' : user_cmd result) (cmd2 : result -> user_cmd result'),
    step_user (U, usrDat, cmd1) (U', cmd1')
    -> step_user (U, usrDat, Bind cmd1 cmd2) (U', Bind cmd1' cmd2)
| StepBindProceed : forall result result' U usrDat (v : result') (cmd : result' -> user_cmd result),
    step_user (U, usrDat, Bind (Return v) cmd) (U, cmd v)

(* Comms *)
| StepRecv : forall A U usrDat (msg : message A) msgs,
    U.(users_msg_buffer) $? usrDat.(usrid) = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> step_user (U, usrDat, Recv) (updateUniverseDeliverMsg U usrDat msg msgs, Return msg)
| StepSend : forall A U usrDat u_id (msg : message A),
    step_user (U, usrDat, Send u_id msg) (updateUniverseSendMsg U usrDat.(usrid) msg, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall A U usrDat k_id (msg : message A) enc_id encMsg k,
    usrDat.(key_heap) $? k_id = Some k
    -> encryptMessage k msg = Some encMsg
    (* Generate new msg_id and add message to heap *)
    -> ~(enc_id \in (dom U.(encryptions)))
    -> step_user (U, usrDat, Encrypt k msg)
                (updateUniverseCipherMsg U usrDat.(usrid) enc_id encMsg, Return (Ciphertext enc_id))
| StepSymmetricDecrypt : forall A U usrDat msg k_id k enc_id,
    U.(encryptions) $? enc_id = Some (Enc k_id msg)
    -> usrDat.(key_heap) $? k_id = Some (SymKey k)
    -> step_user (U, usrDat, Decrypt (Ciphertext enc_id)) (U, Return (msg : message A))
| StepAsymmetricDecrypt : forall A U usrDat msg k_id k enc_id,
    U.(encryptions) $? enc_id = Some (Enc k_id msg)
    (* Look up asymmetric key by its global universe identifier *)
    -> U.(all_keys) $? k_id = Some (AsymKey k)
    (*  Make sure that the user has the private part of the looked up key, and they are, in fact, the same key *)
    -> usrDat.(key_heap) $? k.(private_key) = Some (AsymKey k)
    -> step_user (U, usrDat, Decrypt (Ciphertext enc_id)) (U, Return (msg : message A))

(* Signing / Verification *)
| StepSign : forall A U usrDat k_id (msg : message A) k sig_id signedMessage,
    usrDat.(key_heap) $? k_id = Some k
    -> signMessage k msg = Some signedMessage
    -> ~(sig_id \in (dom U.(encryptions)))
    -> step_user (U, usrDat, Sign k msg)
                (updateUniverseCipherMsg U usrDat.(usrid) sig_id signedMessage, Return (Signature msg sig_id))
| StepVerify : forall A U usrDat (msg : message A) k_id sig_id,
    (* u.(encryptions) $? sig_id = Some (Sig k_id) *)
    (* (* Look up asymmetric key by its global universe identifier *) *)
    (* -> u.(all_keys) $? k_id = Some (AsymKey k) *)
    (* (*  Make sure that the user has the public part of the looked up key *) *)
    (* -> usrDat.(key_heap) $? k.(public_key).(asym_public_key) = Some (AsymPubKey k') *)
    (* (* Do I need to check that the public parts of the keys are the same?? *) *)
    canVerifySignature U usrDat sig_id k_id
    -> step_user (U, usrDat, Verify (Signature msg sig_id)) (U, Return true)
| StepFailVerify : forall A U usrDat (msg : message A) k_id sig_id,
    ~ canVerifySignature U usrDat sig_id k_id
    -> step_user (U, usrDat, Verify (Signature msg sig_id)) (U, Return false)
| StepFailVerifyUnsigned : forall A U usrDat (msg1 msg2 : message A) sig_id,
    msg1 <> Signature msg2 sig_id
    -> step_user (U, usrDat, Verify msg1) (U, Return false)

(* HMAC / Verify HMAC*)
| StepProduceHMAC : forall A U usrDat (msg : message A) k_id k hmac_id hmacMsg,
    usrDat.(key_heap) $? k_id = Some k
    -> hmacMessage k msg = Some hmacMsg
    -> ~(hmac_id \in (dom U.(encryptions)))
    -> step_user (U, usrDat, ProduceHMAC k msg)
                (updateUniverseCipherMsg U usrDat.(usrid) hmac_id hmacMsg, Return (HMAC_Message msg hmac_id))
| StepVerifyHmac : forall A U usrDat (msg : message A) k_id hmac_id,
    (* u.(encryptions) $? hmac_id = Some (Hmac k_id) *)
    (* -> usrDat.(key_heap) $? k_id = Some (SymKey k) *)
    canVerifyHMAC U usrDat hmac_id k_id
    -> step_user (U, usrDat, VerifyHMAC (HMAC_Message msg hmac_id)) (U, Return true)
| StepFailVerifyHmac : forall A U usrDat (msg : message A) k_id hmac_id,
    ~ canVerifyHMAC U usrDat hmac_id k_id
    -> step_user (U, usrDat, VerifyHMAC (HMAC_Message msg hmac_id)) (U, Return false)
| StepFailVerifyHmacNotHmaced : forall A U usrDat (msg1 msg2 : message A) hmac_id,
    msg1 <> HMAC_Message msg2 hmac_id
    -> step_user (U, usrDat, VerifyHMAC msg1) (U, Return false)

(* Key creation *)
| StepGenerateSymKey: forall U usrDat usage k kid,
    buildSymmetricKey kid usage usrDat.(usrid) = k
    -> ~(kid \in (dom U.(all_keys)))
    -> step_user (U, usrDat, GenerateSymKey usage) (updateUniverseNewKey U usrDat (SymKey k), Return k)
| StepGenerateAsymKey: forall U usrDat usage k kid1 kid2 kid3,
    buildAsymmetricKey kid1 kid2 kid3 usage usrDat.(usrid) = k
    -> ~(kid1 \in (dom U.(all_keys)))
    -> ~(kid2 \in (dom U.(all_keys)))
    -> ~(kid3 \in (dom U.(all_keys)))
    -> step_user (U, usrDat, GenerateAsymKeys usage) (updateUniverseNewKey U usrDat (AsymKey k), Return k)
 
(* | Barrier {result : Set} : user_cmd result. *)
.

Inductive step_universe : universe -> universe -> Prop :=
| StepUser : forall {A} U q q' ud ud' (cmd cmd' : user_cmd A),
    step_user (q,ud,cmd) (q',ud',cmd')
    -> step_universe U ( {| users := U.(users) $+ ( ud'.(usrid), ud' ) ;
                           net   := {|
                                     users_msg_buffer := q';
                                     trace            := U.(net).(trace)
                                   |};
                         |}
                      )
.


(* Additional functionality to implement:
   1. Administration
   2. CA
*) 




















