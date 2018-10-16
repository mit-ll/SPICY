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

Definition buildAsymmetricKey (k_id : asym_private_key_id) (usage : asymmetric_usage) (u_id : user_id) :=
  {|
     asym_key_id             := k_id
   ; public_key              := {| asym_key_ref    := k_id
                                 ; asym_public_key := k_id + 1
                                 ; asym_generating_user_id := u_id
                                 ; asym_usage := usage |}
   ; private_key             := k_id + 2
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
| Sym_Key_Msg  (k : symmetric_key)   : message key
| Asym_Key_Msg (k : asymmetric_key)  : message key

| MsgPair {A B : Set} (msg1 : message A) (msg2 : message B) : message (A*B)

| Ciphertext   (msg_id : encrypted_message_id) : message encrypted_message_id
| Signature    {A : Set} (msg : message A)(sig_id : signed_message_id) : message (A * signed_message_id)
| HMAC_Message {A : Set} (msg : message A)(hmac_id : hmac_message_id) : message (A * hmac_message_id)
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

| Sign    {A : Set} (k : key) (msg : message A) : user_cmd (message (A * signed_message_id))
| Verify  {A : Set} (secret : signed_message_id) (msg : message A) : user_cmd bool

| ProduceHMAC {A : Set} (k : key) (msg : message A) : user_cmd (message (A * hmac_message_id))
| VerifyHMAC  {A : Set} (secret : hmac_message_id) (msg : message A) : user_cmd bool

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
    key_counter      : nat ;
    crypto_counter   : nat
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


Definition updateUniverseDeliverMsg {A} (u : universe) (user : user_data) (msg : message A) (msgs : (list exmsg) ) :=
  {|
     users            := u.(users) $+ (user.(usrid), updateUserKeyHeap (findKeys msg) user) (* add sent keys to user's heap *)
   ; users_msg_buffer := u.(users_msg_buffer) $+ (user.(usrid), msgs)
   ; all_keys         := u.(all_keys)
   ; encryptions      := u.(encryptions)
   ; key_counter      := u.(key_counter)
   ; crypto_counter   := u.(crypto_counter)
  |}.

Definition updateUniverseCipherMsg (u : universe) (uid : user_id) (msg: encrypted_message) :=
  {|
     users            := u.(users)
   ; users_msg_buffer := u.(users_msg_buffer)
   ; all_keys         := u.(all_keys)
   ; encryptions      := u.(encryptions) $+ ( u.(crypto_counter) , msg )
   ; key_counter      := u.(key_counter)
   ; crypto_counter   := u.(crypto_counter) + 1
  |}.

Definition updateUniverseSendMsg {A} (u : universe) (uid : user_id) (msg : message A) :=
  {|
     users            := u.(users)
   ; users_msg_buffer := multiMapAdd uid (Exm msg) u.(users_msg_buffer)
   ; all_keys         := u.(all_keys)
   ; encryptions      := u.(encryptions)
   ; key_counter      := u.(key_counter)
   ; crypto_counter   := u.(crypto_counter)
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

Definition updateUniverseNewKey (u : universe) (user : user_data) (incr : nat) (k : key) :=
  {|
     users            := u.(users) $+ (user.(usrid), updateUserKeyHeap [k] user)
   ; users_msg_buffer := u.(users_msg_buffer)
   ; all_keys         := addKeysHeap [k] u.(all_keys)
   ; encryptions      := u.(encryptions)
   ; key_counter      := u.(key_counter) + incr
   ; crypto_counter   := u.(crypto_counter)
  |}.

Inductive step_user : forall A, universe * user_data * user_cmd A -> universe * user_cmd A -> Prop :=
(* Plumbing *)
| StepBindRecur : forall result result' u u' usrDat (cmd1 cmd1' : user_cmd result) (cmd2 : result -> user_cmd result'),
    step_user (u, usrDat, cmd1) (u', cmd1')
    -> step_user (u, usrDat, Bind cmd1 cmd2) (u', Bind cmd1' cmd2)
| StepBindProceed : forall result result' u usrDat (v : result') (cmd : result' -> user_cmd result),
    step_user (u, usrDat, Bind (Return v) cmd) (u, cmd v)

(* Comms *)
| StepRecv : forall A u usrDat (msg : message A) msgs,
    u.(users_msg_buffer) $? usrDat.(usrid) = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> step_user (u, usrDat, Recv) (updateUniverseDeliverMsg u usrDat msg msgs, Return msg)
| StepSend : forall A u usrDat u_id (msg : message A),
    step_user (u, usrDat, Send u_id msg) (updateUniverseSendMsg u usrDat.(usrid) msg, Return tt)

(* Crypto! *)
| StepEncrypt : forall A u usrDat k_id (msg : message A) encMsg k,
    usrDat.(key_heap) $? k_id = Some k
    -> encryptMessage k msg = Some encMsg
    (* Generate new msg_id and add message to heap *)
    -> step_user (u, usrDat, Encrypt k msg)
                (updateUniverseCipherMsg u usrDat.(usrid) encMsg, Return (Ciphertext u.(crypto_counter)))
| StepSymmetricDecrypt : forall A u usrDat msg k_id k enc_id,
    u.(encryptions) $? enc_id = Some (Enc k_id msg)
    -> usrDat.(key_heap) $? k_id = Some (SymKey k)
    -> step_user (u, usrDat, Decrypt (Ciphertext enc_id)) (u, Return (msg : message A))
| StepAsymmetricDecrypt : forall A u usrDat msg k_id k enc_id,
    u.(encryptions) $? enc_id = Some (Enc k_id msg)
    -> usrDat.(key_heap) $? k_id = Some (AsymKey k)
    -> 
    -> step_user (u, usrDat, Decrypt (Ciphertext enc_id)) (u, Return (msg : message A))

(* | Sign (k : var) (msg : message) : user_cmd message *)
(* | Verify (k : option var) (sig : message) : user_cmd message *)

(* | ProduceHMAC (k : var) (msg : message) : user_cmd message *)
(* | VerifyHMAC (k : option var) (mac : message) : user_cmd message *)

(* Key creation *)
| StepGenerateSymKey: forall u usrDat usage k,
    buildSymmetricKey u.(key_counter) usage usrDat.(usrid) = k
    -> step_user (u, usrDat, GenerateSymKey usage) (updateUniverseNewKey u usrDat 1 (SymKey k), Return k)
| StepGenerateAsymKey: forall u usrDat usage k,
    buildAsymmetricKey u.(key_counter) usage usrDat.(usrid) = k
    -> step_user (u, usrDat, GenerateAsymKeys usage) (updateUniverseNewKey u usrDat 2 (AsymKey k), Return k)

(* | GenerateSymKey (usage : symmetric_usage) : user_cmd var *)
(* | GenerateAsymKeys (usage : asymmetric_usage) : user_cmd (var * var) *)
 
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
                           key_counter := U.(key_counter)
                         |}
                      )
.


(*
 * ******************************************
 * ******************************************
 * What follows was an earlier implementation
 * ******************************************
 * ******************************************
 *)

(* Maybe: 
 * Return' (k : key)
 * Return'' (p : (key * key))
 * instead of adding a message type.
 *)

(* This type defines the syntax for valid commands in user protocols 
   Note: Semantically, GenerateSymKey and GenerateAsymKeys need to return key and key*key, respectively.
         We will define two additional commands ReturnK (k: key) and ReturnKP (p: key * key) to handle this.
         This will allow us to remove the key_pair_message constructor above *)
(* Inductive user_cmd := *)
(* | Return (r : message) *)
(* | Bind (c1 : user_cmd) (c2 : message -> user_cmd) *)
(* | BindSymKey (c1 : user_cmd) (c2 : var -> user_cmd) *)
(* | BindAsymKeys (c1 : user_cmd) (c2 : (var * var) -> user_cmd) *)

(* | Send (uid : user_id) (msg : message) *)
(* | Recv *)
(* | Decrypt (k : option var) (ctxt : message) *)
(* | Encrypt (k : var) (ptxt : message) *)
(* | Sign (k : var) (msg : message) *)
(* | Verify (k : option var) (sig : message) *)
(* | ProduceHMAC (k : var) (msg : message) *)
(* | VerifyHMAC (k : option var) (mac : message) *)
(* | GenerateSymKey (usage : symmetric_usage) *)
(* | GenerateAsymKeys (usage : asymmetric_usage) *)
(* | Barrier. *)

(* Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75). *)
(* Notation "x <<- c1 ; c2" := (BindSymKey c1 (fun x => c2)) (right associativity, at level 75). *)
(* Notation "x <<<- c1 ; c2" := (BindAsymKeys c1 (fun x => c2)) (right associativity, at level 75). *)


(* Return : net *)
(* Definition send_message (msg_var : var) (from_user to_user : user_id) (U : universe) := *)
(* match U.(users) $? from_user with *)
(* | Some u_data => *)
(*   match u_data.(msg_heap) $? msg_var with *)
(*   | Some msg => *)
(*     match (U.(net)).(users_msg_buffer) $? to_user with *)
(*     | Some msg_lst => {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ *)
(*                                              (to_user, msg_lst ++ [msg]) ; *)
(*                          trace := (to_user , msg) :: (U.(net)).(trace) |} *)
(*     | None => U.(net) *)
(*     end *)
(*   | _ => U.(net) (* There was no matching msg to the var *) *)
(*   end *)
(* | _ => U.(net) (* The sender is not valid *) *)
(* end. *)

(* Return : key_heap *)
(* Definition generate_symmetric_key (generating_user : user_id) (key_var : var) (U : universe) (usage : symmetric_usage) := *)
(* match U.(users) $? generating_user with *)
(* | Some u_data => u_data.(key_heap) $+ *)
(*                  (key_var, SymKey {| sym_key_id := U.(key_counter) ; *)
(*                                      sym_generating_user_id := generating_user ; *)
(*                                      sym_usage := usage |}) *)
(* | None => $0 *)
(* end. *)

(* Return : key_heap *)
(* Definition generate_asymmetric_key (generating_user : user_id) (key_var1 key_var2 : var) (U : universe) (usage : asymmetric_usage) := *)
(* let usage' := match usage with *)
(*               | RSA_Enc => RSA_Dec *)
(*               | RSA_Dec => RSA_Enc *)
(*               | ECDSA_Sig => ECDSA_Ver *)
(*               | ECDSA_Ver => ECDSA_Sig *)
(*               end in *)
(* match U.(users) $? generating_user with *)
(* | Some u_data => u_data.(key_heap) $+ *)
(*                  (key_var1, AsymKey {| asym_key_id := U.(key_counter) ; *)
(*                                        asym_generating_user_id := generating_user ; *)
(*                                        asym_usage := usage ; *)
(*                                        asym_paired_key_id := U.(key_counter) + 1 |}) $+ *)
(*                  (key_var2, AsymKey {| asym_key_id := U.(key_counter) + 1 ; *)
(*                                        asym_generating_user_id := generating_user ; *)
(*                                        asym_usage := usage' ; *)
(*                                        asym_paired_key_id := U.(key_counter) |}) *)
(* | None => $0 *)
(* end. *)

(* Return : Universe *)
(* Definition recv_message (recving_user : user_id) (U : universe) (x : var) := *)
(* match (U.(net)).(users_msg_buffer) $? recving_user with *)
(* | Some msg_lst => *)
(*   match msg_lst with *)
(*   | [] => U *)
(*   | h::t => *)
(*     match U.(users) $? recving_user with *)
(*     | Some u_data => *)
(*       match h with *)
(*       | Key_Message sending_user k =>  *)
(*         match (U.(users) $? sending_user) with *)
(*         | Some u_data' => *)
(*           match u_data'.(key_heap) $? k with *)
(*           | Some key => *)
(*             {| users := U.(users) $+ *)
(*                         (recving_user , {| uid := u_data.(uid) ; *)
(*                                            key_heap := u_data.(key_heap) $+ (x, key) ; *)
(*                                            msg_heap := u_data.(msg_heap) ; *)
(*                                            protocol := u_data.(protocol) ; *)
(*                                            is_admin := u_data.(is_admin) |}) ; *)
(*                net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (recving_user, t) ; *)
(*                          trace := (U.(net)).(trace) |} ; *)
(*                key_counter := U.(key_counter) |} *)
(*           | None => U *)
(*           end *)
(*         | None => U *)
(*         end *)
(*       | _ => {| users := U.(users) $+  *)
(*                          (recving_user , {| uid := u_data.(uid) ; *)
(*                                             key_heap := u_data.(key_heap) ; *)
(*                                             msg_heap := u_data.(msg_heap) $+ (x, h) ; *)
(*                                             protocol := u_data.(protocol) ; *)
(*                                             is_admin := u_data.(is_admin) |}) ; *)
(*                 net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (recving_user, t) ; *)
(*                 trace := (U.(net)).(trace) |} ; *)
(*                 key_counter := U.(key_counter) |} *)
(*       end *)
(*     | None => U *)
(*     end *)
(*   end *)
(* | None => U *)
(* end. *)

(* Return : Universe *)
(* Definition decrypt_message (u_id : user_id) (msg_var msg_var': var) (U : universe) (key_var : var) := *)
(* match U.(users) $? u_id with *)
(* | Some u_data => *)
(*   match u_data.(msg_heap) $? msg_var with *)
(*   | Some msg => *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (SymKey k) => *)
(*       match msg with *)
(*       | Ciphertext sending_user msg' k' => *)
(*         match k.(sym_key_id) with *)
(*         | k' => *)
(*           match msg' with *)
(*           | Key_Message sending_user km =>  *)
(*             match U.(users) $? sending_user with *)
(*             | Some u_data' =>  *)
(*               match u_data'.(key_heap) $? km with *)
(*               | Some key => {| users := U.(users) $+ *)
(*                                         (u_id , {| uid := u_id ; *)
(*                                                    key_heap := u_data.(key_heap) $+ (msg_var', key) ; *)
(*                                                    msg_heap := u_data.(msg_heap) ; *)
(*                                                    protocol := u_data.(protocol) ; *)
(*                                                    is_admin := u_data.(is_admin) |}) ; *)
(*                                net := U.(net) ; *)
(*                                key_counter := U.(key_counter) |} *)
(*               | None => U *)
(*               end *)
(*            | None => U *)
(*            end *)
(*           | _ => {| users := U.(users) $+ *)
(*                              (u_id , {| uid := u_id ; *)
(*                                         key_heap := u_data.(key_heap) ; *)
(*                                         msg_heap := u_data.(msg_heap) $+ (msg_var', msg') ; *)
(*                                         protocol := u_data.(protocol) ; *)
(*                                         is_admin := u_data.(is_admin) |}) ; *)
(*                     net := U.(net) ; *)
(*                     key_counter := U.(key_counter) |} *)
(*           end *)
(*         end *)
(*       | _ => U (* There was nothing to decrypt *) *)
(*       end *)
(*     | Some (AsymKey k) => *)
(*       match msg with *)
(*       | Ciphertext sending_user msg' k' => *)
(*         match k.(asym_key_id) with *)
(*         | k' => *)
(*           match msg' with *)
(*           | Key_Message sending_user km => *)
(*             match U.(users) $? sending_user with *)
(*             | Some u_data' =>  *)
(*               match u_data'.(key_heap) $? km with *)
(*               | Some key => {| users := U.(users) $+ *)
(*                                         (u_id , {| uid := u_id ; *)
(*                                                    key_heap := u_data.(key_heap) $+ (msg_var', key) ; *)
(*                                                    msg_heap := u_data.(msg_heap) ; *)
(*                                                    protocol := u_data.(protocol) ; *)
(*                                                    is_admin := u_data.(is_admin) |}) ; *)
(*                                net := U.(net) ; *)
(*                                key_counter := U.(key_counter) |} *)
(*               | None => U *)
(*               end *)
(*            | None => U *)
(*            end *)
(*           | _ => {| users := U.(users) $+ *)
(*                              (u_id , {| uid := u_id ; *)
(*                                         key_heap := u_data.(key_heap) ; *)
(*                                         msg_heap := u_data.(msg_heap) $+ (msg_var', msg') ; *)
(*                                         protocol := u_data.(protocol) ; *)
(*                                         is_admin := u_data.(is_admin) |}) ; *)
(*                     net := U.(net) ; *)
(*                     key_counter := U.(key_counter) |} *)
(*           end *)
(*         end *)
(*       | _ => U (* There was nothing to decrypt *) *)
(*       end *)
(*     | _ => U (* Key_var does not correspond to a key *) *)
(*     end *)
(*   | None => U *)
(*   end *)
(* | None => U *)
(* end. *)

(* Return : msg_heap *)
(* Definition encrypt_message (u_id : user_id) (msg_var msg_var': var) (key_var : var) (U : universe) := *)
(* match U.(users) $? u_id with *)
(* | Some u_data =>  *)
(*   match u_data.(msg_heap) $? msg_var with *)
(*   | Some msg =>  *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (AsymKey k) =>  *)
(*       match k.(asym_usage) with *)
(*       | RSA_Enc => u_data.(msg_heap) $+  *)
(*                    (msg_var', (Ciphertext u_id msg k.(asym_paired_key_id))) *)
(*       | _ => u_data.(msg_heap) *)
(*       end *)
(*     | Some (SymKey k') => *)
(*       match k'.(sym_usage) with *)
(*       | HMAC => u_data.(msg_heap) *)
(*       | _ => u_data.(msg_heap) $+ *)
(*              (msg_var', (Ciphertext u_id msg k'.(sym_key_id))) *)
(*       end *)
(*     | _ => u_data.(msg_heap) *)
(*     end *)
(*   | None => u_data.(msg_heap) *)
(*   end *)
(* | None => $0 *)
(* end. *)

(* Return : msg_heap *)
(* Definition sign (signer : user_id) (key_var msg_var signed_msg_var : var) (U : universe) := *)
(* match U.(users) $? signer with *)
(* | Some u_data => *)
(*   match u_data.(msg_heap) $? msg_var with *)
(*   | Some msg => *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (AsymKey k) => *)
(*       match k.(asym_usage) with *)
(*       | ECDSA_Sig => u_data.(msg_heap) $+ *)
(*                      (signed_msg_var, (Signature k.(asym_paired_key_id) signer msg)) *)
(*       | _ => u_data.(msg_heap) *)
(*       end *)
(*     | _ => u_data.(msg_heap) *)
(*     end *)
(*   | None => u_data.(msg_heap) *)
(*   end *)
(* | None => $0 *)
(* end. *)

(* Return : msg_heap *)
(* Definition produceHMAC (producer : user_id) (key_var msg_var HMAC_var : var) (U : universe) := *)
(* match U.(users) $? producer with *)
(* | Some u_data =>  *)
(*   match u_data.(msg_heap) $? msg_var with *)
(*   | Some msg =>  *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (SymKey k) => *)
(*       match k.(sym_usage) with *)
(*       | HMAC => u_data.(msg_heap) $+ *)
(*                 (HMAC_var, (HMAC_Message producer k.(sym_key_id) msg)) *)
(*       | _ => u_data.(msg_heap) *)
(*       end *)
(*     | _ => u_data.(msg_heap) *)
(*     end *)
(*   | None => u_data.(msg_heap) *)
(*   end *)
(* | None => $0 *)
(* end. *)

(* Return : Universe *)
(* Definition verify (verifier : user_id) (key_var signed_msg_var verified_msg_var : var) (U : universe) := *)
(* match U.(users) $? verifier with *)
(* | Some u_data => *)
(*   match u_data.(msg_heap) $? signed_msg_var with *)
(*   | Some sym_msg => *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (AsymKey k) => *)
(*       match sym_msg with *)
(*       | Signature k_id signer msg => *)
(*         if k_id =? k.(asym_paired_key_id) *)
(*         then match msg with *)
(*              | Key_Message signer key_v =>  *)
(*                match U.(users) $? signer with *)
(*                | Some u_data' =>  *)
(*                  match u_data'.(key_heap) $? key_v with *)
(*                  | Some key => {| users := U.(users) $+ *)
(*                                            (verifier, {| uid := verifier ; *)
(*                                                          key_heap := u_data.(key_heap) $+ *)
(*                                                                      (verified_msg_var, key) ; *)
(*                                                          msg_heap := u_data.(msg_heap) ; *)
(*                                                          protocol := u_data.(protocol) ; *)
(*                                                          is_admin := u_data.(is_admin) |}) ; *)
(*                                   net := U.(net) ; *)
(*                                   key_counter := U.(key_counter) |} *)
(*                  | None => U *)
(*                  end *)
(*                | None => U *)
(*                end *)
(*              | _ => {| users := U.(users) $+ *)
(*                                 (verifier, {| uid := verifier ; *)
(*                                               key_heap := u_data.(key_heap) ; *)
(*                                               msg_heap := u_data.(msg_heap) $+ *)
(*                                                           (verified_msg_var, msg) ; *)
(*                                               protocol := u_data.(protocol) ; *)
(*                                               is_admin := u_data.(is_admin) |}) ; *)
(*                        net := U.(net) ; *)
(*                        key_counter := U.(key_counter) |} *)
(*              end *)
(*         else U *)
(*       | _ => U *)
(*       end *)
(*     | _ => U *)
(*     end *)
(*   | None => U *)
(*   end *)
(* | None => U *)
(* end. *)

(* Return : Universe *)
(* Definition verifyHMAC (verifier : user_id) (key_var HMAC_var verified_msg_var : var) (U : universe) := *)
(* match U.(users) $? verifier with *)
(* | Some u_data =>  *)
(*   match u_data.(msg_heap) $? HMAC_var with *)
(*   | Some HMAC_msg =>  *)
(*     match u_data.(key_heap) $? key_var with *)
(*     | Some (SymKey k) =>  *)
(*       match HMAC_msg with *)
(*       | HMAC_Message sender k_id msg =>  *)
(*         if k_id =? k.(sym_key_id) *)
(*         then match msg with *)
(*              | Key_Message sender' key_var' =>  *)
(*                match U.(users) $? sender with  *)
(*                | Some u_data' =>  *)
(*                  match u_data'.(key_heap) $? key_var' with *)
(*                  | Some key => {| users := U.(users) $+ *)
(*                                            (verifier, {| uid := verifier ; *)
(*                                                          key_heap := u_data.(key_heap) $+  *)
(*                                                                      (verified_msg_var, key) ; *)
(*                                                          msg_heap := u_data.(msg_heap) ; *)
(*                                                          protocol := u_data.(protocol) ; *)
(*                                                          is_admin := u_data.(is_admin) |}) ; *)
(*                                    net := U.(net) ; *)
(*                                    key_counter := U.(key_counter) |} *)
(*                  | None => U *)
(*                  end *)
(*                | None => U *)
(*                end *)
(*              | _ => {| users := U.(users) $+ *)
(*                                 (verifier, {| uid := verifier ; *)
(*                                               key_heap := u_data.(key_heap) ; *)
(*                                               msg_heap := u_data.(msg_heap) $+ *)
(*                                                           (verified_msg_var, msg) ; *)
(*                                               protocol := u_data.(protocol) ; *)
(*                                               is_admin := u_data.(is_admin) |}) ; *)
(*                        net := U.(net) ; *)
(*                        key_counter := U.(key_counter) |} *)
(*              end *)
(*         else U *)
(*       | _ => U *)
(*       end *)
(*     | _ => U *)
(*     end *)
(*   | None => U *)
(*   end *)
(* | None => U *)
(* end. *)


(* Ping Protocol *)

(* U.(users) 
   Check on both ends that received message == "Hello" *)

(* Example howAreWeModelingDecryption := *)
(*   c <- Recv; *)
(*   Return (match c with *)
(*           | Ciphertext msg_fn  => msg *)
(*           | _                  => c *)
(*          end) *)
(*   . *)

(* Example pingUser1 : user_id -> user_cmd message := fun uid => *)
(*   a <- GenerateAsymKeys RSA_Enc ; *)
(*   b <- Send uid (Key_Message 0 (fst a)) ; *)
(*   c <- GenerateAsymKeys ECDSA_Sig ; *)
(*   d <- Send uid (Key_Message 0 (fst c)) ; *)
(*   e <- Sign (snd c) (Plaintext 0 "Hello") ; *)
(*   f <- Encrypt (snd a) e ; *)
(*   g <- Send uid f ; *)
(*   Recv. (* Had better be Plaintext 1 "Hello" *) *)

(* Example pingUser2 : user_id -> user_cmd message := fun uid => *)
(*   a <- Recv ; *)
(*   b <- Recv ; *)
(*   c <- Recv ; *)
(*   (* d <- Decrypt a c; *) *)
(*   (* e <- Verify (match b with *) *)
(*   (*                  | Key_Message 0 k => Some k *) *)
(*   (*                  | _ => None *) *)
(*   (*                  end) d ; *) *)
(*   (* _ <- Send uid e *) *)
(*   Return a. (* delete me *) *)
(*   (* Return e. (* Had better be Plaintext "Hello" *) *) *)

(* Example ping_users := *)
(*  $0 $+ (0, {| uid := 0 ; *)
(*               key_heap := $0 ; *)
(*               msg_heap := nil ; *)
(*               protocol := pingUser1 1 ; *)
(*               is_admin := false |}) *)
(*     $+ (1 , {| uid := 1 ; *)
(*                key_heap := $0 ; *)
(*                msg_heap := nil ; *)
(*                protocol := pingUser2 0 ; *)
(*                is_admin := false |}). *)

(* (* Ping Universe *) *)
(* Example ping_universe := *)
(* {| users := ping_users ; *)
(*    net := {| users_msg_buffer := $0 $+ (0, []) $+ (1, []) ; *)
(*              trace := [] |} ; *)
(*    key_counter := 0 |}. *)

(* Inductive step : universe -> universe -> Prop := *)
(* | StepSign : forall signer key_var msg_var signed_msg_var U u_data k msg msg_heap' users' signed_message, *)
(*     U.(users) $? signer = Some u_data -> *)
(*     u_data.(key_heap) $? key_var = Some (AsymKey k) -> *)
(*     u_data.(msg_heap) $? msg_var = Some msg -> *)
(*     ~ (signed_msg_var \in dom u_data.(msg_heap)) -> *)
(*     k.(asym_usage) = ECDSA_Sig -> *)
(*     u_data.(protocol) = Sign key_var msg -> *)
(*     msg_heap' = (sign signer key_var msg_var signed_msg_var U) -> *)
(*     msg_heap' $? signed_msg_var = Some signed_message ->  *)
(*     users' = U.(users) $+ (signer, {| uid := signer ; *)
(*                                       key_heap := u_data.(key_heap) ; *)
(*                                       msg_heap := msg_heap' ; *)
(*                                       protocol := Return signed_message ; *)
(*                                       is_admin := u_data.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := U.(net) ; *)
(*                 key_counter := U.(key_counter) |} *)
(* | StepProduceHMAC : forall producer key_var msg_var HMAC_var U u_data k msg msg_heap' users' HMAC_Message, *)
(*     U.(users) $? producer = Some u_data -> *)
(*     u_data.(key_heap) $? key_var = Some (SymKey k) -> *)
(*     u_data.(msg_heap) $? msg_var = Some msg -> *)
(*     ~ (HMAC_var \in dom u_data.(msg_heap)) -> *)
(*     k.(sym_usage) = HMAC -> *)
(*     u_data.(protocol) = ProduceHMAC key_var msg -> *)
(*     msg_heap' = (produceHMAC producer key_var msg_var HMAC_var U) -> *)
(*     msg_heap' $? HMAC_var = Some HMAC_Message -> *)
(*     users' = U.(users) $+ (producer, {| uid := producer ; *)
(*                                         key_heap := u_data.(key_heap) ; *)
(*                                         msg_heap := msg_heap' ; *)
(*                                         protocol := Return HMAC_Message ; *)
(*                                         is_admin := u_data.(is_admin) |}) -> *)
(*     step U {| users := users' ; *)
(*               net := U.(net) ; *)
(*               key_counter := U.(key_counter) |} *)
(* | StepVerifyHMAC : forall verifier sender key_var HMAC_var verified_msg_var U u_data HMAC_msg KeyType U' u_data' users' k_id msg k, *)
(*     U.(users) $? verifier = Some u_data -> *)
(*     u_data.(msg_heap) $? HMAC_var = Some HMAC_msg -> *)
(*     u_data.(key_heap) $? key_var = Some KeyType -> *)
(*     HMAC_msg = HMAC_Message sender k_id msg -> *)
(*     KeyType = SymKey k -> *)
(*     k.(sym_key_id) = k_id -> *)
(*     match msg with *)
(*     | Key_Message sender k => ~ (verified_msg_var \in dom u_data.(msg_heap)) *)
(*     | _ => ~ (verified_msg_var \in dom u_data.(key_heap)) *)
(*     end -> *)
(*     U' = (verifyHMAC verifier key_var HMAC_var verified_msg_var U) -> *)
(*     U'.(users) $? verifier = Some u_data' -> *)
(*     users' = U'.(users) $+ (verifier, {| uid := verifier ; *)
(*                                          key_heap := u_data'.(key_heap) ; *)
(*                                          msg_heap := u_data'.(msg_heap) ; *)
(*                                          protocol := Return msg ; *)
(*                                          is_admin := u_data'.(is_admin) |}) -> *)
(*     u_data.(protocol) = VerifyHMAC (Some key_var) HMAC_msg -> *)
(*     step U {| users := users' ; *)
(*               net := U'.(net) ; *)
(*               key_counter := U'.(key_counter) |} *)
(* | StepVerify : forall verifier key_var signed_msg_var verified_msg_var U u_data signed_message KeyType U' u_data' users' k_id msg k signer, *)
(*     U.(users) $? verifier = Some u_data -> *)
(*     u_data.(msg_heap) $? signed_msg_var = Some signed_message -> *)
(*     u_data.(key_heap) $? key_var = Some KeyType -> *)
(*     signed_message = Signature k_id signer msg -> *)
(*     KeyType = AsymKey k -> *)
(*     k.(asym_key_id) = k_id -> *)
(*     match msg with *)
(*     | Key_Message sender k' => ~ (verified_msg_var \in dom u_data.(msg_heap)) *)
(*     | _ => ~ (verified_msg_var \in dom u_data.(key_heap)) *)
(*     end -> *)
(*     U' = (verify verifier key_var signed_msg_var verified_msg_var U) -> *)
(*     U'.(users) $? verifier = Some u_data' -> *)
(*     users' = U'.(users) $+ (verifier, {| uid := verifier ; *)
(*                                          key_heap := u_data'.(key_heap) ; *)
(*                                          msg_heap := u_data'.(msg_heap) ; *)
(*                                          protocol := Return msg ; *)
(*                                          is_admin := u_data'.(is_admin) |}) -> *)
(*     u_data.(protocol) = Verify (Some key_var) signed_message -> *)
(*       step U {| users := users' ; *)
(*                 net := U'.(net) ; *)
(*                 key_counter := U'.(key_counter) |} *)
(* | StepEncrypt : forall u_id msg_var msg_var' key_var U u_data msg KeyType msg_heap' users' encrypted_msg, *)
(*     U.(users) $? u_id = Some u_data -> *)
(*     u_data.(msg_heap) $? msg_var = Some msg -> *)
(*     ~ (msg_var' \in dom u_data.(msg_heap)) -> *)
(*     u_data.(key_heap) $? key_var = Some KeyType -> *)
(*     match KeyType with *)
(*     | AsymKey k => k.(asym_usage) = RSA_Enc *)
(*     | SymKey k => ~ (k.(sym_usage) = HMAC) *)
(*     end -> *)
(*     u_data.(protocol) = Encrypt key_var msg -> *)
(*     msg_heap' = (encrypt_message u_id msg_var msg_var' key_var U) -> *)
(*     msg_heap' $? msg_var' = Some encrypted_msg -> *)
(*     users' = U.(users) $+ (u_id, {| uid := u_id ; *)
(*                                     key_heap := u_data.(key_heap) ; *)
(*                                     msg_heap := msg_heap' ; *)
(*                                     protocol := Return encrypted_msg ; *)
(*                                     is_admin := u_data.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := U.(net) ; *)
(*                 key_counter := U.(key_counter) |} *)
(* | StepDecrypt : forall msg_sender_u_id u_id msg_var msg_var' U key_var u_data msg k_id k U' u_data' users', *)
(*     U.(users) $? u_id = Some u_data -> *)
(*     u_data.(msg_heap) $? msg_var = Some (Ciphertext msg_sender_u_id msg k_id) -> *)
(*     u_data.(key_heap) $? key_var = Some k -> *)
(*     match msg with *)
(*     | Key_Message msg_sender_u_id k => ~ (msg_var' \in dom u_data.(msg_heap)) *)
(*     | _ => ~ (msg_var' \in dom u_data.(key_heap)) *)
(*     end -> *)
(*     match k with *)
(*     | SymKey skey => skey.(sym_key_id) = k_id *)
(*     | AsymKey akey => akey.(asym_key_id) = k_id *)
(*     end -> *)
(*     u_data.(protocol) = Decrypt (Some key_var) (Ciphertext msg_sender_u_id msg k_id) -> *)
(*     U' = (decrypt_message u_id msg_var msg_var' U key_var) -> *)
(*     U'.(users) $? u_id = Some u_data' -> *)
(*     users' = U'.(users) $+ (u_id, {| uid := u_id ; *)
(*                                      key_heap := u_data'.(key_heap) ; *)
(*                                      msg_heap := u_data'.(msg_heap) ; *)
(*                                      protocol := Return msg ; *)
(*                                      is_admin := u_data'.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := U'.(net) ; *)
(*                 key_counter := U'.(key_counter) |} *)
(* | StepGenerateAsymKey : forall generating_user key_var1 key_var2 U usage u_data key_heap' users' key1 key2, *)
(*     U.(users) $? generating_user = Some u_data -> *)
(*     ~ (key_var1 \in dom u_data.(key_heap)) -> *)
(*     ~ (key_var2 \in dom u_data.(key_heap)) -> *)
(*     u_data.(protocol) = GenerateAsymKeys usage -> *)
(*     key_heap' = (generate_asymmetric_key generating_user key_var1 key_var2 U usage) -> *)
(*     key_heap' $? key_var1 = Some key1 -> *)
(*     key_heap' $? key_var2 = Some key2 -> *)
(*     users' = U.(users) $+ (generating_user, {| uid := generating_user ; *)
(*                            key_heap := key_heap' ; *)
(*                            msg_heap := u_data.(msg_heap) ; *)
(*                            protocol := Return (Key_pair_message generating_user (pair key_var1 key_var2)) ; *)
(*                            is_admin := u_data.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := U.(net) ; *)
(*                 key_counter := U.(key_counter) + 2 ;|} *)
(* | StepGenerateSymKey : forall generating_user key_var U usage u_data key_heap' users' key, *)
(*     U.(users) $? generating_user = Some u_data -> *)
(*     ~ (key_var \in dom u_data.(key_heap)) -> *)
(*     u_data.(protocol) = GenerateSymKey usage -> *)
(*     key_heap' = (generate_symmetric_key generating_user key_var U usage) -> *)
(*     key_heap' $? key_var = Some key -> *)
(*     users' = U.(users) $+ (generating_user, {| uid := generating_user ; *)
(*                                          key_heap := key_heap' ; *)
(*                                          msg_heap := u_data.(msg_heap) ; *)
(*                                          protocol := Return (Key_Message generating_user key_var) ; *)
(*                                          is_admin := u_data.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := U.(net) ; *)
(*                 key_counter := U.(key_counter) + 1|} *)
(* | StepRecv : forall U recving_user msg_var u_data msg_buffer U' u_data' users' h t, *)
(*     U.(users) $? recving_user = Some u_data -> *)
(*     (U.(net)).(users_msg_buffer) $? recving_user = Some msg_buffer -> *)
(*     msg_buffer = h::t ->  *)
(*     match h with *)
(*     | Key_Message _ _ => ~ (msg_var \in dom u_data.(key_heap)) *)
(*     | _ => ~ (msg_var \in dom u_data.(msg_heap)) *)
(*     end -> *)
(*     U' = (recv_message recving_user U msg_var) -> *)
(*     U'.(users) $? recving_user = Some u_data' -> *)
(*     users' = U.(users) $+ (recving_user, {| uid := recving_user ; *)
(*                                             key_heap := u_data'.(key_heap) ; *)
(*                                             msg_heap := u_data'.(msg_heap) ; *)
(*                                             protocol := Return h ; *)
(*                                             is_admin := u_data'.(is_admin) |}) -> *)
(*     u_data.(protocol) = Recv -> *)
(*       step U {| users := users' ; *)
(*                 net := U'.(net) ; *)
(*                 key_counter := U'.(key_counter) |} *)
(* | StepSend : forall U msg_var from_id to_id u_data msg users', *)
(*     U.(users) $? from_id = Some u_data -> *)
(*     to_id \in dom U.(users) -> *)
(*     to_id \in dom (U.(net)).(users_msg_buffer) -> *)
(*     u_data.(protocol) = Send to_id msg -> *)
(*     users' = U.(users) $+ (from_id, {| uid := from_id ; *)
(*                                        key_heap := u_data.(key_heap) ; *)
(*                                        msg_heap := u_data.(msg_heap) ; *)
(*                                        protocol := (Return (Plaintext from_id "Sent Message")) ; *)
(*                                        is_admin := u_data.(is_admin) |}) -> *)
(*       step U {| users := users' ; *)
(*                 net := send_message msg_var from_id to_id U ; *)
(*                 key_counter := U.(key_counter) |}. *)

(*
| Return
| Bind
| BindSymKey
| BindAsymKey
| Barrier
*)


(* Changelog
 *  1. Match statements start on the following line to conserve horizontal space.
 *  2. All messages have a [sender_id] argument. This is to allow change 3.
 *  3. Users only deal with variables mapping to keys, instead of keys or their id's directly.
 *)



(*
 * TODO
 * 1. Remove master key type.
 * 2. Change user_cmd to be polymorphic type instead of just messages.
 *)


(* Additional functionality to implement:
   1. Administration
   2. CA
*) 




















