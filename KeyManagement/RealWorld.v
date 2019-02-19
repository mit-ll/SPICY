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

Definition keyId (k : key) :=
  match k with
  | SymKey  ck   => ck.(key_id)
  | AsymKey ck _ => ck.(key_id)
  end.

Definition keyUsage (k : key) :=
  match k with
  | SymKey  ck   => ck.(usage)
  | AsymKey ck _ => ck.(usage)
  end.


Inductive type :=
| Nat
(* | Text *)
| Key
| CipherId
| Pair (t1 t2 : type)
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Key => key
  | CipherId => cipher_id
  | Pair t1 t2 => typeDenote t1 * typeDenote t2
  end.

Inductive message : type -> Type :=
(* This will eventually be a message Text, using nat for now *)
| Plaintext (txt : nat) : message Nat
| KeyMessage  (k : key) : message Key

| MsgPair {t1 t2 : type} (msg1 : message t1) (msg2 : message t2) : message (Pair t1 t2)

| Ciphertext (msg_id : cipher_id) : message CipherId
| Signature {t} (msg : message t) (sig : cipher_id) : message (Pair t CipherId)
.

(* We need to handle non-deterministic message  -- external choice on ordering *)
Inductive msg_pat :=
| Accept
| Paired (pat1 pat2 : msg_pat)
| Signed (k : key_identifier) (pat : msg_pat)
| Encrypted (k : key_identifier) (pat : msg_pat)
.

Inductive cipher : Type :=
| Cipher {t} (c_id : cipher_id) (k_id : key_identifier) (msg : message t) : cipher
.

Definition queued_messages := fmap user_id (list exmsg).
Definition keys            := fmap key_identifier key.
Definition ciphers         := fmap cipher_id cipher.

Definition adversary_knowledge := keys.

Fixpoint msg_accepted_by_pattern {t} (cs : ciphers) (pat : msg_pat) (msg : message t) : bool :=
  match pat, msg with
  | Accept, _ => true
  | Paired p1 p2, MsgPair m1 m2 => msg_accepted_by_pattern cs p1 m1 && msg_accepted_by_pattern cs p2 m2
  | Paired _ _, _ => false
  | Signed k p, Signature _ c_id =>
    match cs $? c_id with
    | Some (Cipher _ k_id m) => if (k ==n k_id) then (msg_accepted_by_pattern cs p m) else false
    | None => false
    end
  | Signed _ _, _ => false
  | Encrypted k p, Ciphertext c_id =>
    match cs $? c_id with
    | Some (Cipher _ k_id m) => if (k ==n k_id) then (msg_accepted_by_pattern cs p m) else false
    | None => false
    end
  | Encrypted _ _, _ => false
  end.

Fixpoint msg_pattern_spoofable (advk : adversary_knowledge) (pat : msg_pat) : bool :=
  match pat with
  | Accept => true
  | Paired p1 p2 => msg_pattern_spoofable advk p1 && msg_pattern_spoofable advk p2
  | Signed k p =>
    match advk $? k with
    | Some _ => msg_pattern_spoofable advk p
    | None   => false
    end
  | Encrypted k p =>
    match advk $? k with
    | Some _ => msg_pattern_spoofable advk p
    | None   => false
    end
  end.

Fixpoint msg_spoofable {t} (cs : ciphers) (advk : adversary_knowledge) (msg : message t) : bool :=
  match msg with
  | Plaintext _ => true
  | KeyMessage _ => true
  | MsgPair m1 m2 => msg_spoofable cs advk m1 && msg_spoofable cs advk m2
  | Ciphertext c_id => true (* TODO -- how should we actually handle this?? *)
  | Signature m c_id =>
    match cs $? c_id with
    | Some (Cipher _ k_id _) => match advk $? k_id with | Some _ => true | None => false end
    | None => false
    end
  end.

Inductive user_cmd : Type -> Type :=
(* Plumbing *)
| Return {A : Type} (res : A) : user_cmd A
| Bind {A A' : Type} (cmd1 : user_cmd A') (cmd2 : A' -> user_cmd A) : user_cmd A

| Gen : user_cmd nat

(* Messaging *)
| Send {t} (uid : user_id) (msg : message t) : user_cmd unit
| Recv {t} (pat : msg_pat) : user_cmd (message t)

(* Crypto!! *)
| Encrypt {t} (k : key) (msg : message t) : user_cmd (message CipherId)
| Decrypt {t} (msg : message CipherId) : user_cmd (message t)

| Sign    {t} (k : key) (msg : message t) : user_cmd (message (Pair t CipherId))
| Verify  {t} (k : key) (msg : message (Pair t CipherId)) : user_cmd bool

| GenerateSymKey  (usage : key_usage) : user_cmd key
| GenerateAsymKey (usage : key_usage) : user_cmd key

(* Allow administrator to make some global change to the universe -- revoke keys, etc. *)
(* This may be a universe level step -- Administrator forces all users to stop *)
(* | Barrier {result : Set} : user_cmd result *)
.

Module RealWorldNotations.
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75) : realworld_scope.
  Delimit Scope realworld_scope with realworld.
End RealWorldNotations.
Import  RealWorldNotations.
Open Scope realworld_scope.

Record user_data (A : Type) :=
  mkUserData {
      key_heap : fmap nat key ;
      protocol : user_cmd A ;
      (* msg_heap : user_msg_heap ; *)
      (* is_admin : bool *)
    }.

Record universe (A : Type) :=
  mkUniverse {
      users            : user_list (user_data A) ;
      users_msg_buffer : queued_messages ;
      all_keys         : keys ;
      all_ciphers      : ciphers ;
      adversary        : adversary_knowledge
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
Fixpoint findKeys {t} (msg : message t) : list key :=
  match msg with
  | Plaintext _        => []

  | KeyMessage (AsymKey k' _) => [AsymKey k' false] (* Only sending public keys *)
  | KeyMessage k       => [k]
  | MsgPair msg1 msg2  => findKeys msg1 ++ findKeys msg2
  | Ciphertext _       => []
  | Signature m _      => findKeys m
  end.

Definition updateKeyHeap (ks : list key) (key_heap : keys) : keys :=
  let addKey (m : keys) (k : key) :=
      match k with
      | SymKey k'     => m $+ (k'.(key_id), k)
      | AsymKey k' b  => m $+ (k'.(key_id), k)
      end
  in  fold_left addKey ks key_heap.

Definition encryptMessage {t} (k : key) (m : message t) (c_id : cipher_id) : option cipher :=
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

Definition signMessage {t} (k : key) (m : message t) (c_id : cipher_id) : option cipher :=
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
  forall t (m : message t) k_id k ,
    ciphers $? c_id = Some (Cipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Definition data_step0 (A : Type) : Type := 
  adversary_knowledge * ciphers * keys * queued_messages * fmap nat key * user_cmd A.

Definition updateUniverse {A} (U : universe A) (advk : adversary_knowledge) (cs : ciphers)
                          (ks : keys) (qmsgs : queued_messages)
                          (u_id : user_id) (userKeys : keys) (cmd : user_cmd A): universe A :=
  {|
    users            := updateUserList U.(users) u_id ( mkUserData userKeys cmd )
  ; users_msg_buffer := qmsgs
  ; all_keys         := ks
  ; all_ciphers      := cs
  ; adversary        := advk
  |}.

Definition addUniverseUsers {A} (U : universe A) (adversaries : user_list (user_data A)) :=
  {|
    users            := U.(users) ++ adversaries
  ; users_msg_buffer := U.(users_msg_buffer)
  ; all_keys         := U.(all_keys)
  ; all_ciphers      := U.(all_ciphers)
  ; adversary        := U.(adversary)
  |}.

Definition extractPlainText {t} (msg : message t) : option nat :=
  match msg with
  | Plaintext t => Some t
  | _           => None
  end.

Definition unPair {t1 t2} (msg : message (Pair t1 t2)) : option (message t1 * message t2)  :=
  match msg
        in (message t)
        (* return (match t with _ => option (message t1 * message t2) end) *)
        return (match t with
                | Pair t1 t2 => option (message t1 * message t2)
                | _ => option (message t1 * message t2) end)
  with
  | MsgPair m1 m2 => Some (m1,m2)
  | _             => None
  end.


(* The Operational Semantics we want --> a labeled transition system *)

Inductive action : Type :=
| Input  t (msg : message t) (pat : msg_pat) (u_id : user_id) (uks : keys) (cs : ciphers)
| Output t (msg : message t) (u_id : user_id)
.

Definition rlabel := @label action.

Definition action_adversary_safe (advk : adversary_knowledge) (a : action) : bool :=
  match a with
  | Input _ pat _ _ _ => negb (msg_pattern_spoofable advk pat)
  | Output _ _        => true
  end.

Definition universe_data_step {A} (U : universe A) (u_data : user_data A) : data_step0 A :=
  (U.(adversary), U.(all_ciphers), U.(all_keys), U.(users_msg_buffer), u_data.(key_heap), u_data.(protocol)).

(* Labeled transition system *)
Inductive lstep_user : forall A, user_id -> rlabel -> data_step0 A -> data_step0 A -> Prop := 

(* Plumbing *)
| LStepBindRecur : forall {r r'} u_id advk advk'
                     cs cs' ks ks' msgs msgs'
                     uks uks' lbl (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      lstep_user u_id lbl (advk, cs, ks, msgs, uks, cmd1) (advk', cs', ks', msgs', uks', cmd1')
    -> lstep_user u_id lbl (advk, cs, ks, msgs, uks, Bind cmd1 cmd2) (advk', cs', ks', msgs', uks', Bind cmd1' cmd2)
| LStepBindProceed : forall {r r'} u_id advk cs ks msgs uks (v : r') (cmd : r' -> user_cmd r),
    lstep_user u_id Silent (advk, cs, ks, msgs, uks, Bind (Return v) cmd) (advk, cs, ks, msgs, uks, cmd v)

| LGen : forall u_id advk cs ks msgs uks n,
    lstep_user u_id Silent (advk, cs, ks, msgs, uks, Gen) (advk, cs, ks, msgs, uks, Return n)

(* Comms  *)
| LStepRecv : forall {t} u_id advk cs ks qmsgs qmsgs' uks (msg : message t) pat msgs newkeys,
    qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
    -> findKeys msg = newkeys
    -> msg_accepted_by_pattern cs pat msg = true
    -> lstep_user u_id (Action (Input msg pat u_id uks cs))
                 (advk, cs, ks, qmsgs, uks, Recv pat)
                 (advk, cs, ks, qmsgs', updateKeyHeap newkeys uks, Return msg)

| LStepRecvDrop : forall {t} u_id advk cs ks qmsgs qmsgs' uks (msg : message t) pat msgs,
      qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
    (* Hrm, when I am dropping the message, do I want to process keys?? *)
    (* -> findKeys msg = newkeys *)
    -> msg_accepted_by_pattern cs pat msg = false
    -> lstep_user u_id Silent (* Error label ... *)
                 (advk, cs, ks, qmsgs,  uks, @Recv t pat)
                 (advk, cs, ks, qmsgs', uks, Recv pat)

(* Augment attacker's keys with those available through messages sent, including traversing through ciphers already known by attacker, etc. *)
| LStepSend : forall {t} u_id advk advk' cs ks qmsgs rec_u_id uks newkeys (msg : message t),
    findKeys msg = newkeys
    -> advk' = updateKeyHeap newkeys advk
    -> lstep_user u_id (Action (Output msg u_id))
               (advk,  cs, ks, qmsgs, uks, Send rec_u_id msg)
               (advk', cs, ks, multiMapAdd rec_u_id (Exm msg) qmsgs, uks, Return tt)

(* Encryption / Decryption *)
| LStepEncrypt : forall {t} u_id advk cs ks qmsgs uks (msg : message t) k k_id c_id cipherMsg,
    keyId k = k_id
    -> uks $? k_id = Some k
    -> ~(c_id \in (dom cs))
    -> encryptMessage k msg c_id = Some cipherMsg
    -> lstep_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Encrypt k msg)
                 (advk, cs $+ (c_id, cipherMsg), ks, qmsgs, uks, Return (Ciphertext c_id))

| LStepDecrypt : forall {t} u_id advk cs ks qmsgs uks (msg : message t) k_id k c_id newkeys,
    cs $? c_id = Some (Cipher c_id k_id msg)
    -> ( uks $? k_id = Some (AsymKey k true) (* check we have access to private key *)
      \/ uks $? k_id = Some (SymKey k) )
    -> k.(key_id) = k_id
    -> findKeys msg = newkeys
    -> lstep_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Decrypt (Ciphertext c_id))
                 (advk, cs, ks, qmsgs, updateKeyHeap newkeys uks, Return msg)

(* Signing / Verification *)
| LStepSign : forall {t} u_id advk cs ks qmsgs uks (msg : message t) k k_id c_id cipherMsg,
      keyId k = k_id
    -> uks $? k_id = Some k
    -> ~(c_id \in (dom cs))
    -> signMessage k msg c_id = Some cipherMsg
    -> lstep_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Sign k msg)
                 (advk, cs $+ (c_id, cipherMsg), ks, qmsgs, uks, Return (Signature msg c_id))

| LStepVerify : forall {t} u_id advk cs ks qmsgs uks (msg : message t) k_id k c_id newkeys,
    (* k is in your key heap *)
    uks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (Cipher c_id k_id msg)
    -> findKeys msg = newkeys (* TODO do we really want this, should have been gotten via recieve???  find keys that might be in message *)
    -> lstep_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, (Verify k (MsgPair msg (Ciphertext c_id))))
                 (advk, cs, ks, qmsgs, updateKeyHeap newkeys uks, Return (if (k_id ==n (keyId k)) then true else false))
.

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

Lemma LStepRecv' : forall {t} u_id advk cs ks qmsgs qmsgs' uks uks' (msg : message t) pat msgs newkeys,
  qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
  -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
  -> msg_accepted_by_pattern cs pat msg = true
  -> findKeys msg = newkeys
  -> uks' = updateKeyHeap newkeys uks
  -> lstep_user u_id (Action (Input msg pat u_id uks cs))
               (advk, cs, ks, qmsgs,  uks,  Recv pat)
               (advk, cs, ks, qmsgs', uks', Return msg).
Proof.
  intros. subst. econstructor; eauto.
Qed.

Lemma LStepRecvDrop' : forall {t} u_id advk cs ks qmsgs qmsgs' uks (msg : message t) pat msgs,
  qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
  -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
  -> msg_accepted_by_pattern cs pat msg = false
  -> lstep_user u_id Silent
               (advk, cs, ks, qmsgs,  uks, @Recv t pat)
               (advk, cs, ks, qmsgs', uks, Recv pat).
Proof.
  intros. subst. econstructor; eauto.
Qed.

Inductive lstep_universe {A} : universe A -> rlabel -> universe A -> Prop :=
| LStepUser : forall U u_id userData uks advk cs ks qmsgs lbl (cmd' : user_cmd A),
    In (u_id,userData) U.(users)
    -> lstep_user u_id lbl
                 (universe_data_step U userData)
                 (advk, cs, ks, qmsgs, uks, cmd')
    -> lstep_universe U lbl (updateUniverse U advk cs ks qmsgs u_id uks cmd')
.

Lemma LStepUser' : forall A U U' u_id userData uks advk cs ks qmsgs lbl ( cmd' : user_cmd A),
  In (u_id,userData) U.(users)
  -> lstep_user u_id lbl
               (universe_data_step U userData)
               (advk, cs, ks, qmsgs, uks, cmd')
  -> U' = (updateUniverse U advk cs ks qmsgs u_id uks cmd')
  -> lstep_universe U lbl U'.
Proof.
  intros. subst. econstructor; eassumption.
Qed.
