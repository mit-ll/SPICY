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
      key_heap : keys ;
      protocol : user_cmd A ;
      (* msg_heap : user_msg_heap ; *)
      (* is_admin : bool *)
    }.

Definition adversaries := user_list (user_data unit).

Record universe_globals :=
  mkUGlobals {
      users_msg_buffer : queued_messages
    ; all_keys         : keys
    ; all_ciphers      : ciphers
    }.

Record universe (A : Type) :=
  mkUniverse {
      users      : user_list (user_data A)
    ; adversary  : adversaries
    ; univ_data  : universe_globals
    }.

(* First in - first out (queue) semantics to keep message order preserved *)
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

Definition findUserKeys {A} (us : user_list (user_data A)) : keys :=
  fold_left (fun ks '(_,usr) => ks $++ usr.(key_heap)) us $0.

Definition addUserKeys {A} (us : user_list (user_data A)) (ks : list key) :=
  map (fun '(u_id,u) => (u_id, {| key_heap := updateKeyHeap ks u.(key_heap) ; protocol := u.(protocol) |})) us.

Definition updateGlobalKeys (ks : list key) (globals : universe_globals) : universe_globals :=
  {| users_msg_buffer := globals.(users_msg_buffer)
   ; all_keys         := updateKeyHeap ks globals.(all_keys)
   ; all_ciphers      := globals.(all_ciphers)
   |}.

Definition setGlobalUserMsgs (u_id : user_id) (msgs : list exmsg) (globals : universe_globals) :=
  {| users_msg_buffer := match msgs with [] => globals.(users_msg_buffer) $- u_id | _ => globals.(users_msg_buffer) $+ (u_id,msgs) end
   ; all_keys         := globals.(all_keys)
   ; all_ciphers      := globals.(all_ciphers)
   |}.

Definition addGlobalUserMsg {t} (u_id : user_id) (msg : message t) (globals : universe_globals) :=
  {| users_msg_buffer := multiMapAdd u_id (Exm msg) globals.(users_msg_buffer)
   ; all_keys         := globals.(all_keys)
   ; all_ciphers      := globals.(all_ciphers)
   |}.

Definition addCipher (cid : cipher_id) (msg : cipher) (globals : universe_globals) :=
  {| users_msg_buffer := globals.(users_msg_buffer)
   ; all_keys         := globals.(all_keys)
   ; all_ciphers      := globals.(all_ciphers) $+ (cid, msg)
   |}.

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
  universe_globals * adversaries * keys * user_cmd A.
  (* adversary_knowledge * ciphers * keys * queued_messages * fmap nat key * user_cmd A. *)

Definition updateUniverse {A}
           (U : universe A) (univ_globals : universe_globals) (advs : adversaries)
           (u_id : user_id) (userKeys : keys) (cmd : user_cmd A): universe A :=
  {|
    users        := updateUserList U.(users) u_id ( mkUserData userKeys cmd )
  ; adversary    := advs
  ; univ_data    := univ_globals
  |}.

Definition updateUniverseAdv {A}
           (U : universe A) (univ_globals : universe_globals) (advs : adversaries)
           (u_id : user_id) (userKeys : keys) (cmd : user_cmd unit): universe A :=
  {|
    users        := U.(users)
  ; adversary    := updateUserList advs u_id ( mkUserData userKeys cmd )
  ; univ_data    := univ_globals
  |}.

Definition addAdversaries {A} (U : universe A) (advs : adversaries) :=
  {|
    users         := U.(users)
  ; adversary     := U.(adversary) ++ advs
  ; univ_data     :=   {| users_msg_buffer := U.(univ_data).(users_msg_buffer)
                          ; all_keys         := U.(univ_data).(all_keys) $++ (findUserKeys advs)
                          ; all_ciphers      := U.(univ_data).(all_ciphers)
                        |}
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

Definition universe_data_step {A B} (U : universe A) (u_data : user_data B) : data_step0 B :=
  (U.(univ_data), U.(adversary), u_data.(key_heap), u_data.(protocol)).

(* Labeled transition system *)
Inductive lstep_user : forall A, user_id -> rlabel -> data_step0 A -> data_step0 A -> Prop := 

(* Plumbing *)
| LStepBindRecur : forall {r r'} u_id adv adv' globals globals'
                     uks uks' lbl (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      lstep_user u_id lbl (globals, adv, uks, cmd1) (globals', adv', uks', cmd1')
    -> lstep_user u_id lbl (globals, adv, uks, Bind cmd1 cmd2) (globals', adv', uks', Bind cmd1' cmd2)
| LStepBindProceed : forall {r r'} u_id adv globals uks (v : r') (cmd : r' -> user_cmd r),
    lstep_user u_id Silent (globals, adv, uks, Bind (Return v) cmd) (globals, adv, uks, cmd v)

| LGen : forall u_id adv globals uks n,
    lstep_user u_id Silent (globals, adv, uks, Gen) (globals, adv, uks, Return n)

(* Comms  *)
| LStepRecv : forall {t} u_id adv globals globals' uks (msg : message t) pat msgs newkeys,
      globals.(users_msg_buffer) $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> globals' = setGlobalUserMsgs u_id msgs globals
    -> findKeys msg = newkeys
    -> msg_accepted_by_pattern globals.(all_ciphers) pat msg = true
    -> lstep_user u_id (Action (Input msg pat u_id uks globals.(all_ciphers)))
                 (globals , adv, uks, Recv pat)
                 (globals', adv, updateKeyHeap newkeys uks, Return msg)

| LStepRecvDrop : forall {t} u_id adv globals globals' uks (msg : message t) pat msgs,
      globals.(users_msg_buffer) $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> globals' = setGlobalUserMsgs u_id msgs globals
    -> msg_accepted_by_pattern globals.(all_ciphers) pat msg = false
    -> lstep_user u_id Silent (* Error label ... *)
                 (globals , adv, uks, @Recv t pat)
                 (globals', adv, uks, Recv pat)

(* Augment attacker's keys with those available through messages sent, including traversing through ciphers already known by attacker, etc. *)
| LStepSend : forall {t} u_id adv adv' globals globals' rec_u_id uks newkeys (msg : message t),
    findKeys msg = newkeys
    -> adv' = addUserKeys adv newkeys
    -> globals' = addGlobalUserMsg rec_u_id msg globals
    -> lstep_user u_id (Action (Output msg u_id))
               (globals,  adv,  uks, Send rec_u_id msg)
               (globals', adv', uks, Return tt)

(* Encryption / Decryption *)
| LStepEncrypt : forall {t} u_id adv globals globals' uks (msg : message t) k k_id c_id cipherMsg,
    keyId k = k_id
    -> uks $? k_id = Some k
    -> ~(c_id \in (dom globals.(all_ciphers)))
    -> encryptMessage k msg c_id = Some cipherMsg
    -> globals' = addCipher c_id cipherMsg globals
    -> lstep_user u_id Silent
                 (globals,  adv, uks, Encrypt k msg)
                 (globals', adv, uks, Return (Ciphertext c_id))

| LStepDecrypt : forall {t} u_id adv globals uks (msg : message t) k_id k c_id newkeys,
    globals.(all_ciphers) $? c_id = Some (Cipher c_id k_id msg)
    -> ( uks $? k_id = Some (AsymKey k true) (* check we have access to private key *)
      \/ uks $? k_id = Some (SymKey k) )
    -> k.(key_id) = k_id
    -> findKeys msg = newkeys
    -> lstep_user u_id Silent
                 (globals, adv, uks, Decrypt (Ciphertext c_id))
                 (globals, adv, updateKeyHeap newkeys uks, Return msg)

(* Signing / Verification *)
| LStepSign : forall {t} u_id adv globals globals' uks (msg : message t) k k_id c_id cipherMsg,
      keyId k = k_id
    -> uks $? k_id = Some k
    -> ~(c_id \in (dom globals.(all_ciphers)))
    -> signMessage k msg c_id = Some cipherMsg
    -> globals' = addCipher c_id cipherMsg globals
    -> lstep_user u_id Silent
                 (globals,  adv, uks, Sign k msg)
                 (globals', adv, uks, Return (Signature msg c_id))

| LStepVerify : forall {t} u_id adv globals uks (msg : message t) k_id k c_id,
    (* k is in your key heap *)
    uks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> globals.(all_ciphers) $? c_id = Some (Cipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> lstep_user u_id Silent
                 (globals, adv, uks, (Verify k (MsgPair msg (Ciphertext c_id))))
                 (globals, adv, uks, Return (if (k_id ==n (keyId k)) then true else false))
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

Lemma LStepRecv' : forall {t} u_id adv globals globals' uks uks' (msg : message t) pat msgs newkeys,
      globals.(users_msg_buffer) $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> globals' = setGlobalUserMsgs u_id msgs globals
    -> findKeys msg = newkeys
    -> msg_accepted_by_pattern globals.(all_ciphers) pat msg = true
    -> uks' = updateKeyHeap newkeys uks
    -> lstep_user u_id (Action (Input msg pat u_id uks globals.(all_ciphers)))
                 (globals , adv, uks,  Recv pat)
                 (globals', adv, uks', Return msg).
Proof.
  intros; subst; econstructor; eauto.
Qed.

Inductive lstep_universe {A} : universe A -> rlabel -> universe A -> Prop :=
| LStepUser : forall U u_id userData uks adv globals lbl (cmd : user_cmd A),
    In (u_id,userData) U.(users)
    -> lstep_user u_id lbl
                 (universe_data_step U userData)
                 (globals, adv, uks, cmd)
    -> lstep_universe U lbl (updateUniverse U globals adv u_id uks cmd)
| LStepAdversary : forall (U : universe A) u_id (userData : user_data unit) uks adv globals lbl (cmd : user_cmd unit),
    In (u_id,userData) U.(adversary)
    -> lstep_user u_id lbl
                 (universe_data_step U userData)
                 (globals, adv, uks, cmd)
    -> lstep_universe U Silent (updateUniverseAdv U globals adv u_id uks cmd)
.

Lemma LStepUser' : forall A U U' u_id userData uks adv globals lbl (cmd : user_cmd A),
    In (u_id,userData) U.(users)
    -> lstep_user u_id lbl
                 (universe_data_step U userData)
                 (globals, adv, uks, cmd)
    -> U' = updateUniverse U globals adv u_id uks cmd
    -> lstep_universe U lbl U'.
Proof.
  intros; subst; econstructor; eassumption.
Qed.

Lemma LStepAdversary' : forall A (U U' : universe A) u_id (userData : user_data unit) uks adv globals lbl cmd,
    In (u_id,userData) U.(adversary)
    -> lstep_user u_id lbl
                 (universe_data_step U userData)
                 (globals, adv, uks, cmd)
    -> U' = updateUniverseAdv U globals adv u_id uks cmd
    -> lstep_universe U Silent U'.
Proof.
  intros; subst; econstructor; eassumption.
Qed.
