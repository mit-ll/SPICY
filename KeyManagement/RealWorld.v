From Coq Require Import String.
Require Import MyPrelude Common Users.

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


Inductive type : Set :=
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

Definition queued_messages := list exmsg.
Definition keys            := NatMap.t key.
Definition ciphers         := NatMap.t cipher.

Definition adversary_knowledge := keys.

Inductive msg_accepted_by_pattern (cs : ciphers) (pat : msg_pat) : forall {t : type}, message t -> Prop :=
| MsgAccept : forall {t} (m : message t),
      pat = Accept
    -> msg_accepted_by_pattern cs pat m
| BothPairsAccepted : forall {t1 t2} m p1 p2 (m1 : message t1) (m2 : message t2),
      pat = Paired p1 p2
    -> m   = MsgPair m1 m2
    -> msg_accepted_by_pattern cs p1 m1
    -> msg_accepted_by_pattern cs p2 m2
    -> msg_accepted_by_pattern cs pat m
| ProperlySigned : forall {t} c_id k p m (m' : message t),
      pat = Signed k p
    -> m   = Signature m' c_id
    -> cs $? c_id = Some (Cipher c_id k m')
    -> msg_accepted_by_pattern cs p m'
    -> msg_accepted_by_pattern cs pat m
| ProperlyEncrypted : forall {t} c_id k p m (m' : message t),
      pat = Encrypted k p
    -> m   = Ciphertext c_id
    -> cs $? c_id = Some (Cipher c_id k m')
    -> msg_accepted_by_pattern cs p m'
    -> msg_accepted_by_pattern cs pat m
.

Fixpoint msg_accepted_by_pattern_compute {t} (cs : ciphers) (pat : msg_pat) (msg : message t) : bool :=
  match pat, msg with
  | Accept, _ => true
  | Paired p1 p2, MsgPair m1 m2 => msg_accepted_by_pattern_compute cs p1 m1 && msg_accepted_by_pattern_compute cs p2 m2
  | Paired _ _, _ => false
  | Signed k p, Signature _ c_id =>
    match cs $? c_id with
    | Some (Cipher _ k_id m) => if (k ==n k_id) then (msg_accepted_by_pattern_compute cs p m) else false
    | None => false
    end
  | Signed _ _, _ => false
  | Encrypted k p, Ciphertext c_id =>
    match cs $? c_id with
    | Some (Cipher _ k_id m) => if (k ==n k_id) then (msg_accepted_by_pattern_compute cs p m) else false
    | None => false
    end
  | Encrypted _ _, _ => false
  end.

Lemma msg_accepted_by_pattern_pred_compute :
  forall {t} cs pat (msg : message t),
    msg_accepted_by_pattern cs pat msg -> msg_accepted_by_pattern_compute cs pat msg = true.
Proof.
  induction 1; unfold msg_accepted_by_pattern_compute; subst; simpl.
  - trivial.
  - fold (@msg_accepted_by_pattern_compute t1) (@msg_accepted_by_pattern_compute t2); apply andb_true_iff; eauto.
  - rewrite H1; simpl; case (k ==n k); intros; eauto.
  - rewrite H1; simpl; case (k ==n k); intros; eauto.
Qed.

Lemma msg_accepted_by_pattern_compute_false_no_pred :
  forall {t} cs pat (msg : message t),
      msg_accepted_by_pattern_compute cs pat msg = false
    -> ~ msg_accepted_by_pattern cs pat msg.
Proof.
  unfold "~"; induction 2; unfold msg_accepted_by_pattern_compute in H; subst; simpl in *.
  - invert H.
  - fold (@msg_accepted_by_pattern_compute t1) (@msg_accepted_by_pattern_compute t2) in H.
    rewrite andb_false_iff in H; destruct H; contradiction.
  - rewrite H2 in H; case (k ==n k) in H; simpl in H; eauto.
  - rewrite H2 in H; case (k ==n k) in H; simpl in H; eauto.
Qed.

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
      key_heap : keys
    ; protocol : user_cmd A
    ; msg_heap : queued_messages
      (* msg_heap : user_msg_heap ; *)
      (* is_admin : bool *)
    }.

Definition adversaries A  := user_list (user_data A).
Definition honest_users A := user_list (user_data A).

(* Record universe_globals := *)
(*   mkUGlobals { *)
(*       users_msg_buffer : queued_messages *)
(*     ; all_keys         : keys *)
(*     ; all_ciphers      : ciphers *)
(*     }. *)

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : adversaries B
    ; all_ciphers : ciphers
    }.

(* First in - first out (queue) semantics to keep message order preserved *)
(* Definition multiMapAdd {V} (k : nat)(v : V)(m : NatMap.t (list V)) : NatMap.t (list V) := *)
(*   match m $? k with *)
(*   | None => m $+ (k, [v]) *)
(*   | Some vs => m $+ (k, vs ++ [v]) (* add new element to end, to preserve order *) *)
(*   end. *)

(* When we are finding keys, we need to check whether they are asymmetric.  If
   so, we mark them as not having access to the private key, since the intent is to
   send only the public part of the key *)
Fixpoint findKeys {t} (msg : message t) : keys :=
  match msg with
  | Plaintext _        => $0

  | KeyMessage (AsymKey k' _) => $0 $+ (k'.(key_id), AsymKey k' false) (* Only sending public keys *)
  | KeyMessage k       => $0 $+ (keyId k, k)
  | MsgPair msg1 msg2  => (findKeys msg1) $++ (findKeys msg2)
  | Ciphertext _       => $0
  | Signature m _      => findKeys m
  end.

Definition findUserKeys {A} (us : user_list (user_data A)) : keys :=
  fold (fun u_id u ks => ks $++ u.(key_heap)) us $0.

Definition addUserKeys {A} (us : user_list (user_data A)) (ks : keys) : user_list (user_data A) :=
  map (fun u => {| key_heap := u.(key_heap) $++ ks ; protocol := u.(protocol) ;  msg_heap := u.(msg_heap) |}) us.

(* Definition addCipher {A B} (cid : cipher_id) (msg : cipher) (U : universe A B) := *)
(*   {| users       := U.(users) *)
(*    ; adversary   := U.(adversary) *)
(*    ; all_ciphers := U.(all_ciphers) $+ (cid, msg) *)
(*    |}. *)

Definition encryptMessage {t} (k : key) (m : message t) (c_id : cipher_id) : option cipher :=
  match k with
  | SymKey k'  =>
    match (usage k') with
    | Encryption => Some (Cipher c_id k'.(key_id) m)
    | _          => None
    end
  | AsymKey k' false => (* Encryption always uses the public part of an asymmetric key *)
    match (usage k') with
    | Encryption => Some (Cipher c_id k'.(key_id) m)
    | _          => None
    end
  | _ => None
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

Definition canVerifySignature {A} (cs : ciphers)(usrDat : user_data A)(c_id : cipher_id) : Prop :=
  forall t (m : message t) k_id k ,
    cs $? c_id = Some (Cipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Definition buildUniverse {A B}
           (usrs : honest_users A) (advs : adversaries B) (cs : ciphers)
           (u_id : user_id) (userData : user_data A) : universe A B :=
  {| users        := updateUserList usrs u_id userData
   ; adversary    := advs
   ; all_ciphers  := cs
   |}.

Definition buildUniverseAdv {A B}
           (usrs : honest_users A) (advs : adversaries B) (cs : ciphers)
           (u_id : user_id) (userData : user_data B) : universe A B :=
  {| users        := usrs
   ; adversary    := updateUserList advs u_id userData
   ; all_ciphers  := cs
   |}.

Definition addAdversaries {A B} (U : universe A B) (advs : adversaries B) :=
  {| users       := U.(users)
   ; adversary   := U.(adversary) $++ advs
   ; all_ciphers := U.(all_ciphers)
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

Definition data_step0 (A B C : Type) : Type :=
  honest_users A * adversaries B * ciphers * keys * queued_messages * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B C :=
  (U.(users), U.(adversary), U.(all_ciphers), u_data.(key_heap), u_data.(msg_heap), u_data.(protocol)).

(* Labeled transition system *)
Inductive step_user : forall A B C, user_id -> rlabel -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {B r r'} u_id (usrs usrs' : honest_users r') (adv adv' : adversaries B)
                     lbl cs cs' qmsgs qmsgs' ks ks' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user u_id lbl (usrs, adv, cs, ks, qmsgs, cmd1) (usrs', adv', cs', ks', qmsgs', cmd1')
    -> step_user u_id lbl (usrs, adv, cs, ks, qmsgs, Bind cmd1 cmd2) (usrs', adv', cs', ks', qmsgs', Bind cmd1' cmd2)
| StepBindProceed : forall {B r r'} u_id (usrs : honest_users r) (adv : adversaries B) cs ks qmsgs (v : r') (cmd : r' -> user_cmd r),
    step_user u_id Silent (usrs, adv, cs, ks, qmsgs, Bind (Return v) cmd) (usrs, adv, cs, ks, qmsgs, cmd v)

| StepGen : forall {A B} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs n,
    step_user u_id Silent (usrs, adv, cs, ks, qmsgs, Gen) (usrs, adv, cs, ks, qmsgs, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks ks' qmsgs qmsgs' (msg : message t) msgs pat newkeys,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> findKeys msg = newkeys
    -> ks' = ks $++ newkeys
    -> msg_accepted_by_pattern cs pat msg
    -> step_user u_id (Action (Input msg pat u_id ks cs))
                (usrs, adv, cs, ks , qmsgs , Recv pat)
                (usrs, adv, cs, ks', qmsgs', Return msg)

| StepRecvDrop : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs qmsgs' (msg : message t) pat msgs,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> ~ msg_accepted_by_pattern cs pat msg
    -> step_user u_id Silent (* Error label ... *)
                (usrs, adv, cs, ks, qmsgs , Recv pat)
                (usrs, adv, cs, ks, qmsgs', Return msg)

(* Augment attacker's keys with those available through messages sent,
 * including traversing through ciphers already known by attacker, etc.
 *)
| StepSend : forall {A B} {t} u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B)
               cs ks qmsgs rec_u_id rec_u newkeys (msg : message t),
    findKeys msg = newkeys
    -> adv' = addUserKeys adv newkeys
    -> usrs $? rec_u_id = Some rec_u
    -> usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                  ; protocol := rec_u.(protocol) 
                                  ; msg_heap := rec_u.(msg_heap) ++ [Exm msg]  |})
    -> step_user u_id (Action (Output msg u_id))
                (usrs , adv , cs, ks, qmsgs, Send rec_u_id msg)
                (usrs', adv', cs, ks, qmsgs, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs cs' ks qmsgs (msg : message t) k k_id c_id cipherMsg,
    keyId k = k_id
    -> ks $? k_id = Some k
    -> ~(In c_id cs)
    -> encryptMessage k msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user u_id Silent
                (usrs, adv, cs , ks, qmsgs, Encrypt k msg)
                (usrs, adv, cs', ks, qmsgs, Return (Ciphertext c_id))

| StepDecrypt : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks ks' qmsgs (msg : message t) k_id k c_id newkeys,
      cs $? c_id = Some (Cipher c_id k_id msg)
    -> ( ks $? k_id = Some (AsymKey k true) (* check we have access to private key *)
      \/ ks $? k_id = Some (SymKey k) )
    -> k.(key_id) = k_id
    -> findKeys msg = newkeys
    -> ks' = ks $++ newkeys
    -> step_user u_id Silent
                (usrs, adv, cs, ks , qmsgs, Decrypt (Ciphertext c_id))
                (usrs, adv, cs, ks', qmsgs, Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs cs' ks qmsgs (msg : message t) k k_id c_id cipherMsg,
      keyId k = k_id
    -> ks $? k_id = Some k
    -> ~(In c_id cs)
    -> signMessage k msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user u_id Silent
                (usrs, adv, cs , ks, qmsgs, Sign k msg)
                (usrs, adv, cs', ks, qmsgs, Return (Signature msg c_id))

| StepVerify : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs (msg : message t) k_id k c_id,
    (* k is in your key heap *)
    ks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (Cipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> step_user u_id Silent
                (usrs, adv, cs, ks, qmsgs, (Verify k (MsgPair msg (Ciphertext c_id))))
                (usrs, adv, cs, ks, qmsgs, Return (if (k_id ==n (keyId k)) then true else false))
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

(* Lemma LStepRecv' : forall {B t} u_id (adv : adversaries B) globals globals' uks uks' (msg : message t) pat msgs newkeys, *)
(*       globals.(users_msg_buffer) $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *) *)
(*     -> globals' = setGlobalUserMsgs u_id msgs globals *)
(*     -> findKeys msg = newkeys *)
(*     -> msg_accepted_by_pattern globals.(all_ciphers) pat msg = true *)
(*     -> uks' = uks $++ newkeys *)
(*     -> lstep_user u_id (Action (Input msg pat u_id uks globals.(all_ciphers))) *)
(*                  (globals , adv, uks,  Recv pat) *)
(*                  (globals', adv, uks', Return msg). *)
(* Proof. *)
(*   intros; subst; econstructor; eauto. *)
(* Qed. *)

Inductive step_universe {A B} : universe A B -> rlabel -> universe A B -> Prop :=
| StepUser : forall U U' u_id userData usrs adv cs ks qmsgs lbl (cmd : user_cmd A),
    U.(users) $? u_id = Some userData
    -> step_user u_id lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverse usrs adv cs u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U lbl U'
| StepAdversary : forall U U' u_id userData usrs adv cs ks qmsgs lbl (cmd : user_cmd B),
    U.(adversary) $? u_id = Some userData
    -> step_user u_id lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverseAdv usrs adv cs u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U Silent U'
.
