From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := nat.

(* Possible usages for symmetric keys *)
Inductive symmetric_usage :=
| AES_GCM
| AES_CTR
| AES_KW
| HMAC.

(* Possible usages for asymmetric keys *)
Inductive asymmetric_usage :=
| RSA_Enc
| RSA_Dec
| ECDSA_Sig
| ECDSA_Ver.

(* Keys track identifiers, the user_id of the generating user, and a usage *) 
Record symmetric_key :=
  {sym_key_id : nat ;
   sym_generating_user_id : user_id ;
   sym_usage : symmetric_usage}.

(* Asymmetric keys track the above as well as the ID of the other key in the pair *)
Record asymmetric_key :=
  {asym_key_id : nat ;
   asym_generating_user_id : user_id ;
   asym_usage : asymmetric_usage ;
   asym_paired_key_id : nat}.

(* A master key type *)
Inductive key :=
| SymKey (k : symmetric_key)
| AsymKey (k : asymmetric_key).

(* Messages ultimately wrap either a string or a key 
   Messages can be encrypted, signed, or HMACed in a nested fashion any number of times 
   Note: the key_pair_message constructor is temporary and will be removed *)
Inductive message :=
| Plaintext (txt : string)
| Ciphertext (msg : message) (k_id : nat)
| Key_message (k : key)
| Key_pair_message (p : (key * key))
| Signature (k_id : nat) (signer_id : user_id) (msg : message)
| HMAC_message (k_id : nat) (msg : message).

(* Maybe: 
 * Return' (k : key)
 * Return'' (p : (key * key))
 * instead of adding a message type.
 *)

(* This type defines the syntax for valid commands in user protocols 
   Note: Semantically, GenerateSymKey and GenerateAsymKeys need to return key and key*key, respectively.
         We will define two additional commands ReturnK (k: key) and ReturnKP (p: key * key) to handle this.
         This will allow us to remove the key_pair_message constructor above *)
Inductive user_cmd :=
| Return (r : message)
| Bind (c1 : user_cmd) (c2 : message -> user_cmd)
| Send (uid : user_id) (msg : message)
| Recv
| Decrypt (k : option key) (ctxt : message)
| Encrypt (k : key) (ptxt : message)
| Sign (k : key) (msg : message)
| Verify (k : option key) (sig : message)
| ProduceHMAC (k : key) (msg : message)
| VerifyHMAC (k : option key) (mac : message)
| BindSymKey (c1 : user_cmd) (c2 : key -> user_cmd)
| BindAsymKeys (c1 : user_cmd) (c2 : (key * key) -> user_cmd)
| GenerateSymKey (usage : symmetric_usage)
| GenerateAsymKeys (usage : asymmetric_usage)
| Barrier.

(* A user has an id, memory heaps for keys and messages, a protocol, and a boolean administrator status *)
Record user_data :=
  {uid : user_id ;
   key_heap : fmap var key ;
   msg_heap : fmap var message ;
   protocol : user_cmd ;
   is_admin : bool }.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).
Notation "x <<- c1 ; c2" := (BindSymKey c1 (fun x => c2)) (right associativity, at level 75).
Notation "x <<<- c1 ; c2" := (BindAsymKeys c1 (fun x => c2)) (right associativity, at level 75).

(* The network stores message buffers for each user. Any messages sent to a user are stored here until
   the user calls Recv, at which point they are removed from the buffer and added to the user's msg_heap *)
Record network := construct_network
  { users_msg_buffer : fmap user_id (list message) ;
    trace : list (user_id * message) }.

(* The universe consists of some number of users and a network.
   The key_counter is a temporary hack to keep track of key_ids and make sure two users don't generate
   keys with the same id. *)
Record universe := construct_universe
  { users : fmap user_id user_data ;
    net : network ;
    key_counter : nat }.

(* Return : net *)
Definition send_message (msg_var : var) (from_user to_user : user_id) (U : universe) :=
match U.(users) $? from_user with
| Some u_data => match u_data.(msg_heap) $? msg_var with
                 | Some msg => match (U.(net)).(users_msg_buffer) $? to_user with
                               | Some msg_lst => {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (to_user, msg_lst ++ [msg]) ;
                                                    trace := (to_user , msg) :: (U.(net)).(trace) |} 
                               | None => U.(net)
                               end
                 | _ => U.(net) (* There was no matching msg to the var *)
                 end
| _ => U.(net) (* The sender is not valid *)
end.

(* Return : key_heap *)
Definition generate_symmetric_key (generating_user : user_id) (key_var : var) (U : universe) (usage : symmetric_usage) :=
match U.(users) $? generating_user with
| Some u_data => u_data.(key_heap) $+ (key_var, SymKey {| sym_key_id := U.(key_counter) ;
                                                        sym_generating_user_id := generating_user ;
                                                        sym_usage := usage |})
| None => $0
end.

(* Return : key_heap *)
Definition generate_asymmetric_key (generating_user : user_id) (key_var1 key_var2 : var) (U : universe) (usage : asymmetric_usage) :=
let usage' := match usage with
              | RSA_Enc => RSA_Dec
              | RSA_Dec => RSA_Enc
              | ECDSA_Sig => ECDSA_Ver
              | ECDSA_Ver => ECDSA_Sig
              end in
match U.(users) $? generating_user with
| Some u_data => u_data.(key_heap) $+ (key_var1, AsymKey {| asym_key_id := U.(key_counter) ;
                                                         asym_generating_user_id := generating_user ;
                                                         asym_usage := usage ;
                                                         asym_paired_key_id := U.(key_counter) + 1 |})
                                   $+ (key_var2, AsymKey {| asym_key_id := U.(key_counter) + 1 ;
                                                         asym_generating_user_id := generating_user ;
                                                         asym_usage := usage' ;
                                                         asym_paired_key_id := U.(key_counter) |}) 
| None => $0
end.

(* Return : Universe *)
Definition recv_message (recving_user : user_id) (U : universe) (x : var) :=
match (U.(net)).(users_msg_buffer) $? recving_user with
| Some msg_lst => match msg_lst with
                  | [] => U
                  | h::t => match U.(users) $? recving_user with 
                            | Some u_data => match h with
                                             | Key_message k => {| users := U.(users) $+
                                                                            (recving_user , {| uid := u_data.(uid) ;
                                                                                               key_heap := u_data.(key_heap) $+ (x, k) ;
                                                                                               msg_heap := u_data.(msg_heap) ;
                                                                                               protocol := u_data.(protocol) ;
                                                                                               is_admin := u_data.(is_admin) |}) ;
                                                                   net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (recving_user, t) ;
                                                                             trace := (U.(net)).(trace) |} ;
                                                                   key_counter := U.(key_counter) |}
                                             | _ => {| users := U.(users) $+ (recving_user , {| uid := u_data.(uid) ;
                                                                                                key_heap := u_data.(key_heap) ;
                                                                                                msg_heap := u_data.(msg_heap) $+ (x, h) ;
                                                                                                protocol := u_data.(protocol) ;
                                                                                                is_admin := u_data.(is_admin) |}) ;
                                                       net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (recving_user, t) ;
                                                                 trace := (U.(net)).(trace) |} ;
                                                       key_counter := U.(key_counter) |}
                                             end
                            | None => U
                            end
                  end
| None => U
end.

(* Return : Universe *)
Definition decrypt_message (u_id : user_id) (msg_var msg_var': var) (U : universe) (key_var : var) :=
match U.(users) $? u_id with
| Some u_data => match u_data.(msg_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (SymKey k) => match msg with
                                                  | Ciphertext msg' k' => match k.(sym_key_id) with
                                                                                 | k' => match msg' with
                                                                                         | Key_message km => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                                 key_heap := u_data.(key_heap) $+ (msg_var', km) ;
                                                                                                                                                 msg_heap := u_data.(msg_heap) ;
                                                                                                                                                 protocol := u_data.(protocol) ;
                                                                                                                                                 is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                         | _ => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                                                    msg_heap := u_data.(msg_heap) $+ (msg_var', msg') ;
                                                                                                                                    protocol := u_data.(protocol) ;
                                                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                                   net := U.(net) ;
                                                                                                   key_counter := U.(key_counter) |}
                                                                                         end
                                                                                 end
                                                  | _ => U (* There was nothing to decrypt *)
                                                  end
                               | Some (AsymKey k) => match msg with
                                                  | Ciphertext msg' k' => match k.(asym_key_id) with 
                                                                                 | k' => match msg' with
                                                                                         | Key_message km => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                                 key_heap := u_data.(key_heap) $+ (msg_var', km) ;
                                                                                                                                                 msg_heap := u_data.(msg_heap) ;
                                                                                                                                                 protocol := u_data.(protocol) ;
                                                                                                                                                 is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                         | _ => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                                                    msg_heap := u_data.(msg_heap) $+ (msg_var', msg') ;
                                                                                                                                    protocol := u_data.(protocol) ;
                                                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                                   net := U.(net) ;
                                                                                                   key_counter := U.(key_counter) |}
                                                                                         end
                                                                                 end
                                                  | _ => U (* There was nothing to decrypt *)
                                                  end
                               | _ => U (* Key_var does not correspond to a key *)
                               end
                 | None => U
                 end
| None => U
end.

(* Return : msg_heap *)
Definition encrypt_message (u_id : user_id) (msg_var msg_var': var) (key_var : var) (U : universe) :=
match U.(users) $? u_id with
| Some u_data => match u_data.(msg_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AsymKey k) => match k.(asym_usage) with
                                                  | RSA_Enc => u_data.(msg_heap) $+ (msg_var', (Ciphertext msg k.(asym_paired_key_id)))
                                                  | _ => u_data.(msg_heap)
                                                  end
                               | Some (SymKey k') => match k'.(sym_usage) with
                                                   | HMAC => u_data.(msg_heap)
                                                   | _ => u_data.(msg_heap) $+ (msg_var', (Ciphertext msg k'.(sym_key_id)))
                                                   end
                               | _ => u_data.(msg_heap)
                               end
                 | None => u_data.(msg_heap)
                 end
| None => $0
end.

(* Return : msg_heap *)
Definition sign (signee : user_id) (key_var msg_var signed_msg_var : var) (U : universe) :=
match U.(users) $? signee with
| Some u_data => match u_data.(msg_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AsymKey k) => match k.(asym_usage) with
                                                  | ECDSA_Sig => u_data.(msg_heap) $+ (signed_msg_var, (Signature k.(asym_paired_key_id) signee msg))
                                                  | _ => u_data.(msg_heap)
                                                  end
                               | _ => u_data.(msg_heap)
                               end
                 | None => u_data.(msg_heap)
                 end
| None => $0
end.

(* Return : msg_heap *)
Definition produceHMAC (producer : user_id) (key_var msg_var HMAC_var : var) (U : universe) :=
match U.(users) $? producer with
| Some u_data => match u_data.(msg_heap) $? msg_var with
              | Some msg => match u_data.(key_heap) $? key_var with
                            | Some (SymKey k) => match k.(sym_usage) with
                                               | HMAC => u_data.(msg_heap) $+ (HMAC_var, (HMAC_message k.(sym_key_id) msg))
                                               | _ => u_data.(msg_heap)
                                               end
                            | _ => u_data.(msg_heap)
                            end
              | None => u_data.(msg_heap)
              end
| None => $0
end.

(* Return : Universe *)
Definition verify (verifier : user_id) (key_var signed_msg_var verified_msg_var : var) (U : universe) :=
match U.(users) $? verifier with
| Some u_data => match u_data.(msg_heap) $? signed_msg_var with
                 | Some sym_msg => match u_data.(key_heap) $? key_var with
                                 | Some (AsymKey k) => match sym_msg with
                                                    | Signature k_id signee msg => if k_id =? k.(asym_paired_key_id)
                                                                                   then match msg with
                                                                                        | Key_message key => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                                    key_heap := u_data.(key_heap) $+ (verified_msg_var, key) ;
                                                                                                                                                    msg_heap := u_data.(msg_heap) ;
                                                                                                                                                    protocol := u_data.(protocol) ;
                                                                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                        | _ => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                             key_heap := u_data.(key_heap) ;
                                                                                                                                             msg_heap := u_data.(msg_heap) $+ (verified_msg_var, msg) ;
                                                                                                                                             protocol := u_data.(protocol) ;
                                                                                                                                             is_admin := u_data.(is_admin) |}) ;
                                                                                                  net := U.(net) ;
                                                                                                  key_counter := U.(key_counter) |}
                                                                                        end
                                                                                   else U
                                                    | _ => U
                                                    end
                                 | _ => U
                                 end
                 | None => U
                 end
| None => U
end.

(* Return : Universe *)
Definition verifyHMAC (verifier : user_id) (key_var HMAC_var verified_msg_var : var) (U : universe) :=
match U.(users) $? verifier with
| Some u_data => match u_data.(msg_heap) $? HMAC_var with
                 | Some HMAC_msg => match u_data.(key_heap) $? key_var with
                                 | Some (SymKey k) => match HMAC_msg with
                                                    | HMAC_message k_id msg => if k_id =? k.(sym_key_id)
                                                                               then match msg with
                                                                                    | Key_message key => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                                key_heap := u_data.(key_heap) $+ (verified_msg_var, key) ;
                                                                                                                                                msg_heap := u_data.(msg_heap) ;
                                                                                                                                                protocol := u_data.(protocol) ;
                                                                                                                                                is_admin := u_data.(is_admin) |}) ;
                                                                                                            net := U.(net) ;
                                                                                                            key_counter := U.(key_counter) |}
                                                                                    | _ => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                  key_heap := u_data.(key_heap) ;
                                                                                                                                  msg_heap := u_data.(msg_heap) $+ (verified_msg_var, msg) ;
                                                                                                                                  protocol := u_data.(protocol) ;
                                                                                                                                  is_admin := u_data.(is_admin) |}) ;
                                                                                              net := U.(net) ;
                                                                                              key_counter := U.(key_counter) |}
                                                                                        end
                                                                                   else U
                                                    | _ => U
                                                    end
                                 | _ => U
                                 end
                 | None => U
                 end
| None => U
end.

(* Ping Protocol *)

(* U.(users) *)
Example ping_users :=
 $0 $+ (0, {| uid := 0 ;
              key_heap := $0 ;
              msg_heap := $0 ;
              protocol := (a <<<- (GenerateAsymKeys RSA_Enc) ;
                                  (b <- (Send 1 (Key_message (match a with
                                                      | (pair p s) => p
                                                      end))) ;
                                        (c <<<- (GenerateAsymKeys ECDSA_Sig) ;
                                               (d <- (Send 1 (Key_message (match c with
                                                                           | (pair p s) => p
                                                                           end))) ;
                                                     (e <- (Sign (match c with
                                                                           | (pair p s) => s
                                                                           end) (Plaintext "Hello")) ;
                                                           (f <- (Encrypt (match a with
                                                                           | (pair p s) => s
                                                                           end) e) ;
                                                                 (g <- (Send 1 f) ;
                                                                        Recv))))))) ;
              is_admin := false |})
    $+ (1 , {| uid := 1 ;
               key_heap := $0 ;
               msg_heap := $0 ;
               protocol := (a <- Recv ;
                                (b <- Recv ;
                                     (c <- Recv ;
                                          (d <- (Decrypt (match a with
                                                                | Key_message k' => Some k'
                                                                | _ => None
                                                                end) c) ;
                                                (e <- (Verify (match b with
                                                         | Key_message k => Some k
                                                         | _ => None
                                                         end) d) ;
                                                      (Send 0 e)))))) ;
               is_admin := false |}).

(* Ping Universe *)
Example ping_universe :=
{| users := ping_users ;
   net := {| users_msg_buffer := $0 $+ (0, []) $+ (1, []) ;
             trace := [] |} ;
   key_counter := 0 |}.

Inductive step : universe -> universe -> Prop :=
| StepSign : forall signee key_var msg_var signed_msg_var U u_data k msg msg_heap' users' signed_message,
    U.(users) $? signee = Some u_data ->
    u_data.(key_heap) $? key_var = Some (AsymKey k) ->
    u_data.(msg_heap) $? msg_var = Some msg ->
    ~ (signed_msg_var \in dom u_data.(msg_heap)) ->
    k.(asym_usage) = ECDSA_Sig ->
    u_data.(protocol) = Sign (AsymKey k) msg ->
    msg_heap' = (sign signee key_var msg_var signed_msg_var U) ->
    msg_heap' $? signed_msg_var = Some signed_message -> 
    users' = U.(users) $+ (signee, {| uid := signee ;
                                      key_heap := u_data.(key_heap) ;
                                      msg_heap := msg_heap' ;
                                      protocol := Return signed_message ;
                                      is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) |}
| StepProduceHMAC : forall producer key_var msg_var HMAC_var U u_data k msg msg_heap' users' HMAC_message,
    U.(users) $? producer = Some u_data ->
    u_data.(key_heap) $? key_var = Some (SymKey k) ->
    u_data.(msg_heap) $? msg_var = Some msg ->
    ~ (HMAC_var \in dom u_data.(msg_heap)) ->
    k.(sym_usage) = HMAC ->
    u_data.(protocol) = ProduceHMAC (SymKey k) msg ->
    msg_heap' = (produceHMAC producer key_var msg_var HMAC_var U) ->
    msg_heap' $? HMAC_var = Some HMAC_message ->
    users' = U.(users) $+ (producer, {| uid := producer ;
                                        key_heap := u_data.(key_heap) ;
                                        msg_heap := msg_heap' ;
                                        protocol := Return HMAC_message ;
                                        is_admin := u_data.(is_admin) |}) ->
    step U {| users := users' ;
              net := U.(net) ;
              key_counter := U.(key_counter) |}
| StepVerifyHMAC : forall verifier key_var HMAC_var verified_msg_var U u_data HMAC_msg KeyType U' u_data' users' k_id msg k,
    U.(users) $? verifier = Some u_data ->
    u_data.(msg_heap) $? HMAC_var = Some HMAC_msg ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    HMAC_msg = HMAC_message k_id msg ->
    KeyType = SymKey k ->
    k.(sym_key_id) = k_id ->
    match msg with
    | Key_message k => ~ (verified_msg_var \in dom u_data.(msg_heap))
    | _ => ~ (verified_msg_var \in dom u_data.(key_heap))
    end ->
    U' = (verifyHMAC verifier key_var HMAC_var verified_msg_var U) ->
    U'.(users) $? verifier = Some u_data' ->
    users' = U'.(users) $+ (verifier, {| uid := verifier ;
                                         key_heap := u_data'.(key_heap) ;
                                         msg_heap := u_data'.(msg_heap) ;
                                         protocol := Return msg ;
                                         is_admin := u_data'.(is_admin) |}) ->
    u_data.(protocol) = VerifyHMAC (Some KeyType) HMAC_msg ->
    step U {| users := users' ;
              net := U'.(net) ;
              key_counter := U'.(key_counter) |}
| StepVerify : forall verifier key_var signed_msg_var verified_msg_var U u_data signed_message KeyType U' u_data' users' k_id msg k signee,
    U.(users) $? verifier = Some u_data ->
    u_data.(msg_heap) $? signed_msg_var = Some signed_message ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    signed_message = Signature k_id signee msg ->
    KeyType = AsymKey k ->
    k.(asym_key_id) = k_id ->
    match msg with
    | Key_message k' => ~ (verified_msg_var \in dom u_data.(msg_heap))
    | _ => ~ (verified_msg_var \in dom u_data.(key_heap))
    end ->
    U' = (verify verifier key_var signed_msg_var verified_msg_var U) ->
    U'.(users) $? verifier = Some u_data' ->
    users' = U'.(users) $+ (verifier, {| uid := verifier ;
                                         key_heap := u_data'.(key_heap) ;
                                         msg_heap := u_data'.(msg_heap) ;
                                         protocol := Return msg ;
                                         is_admin := u_data'.(is_admin) |}) ->
    u_data.(protocol) = Verify (Some KeyType) signed_message ->
      step U {| users := users' ;
                net := U'.(net) ;
                key_counter := U'.(key_counter) |}
| StepEncrypt : forall u_id msg_var msg_var' key_var U u_data msg KeyType msg_heap' users' encrypted_msg,
    U.(users) $? u_id = Some u_data ->
    u_data.(msg_heap) $? msg_var = Some msg ->
    ~ (msg_var' \in dom u_data.(msg_heap)) ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    match KeyType with
    | AsymKey k => k.(asym_usage) = RSA_Enc
    | SymKey k => ~ (k.(sym_usage) = HMAC)
    end ->
    u_data.(protocol) = Encrypt KeyType msg ->
    msg_heap' = (encrypt_message u_id msg_var msg_var' key_var U) ->
    msg_heap' $? msg_var' = Some encrypted_msg ->
    users' = U.(users) $+ (u_id, {| uid := u_id ;
                                    key_heap := u_data.(key_heap) ;
                                    msg_heap := msg_heap' ;
                                    protocol := Return encrypted_msg ;
                                    is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) |}
| StepDecrypt : forall u_id msg_var msg_var' U key_var u_data msg k_id k U' u_data' users',
    U.(users) $? u_id = Some u_data ->
    u_data.(msg_heap) $? msg_var = Some (Ciphertext msg k_id) ->
    u_data.(key_heap) $? key_var = Some k ->
    match msg with
    | Key_message k => ~ (msg_var' \in dom u_data.(msg_heap))
    | _ => ~ (msg_var' \in dom u_data.(key_heap))
    end ->
    match k with
    | SymKey skey => skey.(sym_key_id) = k_id
    | AsymKey akey => akey.(asym_key_id) = k_id
    end ->
    u_data.(protocol) = Decrypt (Some k) (Ciphertext msg k_id) ->
    U' = (decrypt_message u_id msg_var msg_var' U key_var) ->
    U'.(users) $? u_id = Some u_data' ->
    users' = U'.(users) $+ (u_id, {| uid := u_id ;
                                     key_heap := u_data'.(key_heap) ;
                                     msg_heap := u_data'.(msg_heap) ;
                                     protocol := Return msg ;
                                     is_admin := u_data'.(is_admin) |}) ->
      step U {| users := users' ;
                net := U'.(net) ;
                key_counter := U'.(key_counter) |}
| StepGenerateAsymKey : forall generating_user key_var1 key_var2 U usage u_data key_heap' users' key1 key2,
    U.(users) $? generating_user = Some u_data ->
    ~ (key_var1 \in dom u_data.(key_heap)) ->
    ~ (key_var2 \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateAsymKeys usage ->
    key_heap' = (generate_asymmetric_key generating_user key_var1 key_var2 U usage) ->
    key_heap' $? key_var1 = Some key1 ->
    key_heap' $? key_var2 = Some key2 ->
    users' = U.(users) $+ (generating_user, {| uid := generating_user ;
                           key_heap := key_heap' ;
                           msg_heap := u_data.(msg_heap) ;
                           protocol := Return (Key_pair_message (pair key1 key2)) ;
                           is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) + 2 ;|}
| StepGenerateSymKey : forall generating_user key_var U usage u_data key_heap' users' key,
    U.(users) $? generating_user = Some u_data ->
    ~ (key_var \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateSymKey usage ->
    key_heap' = (generate_symmetric_key generating_user key_var U usage) ->
    key_heap' $? key_var = Some key ->
    users' = U.(users) $+ (generating_user, {| uid := generating_user ;
                                         key_heap := key_heap' ;
                                         msg_heap := u_data.(msg_heap) ;
                                         protocol := Return (Key_message key) ;
                                         is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) + 1|}
| StepRecv : forall U recving_user msg_var u_data msg_buffer U' u_data' users' h t,
    U.(users) $? recving_user = Some u_data ->
    (U.(net)).(users_msg_buffer) $? recving_user = Some msg_buffer ->
    msg_buffer = h::t -> 
    match h with
    | Key_message _ => ~ (msg_var \in dom u_data.(key_heap))
    | _ => ~ (msg_var \in dom u_data.(msg_heap))
    end ->
    U' = (recv_message recving_user U msg_var) ->
    U'.(users) $? recving_user = Some u_data' ->
    users' = U.(users) $+ (recving_user, {| uid := recving_user ;
                                            key_heap := u_data'.(key_heap) ;
                                            msg_heap := u_data'.(msg_heap) ;
                                            protocol := Return h ;
                                            is_admin := u_data'.(is_admin) |}) ->
    u_data.(protocol) = Recv ->
      step U {| users := users' ;
                net := U'.(net) ;
                key_counter := U'.(key_counter) |}
| StepSend : forall U msg_var from_id to_id u_data msg users',
    U.(users) $? from_id = Some u_data ->
    to_id \in dom U.(users) ->
    to_id \in dom (U.(net)).(users_msg_buffer) ->
    u_data.(protocol) = Send to_id msg ->
    users' = U.(users) $+ (from_id, {| uid := from_id ;
                                       key_heap := u_data.(key_heap) ;
                                       msg_heap := u_data.(msg_heap) ;
                                       protocol := (Return (Plaintext "Sent Message")) ;
                                       is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := send_message msg_var from_id to_id U ;
                key_counter := U.(key_counter) |}.
(*
Need to work with Alice for semantics for the following commands:
| Return
| Bind
| BindSymKey
| BindAsymKey
| Barrier
*)

(* Outstanding Questions
  1. Can we implement a notion of "randomness" that will prevent two users from generating the same key id?
  2. What is the correct way to do error handling? Problem observed by reciever during ping protocol.
     Currently using option type.
 *)

(* Not as hard questions
 * 1. semantic definitions : When key doesn't match, we currently return the original Universe instead of returning an error of
 *                           some kind. I think this can be checked beforehand in the step function...
 * 2. user_cmd : Because sign and verify require [option key], should encrypt and sign require that as well?
 *)

(* Additional functionality to implement:
   1. Administration
   2. CA
*) 