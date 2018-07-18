From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

Definition user_id := nat.

Inductive symmetric_usage :=
| GCM
| CTR
| KW
| HMAC.

Inductive asymmetric_usage :=
| RSA_E
| RSA_D
| ECDSA_S
| ECDSA_V.

Record symmetric_key :=
  {s_key_id : nat ;
   s_generator_id : user_id ;
   s_usage : symmetric_usage}.

Record asymmetric_key :=
  {a_key_id : nat ;
   a_generator_id : user_id ;
   a_usage : asymmetric_usage ;
   a_paired_key_id : nat}.

Inductive key :=
| SKey (k : symmetric_key)
| AKey (k : asymmetric_key).

Inductive message :=
| Plaintext (txt : string)
| Ciphertext (msg : message) (k_id : nat)
| Key_message (k : key)
| Key_pair_message (p : (key * key)) (* Added this type to make RETURN typecheck with generate_asymmetric_key *)
| Signature (k_id : nat) (signer_id : user_id) (msg : message)
| HMAC_message (k_id : nat) (msg : message).

(* Maybe: 
 * Return' (k : key)
 * Return'' (p : (key * key))
 * instead of adding a message type.
 *)
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
| BindSKey (c1 : user_cmd) (c2 : key -> user_cmd)
| BindAKeys (c1 : user_cmd) (c2 : (key * key) -> user_cmd)
| GenerateSKey (usage : symmetric_usage)
| GenerateAKeys (usage : asymmetric_usage)
| Barrier.

Record user_data :=
  {uid : user_id ;
   key_heap : fmap var key ;
   mem_heap : fmap var message ;
   protocol : user_cmd ;
   is_admin : bool }.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).
Notation "x <<- c1 ; c2" := (BindSKey c1 (fun x => c2)) (right associativity, at level 75).
Notation "x >- c1 ; c2" := (BindAKeys c1 (fun x => c2)) (right associativity, at level 75).

Record network := construct_network
  { users_msg_buffer : fmap user_id (list message) ;
    trace : list (user_id * message) }.

(* Hack to keep track of key_ids : key_counter *)
Record universe := construct_universe
  { users : fmap user_id user_data ;
    net : network ;
    key_counter : nat }.

(* Return : net *)
Definition send_message (msg_var : var) (from_user to_user : user_id) (U : universe) :=
match U.(users) $? from_user with
| Some u_data => match u_data.(mem_heap) $? msg_var with
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
Definition generate_symmetric_key (generator : user_id) (key_var : var) (U : universe) (usage : symmetric_usage) :=
match U.(users) $? generator with
| Some u_data => u_data.(key_heap) $+ (key_var, SKey {| s_key_id := U.(key_counter) ;
                                                        s_generator_id := generator ;
                                                        s_usage := usage |})
| None => $0
end.

(* Return : key_heap *)
Definition generate_asymmetric_key (generator : user_id) (key_var1 key_var2 : var) (U : universe) (usage : asymmetric_usage) :=
let usage' := match usage with
              | RSA_E => RSA_D
              | RSA_D => RSA_E
              | ECDSA_S => ECDSA_V
              | ECDSA_V => ECDSA_S
              end in
match U.(users) $? generator with
| Some u_data => u_data.(key_heap) $+ (key_var1, AKey {| a_key_id := U.(key_counter) ;
                                                         a_generator_id := generator ;
                                                         a_usage := usage ;
                                                         a_paired_key_id := U.(key_counter) + 1 |})
                                   $+ (key_var2, AKey {| a_key_id := U.(key_counter) + 1 ;
                                                         a_generator_id := generator ;
                                                         a_usage := usage' ;
                                                         a_paired_key_id := U.(key_counter) |}) 
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
                                                                                               mem_heap := u_data.(mem_heap) ;
                                                                                               protocol := u_data.(protocol) ;
                                                                                               is_admin := u_data.(is_admin) |}) ;
                                                                   net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (recving_user, t) ;
                                                                             trace := (U.(net)).(trace) |} ;
                                                                   key_counter := U.(key_counter) |}
                                             | _ => {| users := U.(users) $+ (recving_user , {| uid := u_data.(uid) ;
                                                                                                key_heap := u_data.(key_heap) ;
                                                                                                mem_heap := u_data.(mem_heap) $+ (x, h) ;
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
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (SKey k) => match msg with
                                                  | Ciphertext msg' k' => match k.(s_key_id) with
                                                                                 | k' => match msg' with
                                                                                         | Key_message km => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                                 key_heap := u_data.(key_heap) $+ (msg_var', km) ;
                                                                                                                                                 mem_heap := u_data.(mem_heap) ;
                                                                                                                                                 protocol := u_data.(protocol) ;
                                                                                                                                                 is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                         | _ => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                                                    mem_heap := u_data.(mem_heap) $+ (msg_var', msg') ;
                                                                                                                                    protocol := u_data.(protocol) ;
                                                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                                   net := U.(net) ;
                                                                                                   key_counter := U.(key_counter) |}
                                                                                         end
                                                                                 end
                                                  | _ => U (* There was nothing to decrypt *)
                                                  end
                               | Some (AKey k) => match msg with
                                                  | Ciphertext msg' k' => match k.(a_key_id) with 
                                                                                 | k' => match msg' with
                                                                                         | Key_message km => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                                 key_heap := u_data.(key_heap) $+ (msg_var', km) ;
                                                                                                                                                 mem_heap := u_data.(mem_heap) ;
                                                                                                                                                 protocol := u_data.(protocol) ;
                                                                                                                                                 is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                         | _ => {| users := U.(users) $+ (u_id , {| uid := u_id ;
                                                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                                                    mem_heap := u_data.(mem_heap) $+ (msg_var', msg') ;
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

(* Return : mem_heap *)
Definition encrypt_message (u_id : user_id) (msg_var msg_var': var) (key_var : var) (U : universe) :=
match U.(users) $? u_id with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | RSA_E => u_data.(mem_heap) $+ (msg_var', (Ciphertext msg k.(a_paired_key_id)))
                                                  | _ => u_data.(mem_heap)
                                                  end
                               | Some (SKey k') => match k'.(s_usage) with
                                                   | HMAC => u_data.(mem_heap)
                                                   | _ => u_data.(mem_heap) $+ (msg_var', (Ciphertext msg k'.(s_key_id)))
                                                   end
                               | _ => u_data.(mem_heap)
                               end
                 | None => u_data.(mem_heap)
                 end
| None => $0
end.

(* Return : mem_heap *)
Definition sign (signee : user_id) (key_var msg_var signed_msg_var : var) (U : universe) :=
match U.(users) $? signee with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | ECDSA_S => u_data.(mem_heap) $+ (signed_msg_var, (Signature k.(a_paired_key_id) signee msg))
                                                  | _ => u_data.(mem_heap)
                                                  end
                               | _ => u_data.(mem_heap)
                               end
                 | None => u_data.(mem_heap)
                 end
| None => $0
end.

(* Return : mem_heap *)
Definition produceHMAC (producer : user_id) (key_var msg_var HMAC_var : var) (U : universe) :=
match U.(users) $? producer with
| Some u_data => match u_data.(mem_heap) $? msg_var with
              | Some msg => match u_data.(key_heap) $? key_var with
                            | Some (SKey k) => match k.(s_usage) with
                                               | HMAC => u_data.(mem_heap) $+ (HMAC_var, (HMAC_message k.(s_key_id) msg))
                                               | _ => u_data.(mem_heap)
                                               end
                            | _ => u_data.(mem_heap)
                            end
              | None => u_data.(mem_heap)
              end
| None => $0
end.

(* Return : Universe *)
Definition verify (verifier : user_id) (key_var signed_msg_var verified_msg_var : var) (U : universe) :=
match U.(users) $? verifier with
| Some u_data => match u_data.(mem_heap) $? signed_msg_var with
                 | Some s_msg => match u_data.(key_heap) $? key_var with
                                 | Some (AKey k) => match s_msg with
                                                    | Signature k_id signee msg => if k_id =? k.(a_paired_key_id)
                                                                                   then match msg with
                                                                                        | Key_message key => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                                    key_heap := u_data.(key_heap) $+ (verified_msg_var, key) ;
                                                                                                                                                    mem_heap := u_data.(mem_heap) ;
                                                                                                                                                    protocol := u_data.(protocol) ;
                                                                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                                                net := U.(net) ;
                                                                                                                key_counter := U.(key_counter) |}
                                                                                        | _ => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                             key_heap := u_data.(key_heap) ;
                                                                                                                                             mem_heap := u_data.(mem_heap) $+ (verified_msg_var, msg) ;
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
| Some u_data => match u_data.(mem_heap) $? HMAC_var with
                 | Some HMAC_msg => match u_data.(key_heap) $? key_var with
                                 | Some (SKey k) => match HMAC_msg with
                                                    | HMAC_message k_id msg => if k_id =? k.(s_key_id)
                                                                               then match msg with
                                                                                    | Key_message key => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                                key_heap := u_data.(key_heap) $+ (verified_msg_var, key) ;
                                                                                                                                                mem_heap := u_data.(mem_heap) ;
                                                                                                                                                protocol := u_data.(protocol) ;
                                                                                                                                                is_admin := u_data.(is_admin) |}) ;
                                                                                                            net := U.(net) ;
                                                                                                            key_counter := U.(key_counter) |}
                                                                                    | _ => {| users := U.(users) $+ (verifier, {| uid := verifier ;
                                                                                                                                  key_heap := u_data.(key_heap) ;
                                                                                                                                  mem_heap := u_data.(mem_heap) $+ (verified_msg_var, msg) ;
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
              mem_heap := $0 ;
              protocol := (a >- (GenerateAKeys RSA_E) ;
                                  (b <- (Send 1 (Key_message (match a with
                                                      | (pair p s) => p
                                                      end))) ;
                                        (c >- (GenerateAKeys ECDSA_S) ;
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
               mem_heap := $0 ;
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
| StepSign : forall signee key_var msg_var signed_msg_var U u_data k msg mem_heap' users' signed_message,
    U.(users) $? signee = Some u_data ->
    u_data.(key_heap) $? key_var = Some (AKey k) ->
    u_data.(mem_heap) $? msg_var = Some msg ->
    ~ (signed_msg_var \in dom u_data.(mem_heap)) ->
    k.(a_usage) = ECDSA_S ->
    u_data.(protocol) = Sign (AKey k) msg ->
    mem_heap' = (sign signee key_var msg_var signed_msg_var U) ->
    mem_heap' $? signed_msg_var = Some signed_message -> 
    users' = U.(users) $+ (signee, {| uid := signee ;
                                      key_heap := u_data.(key_heap) ;
                                      mem_heap := mem_heap' ;
                                      protocol := Return signed_message ;
                                      is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) |}
| StepProduceHMAC : forall producer key_var msg_var HMAC_var U u_data k msg mem_heap' users' HMAC_message,
    U.(users) $? producer = Some u_data ->
    u_data.(key_heap) $? key_var = Some (SKey k) ->
    u_data.(mem_heap) $? msg_var = Some msg ->
    ~ (HMAC_var \in dom u_data.(mem_heap)) ->
    k.(s_usage) = HMAC ->
    u_data.(protocol) = ProduceHMAC (SKey k) msg ->
    mem_heap' = (produceHMAC producer key_var msg_var HMAC_var U) ->
    mem_heap' $? HMAC_var = Some HMAC_message ->
    users' = U.(users) $+ (producer, {| uid := producer ;
                                        key_heap := u_data.(key_heap) ;
                                        mem_heap := mem_heap' ;
                                        protocol := Return HMAC_message ;
                                        is_admin := u_data.(is_admin) |}) ->
    step U {| users := users' ;
              net := U.(net) ;
              key_counter := U.(key_counter) |}
| StepVerifyHMAC : forall verifier key_var HMAC_var verified_msg_var U u_data HMAC_msg KeyType U' u_data' users' k_id msg k,
    U.(users) $? verifier = Some u_data ->
    u_data.(mem_heap) $? HMAC_var = Some HMAC_msg ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    HMAC_msg = HMAC_message k_id msg ->
    KeyType = SKey k ->
    k.(s_key_id) = k_id ->
    match msg with
    | Key_message k => ~ (verified_msg_var \in dom u_data.(mem_heap))
    | _ => ~ (verified_msg_var \in dom u_data.(key_heap))
    end ->
    U' = (verifyHMAC verifier key_var HMAC_var verified_msg_var U) ->
    U'.(users) $? verifier = Some u_data' ->
    users' = U'.(users) $+ (verifier, {| uid := verifier ;
                                         key_heap := u_data'.(key_heap) ;
                                         mem_heap := u_data'.(mem_heap) ;
                                         protocol := Return msg ;
                                         is_admin := u_data'.(is_admin) |}) ->
    u_data.(protocol) = VerifyHMAC (Some KeyType) HMAC_msg ->
    step U {| users := users' ;
              net := U'.(net) ;
              key_counter := U'.(key_counter) |}
| StepVerify : forall verifier key_var signed_msg_var verified_msg_var U u_data signed_message KeyType U' u_data' users' k_id msg k signee,
    U.(users) $? verifier = Some u_data ->
    u_data.(mem_heap) $? signed_msg_var = Some signed_message ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    signed_message = Signature k_id signee msg ->
    KeyType = AKey k ->
    k.(a_key_id) = k_id ->
    match msg with
    | Key_message k' => ~ (verified_msg_var \in dom u_data.(mem_heap))
    | _ => ~ (verified_msg_var \in dom u_data.(key_heap))
    end ->
    U' = (verify verifier key_var signed_msg_var verified_msg_var U) ->
    U'.(users) $? verifier = Some u_data' ->
    users' = U'.(users) $+ (verifier, {| uid := verifier ;
                                         key_heap := u_data'.(key_heap) ;
                                         mem_heap := u_data'.(mem_heap) ;
                                         protocol := Return msg ;
                                         is_admin := u_data'.(is_admin) |}) ->
    u_data.(protocol) = Verify (Some KeyType) signed_message ->
      step U {| users := users' ;
                net := U'.(net) ;
                key_counter := U'.(key_counter) |}
| StepEncrypt : forall u_id msg_var msg_var' key_var U u_data msg KeyType mem_heap' users' encrypted_msg,
    U.(users) $? u_id = Some u_data ->
    u_data.(mem_heap) $? msg_var = Some msg ->
    ~ (msg_var' \in dom u_data.(mem_heap)) ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    match KeyType with
    | AKey k => k.(a_usage) = RSA_E
    | SKey k => ~ (k.(s_usage) = HMAC)
    end ->
    u_data.(protocol) = Encrypt KeyType msg ->
    mem_heap' = (encrypt_message u_id msg_var msg_var' key_var U) ->
    mem_heap' $? msg_var' = Some encrypted_msg ->
    users' = U.(users) $+ (u_id, {| uid := u_id ;
                                    key_heap := u_data.(key_heap) ;
                                    mem_heap := mem_heap' ;
                                    protocol := Return encrypted_msg ;
                                    is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) |}
| StepDecrypt : forall u_id msg_var msg_var' U key_var u_data msg k_id k U' u_data' users',
    U.(users) $? u_id = Some u_data ->
    u_data.(mem_heap) $? msg_var = Some (Ciphertext msg k_id) ->
    u_data.(key_heap) $? key_var = Some k ->
    match msg with
    | Key_message k => ~ (msg_var' \in dom u_data.(mem_heap))
    | _ => ~ (msg_var' \in dom u_data.(key_heap))
    end ->
    match k with
    | SKey skey => skey.(s_key_id) = k_id
    | AKey akey => akey.(a_key_id) = k_id
    end ->
    u_data.(protocol) = Decrypt (Some k) (Ciphertext msg k_id) ->
    U' = (decrypt_message u_id msg_var msg_var' U key_var) ->
    U'.(users) $? u_id = Some u_data' ->
    users' = U'.(users) $+ (u_id, {| uid := u_id ;
                                     key_heap := u_data'.(key_heap) ;
                                     mem_heap := u_data'.(mem_heap) ;
                                     protocol := Return msg ;
                                     is_admin := u_data'.(is_admin) |}) ->
      step U {| users := users' ;
                net := U'.(net) ;
                key_counter := U'.(key_counter) |}
| StepGenerateAKey : forall generator key_var1 key_var2 U usage u_data key_heap' users' key1 key2,
    U.(users) $? generator = Some u_data ->
    ~ (key_var1 \in dom u_data.(key_heap)) ->
    ~ (key_var2 \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateAKeys usage ->
    key_heap' = (generate_asymmetric_key generator key_var1 key_var2 U usage) ->
    key_heap' $? key_var1 = Some key1 ->
    key_heap' $? key_var2 = Some key2 ->
    users' = U.(users) $+ (generator, {| uid := generator ;
                           key_heap := key_heap' ;
                           mem_heap := u_data.(mem_heap) ;
                           protocol := Return (Key_pair_message (pair key1 key2)) ;
                           is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := U.(net) ;
                key_counter := U.(key_counter) + 2 ;|}
| StepGenerateSKey : forall generator key_var U usage u_data key_heap' users' key,
    U.(users) $? generator = Some u_data ->
    ~ (key_var \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateSKey usage ->
    key_heap' = (generate_symmetric_key generator key_var U usage) ->
    key_heap' $? key_var = Some key ->
    users' = U.(users) $+ (generator, {| uid := generator ;
                                         key_heap := key_heap' ;
                                         mem_heap := u_data.(mem_heap) ;
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
    | _ => ~ (msg_var \in dom u_data.(mem_heap))
    end ->
    U' = (recv_message recving_user U msg_var) ->
    U'.(users) $? recving_user = Some u_data' ->
    users' = U.(users) $+ (recving_user, {| uid := recving_user ;
                                            key_heap := u_data'.(key_heap) ;
                                            mem_heap := u_data'.(mem_heap) ;
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
                                       mem_heap := u_data.(mem_heap) ;
                                       protocol := (Return (Plaintext "Sent Message")) ;
                                       is_admin := u_data.(is_admin) |}) ->
      step U {| users := users' ;
                net := send_message msg_var from_id to_id U ;
                key_counter := U.(key_counter) |}.
(*
Need Alice for the ones below.
| Return
| Bind
| BindSKey
| BindAKey
| Barrier
*)

(* Outstanding Questions
 * 1. What is the best way to keep track of the count of already existing keys? Or, better yet, what
 *    is the best way to generate random key ids?
 * 2. What is the correct way to do error handling? Problem observed by reciever during ping protocol.
 *    Currently using option type.
 *)

(* Not as hard questions ?
 * 1. semantic definitions : When key doesn't match, we currently return the original Universe instead of returning an error of
 *                           some kind. I think this can be checked beforehand in the step function...
 * 2. network_message : Are we still using the network_message type?
 * 3. user_cmd : Because sign and verify require [option key], should encrypt and sign require that as well?
 *)