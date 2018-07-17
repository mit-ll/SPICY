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

(* Changing (k : key) to (k_id : nat) in Ciphertext.
 * When a user will decrypt a ciphertext, it will provide a key var.
 *  That key var should map to a key, which has the same key_id that
 *  matches the one necessary for the ciphertext.
 *
 * This change may also need to be done on HMAC message
 *)
Inductive message :=
| Plaintext (txt : string)
| Ciphertext (msg : message) (k_id : nat)
| Key_message (k : key)
| Signature (k_id : nat) (signer_id : user_id) (msg : message)
| HMAC_message (k : symmetric_key) (msg : message).

Inductive network_message := (* Not even really used at this point? *)
| nmessage (msg : message) (uid : user_id).

Inductive user_cmd := (* Because sign and verify require [option key], should encrypt and sign require that as well? *)
| Return (r : message)
| Bind (c1 : user_cmd) (c2 : message -> user_cmd)
| Send (uid : user_id) (msg : message)
| Recv
| Decrypt (k : option key) (ctxt : message)
| Encrypt (k : key) (ptxt : message)
| Sign (k : key) (msg : message)
| Verify (k : option key) (sig : message)
| ProduceHMAC (k : key) (msg : message)
| VerifyHMAC (k : key) (mac : message)
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
Notation "x >--- c1 ; c2" := (BindAKeys c1 (fun x => c2)) (right associativity, at level 75).

Record network := construct_network
  { users_msg_buffer : fmap user_id (list message) ;
    trace : list (user_id * message) }.

(* Hack to keep track of key_ids : key_counter *)
Record universe := construct_universe
  { users : fmap user_id user_data ;
    net : network ;
    key_counter : nat }.

(* For the below, the cmd's will be removed from protocol in the step function to 
 * resemble what is done in the ideal model 
 *)
Definition send_message (msg_var : var) (from_user to_user : user_id) (U : universe) :=
match U.(users) $? from_user with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match (U.(net)).(users_msg_buffer) $? to_user with
                               | Some msg_lst => {| users := U.(users) ;
                                                    net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (to_user, msg_lst ++ [msg]) ;
                                                              trace := (to_user , msg) :: (U.(net)).(trace) |} ;
                                                    key_counter := U.(key_counter) |}
                               | None => U
                               end
                 | _ => U (* There was no matching msg to the var *)
                 end
| _ => U (* The sender is not valid *)
end.

Definition generate_symmetric_key (generator : user_id) (key_var : var) (U : universe) (usage : symmetric_usage) :=
match U.(users) $? generator with
| Some u_data => {| users := U.(users) $+ (generator, {| uid := generator ;
                                                         key_heap := u_data.(key_heap) $+ (key_var, SKey {| s_key_id := U.(key_counter) ;
                                                                                                            s_generator_id := generator ;
                                                                                                            s_usage := usage |}) ;
                                                         mem_heap := u_data.(mem_heap) ;
                                                         protocol := u_data.(protocol) ;
                                                         is_admin := u_data.(is_admin) |}) ;
                    net := U.(net) ;
                    key_counter := U.(key_counter) + 1 |}
| None => U
end.

Definition generate_asymmetric_key (generator : user_id) (key_var1 key_var2 : var) (U : universe) (usage : asymmetric_usage) :=
let usage' := match usage with
              | RSA_E => RSA_D
              | RSA_D => RSA_E
              | ECDSA_S => ECDSA_V
              | ECDSA_V => ECDSA_S
              end in
match U.(users) $? generator with
| Some u_data => {| users := U.(users) $+ (generator, {| uid := generator ;
                                                         key_heap := u_data.(key_heap) $+ (key_var1, AKey {| a_key_id := U.(key_counter) ;
                                                                                                             a_generator_id := generator ;
                                                                                                             a_usage := usage ;
                                                                                                             a_paired_key_id := U.(key_counter) + 1 |})
                                                                                       $+ (key_var2, AKey {| a_key_id := U.(key_counter) + 1 ;
                                                                                                             a_generator_id := generator ;
                                                                                                             a_usage := usage' ;
                                                                                                             a_paired_key_id := U.(key_counter) |}) ;
                                                         mem_heap := u_data.(mem_heap) ;
                                                         protocol := u_data.(protocol) ;
                                                         is_admin := u_data.(is_admin) |}) ;
                    net := U.(net) ;
                    key_counter := U.(key_counter) + 2 |}
| None => U
end.

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

Definition encrypt_message (u_id : user_id) (msg_var msg_var': var) (key_var : var) (U : universe) :=
match U.(users) $? u_id with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | RSA_E => {| users := U.(users) $+ (u_id, {| uid := u_id ;
                                                                                                key_heap := u_data.(key_heap) ;
                                                                                                mem_heap := u_data.(mem_heap) $+ (msg_var', (Ciphertext msg k.(a_paired_key_id))) ;
                                                                                                protocol := u_data.(protocol) ;
                                                                                                is_admin := u_data.(is_admin) |}) ;
                                                                net := U.(net) ;
                                                                key_counter := U.(key_counter) |}
                                                  | _ => U
                                                  end
                               | Some (SKey k') => match k'.(s_usage) with
                                                   | HMAC => U
                                                   | _ => {| users := U.(users) $+ (u_id, {| uid := u_id ;
                                                                                             key_heap := u_data.(key_heap) ;
                                                                                             mem_heap := u_data.(mem_heap) $+ (msg_var', (Ciphertext msg k'.(s_key_id))) ;
                                                                                             protocol := u_data.(protocol) ;
                                                                                             is_admin := u_data.(is_admin) |}) ; (* Might want to change to only return the changed fields, mem_heap in this case, so that 
                                                                                                                                  * the step function can build the correct universe
                                                                                                                                  *)
                                                             net := U.(net) ;
                                                             key_counter := U.(key_counter) |}
                                                   end
                               | _ => U
                               end
                 | None => U
                 end
| None => U
end.

Definition sign (signee : user_id) (key_var msg_var signed_msg_var : var) (U : universe) :=
match U.(users) $? signee with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | ECDSA_S => {| users := U.(users) $+ (signee, {| uid := signee ;
                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                    mem_heap := u_data.(mem_heap) $+ (signed_msg_var, (Signature k.(a_paired_key_id) signee msg)) ;
                                                                                                    protocol := u_data.(protocol) ;
                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                  net := U.(net) ;
                                                                  key_counter := U.(key_counter) |}
                                                  | _ => U
                                                  end
                               | Some (SKey k') => U
                               | None => U
                               end
                 | None => U
                 end
| None => U
end.

Definition verify (verifier : user_id) (key_var signed_msg_var verified_msg_var : var) (U : universe) :=
match U.(users) $? verifier with
| Some u_data => match u_data.(mem_heap) $? signed_msg_var with
                 | Some s_msg => match u_data.(key_heap) $? key_var with
                                 | Some (AKey k) => match s_msg with
                                                    | Signature k_id signee msg => if k_id =? k.(a_paired_key_id)
                                                                                   then {| users := U.(users) $+ (signee, {| uid := signee ;
                                                                                                    key_heap := u_data.(key_heap) ;
                                                                                                    mem_heap := u_data.(mem_heap) $+ (verified_msg_var, msg) ;
                                                                                                    protocol := u_data.(protocol) ;
                                                                                                    is_admin := u_data.(is_admin) |}) ;
                                                                                           net := U.(net) ;
                                                                                           key_counter := U.(key_counter) |}
                                                                                   else U
                                                    | _ => U
                                                    end
                                 | Some (SKey k') => U
                                 | _ => U
                                 end
                 | None => U
                 end
| None => U
end.


(* Ping Protocol *)

(* U.(users) *)
(* In the reciever's protocol, not sure what would be the best to 
 *  do when a message recieved is not a Key_message for the match 
 *  statement. Currently using a new error_key type
 *)
Example ping_users :=
 $0 $+ (0, {| uid := 0 ;
              key_heap := $0 ;
              mem_heap := $0 ;
              protocol := (a >--- (GenerateAKeys RSA_E) ;
                                  (b <- (Send 1 (Key_message (match a with
                                                      | (pair p s) => p
                                                      end))) ;
                                        (c >--- (GenerateAKeys ECDSA_S) ;
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

(* Need to enforce using correct types of keys for usages: ProduceHMAC *)
Inductive step : universe -> universe -> Prop :=
| StepSign : forall signee key_var msg_var signed_msg_var U u_data k msg,
    U.(users) $? signee = Some u_data ->
    u_data.(key_heap) $? key_var = Some (AKey k) ->
    u_data.(mem_heap) $? msg_var = Some msg ->
    ~ (signed_msg_var \in dom u_data.(mem_heap)) ->
    k.(a_usage) = ECDSA_S ->
    u_data.(protocol) = Sign (AKey k) msg ->
      step U (sign signee key_var msg_var signed_msg_var U)
| StepVerify : forall verifier key_var signed_msg_var verified_msg_var U u_data signed_message KeyType,
    U.(users) $? verifier = Some u_data -> 
    u_data.(mem_heap) $? signed_msg_var = Some signed_message ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    match signed_message with
    | Signature k_id _ msg => match KeyType with
                              | AKey k => k.(a_key_id) = k_id
                              | _ => true = false (* Should only be able to verify signature with AKey with same key_id
                                                   * but this is still bad. *)
                              end
    | _ => true = false (* This is bad and you should feel bad *)
    end -> 
    u_data.(protocol) = Verify (Some KeyType) signed_message ->
      step U (verify verifier key_var signed_msg_var verified_msg_var U)
| StepEncrypt : forall u_id msg_var msg_var' key_var U u_data msg KeyType,
    U.(users) $? u_id = Some u_data ->
    u_data.(mem_heap) $? msg_var = Some msg ->
    ~ (msg_var' \in dom u_data.(mem_heap)) ->
    u_data.(key_heap) $? key_var = Some KeyType ->
    match KeyType with
    | AKey k => k.(a_usage) = RSA_E
    | SKey k => ~ (k.(s_usage) = HMAC)
    end ->
    u_data.(protocol) = Encrypt KeyType msg ->
      step U (encrypt_message u_id msg_var msg_var' key_var U)
| StepDecrypt : forall u_id msg_var msg_var' U key_var u_data msg k_id k,
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
      step U (decrypt_message u_id msg_var msg_var' U key_var)
| StepGenerateAKey : forall generator key_var1 key_var2 U usage u_data,
    U.(users) $? generator = Some u_data ->
    ~ (key_var1 \in dom u_data.(key_heap)) ->
    ~ (key_var2 \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateAKeys usage ->
      step U (generate_asymmetric_key generator key_var1 key_var2 U usage)
| StepGenerateSKey : forall generator key_var U usage u_data,
    U.(users) $? generator = Some u_data ->
    ~ (key_var \in dom u_data.(key_heap)) ->
    u_data.(protocol) = GenerateSKey usage ->
      step U (generate_symmetric_key generator key_var U usage)
| StepRecv : forall U recving_user msg_var u_data msg_buffer,
    U.(users) $? recving_user = Some u_data ->
    (U.(net)).(users_msg_buffer) $? recving_user = Some msg_buffer ->
    match msg_buffer with
    | h::t => match h with
              | Key_message _ => ~ (msg_var \in dom u_data.(key_heap))
              | _ => ~ (msg_var \in dom u_data.(mem_heap))
              end
    | [] => true = false (* This is bad, and you should feel bad.
                          * Alternative: [] => ~ (msg_buffer = [])
                          *  This should also always be false *)
    end ->
    u_data.(protocol) = Recv ->
      step U (recv_message recving_user U msg_var)
| StepSend : forall U msg_var from_id to_id u_data msg,
    U.(users) $? from_id = Some u_data ->
    to_id \in dom U.(users) ->
    to_id \in dom (U.(net)).(users_msg_buffer) ->
    u_data.(protocol) = Send to_id msg ->
      step U (send_message msg_var from_id to_id U).
(*
| ProduceHMAC
| VerifyHMAC

Need Alice for the ones below.
| Bind
| BindSKey
| BindAKey
| Barrier
*)


(* TODO for Daniel
 * 1. For step function, include [Return].
 *     a. Change all previous semantic definitions to be only the 
          modified fields of the net or user_data.
 * 2. Write ProduceHMAC semantic defintion.
 * 3. Write VerifyHMAC semantic definition.
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
 * 4. semantic definitions : Regarding [Return], we might want to change so that the definitions only 'return' the changed fields
 *                           of the universe, such as mem_heap of user_data, so that the step function can build the full user_data
 *                           with an altered protocol field.
 * 5. Because we use (k_id : nat) instead of (k : key) in message:Ciphertext, we should(?) also change message:HMAC to use key_id 
 *    as well (the id of the key needed to verify the HMAC
 * 6. Is it possible to get a key message after verifying a signed message? In that case, just also put into key_heap.
 *)