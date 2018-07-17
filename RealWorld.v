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

Record error_key :=
  {error_id : nat}.

Inductive key :=
| SKey (k : symmetric_key)
| AKey (k : asymmetric_key)
| EKey (k : error_key).

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

Inductive network_message :=
| nmessage (msg : message) (uid : user_id).

Inductive user_cmd :=
| Return (r : message)
| Bind (c1 : user_cmd) (c2 : message -> user_cmd)
| Send (uid : user_id) (msg : message)
| Recv
| Decrypt (k : key) (ctxt : message)
| Encrypt (k : key) (ptxt : message)
| Sign (k : key) (msg : message)
| Verify (k : key) (sig : message)
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
Notation "x <-k c1 ; c2" := (BindAKeys c1 (fun x => c2)) (right associativity, at level 75).

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

Definition recv_message (reading_user : user_id) (U : universe) (x : var) :=
match (U.(net)).(users_msg_buffer) $? reading_user with
| Some msg_lst => match msg_lst with
                  | [] => U
                  | h::t => match U.(users) $? reading_user with 
                            | Some u_data => match h with
                                             | Key_message k => {| users := U.(users) $+
                                                                            (reading_user , {| uid := u_data.(uid) ;
                                                                                               key_heap := u_data.(key_heap) $+ (x, k) ;
                                                                                               mem_heap := u_data.(mem_heap) ;
                                                                                               protocol := u_data.(protocol) ;
                                                                                               is_admin := u_data.(is_admin) |}) ;
                                                                   net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (reading_user, t) ;
                                                                             trace := (U.(net)).(trace) |} ;
                                                                   key_counter := U.(key_counter) |}
                                             | _ => {| users := U.(users) $+ (reading_user , {| uid := u_data.(uid) ;
                                                                                                key_heap := u_data.(key_heap) ;
                                                                                                mem_heap := u_data.(mem_heap) $+ (x, h) ;
                                                                                                protocol := u_data.(protocol) ;
                                                                                                is_admin := u_data.(is_admin) |}) ;
                                                       net := {| users_msg_buffer := (U.(net)).(users_msg_buffer) $+ (reading_user, t) ;
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

(* Returns OPTION type *)
Definition encrypt_message (u_id : user_id) (msg_var : var) (key_var : var) (U : universe) :=
match U.(users) $? u_id with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | RSA_E => Some (Ciphertext msg k.(a_paired_key_id))
                                                  | _ => None
                                                  end
                               | Some (SKey k') => match k'.(s_usage) with
                                                   | HMAC => None
                                                   | _ => Some (Ciphertext msg k'.(s_key_id))
                                                   end
                               | _ => None
                               end
                 | None => None
                 end
| None => None
end.

(* Instead of signing a hash/message and appending to original message, the below
 *  just signs and returns the message for now. Should work for our current purposes.
 * The sign/verify also return an Option type for a message instead of editing the universe, i.e.,
 *  adding messages to the memory heaps. Does this need to change? !!!!!!!!!!!
 *)
Definition sign (signee : user_id) (key_var msg_var signed_msg_var : var) (U : universe) :=
match U.(users) $? signee with
| Some u_data => match u_data.(mem_heap) $? msg_var with
                 | Some msg => match u_data.(key_heap) $? key_var with
                               | Some (AKey k) => match k.(a_usage) with
                                                  | ECDSA_S => Some (Signature k.(a_paired_key_id) signee msg)
                                                  | _ => None
                                                  end
                               | Some (SKey k') => None
                               | _ => None
                               end
                 | None => None
                 end
| None => None
end.

Definition verify (verifier : user_id) (key_var signed_msg_var verified_msg_var : var) (U : universe) :=
match U.(users) $? verifier with
| Some u_data => match u_data.(mem_heap) $? signed_msg_var with
                 | Some s_msg => match u_data.(key_heap) $? key_var with
                                 | Some (AKey k) => match s_msg with
                                                    | Signature k_id signee msg => if k_id =? k.(a_paired_key_id)
                                                                                   then Some msg
                                                                                   else None
                                                    | _ => None
                                                    end
                                 | Some (SKey k') => None
                                 | _ => None
                                 end
                 | None => None
                 end
| None => None
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
                                        (c <<- (GenerateAKeys ECDSA_S) ;
                                               (d <- (Send 1 (Key_message c)) ;
                                                     (e <- (Sign c (Plaintext "Hello")) ;
                                                           (f <- (Encrypt (match a with
                                                                           | (pair p s) => p
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
                                          (d <- (Verify (match b with
                                                         | Key_message k => k
                                                         | _ => EKey {| error_id := 1 |}
                                                         end) c) ;
                                                (e <- (Decrypt (match a with
                                                                | Key_message k' => k'
                                                                | _ => EKey {| error_id := 1 |}
                                                                end) d) ;
                                                      (Send 0 e)))))) ;
               is_admin := false |}).

(* Ping Universe *)
Example ping_universe :=
{| users := ping_users ;
   net := {| users_msg_buffer := $0 $+ (0, []) $+ (1, []) ;
             trace := [] |} ;
   key_counter := 0 |}.




(* Outstanding Questions
 * 1. What is the best way to keep track of the count of already existing keys? Or, better yet, what
 *    is the best way to generate random key ids?
 *
 * 2. Ping Protocol, Reciever: Question about the error_key. What is the best thing to do when when matching
 *    on a message, it is not a Key_message?
 * 3. Sign/Verify: Currently 'signs' by basically encrypting the message instead of appending the signature to the
 *    original message. Should this be changed?
 *)