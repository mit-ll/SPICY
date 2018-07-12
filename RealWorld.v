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
   a_usage : asymmetric_usage}.

Inductive key :=
| SKey (k : symmetric_key)
| Akey (k : asymmetric_key).

(* POC type of ciphertypes *)
Inductive ciphertype := 
| type : ciphertype
| type' : ciphertype
| type'' : ciphertype.

Inductive message :=
| Plaintext (txt : string)
| Ciphertext (msg : message) (cipher : ciphertype) (k : key)
| Key_message (k : key)
| Signature (k : asymmetric_key) (signer_id : user_id) (msg : message)
| HMAC_message (k : symmetric_key) (msg : message).

Record user :=
  {uid : user_id ;
   key_heap : fmap var key ;
   mem_heap : fmap var message ;
   protocol : list var ;
   is_admin : bool }.

(* POC newtork_message. Used for modeling
 * the network
 *)
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
| Barrier.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75).

(* 
Work in Progress
 *)
Record network := construct_network
  { users : fmap user_id (list message) ;
    trace : list (user_id * message) }.


Inductive step : network -> network -> Prop :=
| 














