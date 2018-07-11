From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

(* Not sure what type key's should be. 
 *  Will they be represented with by a nat, or do we need
 *  an actual bit string?
 *)
Definition key := nat.
Definition user_id := var.

(* POC type of ciphertypes *)
Inductive ciphertype := 
| type : ciphertype
| type' : ciphertype
| type'' : ciphertype.

Inductive message :=
| Plaintext (txt : string)
| Ciphertext (msg : message) (cipher : ciphertype) (k : key)
| Signature (k : key) (txt : string)
| HMAC (k : key) (txt : string).

Check Plaintext.
Check Ciphertext.
Check Signature.
Check HMAC.

(* Example of match arguments of ciphertext to know
 * which ciphertype it is, so that the correct key 
 * can be used to decrypt it by a valid reciever.
 *)
Fixpoint check_message (ctxt : message) : nat := 
match ctxt with
| Plaintext txt => 0
| Ciphertext _ cipher' k => match cipher' with
                              | type => 1
                              | type' => 2
                              | type'' => 3
                              end
| Signature k t => 0
| HMAC k t => 0
end.

(* POC newtork_message. Used for modeling
 * the network
 *)
Inductive network_message :=
| nmessage (msg : message) (uid : user_id).




(* Open Questions:
 * 1. For network modeling, how does the network send a message to a destination without
      a concept of channels? Or in general, how is a message sent?
 *)