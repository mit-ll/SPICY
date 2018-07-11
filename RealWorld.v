From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.
Set Implicit Arguments.

Definition key := nat.

Inductive cipher := 
| type : cipher
| type' : cipher
| type'' : cipher.

(* Have separate records, and then have a transition rule
 * or a step for encryption/decryption
 *)

(* Issue with below is that you can also just access the plaintext... *)
Inductive message :=
| Plaintext (txt : string)
| Ciphertext (txt : message) (ciphertype : cipher) (k : key)
| Signature (k : key) (txt : string)
| HMAC (k : key) (txt : string).

Check Plaintext.
Check Ciphertext.
Check Signature.
Check HMAC.

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

Fixpoint check_message' (ctxt : message) : nat := 
match ctxt with
| Plaintext txt => 0
| Ciphertext msg cipher' k => match cipher' with
                              | type => 1
                              | type' => 2
                              | type'' => 3
                              end
| Signature k t => 0
| HMAC k t => 0
end.