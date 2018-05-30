From Coq Require Import Arith String.
Require Import Frap.

(* This file represents a full model of the ideal security properties for a key management system
   The model covers both symmetric and asymmetric keys
*)

(* State of the universe:
    A map from keys to sigma/epsilon lists
    Sigma stores data signed by the associated user and is query-only to the world
    Epsilon stores data encrypted to the associated user and is write-only to the world
*)
Definition data_store := fmap nat (list nat * list nat).

(* Define permission types:
    Encrypt / sign return a permutation on the data store
    Verify / Decrypt return bools describing if you have the permission requested
   Permissions is a map from a key to that key's permissions
*)
Record key_procs :=
  { sign : data_store -> nat -> data_store ;
    verify : data_store -> nat -> nat -> bool ;
    encrypt : data_store -> nat -> nat -> data_store ;
    decrypt : data_store -> nat -> bool }.
Definition permissions := fmap nat key_procs.

(* why doesn't this work?
Definition universe := permissions * data_store. *)

(* Produces an empty sigma/epsilon list for the given key and set of permissions
   Helper function for specific keygen functions
*)
Definition gen_key (U : permissions * data_store) user_id
  (key_permissions : key_procs) :=
  ((fst U) $+ (user_id, key_permissions), (snd U) $+ (user_id, ([], []))).

(* For a given user_id, produce a function allowing signatures with that key
*)
Definition sign_template user_id := 
  fun (ds : data_store) n => match (ds $? user_id) with
              | None => ds
              | Some (sigma, epsilon) => ds $+ (user_id, (n::sigma, epsilon))                                            
              end.

(* For a given user_id:
    If it already exists, add a signing permission (in the form of a lambda function permitting signatures with that key)
    Otherwise, create a new key and add the permission
*)
Definition gen_sign_key U user_id :=
  match (fst U) $? user_id with
  | None => gen_key U user_id {| sign := sign_template user_id ;
                                 verify := fun ds n m => false ;
                                 encrypt := fun ds n m => ds ;
                                 decrypt := fun ds n => false |}
  | Some kp => ((fst U) $+ (user_id,
                              {| sign := sign_template user_id ;
                                    verify := verify kp ;
                                    encrypt := encrypt kp ;
                                    decrypt := decrypt kp |}), snd U)
  end.

(* Anyone can verify any data in any sigma using this function *)
Definition ver_template :=
  fun (ds : data_store) data_id signer_id => match (ds $? signer_id) with
                             | None => false
                             | Some (sigma, epsilon) => member data_id sigma
                             end.

(* For a given user_id:
    Add a new verification permission or create a new key with that permission
*)
Definition gen_ver_key U user_id :=
  match (fst U) $? user_id with
  | None => gen_key U user_id {| sign := fun ds n => ds ;
                                verify := ver_template ;
                                encrypt := fun ds n m => ds ;
                                decrypt := fun ds n => false |}
  | Some kp => ((fst U) $+ (user_id,
                            {| sign := sign kp ;
                               verify := ver_template ;
                               encrypt := encrypt kp ;
                               decrypt := decrypt kp |}), snd U)
  end.

(* Anyone can encrypt any data to any epsilon using this function *)
Definition enc_template :=
  fun (ds : data_store) data_id recipient_id => match (ds $? recipient_id) with
                             | None => ds
                             | Some (sigma, epsilon) => ds $+ (recipient_id, (sigma, data_id::epsilon))
                             end.

(*
  For a given user_id:
    Add a new encryption permission or create a new key with that permission
*)
Definition gen_enc_key U user_id :=
  match (fst U) $? user_id with
  | None => gen_key U user_id {| sign := fun ds n => ds ;
                                verify := fun ds n m => false ;
                                encrypt := enc_template ;
                                decrypt := fun ds n => false |}
  | Some kp => ((fst U) $+ (user_id,
                            {| sign := sign kp ;
                               verify := verify kp ;
                               encrypt := enc_template ;
                               decrypt := fun ds n => false |}), snd U)
  end.

(* For a given user_id produce a function that allows confirming an encryption to that user_id.
*)
Definition dec_template user_id :=
  fun (ds : data_store) n => match (ds $? user_id) with
                             | None => false
                             | Some (sigma, epsilon) => member n epsilon
                             end.

(* For a given user_id:
     Add a new decryption permission or create a new user witht that permission.*)
Definition gen_dec_key U user_id :=
  match (fst U) $? user_id with
  | None => gen_key U user_id {| sign := fun ds n => ds ;
                                verify := fun ds n m => false ;
                                encrypt := fun ds n m => ds ;
                                decrypt := dec_template user_id |}
  | Some kp => ((fst U) $+ (user_id,
                            {| sign := sign kp ;
                               verify := verify kp ;
                               encrypt := encrypt kp ;
                               decrypt := dec_template user_id |}), snd U)
  end.

(* Return permissions for a key (or empty permissions if the key does not exist), stripping the option type
*)
Definition lookup (perms : permissions) n :=
  match (perms $? n) with
  | None => {| sign := fun ds n => ds ;
               verify := fun ds n m => false ;
               encrypt := fun ds n m => ds ;
               decrypt := fun ds n => false |}
  | Some ps => ps
  end.

Hint Rewrite Nat.eqb_refl.

(* Test encrypting and decrypting data with no adversary
*)
Theorem encryption_test : forall Alice Bob U U' data,
    Alice <> Bob ->
    U = gen_dec_key (gen_enc_key ($0, $0) Alice) Bob ->
    U' = ((fst U), (lookup (fst U) Alice).(encrypt) (snd U) data Bob) ->
    (lookup (fst U') Bob).(decrypt) (snd U') data = true.
Proof. 
  unfold gen_enc_key, gen_dec_key, lookup, gen_key. simplify.
  rewrite H0 in H1. rewrite H1. unfold dec_template, enc_template.
  simplify. equality.
Qed.

(* Test signing and verifying data with no adversary
*)
Theorem signature_test : forall Alice Bob U U' data,
    Alice <> Bob ->
    U = gen_ver_key (gen_sign_key ($0, $0) Alice) Bob ->
    U' = ((fst U), (lookup (fst U) Alice).(sign) (snd U) data) ->
    (lookup (fst U') Bob).(verify) (snd U') data Alice = true.
Proof.
  unfold gen_ver_key, gen_sign_key, lookup, gen_key. simplify.
  rewrite H0 in H1. rewrite H1. unfold ver_template, sign_template.
  simplify. equality.
Qed.


(* Work in progress: two possible ways to model restricted knowledge and an adversary 

An attempt to use scoping so that any value can be treated as "plaintext" but 
not revealed to the adversary. This does not compile with anything after the 
second forall implication.
Theorem signature_test_separate_forall_data : forall Alice Bob Mal U U',
    Alice <> Bob ->
    U = gen_sign_key (gen_ver_key (gen_sign_key ($0, $0) Alice) Bob) Mal ->
    (forall data, U' = ((fst U), (lookup (fst U) Alice).(sign) (snd U) data)) ->
               (lookup (fst U') Bob).(verify) (snd U') data Alice = true) ->
    U' = (lookup (fst U') Mal).(sign) (snd U') data).
Proof.
  unfold gen_ver_key, gen_sign_key, lookup, gen_key. simplify.
  rewrite H0 in H1. rewrite H1. unfold ver_template, sign_template.
  simplify. equality.
Qed.

An attempt to use an existential declaration for scoping. Also does not pass 
muster.
Theorem signature_test_existential_data : forall Alice Bob U U',
    Alice <> Bob ->
    U = gen_ver_key (gen_sign_key ($0, $0) Alice) Bob ->
    exists data, U' = ((fst U), (lookup (fst U) Alice).(sign) (snd U) data) ->
              (lookup (fst U') Bob).(verify) (snd U') data Alice = true.
Proof.
  unfold gen_ver_key, gen_sign_key, lookup, gen_key. simplify.
  rewrite H0. exists 2. simplify. rewrite H1. unfold ver_template, sign_template.
  simplify. equality.
Qed.

*)

(* Additional notions to prove:
    1. Eve can't read messages encrypted to Bob
    2. Mallory can't forge data signed by Alice (i.e., make Bob think Alice signed data she didn't)
*)
