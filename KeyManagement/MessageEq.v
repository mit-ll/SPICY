Require Import Common.
Require RealWorld.
Require IdealWorld.
Require Import Users.
From Coq Require Import List.

Import RealWorld.RealWorldNotations.
Import IdealWorld.IdealNotations.
(* assumes that there is a shadow copy of the built message in every store in the cipherheap *)
(* potential major refactor for usage/id/sym interraction?*)

Inductive message_form :=
| PtKeyForm : message_form
| Crypto : message_form -> message_form
| Pair : message_form -> message_form -> message_form.

Fixpoint key_sets {t : RealWorld.type} (msg : RealWorld.message t) (cipher_heap : RealWorld.ciphers) (form : message_form) :=
  match form with
  | PtKeyForm => match msg with
                | RealWorld.Plaintext c => (Some nil) :: nil
                | RealWorld.KeyMessage k => (Some nil) :: nil
                | _ => None :: nil
                end
                  
  | Crypto f => match msg with
               | RealWorld.Ciphertext id =>
                 match cipher_heap $? id with
                 | Some (RealWorld.Cipher _ k_id m) =>
                   map (fun x => match x with
                              | Some ls => Some (k_id :: ls)
                              | None => None        
                              end) (key_sets m cipher_heap f)
                 | None => None :: nil
                 end
               | RealWorld.Signature _ id =>
                 match cipher_heap $? id with
                 | Some (RealWorld.Cipher _ k_id m) =>
                   map (fun x => match x with
                              | Some ls => Some (k_id :: ls)
                              | None => None
                              end) (key_sets m cipher_heap f)
                 | None => None :: nil
                 end                        
               | _ => None :: nil
               end
  | Pair f1 f2 => match msg with
                 | RealWorld.MsgPair m1 m2 => app (key_sets m1 cipher_heap f1) (key_sets m2 cipher_heap f2)
                 | _ => None :: nil
                 end
  end.

Definition get_keys_from_ids (ks : list (RealWorld.key_identifier)) (heap : RealWorld.keys) :=
  map (fun k => heap $? k) ks.

(* This list represents all the keys that must be owned by the readers of the channel this message is 
   sent on. *)
Fixpoint encrypting_keys (ks : list (option RealWorld.key)) : list RealWorld.key_identifier :=
  match ks with
  | nil => nil
  | k :: ks' => match k with
               | Some k' => match k'.(RealWorld.keyUsage) with
                           | (RealWorld.Encryption) => k'.(RealWorld.keyId) :: (encrypting_keys ks')
                           | _ => encrypting_keys ks'
                           end
               | _ => encrypting_keys ks' (* handle differently? this key doesn't exist so it should be handled when attempting to send *)
               end
  end.

(* If this returns Some key then that is the last key to sign the message. That means that the last place 
   this message should have been written is on channel on which only the owner of this key can write. That 
   channel may have limited readability; use "encrypting keys" to find the set of keys owned by readers *)
Fixpoint asym_sign (ks : list (option RealWorld.key)) : option RealWorld.key_identifier :=
  match ks with
  | nil => None
  | k :: ks' => match k with
               | Some k' => match (k'.(RealWorld.keyUsage), k'.(RealWorld.keyType)) with
                           | (RealWorld.Signing, RealWorld.AsymKey _) => Some k'.(RealWorld.keyId)
                           | _ => asym_sign ks'
                           end
               | None => asym_sign ks' (* handle differently? *)
               end
  end.
(* The owners of the set of all these keys should be able to read and  write to the channel this message 
   is sent on. *)
Fixpoint sym_keys (ks : list (option RealWorld.key)) : list RealWorld.key_identifier :=
  match ks with
  | nil => nil
  | k :: ks' => match k with
               | Some k' => match k'.(RealWorld.keyType) with
                           | RealWorld.SymKey => k'.(RealWorld.keyId) :: sym_keys ks'
                           | _ => sym_keys ks'                                   
                           end
               | None => sym_keys ks' (* handle differently? *)
               end
  end.