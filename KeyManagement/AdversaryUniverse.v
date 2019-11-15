From Coq Require Import
     List
     Morphisms
     Eqdep
.

Require Import
        MyPrelude
        Maps
        Messages
        Common
        MapLtac
        Keys
        RealWorld
.

Set Implicit Arguments.

Section Cleanliness.

  Variable honestk : key_perms.

  (******************** KEYS CLEANING ************************)

  Definition honest_key_filter_fn (k_id : key_identifier) (k : key) :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Definition clean_keys :=
    filter honest_key_filter_fn.

  Definition honest_perm_filter_fn (k_id : key_identifier) (kp : bool) :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Definition clean_key_permissions :=
    filter honest_perm_filter_fn.

  (******************** CIPHERS CLEANING *********************)

  Definition honest_cipher_filter_fn (c_id : cipher_id) (c : cipher) :=
    cipher_honestly_signed honestk c.

  Definition clean_ciphers (cs : ciphers) :=
    filter honest_cipher_filter_fn cs.

  (******************** MESSAGES CLEANING ********************)

  Section Messages.
  
    Variable cs : ciphers.

    Definition msg_nonce_ok {t} (froms : recv_nonces) (msg : crypto t) : option recv_nonces :=
      match msg with
      | Content _ => Some froms
      | SignedCiphertext c_id =>
        match cs $? c_id with
        | None => None
        | Some c =>
          match count_occ msg_seq_eq froms (cipher_nonce c) with
          | 0 => Some (cipher_nonce c :: froms)
          | _ => None
          end
        end
      end.

    Definition msg_filter
               (to_user_id : option user_id) 
               (fld_param : queued_messages * recv_nonces)
               (sigM : { t & crypto t } ) : queued_messages * recv_nonces :=
      match sigM with
      | existT _ _ msg =>
        if msg_signed_addressed honestk cs to_user_id msg
        then match msg_nonce_ok (snd fld_param) msg with
             | None => fld_param
             | Some froms => (fst fld_param ++ [sigM], froms)
             end
        else fld_param
      end.

    Definition clean_messages' (to_usr_id : option user_id) (froms : recv_nonces) (acc msgs : queued_messages) :=
      List.fold_left (msg_filter to_usr_id) msgs (acc, froms).
    
    Definition clean_messages (to_usr_id : option user_id) (froms : recv_nonces) (msgs : queued_messages) :=
      fst (clean_messages' to_usr_id froms [] msgs).
    
  End Messages.

  (******************** USERS CLEANING ***********************)

  Definition clean_users {A} (cs : ciphers) (usrs : honest_users A) :=
    mapi (fun u_id u_d => {| key_heap  := clean_key_permissions u_d.(key_heap)
                        ; protocol  := u_d.(protocol)
                        ; msg_heap  := clean_messages cs (Some u_id) u_d.(from_nons) u_d.(msg_heap)
                        ; c_heap    := u_d.(c_heap)
                        ; from_nons := u_d.(from_nons)
                        ; sent_nons := u_d.(sent_nons)
                        ; cur_nonce := u_d.(cur_nonce) |}) usrs.

End Cleanliness.

(******************** UNIVERSE CLEANING ***********************)

Definition clean_adv_msgs (honestk : key_perms) (cs : ciphers) (msgs : queued_messages) :=
  List.filter (fun sigM => match sigM with 
                        | existT _ _ msg => msg_honestly_signed honestk cs msg
                        end) msgs.

Definition clean_adv {B} (adv : user_data B) (honestk : key_perms) (cs : ciphers) (b : B) :=
  {| key_heap := clean_key_permissions honestk adv.(key_heap)
   ; protocol := Return b
   ; msg_heap := clean_adv_msgs honestk cs adv.(msg_heap)
   ; c_heap   := []
   ; from_nons := []
   ; sent_nons := []
   ; cur_nonce := adv.(cur_nonce) |}.

Definition strip_adversary_univ {A B} (U__r : universe A B) (b : B) : universe A B :=
  let honestk := findUserKeys U__r.(users)
  in {| users       := clean_users honestk U__r.(all_ciphers) U__r.(users)
      ; adversary   := clean_adv U__r.(adversary) honestk U__r.(all_ciphers) b
      ; all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
      ; all_keys    := clean_keys honestk U__r.(all_keys)
     |}.

Definition strip_adversary {A B} (U__r : universe A B) : simpl_universe A :=
  let honestk := findUserKeys U__r.(users)
  in {| s_users       := clean_users honestk U__r.(all_ciphers) U__r.(users)
      ; s_all_ciphers := clean_ciphers honestk U__r.(all_ciphers)
      ; s_all_keys    := clean_keys honestk U__r.(all_keys)
     |}.

Definition strip_adversary_simpl {A} (U__r : simpl_universe A) : simpl_universe A :=
  let honestk := findUserKeys U__r.(s_users)
  in {| s_users       := clean_users honestk U__r.(s_all_ciphers) U__r.(s_users)
      ; s_all_ciphers := clean_ciphers honestk U__r.(s_all_ciphers)
      ; s_all_keys    := clean_keys honestk U__r.(s_all_keys)
     |}.

Definition strip_action (honestk : key_perms) (cs : ciphers) (act : action) :=
  match act with
  | Input msg pat froms     => Input msg pat froms
  | Output msg msg_from msg_to sents => Output msg msg_from msg_to sents
  end.

Definition strip_label (honestk : key_perms) (cs : ciphers) (lbl : label) :=
  match lbl with
  | Silent => Silent
  | Action a => Action (strip_action honestk cs a)
  end.

Lemma peel_strip_univ_eq_strip_adv :
  forall A B (U : universe A B) b,
    peel_adv (strip_adversary_univ U b) = strip_adversary U.
Proof.
  unfold peel_adv, strip_adversary, strip_adversary_univ; trivial.
Qed.
