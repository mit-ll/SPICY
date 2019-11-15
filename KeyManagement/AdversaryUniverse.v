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
        Automation
        Tactics
        CipherTheory
        MessagesTheory
        UsersTheory
        KeysTheory
.

Require IdealWorld
        RealWorld.

Set Implicit Arguments.

Lemma accepted_safe_msg_pattern_msg_filter_true :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true
    /\ RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros.
  destruct msg;
    repeat match goal with
           | [ H : RealWorld.msg_pattern_safe _ _ |- _] => invert H
           | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ |- _] => invert H
           end;
    unfold RealWorld.msg_honestly_signed, RealWorld.msg_to_this_user;
    simpl; context_map_rewrites; unfold RealWorld.cipher_to_user;
      destruct (msg_to0 ==n msg_to0); subst; try contradiction;
      rewrite <- RealWorld.honest_key_honest_keyb; auto.
Qed.

Lemma accepted_safe_msg_pattern_honestly_signed :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_honestly_signed honestk cs msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Lemma accepted_safe_msg_pattern_to_this_user :
  forall {t} (msg : RealWorld.crypto t) honestk cs msg_to pat,
    RealWorld.msg_pattern_safe honestk pat
    -> RealWorld.msg_accepted_by_pattern cs msg_to pat msg
    -> RealWorld.msg_to_this_user cs msg_to msg = true.
Proof.
  intros;
    pose proof (accepted_safe_msg_pattern_msg_filter_true H H0); split_ands; assumption.
Qed.

Hint Resolve
     accepted_safe_msg_pattern_honestly_signed
     accepted_safe_msg_pattern_to_this_user.


Section StripAdv.
  Import RealWorld.

  Definition clean_adv_msgs (honestk : key_perms) (cs : ciphers) (msgs : queued_messages) :=
    List.filter (fun sigM => match sigM with 
                          | existT _ _ msg => msg_honestly_signed honestk cs msg
                          end) msgs.

  Definition clean_adv {B} (adv : user_data B) (honestk : key_perms) (cs : ciphers) (b : B) :=
    {| key_heap := clean_key_permissions honestk adv.(key_heap)
     ; protocol := Return b
     (* ; msg_heap := clean_messages honestk cs None adv.(from_ids) adv.(msg_heap) *)
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

End StripAdv.
