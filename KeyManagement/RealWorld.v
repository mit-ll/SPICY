From Coq Require Import String Sumbool Morphisms.

Require Import
        MyPrelude
        Common
        Maps
        Tactics
        Keys
        Messages.

Set Implicit Arguments.

Module RW_message <: GRANT_ACCESS.
  Definition access := key_permission.
End RW_message.

Module message := Messages(RW_message).
Import message.

Definition cipher_id := nat.

Inductive crypto : type -> Type :=
| Content {t} (c : message t) : crypto t
| SignedCiphertext {t} (k__sign k__enc : key_identifier) (msg_id : cipher_id) : crypto t
| Signature {t} (msg : crypto t) (k : key_identifier) (sig : cipher_id) : crypto t
.

(* We need to handle non-deterministic message  -- external choice on ordering *)
Inductive msg_pat :=
| Accept
| Signed (k : key_identifier)
| SignedEncrypted (k__sign k__enc : key_identifier)
.
(* We also need to store the form of the message with each cipher in the cipher
   heap to prove functions halt *)
Inductive message_form :=
| PtKeyForm : message_form
| EncForm : message_form -> message_form
| SigForm : message_form -> message_form                        
| PairForm : message_form -> message_form -> message_form.

Inductive cipher : Type :=
| SigCipher {t} (k_id : key_identifier) (c : crypto t) : cipher
| SigEncCipher {t} (k__sign k__enc : key_identifier) (c : crypto t) : cipher
.

Definition cipher_signing_key (c : cipher) :=
  match c with
  | SigCipher k _      => k
  | SigEncCipher k _ _ => k
  end.

Definition queued_messages := list (sigT crypto).
Definition ciphers         := NatMap.t cipher.
Definition my_ciphers      := list cipher_id.

Inductive msg_accepted_by_pattern : forall {t : type}, msg_pat -> crypto t -> Prop :=
| MsgAccept : forall {t} (m : crypto t),
    msg_accepted_by_pattern Accept m
| ProperlySigned : forall {t} c_id k (m : crypto t),
    msg_accepted_by_pattern (Signed k) (Signature m k c_id)
| ProperlyEncrypted : forall {t} c_id k__sign k__enc (m : message t),
    msg_accepted_by_pattern (SignedEncrypted k__sign k__enc) (@SignedCiphertext t k__sign k__enc c_id).

Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff.

Section SafeMessages.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Inductive honest_key (k_id : key_identifier) : Prop :=
  | HonestKey :
        honestk $? k_id = Some true
      -> honest_key k_id.

  Definition honest_keyb (k_id : key_identifier) : bool :=
    match honestk $? k_id with
    | Some true => true
    | _ => false
    end.

  Hint Constructors honest_key.

  Lemma honest_key_honest_keyb :
    forall k,
      honest_key k <-> honest_keyb k = true.
  Proof.
    split; unfold honest_keyb; intros.
    - destruct H; context_map_rewrites; trivial.
    - cases (honestk $? k); subst; try discriminate.
      cases b; try discriminate; eauto.
  Qed.

  Lemma not_honest_key_honest_keyb :
    forall k,
      not (honest_key k) <-> honest_keyb k = false.
  Proof.
    split; unfold honest_keyb; intros.
    - cases (honestk $? k); trivial.
      cases b; trivial.
      assert (honest_key k) by eauto; contradiction.
    - unfold not; intro HK; destruct HK; context_map_rewrites; discriminate.
  Qed.

  Lemma honest_keyb_true_findKeys :
    forall k,
      honest_keyb k = true
      -> honestk $? k = Some true.
  Proof.
    intros; rewrite <- honest_key_honest_keyb in H; invert H; eauto.
  Qed.

  Inductive content_only_honest_public_keys : forall {t}, message t -> Prop :=
  | ContentHPK : forall txt,
      content_only_honest_public_keys (message.Content txt)
  | AccessHPK : forall kp,
      honestk $? fst kp = Some true
      -> snd kp = false
      -> content_only_honest_public_keys (message.Permission kp)
  | PairHPK : forall t1 t2 (m1 : message t1) (m2 : message t2),
      content_only_honest_public_keys m1
      -> content_only_honest_public_keys m2
      -> content_only_honest_public_keys (message.MsgPair m1 m2).

  Inductive msg_contains_only_honest_public_keys :  forall {t}, crypto t -> Prop :=
  | PlaintextHPK : forall {t} (txt : message t),
      content_only_honest_public_keys txt
      -> msg_contains_only_honest_public_keys (Content txt)
  | HonestlyEncryptedHPK :
      forall t c_id k__signid k__encid,
        honest_key k__encid
      -> msg_contains_only_honest_public_keys (@SignedCiphertext t k__signid k__encid c_id)
  | SignedPayloadHPK : forall {t} (msg : crypto t) k c_id,
        msg_contains_only_honest_public_keys msg
      -> msg_contains_only_honest_public_keys (Signature msg k c_id).

  Hint Constructors msg_contains_only_honest_public_keys.

  Definition msg_honestly_signed {t} (msg : crypto t) : bool :=
    match msg with
    | SignedCiphertext k__signid _ _ => honest_keyb k__signid
    | Signature _ k _ => honest_keyb k
    | _ => false
    end.

  Definition keys_mine (my_perms key_perms: key_perms) : Prop :=
    forall k_id kp,
      key_perms $? k_id = Some kp
    ->  my_perms $? k_id = Some kp
    \/ (my_perms $? k_id = Some true /\ kp = false).

  Definition cipher_honestly_signed (c : cipher) : bool :=
    match c with
    | SigCipher k_id _              => honest_keyb k_id
    | SigEncCipher k__signid k__encid _ => honest_keyb k__signid
    end.

  Definition ciphers_honestly_signed :=
    Forall_natmap (fun c => cipher_honestly_signed c = true).

  Inductive msg_pattern_safe : msg_pat -> Prop :=
  | HonestlySignedSafe : forall k,
        honest_key k
      -> msg_pattern_safe (Signed k)
  | HonestlySignedEncryptedSafe : forall k__sign k__enc,
        honest_key k__sign
      -> msg_pattern_safe (SignedEncrypted k__sign k__enc).

End SafeMessages.

Hint Constructors honest_key
     msg_pattern_safe.

Lemma cipher_honestly_signed_proper :
  Proper (eq ==> eq ==> eq) (fun _ : NatMap.key => cipher_honestly_signed).
Proof.
  unfold Proper, respectful; intros; subst; eauto.
Qed.

Hint Resolve cipher_honestly_signed_proper.

Inductive user_cmd : Type -> Type :=
(* Plumbing *)
| Return {A : Type} (res : A) : user_cmd A
| Bind {A A' : Type} (cmd1 : user_cmd A') (cmd2 : A' -> user_cmd A) : user_cmd A

| Gen : user_cmd nat

(* Messaging *)
| Send {t} (uid : user_id) (msg : crypto t) : user_cmd unit
| Recv {t} (pat : msg_pat) : user_cmd (crypto t)

(* Crypto!! *)
| SignEncrypt {t} (k__sign k__enc : key_identifier) (msg : crypto t) : user_cmd (crypto t)
| Decrypt {t} (c : crypto t) : user_cmd (crypto t)

| Sign    {t} (k : key_identifier) (msg : crypto t) : user_cmd (crypto t)
| Verify  {t} (k : key_identifier) (msg : crypto t) : user_cmd bool

| GenerateSymKey  (usage : key_usage) : user_cmd key_permission
| GenerateAsymKey (usage : key_usage) : user_cmd key_permission
.

Module RealWorldNotations.
  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 75) : realworld_scope.
  Delimit Scope realworld_scope with realworld.
End RealWorldNotations.
Import  RealWorldNotations.
Open Scope realworld_scope.

Record user_data (A : Type) :=
  mkUserData {
      key_heap : key_perms
    ; protocol : user_cmd A
    ; msg_heap : queued_messages
    ; c_heap   : my_ciphers
    }.

Definition honest_users A := user_list (user_data A).

Record simpl_universe (A : Type) :=
  mkSimplUniverse {
      s_users       : honest_users A
    ; s_all_ciphers : ciphers
    ; s_all_keys    : keys
    }.

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : user_data B
    ; all_ciphers : ciphers
    ; all_keys    : keys
    }.

Definition peel_adv {A B} (U : universe A B) : simpl_universe A :=
   {| s_users       := U.(users)
    ; s_all_ciphers := U.(all_ciphers)
    ; s_all_keys    := U.(all_keys) |}.

Definition findUserKeys {A} (us : user_list (user_data A)) : key_perms :=
  fold (fun u_id u ks => ks $k++ u.(key_heap)) us $0.

Definition addUserKeys {A} (ks : key_perms) (u : user_data A) : user_data A :=
  {| key_heap := u.(key_heap) $k++ ks
   ; protocol := u.(protocol)
   ; msg_heap := u.(msg_heap)
   ; c_heap   := u.(c_heap) |}.

Definition addUsersKeys {A} (us : user_list (user_data A)) (ks : key_perms) : user_list (user_data A) :=
  map (addUserKeys ks) us.

Lemma Forall_app_sym :
  forall {A} (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P (l2 ++ l1).
Proof.
  split; intros;
    rewrite Forall_forall in *; intros;
      eapply H;
      apply in_or_app; apply in_app_or in H0; intuition idtac.
Qed.

Lemma Forall_app :
  forall {A} (P : A -> Prop) (l : list A) a,
    Forall P (l ++ [a]) <-> Forall P (a :: l).
Proof.
  intros.
  rewrite Forall_app_sym; simpl; split; trivial.
Qed.

Lemma Forall_dup :
  forall {A} (P : A -> Prop) (l : list A) a,
    Forall P (a :: a :: l) <-> Forall P (a :: l).
Proof.
  split; intros;
    rewrite Forall_forall in *; intros;
      eapply H;
      apply in_inv in H0; split_ors; subst; simpl; eauto.
Qed.

Fixpoint findKeysMessage {t} (msg : message t) : key_perms :=
  match msg with
  | message.Permission k => $0 $+ (fst k, snd k) 
  | message.Content _ => $0
  | message.MsgPair m1 m2 => findKeysMessage m1 $k++ findKeysMessage m2
  end.

Fixpoint findKeysCrypto {t} (msg : crypto t) : key_perms :=
  match msg with
  | Content  m             => findKeysMessage m
  | SignedCiphertext _ _ _ => $0
  | Signature m _ _        => findKeysCrypto m
  end.

Fixpoint findCiphers {t} (msg : crypto t) : my_ciphers :=
  match msg with
  | Content _            => []
  | SignedCiphertext _ _ c => [c]
  | Signature m _ c        => c :: findCiphers m
  end.

Fixpoint findMsgCiphers {t} (msg : crypto t) : queued_messages :=
  match msg with
  | Content _            => []
  | SignedCiphertext _ _ _ => [existT _ _ msg]
  | Signature m k c        => (existT _ _ msg) :: findMsgCiphers m
  end.

Definition msgCipherOk (honestk : key_perms) (cs : ciphers) (sigm : sigT crypto):=
  match sigm with
  | (existT _ _ m) =>
    msg_honestly_signed honestk m = true
  /\ match m with
    | SignedCiphertext k__sign k__enc msg_id
      => exists t (m' : crypto t), cs $? msg_id = Some (SigEncCipher k__sign k__enc m')
    | Signature m' k sig
      => cs $? sig = Some (SigCipher k m')
    | _ => False
    end
  end.

Definition msgCiphersSigned {t} (honestk : key_perms) (cs : ciphers) (msg : crypto t) :=
  Forall (msgCipherOk honestk cs) (findMsgCiphers msg).

Definition user_keys {A} (usrs : honest_users A) (u_id : user_id) : option key_perms :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(key_heap)
  | None     => None
  end.

Definition user_queue {A} (usrs : honest_users A) (u_id : user_id) : option queued_messages :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(msg_heap)
  | None     => None
  end.

Definition user_cipher_queue {A} (usrs : honest_users A) (u_id : user_id) : option my_ciphers :=
  match usrs $? u_id with
  | Some u_d => Some u_d.(c_heap)
  | None     => None
  end.

Section RealWorldLemmas.

  Lemma findUserKeys_foldfn_proper :
    forall {A},
      Proper (eq ==> eq ==> eq ==> eq) (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold Proper, respectful; intros; subst; trivial.
  Qed.

  Lemma findUserKeys_foldfn_proper_Equal :
    forall {A},
      Proper (eq ==> eq ==> Equal ==> Equal) (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.

    unfold Proper, respectful; intros; subst; Equal_eq; unfold Equal; intros; trivial.
  Qed.

  Lemma findUserKeys_foldfn_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite !merge_perms_assoc,merge_perms_sym with (ks1:=key_heap e'); trivial.
  Qed.

  Lemma findUserKeys_foldfn_transpose_Equal :
    forall {A},
      transpose_neqkey Equal (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros; unfold Equal; intros.
    rewrite !merge_perms_assoc,merge_perms_sym with (ks1:=key_heap e'); trivial.
  Qed.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose
       findUserKeys_foldfn_proper_Equal findUserKeys_foldfn_transpose_Equal.

  Lemma findUserKeys_notation :
    forall {A} (usrs : honest_users A),
      fold (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u) usrs $0 = findUserKeys usrs.
    unfold findUserKeys; trivial.
  Qed.

  Lemma findUserKeys_readd_user_same_keys_idempotent :
    forall {A} (usrs : honest_users A) u_id u_d proto msgs mycs,
      usrs $? u_id = Some u_d
      -> findUserKeys usrs = findUserKeys (usrs $+ (u_id, {| key_heap := key_heap u_d
                                                          ; protocol := proto
                                                          ; msg_heap := msgs
                                                          ; c_heap   := mycs |} )).
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; auto.

    cases (x ==n u_id); subst; clean_map_lookups.
    - rewrite map_add_eq.
      unfold findUserKeys.
      rewrite !fold_add; auto.
    - rewrite map_ne_swap; auto.
      unfold findUserKeys.
      rewrite fold_add; auto.
      rewrite fold_add; auto; clean_map_lookups.
      rewrite !findUserKeys_notation.
      rewrite IHusrs at 1; auto.
      rewrite not_find_in_iff; clean_map_lookups; trivial.
  Qed.

  Lemma findUserKeys_readd_user_same_keys_idempotent' :
    forall {A} (usrs : honest_users A) u_id ks proto msgs mycs,
      user_keys usrs u_id = Some ks
      -> findUserKeys (usrs $+ (u_id, {| key_heap := ks
                                      ; protocol := proto
                                      ; msg_heap := msgs
                                      ; c_heap   := mycs |})) = findUserKeys usrs.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; auto.
    cases (x ==n u_id); subst; clean_map_lookups.
    - rewrite map_add_eq.
      unfold findUserKeys.
      unfold user_keys in *; rewrite add_eq_o in H; invert H; auto.
      rewrite !fold_add; simpl; eauto.
    - rewrite map_ne_swap; auto.
      unfold findUserKeys.
      assert (user_keys usrs u_id = Some ks) by (unfold user_keys in H; rewrite add_neq_o in H; auto).
      rewrite fold_add; auto.
      rewrite !findUserKeys_notation.
      rewrite IHusrs; auto.
      unfold findUserKeys at 2.
      rewrite fold_add; auto.
      rewrite not_find_in_iff; clean_map_lookups; trivial.
  Qed.

  Lemma findUserKeys_readd_user_addnl_keys :
    forall {A} (usrs : honest_users A) u_id proto msgs ks ks' mycs,
      user_keys usrs u_id = Some ks
      -> findUserKeys (usrs $+ (u_id, {| key_heap := ks $k++ ks'
                                      ; protocol := proto
                                      ; msg_heap := msgs
                                      ; c_heap   := mycs |})) = findUserKeys usrs $k++ ks'.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; auto.
    cases (x ==n u_id); subst; clean_map_lookups; try rewrite map_add_eq.
    - unfold findUserKeys. rewrite !fold_add; auto.
      rewrite findUserKeys_notation; simpl.
      unfold user_keys in H; rewrite add_eq_o in H; invert H; auto.
      rewrite merge_perms_assoc; trivial.
    - rewrite map_ne_swap; auto.
      unfold findUserKeys.
      assert (user_keys usrs u_id = Some ks) by (unfold user_keys in H; rewrite add_neq_o in H; auto).
      rewrite fold_add; auto.
      rewrite findUserKeys_notation.
      rewrite fold_add; auto.
      rewrite IHusrs; auto.
      rewrite findUserKeys_notation.
      rewrite !merge_perms_assoc, merge_perms_sym with (ks1:=ks'); trivial.
      rewrite not_find_in_iff; clean_map_lookups; auto.
  Qed.

  Lemma findUserKeys_has_key_of_user :
    forall {A} (usrs : honest_users A) u_id u_d ks k kp,
      usrs $? u_id = Some u_d
      -> ks = key_heap u_d
      -> ks $? k = Some kp
      -> findUserKeys usrs $? k <> None.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; contra_map_lookup; auto.
    cases (x ==n u_id); subst; clean_map_lookups.
    - unfold findUserKeys.
      rewrite fold_add; auto.
      rewrite findUserKeys_notation.
      cases (findUserKeys usrs $? k); subst; unfold not; intros.
      + erewrite merge_perms_chooses_greatest in H; eauto; discriminate.
      + eapply merge_perms_no_disappear_perms in H; split_ands; contra_map_lookup.
    - unfold findUserKeys; rewrite fold_add; auto; rewrite findUserKeys_notation; unfold not; intros.
      cases (key_heap e $? k); subst; auto.
      + eapply merge_perms_no_disappear_perms in H0; split_ands; contra_map_lookup.
      + eapply merge_perms_no_disappear_perms in H0; split_ands. assert ( findUserKeys usrs $? k <> None ); eauto.
  Qed.

  Lemma findUserKeys_has_private_key_of_user :
    forall {A} (usrs : honest_users A) u_id u_d ks k,
      usrs $? u_id = Some u_d
      -> ks = key_heap u_d
      -> ks $? k = Some true
      -> findUserKeys usrs $? k = Some true.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; contra_map_lookup; auto.
    cases (x ==n u_id); subst; clean_map_lookups.
    - unfold findUserKeys.
      rewrite fold_add; auto.
      rewrite findUserKeys_notation.
      cases (findUserKeys usrs $? k); subst.
      + erewrite merge_perms_chooses_greatest; eauto; unfold greatest_permission; rewrite orb_true_r; auto.
      + erewrite merge_perms_adds_ks2; eauto.
    - unfold findUserKeys; rewrite fold_add; auto; rewrite findUserKeys_notation; eauto.
      cases (key_heap e $? k); subst; auto.
      + erewrite merge_perms_chooses_greatest; eauto; unfold greatest_permission; rewrite orb_true_l; auto.
      + erewrite merge_perms_adds_ks1 with (ks1:=findUserKeys usrs); eauto.
  Qed.

  Lemma findUserKeys_readd_user_same_key_heap_idempotent :
    forall {A} (usrs : honest_users A) u_id ks,
      user_keys usrs u_id = Some ks
      -> findUserKeys usrs $k++ ks = findUserKeys usrs.
  Proof.
    intros.
    induction usrs using P.map_induction_bis; intros; Equal_eq; subst; contra_map_lookup; auto.
    unfold user_keys in H.
    cases (x ==n u_id); subst.
    - rewrite add_eq_o in H; simpl in H; auto.
      unfold findUserKeys; rewrite fold_add; auto.
      rewrite findUserKeys_notation.
      invert H.
      rewrite merge_perms_assoc; rewrite merge_perms_refl; trivial.
    - rewrite add_neq_o in H; auto.
      unfold findUserKeys; rewrite fold_add; auto.
      rewrite findUserKeys_notation.
      cases (usrs $? u_id); subst; try discriminate; invert H.
      rewrite merge_perms_assoc. rewrite merge_perms_sym with (ks2:=key_heap u); rewrite <- merge_perms_assoc.
      rewrite IHusrs.
      trivial.
      unfold user_keys; context_map_rewrites; trivial.
  Qed.

  Lemma honest_key_after_new_keys :
    forall honestk msgk k_id,
        honest_key honestk k_id
      -> honest_key (honestk $k++ msgk) k_id.
  Proof.
    invert 1; intros; econstructor; eauto.
    cases (msgk $? k_id); subst; eauto.
    - erewrite merge_perms_chooses_greatest by eauto; eauto.
    - erewrite merge_perms_adds_ks1; eauto.
  Qed.

  Hint Resolve honest_key_after_new_keys.

  Lemma honest_keyb_after_new_keys :
    forall honestk msgk k_id,
      honest_keyb honestk k_id = true
      -> honest_keyb (honestk $k++ msgk) k_id = true.
  Proof.
    intros; rewrite <- honest_key_honest_keyb in *; eauto.
  Qed.

  Hint Resolve honest_keyb_after_new_keys.

  Lemma not_honest_key_after_new_msg_keys :
    forall {t} (msg : crypto t) honestk k,
      ~ honest_key honestk k
      -> (forall (k_id : NatMap.key) (kp : bool), findKeysCrypto msg $? k_id = Some kp -> kp = false)
      -> ~ honest_key (honestk $k++ findKeysCrypto msg) k.
  Proof.
    unfold not; invert 3; intros.
    cases (honestk $? k); cases (findKeysCrypto msg $? k); subst; eauto.
    - cases b; eauto.
      erewrite merge_perms_chooses_greatest in H2; unfold greatest_permission in *; eauto.
      rewrite orb_false_l in H2; invert H2.
      specialize (H0 _ _ Heq0); discriminate.
    - cases b; eauto.
      erewrite merge_perms_adds_ks1 in H2; eauto.
      discriminate.
    - erewrite merge_perms_adds_ks2 in H2; eauto.
      invert H2.
      specialize (H0 _ _ Heq0); discriminate.
    - rewrite merge_perms_adds_no_new_perms in H2; eauto; discriminate.
  Qed.

  Hint Resolve not_honest_key_after_new_msg_keys.

  Lemma message_honestly_signed_after_add_keys :
    forall {t} (msg : crypto t) honestk ks,
      msg_honestly_signed honestk msg = true
      -> msg_honestly_signed (honestk $k++ ks) msg = true.
  Proof.
    intros.
    destruct msg; simpl in *; eauto.
  Qed.

  Lemma message_honestly_signed_after_remove_pub_keys :
    forall {t} (msg : crypto t) honestk pubk,
      msg_honestly_signed (honestk $k++ pubk) msg = true
      -> (forall k kp, pubk $? k = Some kp -> kp = false)
      -> msg_honestly_signed honestk msg = true.
  Proof.
    intros.
    destruct msg; simpl in *; eauto;
      unfold honest_keyb in *.

    - cases (honestk $? k__sign); cases (pubk $? k__sign); subst.
      + erewrite merge_perms_chooses_greatest in H; unfold greatest_permission in *; simpl in *; eauto.
        specialize (H0 _ _ Heq0);
          cases b; subst; eauto.
      + erewrite merge_perms_adds_ks1 in H; eauto.
      + erewrite merge_perms_adds_ks2 in H; eauto.
        specialize (H0 _ _ Heq0); subst; discriminate.
      + rewrite merge_perms_adds_no_new_perms in H; auto.

    - cases (honestk $? k); cases (pubk $? k); subst.
      + erewrite merge_perms_chooses_greatest in H; unfold greatest_permission in *; simpl in *; eauto.
        specialize (H0 _ _ Heq0);
          cases b; subst; eauto.
      + erewrite merge_perms_adds_ks1 in H; eauto.
      + erewrite merge_perms_adds_ks2 in H; eauto.
        specialize (H0 _ _ Heq0); subst; discriminate.
      + rewrite merge_perms_adds_no_new_perms in H; auto.
  Qed.

  Lemma cipher_honestly_signed_after_msg_keys :
    forall honestk msgk c,
      cipher_honestly_signed honestk c = true
      -> cipher_honestly_signed (honestk $k++ msgk) c = true.
  Proof.
    unfold cipher_honestly_signed. intros; cases c; trivial;
      rewrite <- honest_key_honest_keyb in *; eauto.
  Qed.

  Hint Resolve cipher_honestly_signed_after_msg_keys.

  Lemma ciphers_honestly_signed_after_msg_keys :
    forall honestk msgk cs,
      ciphers_honestly_signed honestk cs
      -> ciphers_honestly_signed (honestk $k++ msgk) cs.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

End RealWorldLemmas.


Lemma safe_messages_have_only_honest_public_keys :
  forall {t} (msg : crypto t) honestk,
    msg_contains_only_honest_public_keys honestk msg
    -> forall k_id,
      findKeysCrypto msg $? k_id = None
      \/ (honestk $? k_id <> None /\ findKeysCrypto msg $? k_id = Some false).
Proof.
  induction 1; eauto; intros; subst. induction txt.
  - destruct acc; cases (k ==n k_id); cases b; invert H; simpl in *; clean_map_lookups.
    + right; split. rewrite H1. discriminate. constructor.
    + left; trivial.
  - invert H; left; trivial.
  - invert H. apply IHtxt1 in H3; destruct H3; apply IHtxt2 in H5; destruct H5.
    + left. simpl in *. apply merge_perms_adds_no_new_perms; assumption.
    + right. simpl in *. destruct H0. split. assumption. apply merge_perms_adds_ks2 with (ks1 := findKeysMessage txt1) (ks2 := findKeysMessage txt2). assumption. assumption. reflexivity.
    + right. simpl in *. destruct H. split. assumption. apply merge_perms_adds_ks1 with (ks1 := findKeysMessage txt1) (ks2 := findKeysMessage txt2). assumption. assumption. reflexivity.
    + right. simpl in *. destruct H. split. assumption. destruct H0. Search merge_perms. pose proof merge_perms_chooses_greatest. apply H3 with (ks1 := findKeysMessage txt1) (k := k_id) (kp := false) (ks2 := findKeysMessage txt2) (k' := k_id) (kp' := false) in H1. simpl in H1. assumption. assumption. reflexivity.
Qed.
  (*   + rewrite merge_perms_adds_no_new_perms; eauto. *)
  (*   + erewrite merge_perms_adds_ks1; eauto. *)
  (*   + erewrite merge_perms_adds_ks2; eauto. *)
  (*   + erewrite merge_perms_chooses_greatest; eauto; simpl; auto. *)

Lemma safe_messages_perm_merge_honestk_idempotent :
  forall {t} (msg : crypto t) honestk,
    msg_contains_only_honest_public_keys honestk msg
    -> honestk $k++ findKeysCrypto msg = honestk.
Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    apply safe_messages_have_only_honest_public_keys with (k_id := y) in H; split_ors; split_ands.
    - cases (honestk $? y); eauto.
      + erewrite merge_perms_adds_ks1; eauto.
      + rewrite merge_perms_adds_no_new_perms; auto.
    - cases (honestk $? y); try contradiction.
      erewrite merge_perms_chooses_greatest; eauto; unfold greatest_permission; rewrite orb_false_r; auto.
Qed.

Definition buildUniverse {A B}
           (usrs : honest_users A) (adv : user_data B) (cs : ciphers) (ks : keys)
           (u_id : user_id) (userData : user_data A) : universe A B :=
  {| users        := usrs $+ (u_id, userData)
   ; adversary    := adv
   ; all_ciphers  := cs
   ; all_keys     := ks
   |}.

Definition buildUniverseAdv {A B}
           (usrs : honest_users A) (cs : ciphers) (ks : keys)
           (userData : user_data B) : universe A B :=
  {| users        := usrs
   ; adversary    := userData
   ; all_ciphers  := cs
   ; all_keys     := ks
   |}.

Definition extractPlainText {t} (msg : message t) : option nat :=
  match msg with
  | message.Content t => Some t
  | _           => None
  end.

Definition unSig {t} (msg : crypto t) : option (crypto t) :=
  match msg with
  | Signature m _ _ => Some m
  | _               => None
  end.

Inductive action : Type :=
| Input  t (msg : crypto t) (pat : msg_pat) (uks : key_perms)
| Output t (msg : crypto t)
.

Definition rlabel := @label action.

Definition action_adversary_safe (honestk : key_perms) (cs : ciphers) (a : action) : Prop :=
  match a with
  | Input  msg pat _ => msg_pattern_safe honestk pat
  | Output msg       => msg_contains_only_honest_public_keys honestk msg
                     /\ msg_honestly_signed honestk msg = true
                     /\ msgCiphersSigned honestk cs msg
  end.

Definition data_step0 (A B C : Type) : Type :=
  honest_users A * user_data B * ciphers * keys * key_perms * queued_messages * my_ciphers * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B C :=
  (U.(users), U.(adversary), U.(all_ciphers), U.(all_keys), u_data.(key_heap), u_data.(msg_heap), u_data.(c_heap), u_data.(protocol)).

Inductive step_user : forall A B C, rlabel -> option user_id -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {B r r'} (usrs usrs' : honest_users r') (adv adv' : user_data B)
                    lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs'
                    (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd1) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd1')
    -> step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind cmd1 cmd2) (usrs', adv', cs', gks', ks', qmsgs', mycs', Bind cmd1' cmd2)
| StepBindProceed : forall {B r r'} (usrs : honest_users r) (adv : user_data B) cs u_id gks ks qmsgs mycs (v : r') (cmd : r' -> user_cmd r),
    step_user Silent u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind (Return v) cmd) (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd v)

| StepGen : forall {A B} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs n,
    step_user Silent u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Gen) (usrs, adv, cs, gks, ks, qmsgs, mycs, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs qmsgs' mycs mycs'
               (msg : crypto t) msgs pat newkeys newcs,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> findKeysCrypto msg = newkeys
    -> newcs = findCiphers msg
    -> ks' = ks $k++ newkeys
    -> mycs' = newcs ++ mycs
    -> msg_accepted_by_pattern pat msg
    -> step_user (Action (Input msg pat ks)) u_id
                (usrs, adv, cs, gks, ks , qmsgs , mycs,  Recv pat)
                (usrs, adv, cs, gks, ks', qmsgs', mycs', Return msg)

| StepRecvDrop : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs qmsgs' mycs (msg : crypto t) pat msgs,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> ~ msg_accepted_by_pattern pat msg
    -> step_user Silent u_id (* Error label ... *)
                (usrs, adv, cs, gks, ks, qmsgs , mycs, Recv pat)
                (usrs, adv, cs, gks, ks, qmsgs', mycs, @Recv t pat)

(* Augment attacker's keys with those available through messages sent, *)
(*  * including traversing through ciphers already known by attacker, etc. *)
(*  *)
| StepSend : forall {A B} {t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
               cs u_id gks ks qmsgs mycs rec_u_id rec_u newkeys (msg : crypto t),
    findKeysCrypto msg = newkeys
    -> keys_mine ks newkeys
    -> incl (findCiphers msg) mycs
    -> adv' = addUserKeys newkeys adv (* TODO: also add ciphers to adv??? *)
    -> usrs $? rec_u_id = Some rec_u
    -> rec_u_id <> u_id
    -> usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                  ; protocol := rec_u.(protocol)
                                  ; msg_heap := rec_u.(msg_heap) ++ [existT _ _ msg]
                                  ; c_heap   := rec_u.(c_heap) |})
    -> step_user (Action (Output msg)) (Some u_id)
                (usrs , adv , cs, gks, ks, qmsgs, mycs, Send rec_u_id msg)
                (usrs', adv', cs, gks, ks, qmsgs, mycs, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs'
                  (msg : crypto t) k__signid k__encid kp__enc kt__enc kt__sign c_id cipherMsg,
      gks $? k__encid  = Some (MkCryptoKey k__encid Encryption kt__enc)
    -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt__sign)
    -> ks $? k__encid   = Some kp__enc
    -> ks $? k__signid  = Some true
    -> ~ In c_id cs
    -> keys_mine ks (findKeysCrypto msg)
    -> incl (findCiphers msg) mycs
    -> cipherMsg = SigEncCipher k__signid k__encid msg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> mycs' = c_id :: mycs
    -> step_user Silent u_id
                (usrs, adv, cs , gks, ks, qmsgs, mycs,  SignEncrypt k__signid k__encid msg)
                (usrs, adv, cs', gks, ks, qmsgs, mycs', Return (@SignedCiphertext t k__signid k__encid c_id))

| StepDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks ks' qmsgs mycs mycs'
                  (msg : crypto t) k__signid kp__sign k__encid c_id newkeys kt__sign kt__enc newcs,
      cs $? c_id     = Some (SigEncCipher k__signid k__encid msg)
    -> gks $? k__encid  = Some (MkCryptoKey k__encid Encryption kt__enc)
    -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt__sign)
    -> ks  $? k__encid  = Some true
    -> ks  $? k__signid = Some kp__sign
    -> findKeysCrypto msg = newkeys
    -> newcs = findCiphers msg
    -> ks' = ks $k++ newkeys
    -> mycs' = newcs ++ mycs
    -> List.In c_id mycs
    -> step_user Silent u_id
                (usrs, adv, cs, gks, ks , qmsgs, mycs,  Decrypt (SignedCiphertext k__signid k__encid c_id))
                (usrs, adv, cs, gks, ks', qmsgs, mycs', Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' u_id gks ks qmsgs mycs mycs'
               (msg : crypto t) k_id kt c_id cipherMsg,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
    -> ks  $? k_id = Some true
    -> ~ In c_id cs
    -> cipherMsg = SigCipher k_id msg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> mycs' = c_id :: mycs
    -> step_user Silent u_id
                (usrs, adv, cs , gks, ks, qmsgs, mycs,  Sign k_id msg)
                (usrs, adv, cs', gks, ks, qmsgs, mycs', Return (Signature msg k_id c_id))

| StepVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs u_id gks ks qmsgs mycs
                 (msg : crypto t) k_id kp kt c_id,
      gks $? k_id = Some (MkCryptoKey k_id Signing kt)
    -> ks  $? k_id = Some kp
    -> cs $? c_id = Some (SigCipher k_id msg)
    -> List.In c_id mycs
    -> step_user Silent u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, Verify k_id (Signature msg k_id c_id))
                (usrs, adv, cs, gks, ks, qmsgs, mycs, Return true)
.

(* Key creation *)
(* | StepGenerateSymKey: forall A cs ks qmsgs (usrDat : user_data A) usage k kid, *)
(*     ~(kid \in (dom ks)) *)
(*     -> k = SymKey (MkCryptoKey kid usage) *)
(*     -> step_user (cs, ks, qmsgs, usrDat, GenerateSymKey usage) *)
(*                 (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k) *)
(* | StepGenerateAsymKey: forall {a : Set} cs ks qmsgs (usrDat : user_data a) usage k kid, *)
(*     ~(kid \in (dom ks)) *)
(*     -> k = AsymKey (MkCryptoKey kid usage) true *)
(*     -> step_user (cs, ks, qmsgs, usrDat, GenerateAsymKey usage) *)
(*                 (cs, ks $+ (kid, k), qmsgs, updateUserKeyHeap [k] usrDat, Return k) *)

(* | Barrier {result : Set} : user_cmd result. *)


Inductive step_universe {A B} : universe A B -> rlabel -> universe A B -> Prop :=
| StepUser : forall U U' (u_id : user_id) userData usrs adv cs gks ks qmsgs mycs lbl (cmd : user_cmd A),
    U.(users) $? u_id = Some userData
    -> step_user lbl (Some u_id)
                (build_data_step U userData)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
    -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks
                                               ; msg_heap := qmsgs
                                               ; protocol := cmd
                                               ; c_heap   := mycs |}
    -> step_universe U lbl U'
| StepAdversary : forall U U' usrs adv cs gks ks qmsgs mycs lbl (cmd : user_cmd B),
    step_user lbl None
              (build_data_step U U.(adversary))
              (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd)
    -> U' = buildUniverseAdv usrs cs gks {| key_heap := ks
                                         ; msg_heap := qmsgs
                                         ; protocol := cmd
                                         ; c_heap   := mycs |}
    -> step_universe U Silent U'
.
