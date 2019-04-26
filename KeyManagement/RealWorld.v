From Coq Require Import String Sumbool Morphisms.

Require Import MyPrelude Common Maps.

Set Implicit Arguments.

Definition key_identifier := nat.

Inductive key_usage :=
| Encryption
| Signing.

Lemma key_usage_eq_dec :
  forall u1 u2 : key_usage, { u1 = u2 } + { u1 <> u2 }.
  decide equality.
Defined.

Inductive key_type :=
| SymKey
| AsymKey.

Lemma key_type_eq_dec :
  forall kt1 kt2 : key_type, { kt1 = kt2 } + { kt1 <> kt2 }.
  decide equality.
Defined.

Record key :=
  MkCryptoKey { keyId    : key_identifier
              ; keyUsage : key_usage
              ; keyType  : key_type
              }.

Lemma key_eq_dec :
  forall k1 k2 : key, { k1 = k2 } + { k1 <> k2 }.
  decide equality; auto using Nat.eq_dec, key_usage_eq_dec, key_type_eq_dec.
Defined.

Definition key_permission : Set := key_identifier * bool.

(* Record key_permission := *)
(*   MkKeyPerm { key_ref            : key_identifier *)
(*             ; has_private_access : bool *)
(*             }. *)

Lemma key_permission_eq_dec :
  forall kp1 kp2 : key_permission, { kp1 = kp2 } + { kp1 <> kp2 }.
  decide equality; auto using Nat.eq_dec, Bool.bool_dec.
Defined.

Notation "x ==kk y" := (key_eq_dec x y) (right associativity, at level 75).
Notation "x ==ku y" := (key_usage_eq_dec x y) (right associativity, at level 75).
Notation "x ==kt y" := (key_type_eq_dec x y) (right associativity, at level 75).
Notation "x ==kp y" := (key_permission_eq_dec x y) (right associativity, at level 75).

Definition cipher_id := nat.

Inductive type : Set :=
| Nat
(* | Text *)
| Key
| CipherId
| Pair (t1 t2 : type)
.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Key => key_permission
  | CipherId => cipher_id
  | Pair t1 t2 => typeDenote t1 * typeDenote t2
  end.

Inductive message : type -> Type :=
(* This will eventually be a message Text, using nat for now *)
| Plaintext (txt : nat) : message Nat
| KeyMessage  (k : key_permission) : message Key

| MsgPair {t1 t2 : type} (msg1 : message t1) (msg2 : message t2) : message (Pair t1 t2)

| SignedCiphertext (msg_id : cipher_id) : message CipherId
| Signature {t} (msg : message t) (sig : cipher_id) : message t
.

(* We need to handle non-deterministic message  -- external choice on ordering *)
Inductive msg_pat :=
| Accept
| Paired (pat1 pat2 : msg_pat)
| Signed (k : key_identifier)
| SignedEncrypted (k__sign k__enc : key_identifier)
.

Inductive cipher : Type :=
| SigCipher {t} (c_id : cipher_id) (k_id : key_identifier) (msg : message t) : cipher
| SigEncCipher {t} (c_id : cipher_id) (k__sign k__enc : key_identifier) (msg : message t) : cipher
.

Definition cipher_signing_key (c : cipher) :=
  match c with
  | SigCipher _ k _      => k
  | SigEncCipher _ k _ _ => k
  end.

Definition queued_messages := list (sigT message).
Definition keys            := NatMap.t key.
Definition key_perms       := NatMap.t bool.
Definition ciphers         := NatMap.t cipher.

Inductive msg_accepted_by_pattern (cs : ciphers) (pat : msg_pat) : forall {t : type}, message t -> Prop :=
| MsgAccept : forall {t} (m : message t),
      pat = Accept
    -> msg_accepted_by_pattern cs pat m
| BothPairsAccepted : forall {t1 t2} m p1 p2 (m1 : message t1) (m2 : message t2),
      pat = Paired p1 p2
    -> m   = MsgPair m1 m2
    -> msg_accepted_by_pattern cs p1 m1
    -> msg_accepted_by_pattern cs p2 m2
    -> msg_accepted_by_pattern cs pat m
| ProperlySigned : forall {t} c_id k m (m' : message t),
      pat = Signed k
    -> m   = Signature m' c_id
    -> cs $? c_id = Some (SigCipher c_id k m')
    -> msg_accepted_by_pattern cs pat m
| ProperlyEncrypted : forall {t} c_id k__sign k__enc m (m' : message t),
      pat = SignedEncrypted k__sign k__enc
    -> m   = SignedCiphertext c_id
    -> cs $? c_id = Some (SigEncCipher c_id  k__sign k__enc m')
    -> msg_accepted_by_pattern cs pat m
.

Ltac clean_map_lookups1 :=
  match goal with
  | [ H : Some _ = None   |- _ ] => invert H
  | [ H : None = Some _   |- _ ] => invert H
  | [ H : Some _ = Some _ |- _ ] => invert H
  | [ H : $0 $? _ = Some _ |- _ ] => invert H
  | [ H : _ $+ (?k,_) $? ?k = _ |- _ ] => rewrite add_eq_o in H by trivial
  | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by auto
  | [ |- context[_ $+ (?k,_) $? ?k] ] => rewrite add_eq_o by trivial
  | [ |- context[_ $+ (?k1,_) $? ?k2] ] => rewrite add_neq_o by auto
  | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
  | [ H1 : ?m $? ?k = _ , H2 : ?m $? ?k = _ |- _] => rewrite H1 in H2
  end.

(* Ltac contra_map_lookup := *)
(*   match goal with *)
(*   | [ H1 : ?ks $? ?k = Some _, H2 : ?ks $? ?k = None |- _ ] => rewrite H1 in H2; invert H2 *)
(*   | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction *)
(*   end. *)

Ltac contra_map_lookup :=
  repeat
    match goal with
    | [ H1 : ?ks1 $? ?k = _, H2 : ?ks2 $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2
    | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction
    end; try discriminate.

Ltac clean_map_lookups :=
  (repeat clean_map_lookups1);
  try discriminate;
  try contra_map_lookup.

Ltac split_ands :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac split_ors :=
  repeat match goal with
         | [ H : _ \/ _ |- _ ] => destruct H
         end.

Ltac Equal_eq :=
  repeat
    match goal with
    | [ H : Equal _ _ |- _] => apply map_eq_Equal in H; subst
    end.

Ltac context_map_rewrites :=
  repeat
    match goal with
    | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H
    | [ H : match ?matchee with _ => _ end $? _ = _
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    | [ H : match ?matchee with _ => _ end = _
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    end.

Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff.

Section SafeMessages.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Definition has_private_key (k : key_permission) : bool :=
    match (all_keys $? fst k) with
    | None      => false
    | Some (MkCryptoKey _ _ SymKey)  => true
    | Some (MkCryptoKey _ _ AsymKey) => snd k
    end.

    Definition honest_key (k : key_identifier) : bool :=
    match all_keys $? k with
    | None                           => false
    | Some (MkCryptoKey _ _ SymKey)  =>
      match honestk $? k with
      | None   => false
      | Some _ => true
      end
    | Some (MkCryptoKey _ _ AsymKey) =>
      match honestk $? k with
      | None          => false
      | Some has_priv => has_priv
      end
    end.

  Definition honest_signing_key (k : key_identifier) : bool :=
    honest_key k
      && match all_keys $? k with
         | Some (MkCryptoKey _ Signing _) => true
         | _                              => false
         end.

  Definition honest_encryption_key (k : key_identifier) : bool :=
    honest_key k
      && match all_keys $? k with
         | Some (MkCryptoKey _ Encryption _) => true
         | _                              => false
         end.

  Fixpoint msg_needs_encryption {t} (msg : message t) : bool :=
    match msg with
    | Plaintext _        => false
    | KeyMessage k       => match all_keys $? fst k with
                           | None   => false
                           | Some _ => honest_key (fst k)
                           end
    | MsgPair msg1 msg2  => msg_needs_encryption msg1 || msg_needs_encryption msg2
    | SignedCiphertext _ => false
    | Signature msg _    => msg_needs_encryption msg
    end.

  Definition cipher_adversary_safe (c : cipher) : bool :=
    match c with
    | SigCipher _ k_id msg              => negb (msg_needs_encryption msg)
    | SigEncCipher _ k__signid k__encid msg => negb (msg_needs_encryption msg)
                                          || honest_encryption_key k__encid
    end.

  Definition cipher_honestly_signed (c : cipher) : bool :=
    match c with
    | SigCipher _ k_id _              => honest_signing_key k_id
    | SigEncCipher _ k__signid k__encid _ => honest_signing_key k__signid
    end.

  Definition ciphers_honestly_signed (cs : ciphers) : bool :=
    for_all (fun _ => cipher_honestly_signed) cs.

  Definition message_queue_safe : queued_messages -> bool :=
    forallb (fun m => match m with | existT _ _ msg => msg_needs_encryption msg end).

  Fixpoint msg_pattern_spoofable (pat : msg_pat) : bool :=
    match pat with
    | Accept                     => true
    | Paired p1 p2               => msg_pattern_spoofable p1 || msg_pattern_spoofable p2
    | Signed k                   => negb (honest_signing_key k)
    | SignedEncrypted k__sign k__enc => negb (honest_signing_key k__sign)
    end.

End SafeMessages.

Lemma cipher_honestly_signed_proper :
  forall ks perms,
    Proper (eq ==> eq ==> eq) (fun _ : NatMap.key => cipher_honestly_signed ks perms).
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
| Send {t} (uid : user_id) (msg : message t) : user_cmd unit
| Recv {t} (pat : msg_pat) : user_cmd (message t)

(* Crypto!! *)
| SignEncrypt {t} (k__sign k__enc : key_permission) (msg : message t) : user_cmd (message CipherId)
| Decrypt {t} (msg : message CipherId) : user_cmd (message t)

| Sign    {t} (k : key_permission) (msg : message t) : user_cmd (message t)
| Verify  {t} (k : key_permission) (msg : message t) : user_cmd bool

| GenerateSymKey  (usage : key_usage) : user_cmd key_permission
| GenerateAsymKey (usage : key_usage) : user_cmd key_permission

(* Allow administrator to make some global change to the universe -- revoke keys, etc. *)
(* This may be a universe level step -- Administrator forces all users to stop *)
(* | Barrier {result : Set} : user_cmd result *)
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
    }.

Definition honest_users A := user_list (user_data A).
Definition powerless_adv {B} (b : B) : user_data B :=
  {| key_heap := $0
   ; protocol := Return b
   ; msg_heap := []  |}.

Definition is_powerless {B} (usr : user_data B) : bool :=
   is_empty usr.(key_heap)
&& match usr.(protocol) with
   | Return _ => true
   | _        => false
   end
&& match usr.(msg_heap) with
   | [] => true
   | _  => false
   end.

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : user_data B
    ; all_ciphers : ciphers
    ; all_keys    : keys
    }.

Definition keys_good (ks : keys) : Prop :=
  forall k_id k,
    ks $? k_id = Some k
    -> keyId k = k_id.

Definition greatest_permission (kp1 kp2 : bool) : bool :=
  kp1 || kp2.

Definition add_key_perm (k : key_identifier)(kp : bool) (perms : key_perms) : key_perms :=
    match perms $? k with
    | None     => perms $+ (k, kp)
    | Some kp' => perms $+ (k, greatest_permission kp kp')
    end.

Lemma greatest_permission_refl :
  forall k,
    greatest_permission k k = k.
Proof.
  unfold greatest_permission; auto using orb_diag.
Qed.

Lemma greatest_permission_symm :
  forall kp1 kp2,
    greatest_permission kp1 kp2 = greatest_permission kp2 kp1.
Proof.
  unfold greatest_permission; auto using orb_comm.
Qed.

Definition merge_perms (ks ks' : key_perms) : key_perms :=
  fold add_key_perm ks ks'.

Notation "m1 $k++ m2" := (merge_perms m2 m1) (at level 50, left associativity).

Lemma add_key_perm_proper :
  Proper (eq  ==>  eq  ==>  eq  ==>  eq ) add_key_perm.
Proof.
  unfold Proper, respectful; intros; subst; trivial.
Qed.

Lemma add_key_perm_proper_Equal :
  Proper (eq  ==>  eq  ==>  Equal  ==>  Equal ) add_key_perm.
Proof.
  unfold Proper, respectful; intros; Equal_eq;
    unfold Equal; intros; trivial.
Qed.

(* Lemma add_key_perm_fold_fn_transpose' : *)
(*   forall (k k' : nat) (e e' : key_permission) a, *)
(*     k <> k' *)
(*     -> Equal *)
(*         match match a $? key_ref e' with *)
(*               | Some kp' => a $+ (key_ref e', greatest_permission e' kp') *)
(*               | None => a $+ (key_ref e', e') *)
(*               end $? key_ref e with *)
(*         | Some kp' => *)
(*           match a $? key_ref e' with *)
(*           | Some kp'0 => a $+ (key_ref e', greatest_permission e' kp'0) *)
(*           | None => a $+ (key_ref e', e') *)
(*           end $+ (key_ref e, greatest_permission e kp') *)
(*         | None => match a $? key_ref e' with *)
(*                  | Some kp' => a $+ (key_ref e', greatest_permission e' kp') *)
(*                  | None => a $+ (key_ref e', e') *)
(*                  end $+ (key_ref e, e) *)
(*         end *)
(*         match match a $? key_ref e with *)
(*               | Some kp' => a $+ (key_ref e, greatest_permission e kp') *)
(*               | None => a $+ (key_ref e, e) *)
(*               end $? key_ref e' with *)
(*         | Some kp' => *)
(*           match a $? key_ref e with *)
(*           | Some kp'0 => a $+ (key_ref e, greatest_permission e kp'0) *)
(*           | None => a $+ (key_ref e, e) *)
(*           end $+ (key_ref e', greatest_permission e' kp') *)
(*         | None => match a $? key_ref e with *)
(*                  | Some kp' => a $+ (key_ref e, greatest_permission e kp') *)
(*                  | None => a $+ (key_ref e, e) *)
(*                  end $+ (key_ref e', e') *)
(*         end. *)
(* Proof. *)
(*   unfold Equal; intros. *)
(*   destruct e; destruct e'; simpl. *)
(*   cases (key_ref0 ==n key_ref1); subst; auto. *)
(*   - cases (a $? key_ref1); clean_map_lookups; simpl. *)
(*     + cases (y ==n key_ref1); subst; clean_map_lookups; auto. *)
(*       unfold greatest_permission; destruct k0; simpl; auto. *)
(*       rewrite !orb_assoc. *)
(*       rewrite orb_comm with (b1:=has_private_access0). *)
(*       trivial. *)
(*     + unfold greatest_permission; simpl. *)
(*       cases (y ==n key_ref1); subst; clean_map_lookups; auto. *)
(*       rewrite orb_comm; trivial. *)
(*   - cases (a $? key_ref0); cases (a $? key_ref1); clean_map_lookups; *)
(*       rewrite Heq; rewrite Heq0; clean_map_lookups; *)
(*         unfold greatest_permission; try destruct k0; try destruct k1; simpl; *)
(*           cases (y ==n key_ref0); cases (y ==n key_ref1); subst; clean_map_lookups; try contradiction; auto. *)
(* Qed. *)

Lemma add_key_perm_transpose :
  transpose_neqkey eq add_key_perm.
Proof.
  unfold transpose_neqkey, add_key_perm; intros.
  apply map_eq_Equal; unfold Equal; intros;
    cases (a $? k); cases (a $? k');
      repeat (context_map_rewrites; clean_map_lookups);
      cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; trivial; contradiction.
Qed.

Lemma add_key_perm_transpose_Equal :
  transpose_neqkey Equal add_key_perm.
Proof.
  unfold transpose_neqkey, add_key_perm; intros.
  unfold Equal; intros;
    cases (a $? k); cases (a $? k');
      repeat (context_map_rewrites; clean_map_lookups);
      cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; trivial; contradiction.
Qed.

Hint Resolve
     add_key_perm_proper       add_key_perm_transpose
     add_key_perm_proper_Equal add_key_perm_transpose_Equal.

Fixpoint findKeys {t} (msg : message t) : key_perms :=
  match msg with
  | Plaintext _        => $0
  | KeyMessage k       => $0 $+ (fst k, snd k)
  | MsgPair msg1 msg2  => (findKeys msg1) $k++ (findKeys msg2)
  | SignedCiphertext _ => $0
  | Signature m _      => findKeys m
  end.

Definition findUserKeys {A} (us : user_list (user_data A)) : key_perms :=
  fold (fun u_id u ks => ks $k++ u.(key_heap)) us $0.

Definition addUserKeys {A} (ks : key_perms) (u : user_data A) : user_data A :=
  {| key_heap := u.(key_heap) $k++ ks ; protocol := u.(protocol) ; msg_heap := u.(msg_heap) |}.

Definition addUsersKeys {A} (us : user_list (user_data A)) (ks : key_perms) : user_list (user_data A) :=
  map (addUserKeys ks) us.

Definition adv_no_honest_keys (all_keys : keys) (honestk advk : key_perms) : Prop :=
  forall k_id,
    match all_keys $? k_id with
    | None                           => True
    | Some (MkCryptoKey _ _ SymKey)  =>
      match advk $? k_id with
      | None   => True
      | Some _ => False
      end
    | Some (MkCryptoKey _ _ AsymKey) =>
      match advk $? k_id with
      | None       => True
      | Some false => True
      | Some true  => honest_key all_keys honestk k_id = false
      end
    end.

Definition universe_ok {A B} (U : universe A B) : Prop :=
  let honestk := findUserKeys U.(users)
  in  (forall u_id (u_d : user_data A), U.(users) $? u_id = Some u_d -> message_queue_safe U.(all_keys) honestk (u_d.(msg_heap)) = true)
    /\ message_queue_safe U.(all_keys) honestk U.(adversary).(msg_heap) = true
    /\ keys_good U.(all_keys)
    /\ adv_no_honest_keys U.(all_keys) honestk U.(adversary).(key_heap).

Section KeyMergeTheorems.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.
  Variable k_good      : keys_good all_keys.

  Hint Resolve empty_Empty.

  Ltac progress_fold_add1 :=
    match goal with
    | [ H : fold add_key_perm (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H
    | [ H : _ $k++ (_ $+ (_,_)) $? _ = _ |- _ ] => unfold merge_perms in H; rewrite fold_add in H
    | [ |- context[ fold add_key_perm (_ $+ (_,_)) _ ] ] => rewrite fold_add
    | [ |- context[ _ $k++ (_ $+ (_,_))] ] => unfold merge_perms; rewrite fold_add
    end.

  Lemma merge_perms_notation :
    forall ks1 ks2,
      fold add_key_perm ks2 ks1 = ks1 $k++ ks2.
    unfold merge_perms; trivial.
  Qed.

  Lemma merge_perms_left_identity :
    forall ks,
      $0 $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; auto.

    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm; auto.
    rewrite IHks; auto.
    case_eq (ks $? x); intros; subst; clean_map_lookups; trivial.
  Qed.

  Lemma merge_keys_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_perms; intros; rewrite fold_Empty; eauto.
  Qed.

  Hint Rewrite merge_keys_right_identity merge_perms_left_identity.

  Lemma merge_perms_adds_no_new_perms :
    forall ks2 k ks1,
        ks1 $? k = None
      -> ks2 $? k = None
      -> (ks1 $k++ ks2) $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    case (x ==n k); intros; subst; clean_map_lookups.
    cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Hint Resolve merge_perms_adds_no_new_perms.

  Lemma merge_perms_came_from_somewhere1 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks2 $? k = None
      -> ks1 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    case (x ==n k); intros; subst; clean_map_lookups.
    progress_fold_add1; auto.
    rewrite merge_perms_notation in *.
    unfold add_key_perm in *.
    cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_came_from_somewhere2 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks1 $? k = None
      -> ks2 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - rewrite merge_keys_right_identity in H; clean_map_lookups.
    - case (k ==n x); intros; subst; clean_map_lookups;
        progress_fold_add1; auto;
          rewrite merge_perms_notation in *;
          unfold add_key_perm in *.
      + assert (ks1 $k++ ks2 $? x = None) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
      + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_came_from_somewhere1 merge_perms_came_from_somewhere2.

  Lemma merge_perms_adds_ks1 :
    forall ks2 ks1 k v ks,
        ks1 $? k = Some v
      -> ks2 $? k = None
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - subst; rewrite fold_Empty; eauto.
    - case (x ==n k); intros; subst; clean_map_lookups; eauto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm.
      cases ( ks1 $k++ ks2 $? x ); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_adds_ks2 :
    forall ks2 ks1 k v ks,
        ks1 $? k = None
      -> ks2 $? k = Some v
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    subst; progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    cases (k ==n x); subst; clean_map_lookups.
    + assert (ks1 $k++ ks2 $? x = None) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
    + cases ( ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_adds_ks1 merge_perms_adds_ks2.

  Lemma merge_perms_chooses_greatest :
    forall ks2 ks1 k k' kp kp',
        ks1 $? k = Some kp
      -> ks2 $? k' = Some kp'
      -> k = k'
      -> (ks1 $k++ ks2) $? k = Some (greatest_permission kp kp').
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    subst.
    cases (x ==n k'); subst; clean_map_lookups.
    + assert (ks1 $k++ ks2 $? k' = Some kp) by eauto.
      context_map_rewrites; clean_map_lookups; auto.
      rewrite greatest_permission_symm; trivial.
    + cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_perms_chooses_greatest.

  Lemma merge_perms_split :
    forall ks2 ks1 k kp,
      ks1 $k++ ks2 $? k = Some kp
      -> ks1 $? k = Some kp
      \/ ks2 $? k = Some kp.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    cases (x ==n k); subst; clean_map_lookups; auto;
      progress_fold_add1; auto;
        rewrite merge_perms_notation in *;
        unfold add_key_perm in *.

    + subst. clean_map_lookups.
      cases (ks1 $k++ ks2 $? k); clean_map_lookups; auto.
      apply merge_perms_came_from_somewhere1 in Heq; auto.
      unfold greatest_permission; cases e; cases b; simpl; auto.

    + cases (ks1 $k++ ks2 $? x); clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_no_disappear_perms :
    forall ks2 k ks1,
      ks1 $k++ ks2 $? k = None
    -> ks1 $? k = None
    /\ ks2 $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation in *; clean_map_lookups.
    unfold add_key_perm in *.
    cases (ks1 $k++ ks2 $? x);
      cases (x ==n k); subst; clean_map_lookups; auto.
  Qed.

  Lemma merge_keys_neq_add_ok :
    forall ks2 ks1 k k' kp,
      k <> k'
      -> ks1 $+ (k,kp) $k++ ks2 $? k' = ks1 $k++ ks2 $? k'.
  Proof.
    intros.
    cases (ks1 $? k'); cases (ks2 $? k').
    - erewrite !merge_perms_chooses_greatest; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_ks1; auto; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_ks2; auto; clean_map_lookups; eauto.
    - erewrite !merge_perms_adds_no_new_perms; clean_map_lookups; auto.
  Qed.

  Hint Resolve merge_keys_neq_add_ok.

  Lemma merge_keys_pull1 :
    forall ks2 ks1 k kp kp' gkp,
        ks2 $? k = Some kp'
      -> gkp = greatest_permission kp kp'
      -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; contra_map_lookup; eauto.
    apply map_eq_Equal; unfold Equal; intros.
    cases (k ==n x); cases (k ==n y); cases (x ==n y); subst; clean_map_lookups; try contradiction.
    - eapply merge_perms_chooses_greatest; auto; clean_map_lookups; trivial.
    - unfold merge_perms at 1; rewrite fold_add; auto; rewrite merge_perms_notation; unfold add_key_perm.
      assert (ks1 $+ (x, kp) $k++ ks2 $? x = Some kp) by (eapply merge_perms_adds_ks1; eauto; clean_map_lookups; trivial).
      context_map_rewrites; clean_map_lookups.
      unfold merge_perms at 2; rewrite fold_add; auto; rewrite merge_perms_notation with (ks1:=ks1); unfold add_key_perm.
      cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups; eauto.
    - progress_fold_add1; auto.
      rewrite merge_perms_notation; unfold add_key_perm.
      cases (ks1 $+ (y, kp) $k++ ks2 $? x); clean_map_lookups; auto;
        erewrite merge_perms_chooses_greatest; auto; clean_map_lookups; eauto.
    - unfold merge_perms; rewrite !fold_add; auto.
      rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
      unfold add_key_perm.
      cases (ks1 $k++ ks2 $? y); eauto.
      + assert (ks1 $? y = Some b) by eauto.
        assert (ks1 $+ (k, kp) $k++ ks2 $? y = Some b). eapply merge_perms_adds_ks1; auto. clean_map_lookups; auto. auto.
        context_map_rewrites; clean_map_lookups; trivial.
      + eapply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        assert (ks1 $+ (k, kp) $k++ ks2 $? y = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
        context_map_rewrites; clean_map_lookups; auto.
    - unfold merge_perms; rewrite !fold_add; auto.
      rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
      unfold add_key_perm.
      cases (ks1 $k++ ks2 $? x); clean_map_lookups.
      + apply merge_perms_came_from_somewhere1 in Heq; eauto.
        assert (ks1 $+ (k, kp) $k++ ks2 $? x = Some b). eapply merge_perms_adds_ks1; auto. clean_map_lookups; auto. auto.
        context_map_rewrites; clean_map_lookups; auto.
      + eapply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        assert (ks1 $+ (k, kp) $k++ ks2 $? x = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
        context_map_rewrites; clean_map_lookups; auto.
  Qed.

  Lemma merge_keys_pull2 :
    forall ks2 ks1 k kp gkp,
        ks2 $? k = None
      -> gkp = kp
      -> (ks1 $+ (k, kp)) $k++ ks2 = ks1 $k++ ks2 $+ (k, gkp).
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; autorewrite with core; subst; auto.
    cases (x ==n k); subst; clean_map_lookups.
    unfold merge_perms; rewrite !fold_add; auto.
    rewrite merge_perms_notation. rewrite merge_perms_notation with (ks1:=ks1).
    unfold add_key_perm.
    cases (ks1 $k++ ks2 $? x).
    - apply merge_perms_came_from_somewhere1 in Heq; auto.
      assert (ks1 $+ (k, kp) $k++ ks2 $? x = Some b) by (eapply merge_perms_adds_ks1; trivial; clean_map_lookups; auto).
      context_map_rewrites; clean_map_lookups; auto.
      erewrite IHks2; auto.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n x); cases (y ==n k); subst; clean_map_lookups; auto; contradiction.
    - apply merge_perms_no_disappear_perms in Heq; auto; split_ands.
      assert (ks1 $+ (k, kp) $k++ ks2 $? x = None) by (apply merge_perms_adds_no_new_perms; clean_map_lookups; auto).
      context_map_rewrites.
      apply map_eq_Equal; unfold Equal; intros.
      erewrite IHks2; auto.
      cases (y ==n x); cases (y ==n k); subst; clean_map_lookups; auto; contradiction.
  Qed.

  Lemma merge_perms_sym :
    forall ks2 ks1,
      ks1 $k++ ks2 = ks2 $k++ ks1.
  Proof.
    induction ks2 using P.map_induction_bis; intros; Equal_eq; eauto.
    - rewrite merge_keys_right_identity, merge_perms_left_identity; trivial.
    - unfold merge_perms at 1; rewrite fold_add; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm; simpl.

      cases (ks1 $k++ ks2 $? x); subst; clean_map_lookups.
      + apply merge_perms_came_from_somewhere1 in Heq; auto.
        erewrite merge_keys_pull1; eauto; rewrite IHks2; auto.
      + apply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        erewrite merge_keys_pull2; eauto; rewrite IHks2; auto.
  Qed.

  Lemma merge_perms_refl :
    forall ks,
      ks $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros; Equal_eq; auto.
    progress_fold_add1; auto.
    rewrite merge_perms_notation.
    unfold add_key_perm.
    erewrite merge_keys_pull2; clean_map_lookups; auto.
    rewrite map_add_eq, IHks; rewrite greatest_permission_refl; trivial.
  Qed.

  Lemma merge_perms_assoc :
    forall ks3 ks1 ks2,
      ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Proof.
    induction ks3 using P.map_induction_bis; intros; Equal_eq; auto.
    unfold merge_perms at 1.
    unfold merge_perms at 3.
    rewrite !fold_add; auto.
    rewrite merge_perms_notation.
    rewrite merge_perms_notation with (ks1:=ks2).
    unfold add_key_perm.

    cases (ks2 $k++ ks3 $? x).
    - cases (ks1 $k++ ks2 $k++ ks3 $? x);
        subst; rewrite IHks3 in Heq0; clean_map_lookups; eauto.
      + cases (ks1 $? x).
        * assert (ks1 $k++ (ks2 $k++ ks3) $? x = Some (greatest_permission b1 b)) by eauto.
          clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n x); subst; clean_map_lookups.
          ** assert (ks1 $k++ (ks2 $k++ ks3 $+ (x, greatest_permission e b)) $? x = Some (greatest_permission b1 (greatest_permission e b)))
              by (eapply merge_perms_chooses_greatest; auto; clean_map_lookups; auto).
             context_map_rewrites; unfold greatest_permission.
             rewrite !orb_assoc, orb_comm with (b1:=e); trivial.
          ** symmetry; rewrite merge_perms_sym.
             rewrite merge_keys_neq_add_ok, merge_perms_sym, <- IHks3; auto; trivial.
        * assert (ks1 $k++ (ks2 $k++ ks3) $? x = Some b) by eauto; clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n x); subst; clean_map_lookups.
          ** assert (ks1 $k++ (ks2 $k++ ks3 $+ (x, greatest_permission e b)) $? x = Some (greatest_permission e b))
              by (eapply merge_perms_adds_ks2; auto; clean_map_lookups; auto).
             context_map_rewrites; eauto.
          ** symmetry; rewrite merge_perms_sym.
             rewrite merge_keys_neq_add_ok, merge_perms_sym, <- IHks3; auto; trivial.

      + apply merge_perms_no_disappear_perms in Heq0; auto; split_ands; contra_map_lookup.

    - unfold merge_perms at 7.
      rewrite fold_add; auto.
      unfold add_key_perm at 1. rewrite merge_perms_notation with (ks2:=ks2 $k++ ks3).
      rewrite IHks3; trivial.
  Qed.

  Lemma findUserKeys_foldfn_proper :
    forall {A},
      Proper (eq ==> eq ==> eq ==> eq) (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold Proper, respectful; intros; subst; trivial.
  Qed.

  Lemma findUserKeys_foldfn_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite !merge_perms_assoc,merge_perms_sym with (ks1:=key_heap e'); trivial.
  Qed.

  Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose.

  Lemma findUserKeys_notation :
    forall {A} (usrs : honest_users A),
      fold (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u) usrs $0 = findUserKeys usrs.
    unfold findUserKeys; trivial.
  Qed.

  Lemma map_ne_swap :
    forall {V} (m : NatMap.t V) k v k' v',
      k <> k'
      -> m $+ (k,v) $+ (k',v') = m $+ (k',v') $+ (k,v).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; auto; contradiction.
  Qed.

  Lemma findUserKeys_readd_user_same_keys_idempotent :
    forall {A} (usrs : honest_users A) u_id u_d proto msgs,
      usrs $? u_id = Some u_d
      -> findUserKeys usrs = findUserKeys (usrs $+ (u_id, {| key_heap := key_heap u_d; protocol := proto; msg_heap := msgs |})).
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

  Lemma safe_messages_have_no_bad_keys :
    forall {t} (msg : message t) msgk,
      msg_needs_encryption all_keys honestk msg = false
      -> adv_no_honest_keys all_keys honestk advk
      -> msgk = findKeys msg
      -> forall k_id k,
            msgk $? k_id = Some k
          -> honest_key all_keys honestk k_id = false.
  Proof.
    induction msg; auto; intros; simpl in *; subst; clean_map_lookups.

    - destruct k; simpl in *.
      unfold honest_key.
      cases (k ==n k_id); subst; clean_map_lookups.
      cases (all_keys $? k_id); eauto.
      destruct k.
      unfold honest_key in *; context_map_rewrites.
      cases keyType0; eauto.
    - apply orb_false_elim in H; split_ands.
      apply merge_perms_split in H2; auto; split_ors; eauto.
  Qed.

  (* Lemma add_key_results : *)
  (*   forall k v ks ks', *)
  (*     ks' = add_key k v ks *)
  (*     -> ks' = ks *)
  (*     \/ ks' = ks $+ (k,v) *)
  (*     \/ exists k', ks' = ks $+ (k, canonical_key v k'). *)
  (* Proof. *)
  (*   unfold add_key; intros. *)
  (*   cases (ks $? k); auto. *)
  (*   cases (v ==kk k0); auto. *)
  (*   intuition eauto. *)
  (* Qed. *)

  (* Lemma find_user_keys_includes_user_keys: *)
  (*   forall {A} (us : honest_users A) u_id u_d, *)
  (*     us $? u_id = Some u_d *)
  (*     -> findUserKeys us = u_d.(key_heap) $k++ findUserKeys (us $- u_id). *)
  (* Proof. *)
  (*   unfold findUserKeys. *)
  (*   induction us using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - invert H. *)
  (*   - apply map_eq_Equal; unfold Equal; subst; intros. *)
  (*     simpl. *)
  (*     cases (x ==n u_id); intros; subst; clean_map_lookups. *)
  (*     + rewrite add_remove_eq. *)
  (*       rewrite fold_add; auto. rewrite remove_not_in_idempotent by assumption. *)
  (*       rewrite merge_keys_symmetric. *)
  (*       trivial. *)
  (*     + rewrite add_remove_neq by assumption. *)
  (*       rewrite !fold_add; auto. *)
  (*       rewrite <- merge_keys_assoc. *)
  (*       erewrite IHus; eauto. *)
  (*       rewrite not_find_in_iff; rewrite remove_neq_o; auto. *)
  (* Qed. *)

  (* Lemma find_user_keys_universe_user : *)
  (*   forall {A B} (U : universe A B) u_id u_d, *)
  (*       adv_no_honest_keys U.(adversary).(key_heap) (findUserKeys U.(users)) *)
  (*     -> U.(users) $? u_id = Some u_d *)
  (*     -> key_heaps_compatible U.(adversary).(key_heap) (findUserKeys U.(users)) *)
  (*     -> adv_no_honest_keys U.(adversary).(key_heap) u_d.(key_heap). *)
  (* Proof. *)
  (* Admitted. *)

End KeyMergeTheorems.

Definition sign_if_ok (c : cipher) (kt : key_type) (k : key_permission) : option cipher :=
  match (kt,k) with
  | (SymKey,  (_, _))     => Some c
  | (AsymKey, (_, true))  => Some c
  | (AsymKey, (_, false)) => None
  end.

Definition encryptMessage {t} (ks : keys) (k__sign k__enc : key_permission) (m : message t) (c_id : cipher_id) : option cipher :=
  match (ks $? fst k__sign, ks $? fst k__enc) with
  | (Some (MkCryptoKey _ Signing kt__sign), Some (MkCryptoKey _ Encryption kt__enc)) =>
    sign_if_ok (SigEncCipher c_id (fst k__sign) (fst k__enc) m) kt__sign k__sign
  | _ => None
  end.

Definition signMessage {t} (ks : keys) (k : key_permission) (m : message t) (c_id : cipher_id) : option cipher :=
  match ks $? fst k with
  | Some (MkCryptoKey _ Signing kt)     =>
    sign_if_ok (SigCipher c_id (fst k) m) kt k
  | _ => None
  end.

Definition canVerifySignature {A} (cs : ciphers) (usrDat : user_data A) (c_id : cipher_id) : Prop :=
  forall t (m : message t) k_id k ,
    cs $? c_id = Some (SigCipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

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
  | Plaintext t => Some t
  | _           => None
  end.

Definition unSig {t} (msg : message t) : option (message t) :=
  match msg with
  | Signature m _ => Some m
  | _             => None
  end.

(* Definition unPair {t1 t2} (msg : message (Pair t1 t2)) : option (message t1 * message t2)  := *)
(*   match msg *)
(*         in (message t) *)
(*         (* return (match t with _ => option (message t1 * message t2) end) *) *)
(*         return (match t with *)
(*                 | Pair t1 t2 => option (message t1 * message t2) *)
(*                 | _ => option (message t1 * message t2) end) *)
(*   with *)
(*   | MsgPair m1 m2 => Some (m1,m2) *)
(*   | _             => None *)
(*   end. *)


Inductive action : Type :=
| Input  t (msg : message t) (pat : msg_pat) (uks : key_perms)
| Output t (msg : message t)
.

Definition rlabel := @label action.

Definition action_adversary_safe (all_keys : keys) (honestk advk : key_perms) (a : action) : bool :=
  match a with
  | Input _ pat _ => negb (msg_pattern_spoofable all_keys honestk pat)
  | Output _      => true
  end.

Definition data_step0 (A B C : Type) : Type :=
  honest_users A * user_data B * ciphers * keys * key_perms * queued_messages * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B C :=
  (U.(users), U.(adversary), U.(all_ciphers), U.(all_keys), u_data.(key_heap), u_data.(msg_heap), u_data.(protocol)).

(* Labeled transition system *)

Inductive step_user : forall A B C, rlabel -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {B r r'} (usrs usrs' : honest_users r') (adv adv' : user_data B)
                     lbl cs cs' qmsgs qmsgs' gks gks' ks ks' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user lbl (usrs, adv, cs, gks, ks, qmsgs, cmd1) (usrs', adv', cs', gks', ks', qmsgs', cmd1')
    -> step_user lbl (usrs, adv, cs, gks, ks, qmsgs, Bind cmd1 cmd2) (usrs', adv', cs', gks', ks', qmsgs', Bind cmd1' cmd2)
| StepBindProceed : forall {B r r'} (usrs : honest_users r) (adv : user_data B) cs gks ks qmsgs (v : r') (cmd : r' -> user_cmd r),
    step_user Silent (usrs, adv, cs, gks, ks, qmsgs, Bind (Return v) cmd) (usrs, adv, cs, gks, ks, qmsgs, cmd v)

| StepGen : forall {A B} (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs n,
    step_user Silent (usrs, adv, cs, gks, ks, qmsgs, Gen) (usrs, adv, cs, gks, ks, qmsgs, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks ks' qmsgs qmsgs' (msg : message t) msgs pat newkeys,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> msg_accepted_by_pattern cs pat msg
    -> step_user (Action (Input msg pat ks))
                (usrs, adv, cs, gks, ks , qmsgs , Recv pat)
                (usrs, adv, cs, gks, ks', qmsgs', Return msg)

| StepRecvDrop : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs qmsgs' (msg : message t) pat msgs,
      qmsgs = (existT _ _ msg) :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> ~ msg_accepted_by_pattern cs pat msg
    -> step_user Silent (* Error label ... *)
                (usrs, adv, cs, gks, ks, qmsgs , Recv pat)
                (usrs, adv, cs, gks, ks, qmsgs', Return msg)

(* Augment attacker's keys with those available through messages sent,
 * including traversing through ciphers already known by attacker, etc.
 *)
| StepSend : forall {A B} {t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
               cs gks ks qmsgs rec_u_id rec_u newkeys (msg : message t),
    findKeys msg = newkeys
    -> adv' = addUserKeys newkeys adv
    -> usrs $? rec_u_id = Some rec_u
    -> usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                  ; protocol := rec_u.(protocol) 
                                  ; msg_heap := rec_u.(msg_heap) ++ [existT _ _ msg]  |})
    -> step_user (Action (Output msg))
                (usrs , adv , cs, gks, ks, qmsgs, Send rec_u_id msg)
                (usrs', adv', cs, gks, ks, qmsgs, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' gks ks qmsgs (msg : message t)
                  k__sign k__enc k__signid k__encid kp__sign kp__enc c_id cipherMsg,
      k__sign = (k__signid, kp__sign)
    -> k__enc  = (k__encid, kp__enc)
    -> ks $? k__signid = Some (kp__sign)
    -> has_private_key gks k__sign = true
    -> ks $? k__encid = Some (kp__enc)
    -> ~ In c_id cs
    -> encryptMessage gks k__sign k__enc msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , gks, ks, qmsgs, SignEncrypt k__sign k__enc msg)
                (usrs, adv, cs', gks, ks, qmsgs, Return (SignedCiphertext c_id))

| StepDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks ks' qmsgs (msg : message t)
                  k__signid kp__sign k__encid c_id newkeys kt,
      cs $? c_id = Some (SigEncCipher c_id k__signid k__encid msg)
    -> ( (exists kp__enc, gks $? k__encid = Some (MkCryptoKey k__encid Encryption SymKey)  /\ ks $? k__encid = Some kp__enc)
      \/ (gks $? k__encid = Some (MkCryptoKey k__encid Encryption AsymKey) /\ ks $? k__encid = Some true)
      )
    -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt)
    -> ks $? k__signid = Some kp__sign
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> step_user Silent
                (usrs, adv, cs, gks, ks , qmsgs, Decrypt (SignedCiphertext c_id))
                (usrs, adv, cs, gks, ks', qmsgs, Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' gks ks qmsgs (msg : message t) kp k_id c_id cipherMsg,
      ks $? k_id = Some kp
    -> has_private_key gks (k_id,kp) = true
    -> ~(In c_id cs)
    -> signMessage gks (k_id,kp) msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , gks, ks, qmsgs, Sign (k_id,kp) msg)
                (usrs, adv, cs', gks, ks, qmsgs, Return (Signature msg c_id))

| StepVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs (msg : message t) k_id kp c_id,
    (* k is in your key heap *)
      ks $? k_id = Some kp
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (SigCipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> step_user Silent
                (usrs, adv, cs, gks, ks, qmsgs, (Verify (k_id,kp) (Signature msg c_id)))
                (usrs, adv, cs, gks, ks, qmsgs, Return true)
                (* (usrs, adv, cs, ks, qmsgs, Return (if (k_id ==n (keyId k)) then true else false)) *)
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

(* Lemma LStepRecv' : forall {B t} u_id (adv : adversaries B) globals globals' uks uks' (msg : message t) pat msgs newkeys, *)
(*       globals.(users_msg_buffer) $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *) *)
(*     -> globals' = setGlobalUserMsgs u_id msgs globals *)
(*     -> findKeys msg = newkeys *)
(*     -> msg_accepted_by_pattern globals.(all_ciphers) pat msg = true *)
(*     -> uks' = uks $++ newkeys *)
(*     -> lstep_user u_id (Action (Input msg pat u_id uks globals.(all_ciphers))) *)
(*                  (globals , adv, uks,  Recv pat) *)
(*                  (globals', adv, uks', Return msg). *)
(* Proof. *)
(*   intros; subst; econstructor; eauto. *)
(* Qed. *)

Inductive step_universe {A B} : universe A B -> rlabel -> universe A B -> Prop :=
| StepUser : forall U U' u_id userData usrs adv cs gks ks qmsgs lbl (cmd : user_cmd A),
    U.(users) $? u_id = Some userData
    -> step_user lbl
                (build_data_step U userData)
                (usrs, adv, cs, gks, ks, qmsgs, cmd)
    -> U' = buildUniverse usrs adv cs gks u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U lbl U'
| StepAdversary : forall U U' usrs adv cs gks ks qmsgs lbl (cmd : user_cmd B),
      step_user lbl
                (build_data_step U U.(adversary))
                (usrs, adv, cs, gks, ks, qmsgs, cmd)
    -> U' = buildUniverseAdv usrs cs gks {| key_heap := adv.(key_heap) $k++ ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U Silent U'
.
