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

Record key_permission :=
  MkKeyPerm { key_ref            : key_identifier
            ; has_private_access : bool
            }.

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
Definition key_perms       := NatMap.t key_permission.
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

Ltac contra_map_lookup :=
  match goal with
  | [ H1 : ?ks $? ?k = Some _, H2 : ?ks $? ?k = None |- _ ] => rewrite H1 in H2; invert H2
  | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction
  end.

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

Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff.

Section SafeMessages.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Definition has_private_key (k : key_permission) : bool :=
    match (all_keys $? k.(key_ref)) with
    | None      => false
    | Some (MkCryptoKey _ _ SymKey)  => true
    | Some (MkCryptoKey _ _ AsymKey) => k.(has_private_access)
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
      | None                        => false
      | Some (MkKeyPerm _ has_priv) => has_priv
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
    | KeyMessage k       => match all_keys $? k.(key_ref) with
                           | None   => false
                           | Some _ => honest_key k.(key_ref)
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
      (* msg_heap : user_msg_heap ; *)
      (* is_admin : bool *)
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
   end
.

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : user_data B
    ; all_ciphers : ciphers
    ; all_keys    : keys
    }.

(* Definition canonical_key (k1 k2 : key) := *)
(*   match Coq.Init.Nat.compare k1.(keyId) k2.(keyId) with *)
(*   | Gt => k1 *)
(*   | Lt => k2 *)
(*   | Eq => *)
(*     match (k1.(keyUsage), k2.(keyUsage)) with *)
(*     | (Signing, Encryption) => k1 *)
(*     | (Encryption, Signing) => k2 *)
(*     | _                     => *)
(*       match (k1.(keyType), k2.(keyType)) with *)
(*       | (SymKey, _) => k1 *)
(*       | (_, SymKey) => k2 *)
(*       | (AsymKey b1, AsymKey b2) => if b1 then k1 else k2 *)
(*       end *)
(*     end *)
(*   end. *)

Definition keys_good (ks : keys) : Prop :=
  forall k_id k,
    ks $? k_id = Some k
    -> keyId k = k_id.

Definition key_perms_good (perms : key_perms) : Prop :=
  forall k_id k,
      perms $? k_id = Some k
    -> key_ref k = k_id.

Section KeyPermissions.
  Variable perms : key_perms.
  Variable gperms : key_perms_good perms.

  (* Definition greatest_permission (kp1 kp2 : key_permission) (eq_proof : kp1.(key_ref) = kp2.(key_ref)) : key_permission := *)
  (*   match (kp1,kp2) with *)
  (*   | (MkKeyPerm _ has_priv1, MkKeyPerm _ has_priv2) => MkKeyPerm kp1.(key_ref) (has_priv1 || has_priv2) *)
  (*   end. *)

  Definition greatest_permission (kp1 kp2 : key_permission) : key_permission :=
    match (kp1,kp2) with
    | (MkKeyPerm _ has_priv1, MkKeyPerm _ has_priv2) => MkKeyPerm kp1.(key_ref) (has_priv1 || has_priv2)
    end.

  Definition add_key_perm (kp : key_permission) : key_perms :=
    match perms $? key_ref kp with
    | None     => perms $+ (key_ref kp, kp)
    | Some kp' => perms $+ (key_ref kp, greatest_permission kp kp')
    end.

  Lemma add_key_keeps_good :
    forall kp perms',
      perms' = add_key_perm kp
      -> key_perms_good perms'.
  Proof.
    intros.
    unfold key_perms_good in *; intros.
    unfold add_key_perm in *.
    destruct kp; subst; simpl in *.
    cases (k_id ==n key_ref0); cases (perms $? key_ref0); subst; clean_map_lookups; auto.
    unfold greatest_permission; destruct k0; simpl; trivial.
  Qed.

End KeyPermissions.

Lemma greatest_permission_refl :
  forall k,
    greatest_permission k k = k.
Proof.
  unfold greatest_permission; intros; destruct k; simpl in *; rewrite orb_diag; trivial.
Qed.

Lemma greatest_permission_symm :
  forall k1 k2,
    key_ref k1 = key_ref k2
    -> greatest_permission k1 k2 = greatest_permission k2 k1.
Proof.
  unfold greatest_permission; intros; destruct k1; destruct k2; simpl in *; subst; rewrite orb_comm; trivial.
Qed.

Definition add_key_perm_fold_fn (_ : key_identifier) (kp : key_permission) (perms : key_perms) : key_perms :=
  add_key_perm perms kp.

Definition merge_perms (ks ks' : key_perms) : key_perms :=
  fold add_key_perm_fold_fn ks ks'.

Notation "m1 $k++ m2" := (merge_perms m2 m1) (at level 50, left associativity).

Lemma add_key_perm_fold_fn_proper :
  Proper (eq  ==>  eq  ==>  eq  ==>  eq ) add_key_perm_fold_fn.
Proof.
  unfold Proper, respectful; intros; subst; trivial.
Qed.

Lemma add_key_perm_fold_fn_proper_Equal :
  Proper (eq  ==>  eq  ==>  Equal  ==>  Equal ) add_key_perm_fold_fn.
Proof.
  unfold Proper, respectful; intros.
  apply map_eq_Equal in H1; subst; unfold Equal; intros; trivial.
Qed.

Lemma add_key_perm_fold_fn_transpose' :
  forall (k k' : nat) (e e' : key_permission) a,
    k <> k'
    -> Equal
        match match a $? key_ref e' with
              | Some kp' => a $+ (key_ref e', greatest_permission e' kp')
              | None => a $+ (key_ref e', e')
              end $? key_ref e with
        | Some kp' =>
          match a $? key_ref e' with
          | Some kp'0 => a $+ (key_ref e', greatest_permission e' kp'0)
          | None => a $+ (key_ref e', e')
          end $+ (key_ref e, greatest_permission e kp')
        | None => match a $? key_ref e' with
                 | Some kp' => a $+ (key_ref e', greatest_permission e' kp')
                 | None => a $+ (key_ref e', e')
                 end $+ (key_ref e, e)
        end
        match match a $? key_ref e with
              | Some kp' => a $+ (key_ref e, greatest_permission e kp')
              | None => a $+ (key_ref e, e)
              end $? key_ref e' with
        | Some kp' =>
          match a $? key_ref e with
          | Some kp'0 => a $+ (key_ref e, greatest_permission e kp'0)
          | None => a $+ (key_ref e, e)
          end $+ (key_ref e', greatest_permission e' kp')
        | None => match a $? key_ref e with
                 | Some kp' => a $+ (key_ref e, greatest_permission e kp')
                 | None => a $+ (key_ref e, e)
                 end $+ (key_ref e', e')
        end.
Proof.
  unfold Equal; intros.
  destruct e; destruct e'; simpl.
  cases (key_ref0 ==n key_ref1); subst; auto.
  - cases (a $? key_ref1); clean_map_lookups; simpl.
    + cases (y ==n key_ref1); subst; clean_map_lookups; auto.
      unfold greatest_permission; destruct k0; simpl; auto.
      rewrite !orb_assoc.
      rewrite orb_comm with (b1:=has_private_access0).
      trivial.
    + unfold greatest_permission; simpl.
      cases (y ==n key_ref1); subst; clean_map_lookups; auto.
      rewrite orb_comm; trivial.
  - cases (a $? key_ref0); cases (a $? key_ref1); clean_map_lookups;
      rewrite Heq; rewrite Heq0; clean_map_lookups;
        unfold greatest_permission; try destruct k0; try destruct k1; simpl;
          cases (y ==n key_ref0); cases (y ==n key_ref1); subst; clean_map_lookups; try contradiction; auto.
Qed.

Lemma add_key_perm_fold_fn_transpose :
  transpose_neqkey eq add_key_perm_fold_fn.
Proof.
  unfold transpose_neqkey, add_key_perm_fold_fn, add_key_perm; intros.
  apply map_eq_Equal; eauto using add_key_perm_fold_fn_transpose'.
Qed.

Lemma add_key_perm_fold_fn_transpose_Equal :
  transpose_neqkey Equal add_key_perm_fold_fn.
Proof.
  unfold transpose_neqkey, add_key_perm_fold_fn, add_key_perm; intros.
  eauto using add_key_perm_fold_fn_transpose'.
Qed.

Hint Resolve add_key_perm_fold_fn_proper add_key_perm_fold_fn_transpose
     add_key_perm_fold_fn_proper_Equal add_key_perm_fold_fn_transpose_Equal.

(* Definition merge_keys (ks ks' : keys) : keys := *)
(*   fold add_key ks ks'. *)

(* Notation "m1 $k++ m2" := (merge_keys m2 m1) (at level 50, left associativity). *)

Fixpoint findKeys {t} (msg : message t) : key_perms :=
  match msg with
  | Plaintext _        => $0
  | KeyMessage k       => $0 $+ (key_ref k, k)
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
      | None                     => True
      | Some (MkKeyPerm _ false) => True
      | Some (MkKeyPerm _ true)  => honest_key all_keys honestk k_id = false
      end
    end.

Section KeyMergeTheorems.
  Variable all_keys : keys.
  Variable honestk advk : key_perms.

  Variable k_good      : keys_good all_keys.
  Variable honest_good : key_perms_good honestk.
  Variable adv_good    : key_perms_good advk.

  Hint Resolve empty_Empty.

  Ltac progress_fold_add1 :=
    match goal with
    | [ H : fold add_key_perm_fold_fn (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H
    | [ H : _ $k++ (_ $+ (_,_)) $? _ = _ |- _ ] => unfold merge_perms in H; rewrite fold_add in H
    | [ |- context[ fold add_key_perm_fold_fn (_ $+ (_,_)) _ ] ] => rewrite fold_add
    | [ |- context[ _ $k++ (_ $+ (_,_))] ] => unfold merge_perms; rewrite fold_add
    end.

  Lemma merge_perms_notation :
    forall ks1 ks2,
      fold add_key_perm_fold_fn ks2 ks1 = ks1 $k++ ks2.
    unfold merge_perms; trivial.
  Qed.

  Lemma key_perms_good_add :
    forall ks k_id kp,
      key_perms_good (ks $+ (k_id, kp))
      -> ~ In k_id ks
      -> key_ref kp = k_id
      /\ key_perms_good ks.
  Proof.
    intros.
    unfold key_perms_good in H.
    split.
    - apply H; clean_map_lookups; trivial.
    - unfold key_perms_good; intros; cases (k_id ==n k_id0); subst; clean_map_lookups;
        eapply H; clean_map_lookups; auto.
  Qed.

  Lemma empty_key_perms_good :
    key_perms_good $0.
  Proof.
    unfold key_perms_good; intros; invert H.
  Qed.

  Hint Resolve empty_key_perms_good.

  Lemma merge_perms_left_identity :
    forall ks,
        key_perms_good ks
      -> $0 $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - apply fold_Empty; eauto.
    - unfold merge_perms.
      rewrite fold_add; auto.
      apply key_perms_good_add in H0; auto; split_ands.

      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm.
      rewrite IHks; auto.

      case_eq (ks $? key_ref e); intros; subst; clean_map_lookups; trivial.
  Qed.

  Lemma merge_keys_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_perms; intros; rewrite fold_Empty; eauto.
  Qed.

  Lemma key_perms_merge_still_good :
    forall ks2 ks1,
      key_perms_good ks1
      -> key_perms_good ks2
      -> key_perms_good (ks1 $k++ ks2).
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - rewrite merge_keys_right_identity; auto.
    - apply key_perms_good_add in H1; split_ands; subst; auto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm; simpl.
      cases (ks1 $k++ ks2 $? key_ref e).
      + unfold key_perms_good; intros.
        specialize (IHks2 _ H0 H2).
        assert (ks1 $k++ ks2 $? key_ref e = Some k) as EQ by assumption; apply IHks2 in EQ.
        cases (key_ref e ==n k_id); subst; clean_map_lookups; auto.
        unfold greatest_permission; destruct e; destruct k; auto.
      + unfold key_perms_good; intros.
        cases (key_ref e ==n k_id); subst; clean_map_lookups; auto.
        specialize (IHks2 _ H0 H2); auto.
  Qed.

  Lemma merge_perms_adds_no_new_perms :
    forall ks2 k ks1,
        ks1 $? k = None
      -> ks2 $? k = None
      -> key_perms_good ks2
      -> (ks1 $k++ ks2) $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; auto.
    - apply map_eq_Equal in H; subst; auto.
    - progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm.
      apply key_perms_good_add in H2; split_ands; subst; auto.
      case (key_ref e ==n k); intros; subst; clean_map_lookups.
      cases (ks1 $k++ ks2 $? key_ref e); clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_came_from_somewhere1 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> key_perms_good ks1
      -> key_perms_good ks2
      -> ks2 $? k = None
      -> ks1 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - rewrite merge_keys_right_identity in H; auto.
    - case (x ==n k); intros; subst; clean_map_lookups.
      apply key_perms_good_add in H2; split_ands; subst; auto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation in H0.
      unfold add_key_perm_fold_fn, add_key_perm in H0.
      cases (ks1 $k++ ks2 $? key_ref e); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_came_from_somewhere2 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> key_perms_good ks1
      -> key_perms_good ks2
      -> ks1 $? k = None
      -> ks2 $? k = Some v.
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - rewrite merge_keys_right_identity in H; clean_map_lookups.
    - apply key_perms_good_add in H2; split_ands; subst; auto.
      case (k ==n key_ref e); intros; subst; clean_map_lookups.
      + progress_fold_add1; auto.
        rewrite merge_perms_notation in H0.
        unfold add_key_perm_fold_fn, add_key_perm in H0.
        assert (ks1 $k++ ks2 $? key_ref e = None) by eauto using merge_perms_adds_no_new_perms.
        rewrite H2 in H0; clean_map_lookups; trivial.
      + progress_fold_add1; auto.
        rewrite merge_perms_notation in H0.
        unfold add_key_perm_fold_fn, add_key_perm in H0.
        cases (ks1 $k++ ks2 $? key_ref e); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_adds_ks1 :
    forall ks2 ks1 k v ks,
        ks1 $? k = Some v
      -> ks2 $? k = None
      -> key_perms_good ks1                 
      -> key_perms_good ks2
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - subst; rewrite fold_Empty; eauto.
    - case (x ==n k); intros; subst; clean_map_lookups; eauto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm.
      apply key_perms_good_add in H3; split_ands; subst; auto.
      cases ( ks1 $k++ ks2 $? key_ref e ); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_adds_ks2 :
    forall ks2 ks1 k v ks,
        ks1 $? k = None
      -> ks2 $? k = Some v
      -> key_perms_good ks1                 
      -> key_perms_good ks2
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_perms.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - invert H0.
    - apply key_perms_good_add in H3; auto; split_ands; subst.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm.
      cases (k ==n key_ref e); subst; clean_map_lookups.
      + assert (ks1 $k++ ks2 $? key_ref v = None) as RW by eauto using merge_perms_adds_no_new_perms;
          rewrite RW; clean_map_lookups; trivial.
      + cases ( ks1 $k++ ks2 $? key_ref e); clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_split :
    forall ks2 ks1 k,
      ks1 $k++ ks2 $? key_ref k = Some k
      -> key_perms_good ks1
      -> key_perms_good ks2
      -> ks1 $? key_ref k = Some k
      \/ ks2 $? key_ref k = Some k.
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - rewrite merge_keys_right_identity in H; auto.
    - apply key_perms_good_add in H2; auto; split_ands; subst; clean_map_lookups.
      cases (key_ref e ==n key_ref k).
      + progress_fold_add1; auto. rewrite merge_perms_notation in H0.
        unfold add_key_perm_fold_fn, add_key_perm in H0.
        case_eq (ks1 $k++ ks2 $? key_ref e); intros; rewrite H2 in H0; clean_map_lookups; eauto.
        rewrite e0 in H0; clean_map_lookups.
        rewrite <- e0; clean_map_lookups.
        unfold greatest_permission in *; destruct e; destruct k0; simpl in *.
        cases has_private_access0; cases has_private_access1; simpl; auto.
        pose proof (key_perms_merge_still_good H1 H3) as MERGE_GOOD.
        assert (ks1 $k++ ks2 $? key_ref0 = Some {| key_ref := key_ref1; has_private_access := true |}) as EQ by assumption.
        apply MERGE_GOOD in EQ; simpl in EQ; subst.
        remember ({| key_ref := key_ref0; has_private_access := true |}) as k0.
        assert (ks1 $k++ ks2 $? key_ref k0 = Some k0) as IND by (subst; simpl; auto).
        specialize (IHks2 _ _ IND H1 H3); split_ors; subst.
          intuition idtac.
          simpl in *; contra_map_lookup.
          rewrite add_eq_o by auto. rewrite add_eq_o in H0 by auto; intuition idtac.
      + clean_map_lookups. apply IHks2; eauto.
        progress_fold_add1; auto. rewrite merge_perms_notation in H0.
        unfold add_key_perm_fold_fn, add_key_perm in H0; simpl in H0.
        cases (ks1 $k++ ks2 $? key_ref e); clean_map_lookups; auto.
  Qed.

  Lemma key_perms_good_add_good_perm :
    forall ks k,
      key_perms_good ks
      -> key_perms_good (ks $+ (key_ref k, k)).
  Proof.
    unfold key_perms_good; intros.
    cases (key_ref k ==n k_id); subst; clean_map_lookups; auto.
  Qed.

  Hint Resolve key_perms_good_add_good_perm.

  Lemma merge_perms_no_disappear_perms :
    forall ks2 k ks1,
      (ks1 $k++ ks2) $? k = None
    -> key_perms_good ks1
    -> key_perms_good ks2
    -> ks1 $? k = None
    /\ ks2 $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros; auto.
    - apply map_eq_Equal in H; subst; auto.
    - progress_fold_add1; auto.
      rewrite merge_perms_notation in *; clean_map_lookups.
      unfold add_key_perm_fold_fn, add_key_perm in H0.
      apply key_perms_good_add in H2; split_ands; subst; auto.
      cases (ks1 $k++ ks2 $? key_ref e); clean_map_lookups;
        cases (key_ref e ==n k); subst; clean_map_lookups; auto.
  Qed.


  Lemma merge_keys_add_l_pull :
    forall ks2 ks1 k,
      ks2 $? key_ref k = None
      -> key_perms_good ks1
      -> key_perms_good ks2
      -> ks1 $k++ ks2 $+ (key_ref k, k) = (ks1 $+ (key_ref k, k)) $k++ ks2.
  Proof.
    induction ks2 using P.map_induction_bis; auto; intros.
    - apply map_eq_Equal in H; subst; auto.
    - apply key_perms_good_add in H2; split_ands; subst; auto.
      cases (key_ref e ==n key_ref k); try rewrite e0 in *; clean_map_lookups; auto.
      unfold merge_perms at 2. rewrite fold_add; auto.
      unfold add_key_perm_fold_fn at 1.
      unfold add_key_perm.
      rewrite merge_perms_notation with (ks1:=ks1 $+ (key_ref k, k)).
      cases ( (ks1 $+ (key_ref k, k)) $k++ ks2 $? key_ref e); subst; clean_map_lookups; auto.
      + rewrite <- IHks2; clean_map_lookups; auto.
        unfold merge_perms at 1; rewrite fold_add; auto.
        rewrite merge_perms_notation.
        unfold add_key_perm_fold_fn, add_key_perm.
        apply merge_perms_came_from_somewhere1 in Heq; auto.
        clean_map_lookups.
        assert (ks1 $k++ ks2 $? key_ref e = Some k0) as RW by (eauto using merge_perms_adds_ks1);
          rewrite RW; clear RW.
        apply map_eq_Equal; unfold Equal; intros.
        cases (y ==n key_ref e); cases (y ==n key_ref k); subst; clean_map_lookups; trivial.
      + rewrite <- IHks2; clean_map_lookups; auto.
        unfold merge_perms at 1; rewrite fold_add; auto.
        rewrite merge_perms_notation.
        unfold add_key_perm_fold_fn, add_key_perm.
        apply merge_perms_no_disappear_perms in Heq; auto; split_ands; clean_map_lookups.
        assert (ks1 $k++ ks2 $? key_ref e = None) as RW by (eauto using merge_perms_adds_no_new_perms);
          rewrite RW; clear RW.
        apply map_eq_Equal; unfold Equal; intros.
        cases (y ==n key_ref e); cases (y ==n key_ref k); subst; clean_map_lookups; trivial.
  Qed.

  Lemma merge_keys_add_l_pull_in :
    forall ks2 ks1 k k',
        ks2 $? key_ref k  = Some k'
      -> ks1 $? key_ref k' = None
      -> key_perms_good ks1
      -> key_perms_good ks2
      -> key_ref k = key_ref k'
      -> ks1 $k++ ks2 $+ (key_ref k, greatest_permission k k') = (ks1 $+ (key_ref k, k)) $k++ ks2.
  Proof.
    induction ks2 using P.map_induction_bis; auto; intros.
    - apply map_eq_Equal in H; subst; auto.
    - clean_map_lookups.
    - apply key_perms_good_add in H3; split_ands; subst; auto.
      cases (key_ref e ==n key_ref k'); try rewrite e0 in *; clean_map_lookups; auto.
      + unfold merge_perms.
        rewrite !fold_add; auto.
        rewrite merge_perms_notation.
        rewrite merge_perms_notation with (ks1:=ks1 $+ (key_ref k, k)).
        cases (ks2 $? key_ref k).
        * rewrite H4 in *; clean_map_lookups.
        * rewrite <- merge_keys_add_l_pull; auto.
          unfold add_key_perm_fold_fn, add_key_perm.
          assert (ks1 $k++ ks2 $? key_ref k' = None) as RW by (eauto using merge_perms_adds_no_new_perms);
            rewrite <- e0 in RW; rewrite RW; simpl; clean_map_lookups. rewrite e0,H4; clean_map_lookups.
          rewrite H4 in H0; clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (key_ref k' ==n y); subst; clean_map_lookups; auto.
          rewrite greatest_permission_symm; trivial.
      + unfold merge_perms.
        rewrite !fold_add; auto.
        rewrite merge_perms_notation.
        rewrite merge_perms_notation with (ks1:=ks1 $+ (key_ref k, k)).
        rewrite H4 in H0; clean_map_lookups.
        assert (key_ref e <> key_ref k) by (rewrite H4; assumption).
        rewrite <- H4 in H0.
        erewrite <- IHks2; eauto.
        unfold add_key_perm_fold_fn, add_key_perm.
        clean_map_lookups.
        cases (ks1 $k++ ks2 $? key_ref e); subst; clean_map_lookups;
          apply map_eq_Equal; unfold Equal; intros;
            cases (y ==n key_ref e); cases (y ==n key_ref k); subst; clean_map_lookups; auto.
  Qed.

  Lemma merge_perms_sym :
    forall ks2 ks1,
      key_perms_good ks1
      -> key_perms_good ks2
      -> ks1 $k++ ks2 = ks2 $k++ ks1.
  Proof.
    induction ks2 using P.map_induction_bis; auto; intros.
    - apply map_eq_Equal in H; subst; auto.
    - rewrite merge_keys_right_identity, merge_perms_left_identity; trivial.
    - apply key_perms_good_add in H1; split_ands; subst; auto.
      unfold merge_perms at 1; rewrite fold_add; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm; simpl.

      cases (ks1 $k++ ks2 $? key_ref e); subst; clean_map_lookups.
      + apply merge_perms_came_from_somewhere1 in Heq; auto.
        assert (key_ref k = key_ref e) by auto.
        assert (ks2 $? key_ref k = None) by (rewrite H1; assumption).
        rewrite IHks2 by auto.
        erewrite <- merge_keys_add_l_pull_in; eauto.
      + apply merge_perms_no_disappear_perms in Heq; auto; split_ands.
        rewrite <- merge_keys_add_l_pull; auto.
        rewrite IHks2; auto.
  Qed.

  Lemma merge_perms_refl :
    forall ks,
      key_perms_good ks
      -> ks $k++ ks = ks.
  Proof.
    induction ks using P.map_induction_bis; auto.
    - apply map_eq_Equal in H; subst; auto.
    - unfold merge_perms; intros.
      apply key_perms_good_add in H0; split_ands; subst; auto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn , add_key_perm.
      rewrite <- merge_keys_add_l_pull; clean_map_lookups; auto.
      rewrite IHks; auto.
      apply map_eq_Equal; unfold Equal; intros.
      cases (y ==n key_ref e); subst; clean_map_lookups; auto.
      rewrite greatest_permission_refl; trivial.
  Qed.

  Hint Extern 1 (key_perms_good (_ $k++ _)) => apply key_perms_merge_still_good.

  Lemma merge_perms_chooses_greatest :
    forall ks2 ks1 k k',
      key_perms_good ks1
      -> key_perms_good ks2
      -> ks1 $? key_ref k = Some k
      -> ks2 $? key_ref k' = Some k'
      -> key_ref k = key_ref k'
      -> (ks1 $k++ ks2) $? key_ref k = Some (greatest_permission k k').
  Proof.
    induction ks2 using P.map_induction_bis; intros; auto.
    - apply map_eq_Equal in H; subst; auto.
    - invert H2.
    - apply key_perms_good_add in H1; split_ands; subst; auto.
      progress_fold_add1; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn, add_key_perm.
      cases (key_ref e ==n key_ref k'); subst; try rewrite e0 in *; clean_map_lookups.
      + rewrite H4 in H2.
        assert (ks1 $k++ ks2 $? key_ref k' = Some k) as RW by eauto using merge_perms_adds_ks1;
          rewrite RW; rewrite H4; clean_map_lookups.
        rewrite greatest_permission_symm; auto.
      + assert (key_ref e <> key_ref k) by (rewrite H4; assumption).
        cases (ks1 $k++ ks2 $? key_ref e); subst; clean_map_lookups; eauto.
  Qed.

  Lemma merge_perms_assoc_helper :
    forall ks1 ks2 k_id k_id' k k',
      ks1 $k++ ks2 $? k_id = Some k
      -> key_ref k = k_id
      -> key_ref k' = k_id'
      -> k_id <> k_id'
      -> ks1 $k++ (ks2 $+ (k_id',k')) $? k_id = Some k.
  Proof.
  Admitted.


  Lemma merge_perms_assoc :
    forall ks3 ks1 ks2,
      key_perms_good ks1
      -> key_perms_good ks2
      -> key_perms_good ks3
      -> ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Proof.
    induction ks3 using P.map_induction_bis; intros; auto.
    - apply map_eq_Equal in H; subst; auto.
    - apply key_perms_good_add in H2; split_ands; subst; auto.
      unfold merge_perms at 1.
      unfold merge_perms at 3.
      rewrite !fold_add; auto.
      rewrite merge_perms_notation.
      unfold add_key_perm_fold_fn at 1.
      unfold add_key_perm_fold_fn at 1.
      unfold add_key_perm.
      rewrite merge_perms_notation with (ks1:=ks2).

      cases (ks1 $k++ ks2 $k++ ks3 $? key_ref e);
        cases (ks2 $k++ ks3 $? key_ref e); subst; clean_map_lookups;
          rewrite IHks3 in Heq; auto.
      + cases (ks1 $? key_ref e).
        * assert (key_perms_good (ks1 $k++ (ks2 $k++ ks3))) as GD1 by eauto; specialize (GD1 _ _ Heq).
          assert (key_perms_good (ks1)) as GD2 by eauto; specialize (GD2 _ _ Heq1).
          assert (key_perms_good (ks2 $k++ ks3)) as GD3 by eauto; specialize (GD3 _ _ Heq0).
          assert ( ks1 $k++ (ks2 $k++ ks3) $? key_ref k1 = Some (greatest_permission k1 k0) ).
          eapply merge_perms_chooses_greatest; auto. rewrite GD2; auto. rewrite GD3; auto. rewrite GD2,GD3; trivial.
          rewrite GD2 in H2. clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n key_ref e); subst; clean_map_lookups.
          ** symmetry. rewrite <- GD2 in Heq1.
             rewrite <- GD2.
             erewrite merge_perms_chooses_greatest with (k' := greatest_permission e k0); eauto;
               destruct e; destruct k1; destruct k0; simpl in *; subst; simpl in *;
                 unfold greatest_permission; simpl; auto.
             rewrite !orb_assoc, orb_comm with (b1:= has_private_access1); trivial.
             unfold key_perms_good; intros.
             cases (key_ref0 ==n k_id); subst; clean_map_lookups; auto.
             assert (key_perms_good (ks2 $k++ ks3)) by auto. specialize (H4 _ _ H2); eauto.
             clean_map_lookups; trivial.
          ** rewrite IHks3; auto.
             cases (ks1 $k++ (ks2 $k++ ks3) $? y); symmetry.
             *** assert (key_perms_good (ks1 $k++ (ks2 $k++ ks3))) as GD by auto; specialize (GD _ _ Heq2).
                 apply merge_perms_assoc_helper; eauto.
                 unfold greatest_permission; destruct e; destruct k0; simpl in *; eauto.
             *** apply merge_perms_no_disappear_perms in Heq2; auto; split_ands.
                 eapply merge_perms_adds_no_new_perms; clean_map_lookups; auto.
                 unfold key_perms_good; intros.
                 cases (k_id ==n key_ref e); subst; clean_map_lookups.
                 unfold greatest_permission; destruct e; destruct k0; simpl in *; trivial.
                 assert (key_perms_good (ks2 $k++ ks3)) by auto. specialize (H6 _ _ H5); eauto.

        * apply merge_perms_came_from_somewhere2 in Heq; auto; clean_map_lookups.
          apply map_eq_Equal; unfold Equal; intros.
          cases (y ==n key_ref e); subst; clean_map_lookups.
          ** symmetry.
             eapply merge_perms_adds_ks2 with (ks2 := ks2 $k++ ks3 $+ (key_ref e, greatest_permission e k0));
               clean_map_lookups; eauto.
             unfold key_perms_good; intros.
             cases (k_id ==n key_ref e); subst; clean_map_lookups; eauto.
             assert (key_perms_good (ks2 $k++ ks3)) as GD by eauto; specialize (GD _ _ Heq).
             unfold greatest_permission; destruct e; destruct k0; simpl in *; trivial.
             assert (key_perms_good (ks2 $k++ ks3)) as GD by eauto; specialize (GD _ _ H2); auto.
          ** rewrite IHks3; auto.
             cases (ks1 $k++ (ks2 $k++ ks3) $? y); symmetry.
             *** assert (key_perms_good (ks1 $k++ (ks2 $k++ ks3))) as GD by auto; specialize (GD _ _ Heq0).
                 apply merge_perms_assoc_helper; eauto.
                 unfold greatest_permission; destruct e; destruct k0; simpl in *; eauto.
             *** apply merge_perms_no_disappear_perms in Heq0; auto; split_ands.
                 eapply merge_perms_adds_no_new_perms; clean_map_lookups; auto.
                 unfold key_perms_good; intros.
                 cases (k_id ==n key_ref e); subst; clean_map_lookups.
                 unfold greatest_permission; destruct e; destruct k0; simpl in *; trivial.
                 assert (key_perms_good (ks2 $k++ ks3)) by auto. specialize (H6 _ _ H5); eauto.

      + unfold merge_perms at 3.
        rewrite fold_add; auto.
        rewrite merge_perms_notation with (ks2:=ks2 $k++ ks3).
        unfold add_key_perm_fold_fn, add_key_perm.
        rewrite Heq.
        rewrite IHks3; auto.
      + apply merge_perms_no_disappear_perms in Heq; auto; split_ands; contra_map_lookup.

      + unfold merge_perms at 3.
        rewrite fold_add; auto.
        rewrite merge_perms_notation with (ks2:=ks2 $k++ ks3).
        unfold add_key_perm_fold_fn, add_key_perm.
        rewrite Heq.
        rewrite IHks3; auto.
  Qed.

  Lemma merge_perm_heaps_proper :
    forall {A},
      Proper (eq ==> eq ==> eq ==> eq) (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold Proper, respectful; intros; subst; trivial.
  Qed.

  Lemma merge_perm_heaps_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : key_perms) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite !merge_perms_assoc, merge_perms_sym with (ks1:= key_heap e'); trivial.

  Admitted.





  Lemma findKeys_good :
    forall {t} (msg : message t),
      key_perms_good (findKeys msg).
  Proof.
    induction msg; intros; simpl in *; subst; eauto using key_perms_merge_still_good.
  Qed.

  Definition all_user_key_perms_good {A} (usrs : honest_users A) :=
    forall u_id u_d, usrs $? u_id = Some u_d -> key_perms_good u_d.(key_heap).

  Lemma findUserKeys_result_perms_good :
    forall {A} (usrs : honest_users A),
        all_user_key_perms_good usrs
      -> key_perms_good (findUserKeys usrs).
  Proof.
    unfold all_user_key_perms_good, findUserKeys; intros.
    apply P.fold_rec_bis; auto; intros.
    apply find_mapsto_iff in H0.
    apply key_perms_merge_still_good; eauto.
  Qed.

  (* Lemma findUserKeys_as_map_fold : *)
  (*   forall {A} (usrs : honest_users A), *)
  (*     all_user_key_perms_good usrs *)
  (*     -> findUserKeys usrs = fold (fun _ => merge_perms) (map (@key_heap A) usrs) $0. *)
  (* Proof. *)
  (*   unfold findUserKeys; intros. *)
  (*   apply P.fold_rec_bis; intros; subst; eauto. *)
  (*   - apply map_eq_Equal in H0; subst; auto. *)
  (*   - admit. *)
  (* Admitted. *)

  Lemma findUserKeys_readd_user_same_keys_idempotent :
    forall {A} (usrs : honest_users A) u_id u_d proto msgs,
      usrs $? u_id = Some u_d
      -> all_user_key_perms_good usrs
      -> key_perms_good (findUserKeys usrs)
      -> findUserKeys usrs = findUserKeys (usrs $+ (u_id, {| key_heap := key_heap u_d; protocol := proto; msg_heap := msgs |})).
  Proof.
    intros.
    unfold findUserKeys; generalize H H0 H1.
    apply P.fold_rec_bis; intros; subst.
    - apply map_eq_Equal in H2; subst; auto.
    - invert H2.
    - unfold all_user_key_perms_good in H6.
      assert (key_perms_good (key_heap e)) by (eapply H6 with (u_id := k); clean_map_lookups; auto).
      cases (k ==n u_id); subst; clean_map_lookups.

  Admitted.


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
      cases (key_ref0 ==n k_id); subst; clean_map_lookups.
      cases (all_keys $? k_id); eauto.
      destruct k.
      specialize (k_good _ Heq); simpl in k_good; subst.
      unfold honest_key in *. rewrite Heq in H.
      cases keyType0; eauto.
    - apply orb_false_elim in H; split_ands.
      assert (key_perms_good (findKeys msg1 $k++ findKeys msg2)) as FIND by eauto using findKeys_good, key_perms_merge_still_good.
      assert (findKeys msg1 $k++ findKeys msg2 $? k_id = Some k) as KID by assumption.
      apply FIND in KID; rewrite <- KID in H2.
      apply merge_perms_split in H2; eauto using findKeys_good.
      split_ors; eauto.
  Qed.

  (* Definition key_heaps_compatible (ks1 ks2 : keys) := *)
  (*     keys_good ks1 *)
  (*   /\ keys_good ks2 *)
  (*   /\ (forall k_id k k', ks1 $? k_id = Some k -> ks2 $? k_id = Some k' -> keys_compatible k k' = true). *)

  (* Lemma canonical_key_one_other : *)
  (*   forall k1 k2, *)
  (*       canonical_key k1 k2 = k1 *)
  (*     \/ canonical_key k1 k2 = k2. *)
  (* Proof. *)
  (*   intros; unfold canonical_key. *)
  (*   destruct k1; destruct k2; simpl. *)
  (*   cases (keyId0 ?= keyId1); *)
  (*     cases keyUsage0; cases keyUsage1; *)
  (*       cases keyType0; cases keyType1; eauto; *)
  (*         try rewrite Nat.compare_refl; simpl; eauto; *)
  (*           cases has_private_access; cases has_private_access0; eauto. *)
  (* Qed. *)

  (* Lemma canonical_key_refl : *)
  (*   forall k, canonical_key k k = k. *)
  (* Proof. *)
  (*   unfold canonical_key; intros; simpl. *)
  (*   rewrite Nat.compare_refl. *)
  (*   cases (keyUsage k); cases (keyType k); simpl; eauto; cases has_private_access; eauto. *)
  (* Qed. *)

  (* Lemma canonical_key_sym : *)
  (*   forall k1 k2, *)
  (*     canonical_key k1 k2 = canonical_key k2 k1. *)
  (* Proof. *)
  (*   intros; destruct k1; destruct k2; unfold canonical_key; simpl. *)
  (*   cases (keyId0 ?= keyId1). *)
  (*   - apply Nat.compare_eq in Heq; subst. *)
  (*     rewrite Nat.compare_refl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyType0; cases keyType1; eauto. *)
  (*     cases has_private_access; cases has_private_access0; eauto. *)
  (*     cases has_private_access; cases has_private_access0; eauto. *)

  (*   - rewrite Nat.compare_antisym; rewrite Heq; simpl; auto. *)
  (*   - rewrite Nat.compare_antisym; rewrite Heq; simpl; auto. *)
  (* Qed. *)

  (* Lemma canonical_key_assoc : *)
  (*   forall k1 k2 k3, *)
  (*     canonical_key k1 (canonical_key k2 k3) = canonical_key (canonical_key k1 k2) k3. *)
  (* Proof. *)
  (*   intros; destruct k1; destruct k2; destruct k3; unfold canonical_key; simpl. *)

  (*   cases (keyId0 ?= keyId1); cases (keyId1 ?= keyId2). *)
  (*   - apply Nat.compare_eq in Heq; apply Nat.compare_eq in Heq0; subst. simpl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyUsage2; *)
  (*       cases keyType0; cases keyType1; cases keyType2; *)
  (*         simpl; eauto; *)
  (*           try rewrite Nat.compare_refl; eauto; *)
  (*             cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl; *)
  (*               try rewrite Nat.compare_refl; eauto. *)

  (*   - apply Nat.compare_eq in Heq; subst; simpl. *)
  (*     rewrite Heq0; simpl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyUsage2; *)
  (*       cases keyType0; cases keyType1; cases keyType2; *)
  (*         simpl; eauto; try rewrite Heq0; simpl; eauto; *)
  (*           cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl; *)
  (*             rewrite Heq0; simpl; eauto. *)

  (*   - apply Nat.compare_eq in Heq; subst; simpl. *)
  (*     rewrite Nat.compare_refl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyUsage2; *)
  (*       cases keyType0; cases keyType1; cases keyType2; *)
  (*         simpl; eauto; try rewrite Heq0; simpl; eauto; *)
  (*           cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl; *)
  (*             rewrite Heq0; simpl; eauto. *)

  (*   - apply Nat.compare_eq in Heq0; subst; simpl. *)
  (*     rewrite Nat.compare_refl; simpl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyUsage2; *)
  (*       cases keyType0; cases keyType1; cases keyType2; *)
  (*         simpl; eauto; try rewrite Heq; simpl; eauto; *)
  (*           cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl; *)
  (*             rewrite Heq; simpl; eauto. *)

  (*   - simpl. rewrite Heq0. *)
  (*     pose proof Heq as lt1; pose proof Heq0 as lt2. *)
  (*     apply nat_compare_lt in lt1; apply nat_compare_lt in lt2. *)
  (*     pose proof (Nat.lt_trans _ _ _ lt1 lt2). apply nat_compare_lt in H. *)
  (*     rewrite H; eauto. *)

  (*   - simpl; rewrite Heq; rewrite Heq0; eauto. *)

  (*   - apply Nat.compare_eq in Heq0; subst; simpl. *)
  (*     rewrite Heq; simpl. *)
  (*     cases keyUsage0; cases keyUsage1; cases keyUsage2; *)
  (*       cases keyType0; cases keyType1; cases keyType2; *)
  (*         simpl; eauto; try rewrite Heq; simpl; eauto; *)
  (*           cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl; *)
  (*             rewrite Heq; simpl; eauto. *)

  (*   - simpl. cases (keyId0 ?= keyId2); simpl; eauto. *)
  (*   - simpl. rewrite Heq. *)
  (*     pose proof Heq as gt1; pose proof Heq0 as gt2. *)
  (*     apply nat_compare_gt in gt1; apply nat_compare_gt in gt2. *)

  (*     pose proof (gt_trans _ _ _ gt1 gt2); apply nat_compare_gt in H. *)
  (*     rewrite H; simpl; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_fold_fn_proper : *)
  (*     Morphisms.Proper *)
  (*       (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq))) *)
  (*       add_key. *)
  (* Proof. *)
  (*   unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst; trivial. *)
  (* Qed. *)

  (* Lemma merge_keys_fold_fn_proper_flip : *)
  (*     Morphisms.Proper *)
  (*       (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful (Basics.flip eq) (Basics.flip eq)))) *)
  (*       add_key. *)
  (* Proof. *)
  (*   unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; unfold Basics.flip in *; subst; trivial. *)
  (* Qed. *)

  (* Lemma merge_keys_fold_fn_proper_Equal : *)
  (*   Morphisms.Proper *)
  (*     (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful Equal Equal))) *)
  (*     add_key. *)
  (* Proof. *)
  (*   unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst. *)
  (*   apply map_eq_Equal in H1; subst. *)
  (*   apply Equal_refl. *)
  (* Qed. *)

  (* Lemma merge_keys_transpose : *)
  (*   transpose_neqkey eq add_key. *)
  (* Proof. *)
  (*   unfold transpose_neqkey; intros. *)
  (*   unfold add_key; simpl. *)
  (*   case_eq (a $? k); case_eq (a $? k'); intros; subst; simpl. *)

  (*   Ltac work1 := *)
  (*     match goal with *)
  (*     | [ H : ?x <> ?x |- _ ] => contradiction *)
  (*     | [ H1 : ?x <> ?y, H2 : ?x = ?y |- _ ] => contradiction *)
  (*     | [ H : ?a $? ?k  = _ |- context [?a $? ?k]  ] => rewrite H *)
  (*     | [ H : ?a $? ?k' = _ |- context [?a $? ?k'] ] => rewrite H *)
  (*     | [ |- context[ ?k1 ==kk ?k2 ] ] => case (k1 ==kk k2); intros; subst *)
  (*     | [ H : keys_compatible ?k1 ?k2 = _ |- context [ keys_compatible ?k1 ?k2 ]] => rewrite H *)
  (*     | [ |- context [ keys_compatible ?k1 ?k2 ]] => case_eq (keys_compatible k1 k2); intros *)
  (*     | [ H : keyType ?k = _ |- context [ keyType ?k ==kt ?kt ]] => rewrite H *)
  (*     | [ |- context [ keyType ?k ==kt ?kt ]] => case (keyType k ==kt kt); intros *)
  (*     | [ |- context [ _ $+ (?k1, _) $? ?k1 ]] => rewrite add_eq_o by (trivial || auto) *)
  (*     | [ |- context [ _ $+ (?k1, _) $? ?k2 ]] => rewrite add_neq_o by auto *)
  (*     | [ |- context [ _ $- ?k1 $? ?k2 ]] => rewrite remove_neq_o by auto *)
  (*     end. *)

  (*   Ltac maps_equal := *)
  (*     repeat match goal with *)
  (*            | [ |- context[find ?k (add ?k _ _) ] ]  => rewrite add_eq_o by auto *)
  (*            | [ |- context[find ?k (add ?k' _ _) ] ] => rewrite add_neq_o by auto *)
  (*            | [ |- context[find ?k (remove ?k _) ] ]  => rewrite remove_eq_o by auto *)
  (*            | [ |- context[find ?k (remove ?k' _) ] ] => rewrite remove_neq_o by auto *)
  (*            | [ |- _ $+ (?k1,_) $? ?k = _ ] => case (k1 ==n k); intros; subst *)
  (*            | [ |- _ $- ?k1     $? ?k = _ ] => case (k1 ==n k); intros; subst *)
  (*            | [ |- add _ _ _ = _ ] => apply map_eq_Equal; unfold Equal; intros ?y *)
  (*            end. *)

  (*   repeat work1; eauto; *)
  (*     apply map_eq_Equal; unfold Equal; intros; *)
  (*       maps_equal; auto. *)
    
  (*   repeat work1; eauto; *)
  (*     apply map_eq_Equal; unfold Equal; intros; *)
  (*       maps_equal; auto. *)

  (*   repeat work1; eauto; *)
  (*     apply map_eq_Equal; unfold Equal; intros; *)
  (*       maps_equal; auto. *)

  (*   repeat work1; eauto; *)
  (*     apply map_eq_Equal; unfold Equal; intros; *)
  (*       maps_equal; auto. *)

  (* Qed. *)

  (* Lemma merge_keys_transpose_flip : *)
  (*   transpose_neqkey (Basics.flip eq) add_key. *)
  (* Proof. *)
  (*   unfold transpose_neqkey, Basics.flip; intros. *)
  (*   apply merge_keys_transpose; auto. *)
  (* Qed. *)

  (* Lemma eq_Equal : *)
  (*   forall {V} (m m' : NatMap.t V), *)
  (*     m = m' *)
  (*     -> Equal m m'. *)
  (*   intros; subst; apply Equal_refl. *)
  (* Qed. *)

  (* Lemma merge_keys_transpose_Equal : *)
  (*   transpose_neqkey Equal add_key. *)
  (* Proof. *)
  (*   unfold transpose_neqkey; intros. *)
  (*   apply eq_Equal. *)
  (*   apply merge_keys_transpose; auto. *)
  (* Qed. *)

  (* Hint Resolve merge_keys_fold_fn_proper merge_keys_fold_fn_proper_flip merge_keys_fold_fn_proper_Equal *)
  (*              merge_keys_transpose merge_keys_transpose_flip merge_keys_transpose_Equal. *)

  (* Lemma merge_keys_left_identity : *)
  (*   forall ks, *)
  (*     $0 $k++ ks = ks. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; auto. *)
  (*   - apply fold_Empty; eauto. *)
  (*   - rewrite fold_add; clean_map_lookups; eauto. *)
  (*     rewrite IHks; clear IHks. *)
  (*     unfold add_key; rewrite H; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_right_identity : *)
  (*   forall ks, *)
  (*     ks $k++ $0 = ks. *)
  (* Proof. *)
  (*   unfold merge_keys; intros; rewrite fold_Empty; eauto. *)
  (* Qed. *)

  (* Hint Resolve merge_keys_left_identity merge_keys_right_identity. *)

  (* Lemma merge_keys_adds_no_new_keys : *)
  (*   forall ks2 k ks1, *)
  (*       ks1 $? k = None *)
  (*     -> ks2 $? k = None *)
  (*     -> (ks1 $k++ ks2) $? k = None. *)
  (* Proof. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)
  (*   - apply map_eq_Equal in H; subst; auto. *)
  (*   - rewrite merge_keys_right_identity; auto. *)
  (*   - unfold merge_keys; rewrite fold_add; auto. *)
  (*     case (x ==n k); intros; subst; clean_map_lookups. *)
  (*     + rewrite merge_keys_notation; unfold add_key. *)
  (*       cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases (e ==kk k0); subst; eauto. *)
  (*       clean_map_lookups. eapply IHks2; auto. *)
  (* Qed. *)

  (* Lemma merge_keys_no_disappear_keys : *)
  (*   forall ks2 k ks1, *)
  (*     (ks1 $k++ ks2) $? k = None *)
  (*   -> ks1 $? k = None *)
  (*   /\ ks2 $? k = None. *)
  (* Proof. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)
  (*   - apply map_eq_Equal in H; subst; auto. *)
  (*   - rewrite merge_keys_right_identity in H; eauto. *)
  (*   - unfold merge_keys in H0. progress_fold_add1; auto. *)
  (*     rewrite merge_keys_notation in *; clean_map_lookups. *)
  (*     unfold add_key in H0. *)
  (*     cases (ks1 $k++ ks2 $? x); clean_map_lookups; *)
  (*       [cases (e ==kk k0); subst | ]; *)
  (*         case (x ==n k); intros; subst; clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Hint Resolve merge_keys_adds_no_new_keys merge_keys_no_disappear_keys. *)

  (* Lemma merge_keys_adds_ks1 : *)
  (*   forall ks2 ks1 k v ks, *)
  (*       ks1 $? k = Some v *)
  (*     -> ks2 $? k = None *)
  (*     -> ks = ks1 $k++ ks2 *)
  (*     -> ks $? k = Some v. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - subst; rewrite fold_Empty; eauto. *)
  (*   - case (x ==n k); intros; subst; clean_map_lookups; eauto. *)
  (*     rewrite fold_add; eauto. *)
  (*     rewrite merge_keys_notation. *)
  (*     unfold add_key. *)
  (*     cases ( ks1 $k++ ks2 $? x ); clean_map_lookups; eauto. *)
  (*     cases ( e ==kk k0 ); eauto. *)
  (*     clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_adds_ks2 : *)
  (*   forall ks2 ks1 k v ks, *)
  (*       ks1 $? k = None *)
  (*     -> ks2 $? k = Some v *)
  (*     -> ks = ks1 $k++ ks2 *)
  (*     -> ks $? k = Some v. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - invert H0. *)
  (*   - subst. *)
  (*     case (x ==n k); intros; subst; clean_map_lookups; eauto. *)
  (*     + rewrite fold_add; auto. *)
  (*       rewrite merge_keys_notation. *)
  (*       unfold add_key. *)
  (*       pose proof merge_keys_adds_no_new_keys. *)
  (*       cases ( ks1 $k++ ks2 $? k); clean_map_lookups; eauto. *)
  (*       cases ( v ==kk k0 ); subst; clean_map_lookups; eauto. *)
  (*       specialize (H1 _ _ _ H0 H); contra_map_lookup. *)

  (*     + rewrite fold_add; auto. *)
  (*       rewrite merge_keys_notation. *)
  (*       unfold add_key. *)
  (*       cases ( ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases ( e ==kk k0 ); eauto. *)
  (*       clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Hint Resolve merge_keys_adds_ks1 merge_keys_adds_ks2. *)

  (* Lemma merge_keys_came_from_somewhere1 : *)
  (*   forall ks2 ks1 k v, *)
  (*       ks1 $k++ ks2 $? k = Some v *)
  (*     -> ks2 $? k = None *)
  (*     -> ks1 $? k = Some v. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - rewrite fold_Empty in H; auto. *)

  (*   - case (x ==n k); intros; subst; clean_map_lookups. *)
  (*     + progress_fold_add1; auto. *)
  (*       rewrite merge_keys_notation in H0; unfold add_key at 1 in H0. *)

  (*       cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases ( e ==kk k0 ); subst; clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_came_from_somewhere2 : *)
  (*   forall ks2 ks1 k v, *)
  (*       ks1 $k++ ks2 $? k = Some v *)
  (*     -> ks1 $? k = None *)
  (*     -> ks2 $? k = Some v. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - rewrite fold_Empty in H; clean_map_lookups; auto. *)

  (*   - case (x ==n k); intros; subst; clean_map_lookups; progress_fold_add1; auto. *)
  (*     * pose proof (merge_keys_adds_no_new_keys _ _ _ H1 H). *)
  (*       rewrite merge_keys_notation in H0; unfold add_key in H0; auto. *)
  (*       cases (ks1 $k++ ks2 $? k); clean_map_lookups; eauto. *)

  (*     * rewrite merge_keys_notation in H0; unfold add_key in H0; auto. *)
  (*       cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases ( e ==kk k0 ); subst; clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Hint Resolve merge_keys_came_from_somewhere1 merge_keys_came_from_somewhere2. *)

  (* Lemma merge_keys_split : *)
  (*   forall ks2 k_id k ks1, *)
  (*     ks1 $k++ ks2 $? k_id = Some k *)
  (*     -> (ks1 $? k_id = None /\ ks2 $? k_id = Some k) *)
  (*     \/ (ks1 $? k_id = Some k /\ ks2 $? k_id = None) *)
  (*     \/ exists k1 k2, ks1 $? k_id = Some k1 /\ ks2 $? k_id = Some k2 /\ k = canonical_key k1 k2. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)
  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - rewrite merge_keys_right_identity in H. intuition idtac. *)
  (*   - rewrite fold_add in H0; auto. *)
  (*     rewrite merge_keys_notation in H0; unfold add_key in H0; auto. *)
  (*     case (x ==n k_id); intros; subst; clean_map_lookups. *)
  (*     + cases (ks1 $k++ ks2 $? k_id); intros; simpl. *)
  (*       * cases (e ==kk k0); subst. *)
  (*         ** rewrite Heq in H0; invert H0. eapply merge_keys_came_from_somewhere1 in Heq; auto. *)
  (*            right; right. do 2 eexists; intuition eauto. rewrite canonical_key_refl; trivial. *)
  (*         ** clean_map_lookups; eapply merge_keys_came_from_somewhere1 in Heq; auto. *)
  (*            right; right; do 2 eexists; intuition eauto. rewrite canonical_key_sym; trivial. *)

  (*       * clean_map_lookups; eauto. eapply merge_keys_no_disappear_keys in Heq; invert Heq. *)
  (*         intuition idtac. *)
  (*     + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases (e ==kk k0); auto. *)
  (*       cases (x ==n k_id); clean_map_lookups; auto. *)
  (* Qed. *)

  (* Lemma merge_keys_canonicalizes : *)
  (*   forall ks2 k_id k k1 k2 ks1, *)
  (*       ks1 $k++ ks2 $? k_id = Some k *)
  (*     -> ks1 $? k_id = Some k1 *)
  (*     -> ks2 $? k_id = Some k2 *)
  (*     -> k = canonical_key k1 k2. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)
  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - invert H1. *)

  (*   - rewrite fold_add in H0; auto. *)
  (*     rewrite merge_keys_notation in H0; unfold add_key in H0; auto. *)
  (*     case (x ==n k_id); intros; subst; clean_map_lookups. *)
  (*     + cases (ks1 $k++ ks2 $? k_id); intros; simpl. *)
  (*       * cases (k2 ==kk k0); subst; eauto. *)
  (*         ** rewrite Heq in H0; invert H0. eapply merge_keys_came_from_somewhere1 in Heq; auto. rewrite Heq in H1; invert H1. rewrite canonical_key_refl; trivial. *)
  (*         ** clean_map_lookups. eapply merge_keys_came_from_somewhere1 in Heq; auto. rewrite Heq in H1; invert H1. rewrite canonical_key_sym; trivial. *)

  (*       * clean_map_lookups. eapply merge_keys_no_disappear_keys in Heq; destruct Heq; contra_map_lookup. *)

  (*     + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto. *)
  (*       cases (e ==kk k0); subst; clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_canonicalizes' : *)
  (*   forall ks2 k_id k k1 k2 ks1, *)
  (*       ks1 $? k_id = Some k1 *)
  (*     -> ks2 $? k_id = Some k2 *)
  (*     -> k = canonical_key k1 k2 *)
  (*     -> ks1 $k++ ks2 $? k_id = Some k. *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)
  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - invert H0. *)

  (*   - rewrite fold_add; auto. *)
  (*     rewrite merge_keys_notation; unfold add_key. *)
  (*     cases (ks1 $k++ ks2 $? x); case (x ==n k_id); intros; subst; clean_map_lookups. *)
  (*     + cases (k2 ==kk k0); subst. *)
  (*       * eapply (merge_keys_came_from_somewhere1) in Heq; auto. rewrite Heq in H0; invert H0. rewrite canonical_key_refl. eapply merge_keys_adds_ks1; eauto. *)
  (*       * eapply (merge_keys_came_from_somewhere1) in Heq; auto. rewrite Heq in H0; invert H0. rewrite canonical_key_sym. clean_map_lookups; trivial. *)
  (*     + cases (e ==kk k0); subst; clean_map_lookups; eauto. *)
  (*     + eapply merge_keys_no_disappear_keys in Heq; invert Heq; contra_map_lookup. *)
  (*     + eapply IHks2; eauto. *)
  (* Qed. *)

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

  (* Lemma keys_compatible_reflexive : *)
  (*   forall k, *)
  (*     keys_compatible k k = true. *)
  (* Proof. *)
  (*   unfold keys_compatible; intros. *)
  (*   cases (keyId k ==n keyId k); eauto. *)
  (*   cases (keyUsage k ==ku keyUsage k); eauto. *)
  (*   unfold key_type_same; cases (keyType k); eauto. *)
  (* Qed. *)

  (* Lemma keys_compatible_symmetric : *)
  (*   forall k1 k2, *)
  (*     keys_compatible k1 k2 = keys_compatible k2 k1. *)
  (* Proof. *)
  (*   unfold keys_compatible; intros. *)
  (*   cases (keyId k1 ==n keyId k2). *)
  (*   cases (keyUsage k1 ==ku keyUsage k2). *)
  (*   cases (key_type_same (keyType k1) (keyType k2)). *)
  (*   - rewrite e; rewrite e0; cases (keyId k2 ==n keyId k2); cases (keyUsage k2 ==ku keyUsage k2); try contradiction. *)
  (*     unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto. *)
  (*   - rewrite e; rewrite e0; cases (keyId k2 ==n keyId k2); cases (keyUsage k2 ==ku keyUsage k2); try contradiction. *)
  (*     unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto. *)
  (*   - rewrite e; cases (keyId k2 ==n keyId k2); auto. *)
  (*     cases (keyUsage k2 ==ku keyUsage k1); auto. *)
  (*     unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto. *)
  (*   - cases (keyId k2 ==n keyId k1); cases (keyUsage k2 ==ku keyUsage k1); try contradiction; auto. *)
  (*     symmetry in e; contradiction. *)
  (* Qed. *)

  (* Lemma merge_keys_ok : *)
  (*   forall ks2 k_id k1 k2 ks ks1, *)
  (*       ks1 $? k_id = Some k1 *)
  (*     -> ks2 $? k_id = Some k2 *)
  (*     -> ks = ks1 $k++ ks2 *)
  (*     -> ( ks $? k_id = Some k1 /\ k1 = k2) *)
  (*     \/ ( ks $? k_id = Some (canonical_key k1 k2)). *)
  (* Proof. *)
  (*   unfold merge_keys. *)
  (*   induction ks2 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - invert H0. *)

  (*   - subst. progress_fold_add1; clean_map_lookups; eauto. *)
  (*     rewrite merge_keys_notation. *)
  (*     case (x ==n k_id); intros; subst; clean_map_lookups. *)
  (*     + remember (ks1 $k++ ks2) as ks. *)
  (*       specialize (merge_keys_adds_ks1 _ _ _ H0 H Heqks). intros; subst. *)
  (*       cases (k2 ==kk k1). *)
  (*       * unfold add_key; subst. rewrite H1. *)
  (*         rewrite canonical_key_refl; simpl. *)
  (*         cases (k1 ==kk k1); try contradiction; eauto. *)

  (*       * unfold add_key; rewrite H1; simpl. cases (k2 ==kk k1); try contradiction. *)
  (*         rewrite canonical_key_sym. *)
  (*         assert (k1 <> k2) by auto. *)

  (*         clean_map_lookups; intuition idtac. *)

  (*     + unfold add_key. *)
  (*       cases (ks1 $k++ ks2 $? x); eauto. *)
  (*       * cases (e ==kk k); clean_map_lookups; eauto. *)
  (*       * clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_refl : *)
  (*   forall ks, *)
  (*     ks $k++ ks = ks. *)
  (* Proof. *)
  (*   intros; apply map_eq_Equal; unfold Equal; subst; intros. *)
  (*   cases (ks $? y). *)
  (*   - remember (ks $k++ ks) as ksks. *)
  (*     pose proof (merge_keys_ok _ _ _ Heq Heq Heqksks). *)
  (*     rewrite canonical_key_refl in *. *)
  (*     intuition idtac. *)
  (*   - rewrite merge_keys_adds_no_new_keys; eauto. *)
  (* Qed. *)

  (* Lemma merge_keys_symmetric : *)
  (*   forall ks1 ks2, *)
  (*     ks1 $k++ ks2 = ks2 $k++ ks1. *)
  (* Proof. *)
  (*   intros. *)

  (*   apply map_eq_Equal; unfold Equal; subst; intros. *)

  (*   cases (ks1 $? y); cases (ks2 $? y). *)
  (*   - remember (ks1 $k++ ks2) as ks12. remember (ks2 $k++ ks1) as ks21. *)
  (*     pose proof (merge_keys_ok _ _ _ Heq Heq0 Heqks12). *)
  (*     pose proof (merge_keys_ok _ _ _ Heq0 Heq Heqks21). *)

  (*     (repeat match goal with *)
  (*             | [ H : _ /\ _ |- _ ] => destruct H; subst *)
  (*             | [ H : _ \/ _ |- _ ] => destruct H *)
  (*             | [ |- context [canonical_key ?k ?k]] => rewrite canonical_key_refl *)
  (*             | [ H : _ $k++ _ $? _ = Some _ |- _ ] => rewrite H *)
  (*             | [ H : _ $? _ = Some _ |- _ ] => rewrite H *)
  (*             end); *)
  (*       eauto. *)
  (*     rewrite canonical_key_sym; trivial. *)

  (*   - erewrite (merge_keys_adds_ks1); eauto. *)
  (*     erewrite (merge_keys_adds_ks2); eauto. *)
  (*   - erewrite (merge_keys_adds_ks2); eauto. *)
  (*     erewrite (merge_keys_adds_ks1); eauto. *)
  (*   - rewrite merge_keys_adds_no_new_keys; eauto. *)
  (*     rewrite merge_keys_adds_no_new_keys; eauto. *)
  (* Qed. *)

  (* Hint Extern 1 (keys_compatible _ _ = _) => eassumption || (rewrite keys_compatible_symmetric; eassumption). *)

  (* Lemma merge_keys_inequal_addition_no_impact : *)
  (*   forall ks1 ks2 k_id k_id' k, *)
  (*     k_id <> k_id' *)
  (*     -> ks1 $k++ (ks2 $+ (k_id,k)) $? k_id' = ks1 $k++ ks2 $? k_id'. *)
  (* Proof. *)
  (*   intros. *)
  (*   cases (ks1 $k++ ks2 $? k_id'). *)
  (*   - apply merge_keys_split in Heq. *)
  (*     split_ors; split_ands; subst. *)
  (*     + eapply merge_keys_adds_ks2 with (ks2:=ks2 $+ (k_id, k)); clean_map_lookups; eauto. *)
  (*     + eapply merge_keys_adds_ks1 with (ks2:=ks2 $+ (k_id, k)); clean_map_lookups; eauto. *)
  (*     + destruct H0 as [k1 H0]. destruct H0 as [k2 H0]. split_ands. *)
  (*       remember (ks1 $k++ ks2) as ks. *)
  (*       specialize (merge_keys_ok _ _ _ H0 H1 Heqks); intros; split_ors; split_ands; subst. *)
  (*       * rewrite canonical_key_refl. *)
  (*         eapply merge_keys_canonicalizes' with (ks2:=ks2 $+ (k_id, k)). eauto. clean_map_lookups; eauto. rewrite canonical_key_refl; trivial. *)
  (*       * eapply merge_keys_canonicalizes' with (ks2:=ks2 $+ (k_id, k)). eauto. clean_map_lookups; eauto. trivial. *)
  (*   - apply merge_keys_no_disappear_keys in Heq; split_ands. *)
  (*     eapply merge_keys_adds_no_new_keys; auto. *)
  (*     clean_map_lookups; auto. *)
  (* Qed. *)

  (* Lemma merge_keys_assoc : *)
  (*   forall ks3 ks1 ks2 : keys, *)
  (*     ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3). *)
  (* Proof. *)
  (*   induction ks3 using P.map_induction_bis; intros. *)

  (*   - apply map_eq_Equal in H; subst; eauto. *)
  (*   - rewrite !merge_keys_right_identity; trivial. *)
  (*   - apply map_eq_Equal; unfold Equal; subst; intros. *)
  (*     unfold merge_keys. *)
  (*     progress_fold_add1; auto. progress_fold_add1; auto. *)
  (*     rewrite merge_keys_notation with (ks1 := ks1). *)
  (*     rewrite merge_keys_notation with (ks2 := ks3). *)
  (*     unfold add_key at 1; unfold add_key at 2. *)

  (*     (* clean up notation of induction hypothesis *)  *)
  (*     specialize (IHks3 ks1 ks2); unfold merge_keys in IHks3. *)
  (*     rewrite merge_keys_notation  with (ks1 := ks1) in IHks3. *)
  (*     rewrite merge_keys_notation  with (ks1 := ks2) in IHks3. *)
  (*     rewrite merge_keys_notation  with (ks2 := ks3) in IHks3. *)
  (*     rewrite merge_keys_notation  with (ks2 := ks2 $k++ ks3) in IHks3. *)

  (*     rewrite merge_keys_notation with (ks1 := ks2). *)

  (*     Ltac rewrite123 := *)
  (*       match goal with | [ H : _ $k++ _ $k++ _ $? _ = _ |- _ ] => rewrite H end. *)

  (*     cases (ks1 $k++ ks2 $k++ ks3 $? x); *)
  (*       intros; subst; clean_map_lookups. *)

  (*     + cases (ks2 $k++ ks3 $? x). *)
  (*       * assert (ks1 $k++ ks2 $k++ ks3 $? x = Some k) as S by auto. *)
  (*         rewrite IHks3 in S; eapply merge_keys_split in S; auto. *)
  (*         cases (e ==kk k); cases (e ==kk k0); subst. *)
  (*         ** rewrite merge_keys_notation with (ks2:=ks2$k++ks3); rewrite IHks3; trivial. *)
  (*         ** rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3 $+ (x, canonical_key k k0)). *)
  (*            split_ors; split_ands; subst. *)
  (*            *** rewrite Heq0 in H1; invert H1. contradiction. *)
  (*            *** contra_map_lookup. *)
  (*            *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1. symmetry. *)
  (*                rewrite <- canonical_key_assoc. rewrite canonical_key_refl. *)
  (*                cases (x ==n y); subst. *)
  (*                  rewrite Heq. eapply merge_keys_canonicalizes'. eassumption. clean_map_lookups. reflexivity. rewrite canonical_key_assoc, canonical_key_refl; trivial. *)
  (*                  rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption. *)
  (*         ** rewrite merge_keys_notation with (ks2:=ks2$k++ks3). rewrite <- IHks3. *)
  (*            split_ors; split_ands; subst. *)
  (*            *** rewrite Heq0 in H1; invert H1. contradiction. *)
  (*            *** contra_map_lookup. *)
  (*            *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1. *)
  (*                cases (x ==n y); subst. *)
  (*                  rewrite canonical_key_sym, <- canonical_key_assoc, canonical_key_refl. clean_map_lookups; rewrite Heq; trivial. *)
  (*                  clean_map_lookups; trivial. *)
  (*         ** rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3 $+ (x, canonical_key e k0)). *)
  (*            split_ors; split_ands; subst. *)
  (*            *** rewrite Heq0 in H1; invert H1. symmetry. *)
  (*                cases (x ==n y); subst; clean_map_lookups. *)
  (*                  eapply merge_keys_adds_ks2. eauto. 2:reflexivity. clean_map_lookups; trivial. *)
  (*                  rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption. *)
  (*            *** contra_map_lookup. *)
  (*            *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1. *)
  (*                symmetry. *)
  (*                cases (x ==n y); subst; clean_map_lookups. *)
  (*                **** eapply merge_keys_canonicalizes'; clean_map_lookups; eauto. *)
  (*                     rewrite canonical_key_assoc, canonical_key_sym with (k1:=e), <- canonical_key_assoc; trivial. *)
  (*                **** rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption. *)

  (*       * cases (e ==kk k); subst. *)
  (*         ** rewrite fold_add; auto. unfold add_key at 1. rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3), <- IHks3. rewrite Heq. *)
  (*            cases (k ==kk k); simpl; eauto. contradiction. *)
  (*         ** rewrite fold_add; auto. unfold add_key at 1. rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3), <- IHks3. rewrite Heq. *)
  (*            cases (e ==kk k); simpl; eauto. contradiction. *)


  (*     + assert (ks1 $k++ ks2 $k++ ks3 $? x = None) as HH by assumption; rewrite IHks3 in HH; eapply merge_keys_no_disappear_keys in HH; split_ands. *)
  (*       rewrite H1. *)
  (*       progress_fold_add1; auto. *)
  (*       unfold add_key at 1. *)
  (*       rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3). rewrite <- IHks3. rewrite Heq; clean_map_lookups; trivial. *)
  (* Qed. *)

  (* Lemma findUserKeys_fold_fn_proper : *)
  (*   forall {A}, *)
  (*   Morphisms.Proper *)
  (*     (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq))) *)
  (*     (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u). *)
  (*   unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst; trivial. *)
  (* Qed. *)

  (* Lemma findUserKeys_fold_fn_proper_Equal : *)
  (*   forall {A}, *)
  (*   Morphisms.Proper *)
  (*     (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful Equal Equal))) *)
  (*     (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u). *)
  (*   unfold Morphisms.Proper, Morphisms.respectful; intros. *)
  (*   apply map_eq_Equal in H1; subst. *)
  (*   unfold Equal; intros; trivial. *)
  (* Qed. *)

  (* Lemma findUserKeys_transpose : *)
  (*   forall {A}, *)
  (*     transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u). *)
  (* Proof. *)
  (*   unfold transpose_neqkey; intros. *)
  (*   rewrite merge_keys_symmetric with (ks1 := a). *)
  (*   rewrite merge_keys_symmetric with (ks1 := a $k++ key_heap e). *)
  (*   rewrite merge_keys_assoc; trivial. *)
  (* Qed. *)

  (* Lemma findUserKeys_transpose_Equal : *)
  (*   forall {A}, *)
  (*     transpose_neqkey Equal (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u). *)
  (* Proof. *)
  (*   unfold transpose_neqkey; intros. *)
  (*   unfold Equal; intros. *)
  (*   rewrite merge_keys_symmetric with (ks1 := a). *)
  (*   rewrite merge_keys_symmetric with (ks1 := a $k++ key_heap e). *)
  (*   rewrite merge_keys_assoc; trivial. *)
  (* Qed. *)

  (* Hint Resolve findUserKeys_fold_fn_proper findUserKeys_fold_fn_proper_Equal findUserKeys_transpose findUserKeys_transpose_Equal. *)

  (* TODO move to Maps.v *)
  Lemma add_remove_eq :
    forall {V} (m : NatMap.t V) k1 v1,
      m $+ (k1, v1) $- k1 = m $- k1.
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    case (k1 ==n y); intros; subst.
    - rewrite !remove_eq_o; auto.
    - rewrite !remove_neq_o, add_neq_o; auto.
  Qed.

  Lemma add_remove_neq :
    forall {V} (m : NatMap.t V) k1 v1 k2,
        k1 <> k2
      -> m $+ (k1, v1) $- k2 = m $- k2 $+ (k1, v1).
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    case (k2 ==n y); case (k1 ==n y); intros; subst.
    - contradiction.
    - rewrite add_neq_o by assumption; rewrite !remove_eq_o; trivial.
    - rewrite remove_neq_o by assumption; rewrite !add_eq_o; trivial.
    - rewrite remove_neq_o by assumption; rewrite !add_neq_o by assumption; rewrite remove_neq_o; auto.
  Qed.

  Lemma remove_not_in_idempotent :
    forall {V} (m : NatMap.t V) k1,
      m $? k1 = None
      -> m $- k1 = m.
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros.
    cases (y ==n k1); subst; eauto.
    rewrite remove_eq_o by trivial; rewrite H; trivial.
    rewrite remove_neq_o; auto.
  Qed.

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
  | (SymKey,  MkKeyPerm _ _)      => Some c
  | (AsymKey, MkKeyPerm _ true)   => Some c
  | (AsymKey, MkKeyPerm _ false)  => None
  end.

Definition encryptMessage {t} (ks : keys) (k__sign k__enc : key_permission) (m : message t) (c_id : cipher_id) : option cipher :=
  match (ks $? k__sign.(key_ref), ks $? k__enc.(key_ref)) with
  | (Some (MkCryptoKey _ Signing kt__sign), Some (MkCryptoKey _ Encryption kt__enc)) =>
    sign_if_ok (SigEncCipher c_id k__sign.(key_ref) k__enc.(key_ref) m) kt__sign k__sign
  | _ => None
  end.

Definition signMessage {t} (ks : keys) (k : key_permission) (m : message t) (c_id : cipher_id) : option cipher :=
  match (ks $? k.(key_ref)) with
  | Some (MkCryptoKey _ Signing kt)     =>
    sign_if_ok (SigCipher c_id k.(key_ref) m) kt k
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
| StepEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' gks ks qmsgs (msg : message t) k__sign k__enc k__signid k__encid c_id cipherMsg,
      key_ref k__sign = k__signid
    -> key_ref k__enc = k__encid
    -> ks $? k__signid = Some k__sign
    -> has_private_key gks k__sign = true
    -> ks $? k__encid = Some k__enc
    -> ~ In c_id cs
    -> encryptMessage gks k__sign k__enc msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , gks, ks, qmsgs, SignEncrypt k__sign k__enc msg)
                (usrs, adv, cs', gks, ks, qmsgs, Return (SignedCiphertext c_id))

| StepDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks ks' qmsgs (msg : message t) k__signid k__sign k__encid c_id newkeys kt b,
      cs $? c_id = Some (SigEncCipher c_id k__signid k__encid msg)
    -> ( (gks $? k__encid = Some (MkCryptoKey k__encid Encryption SymKey)  /\ ks $? k__encid = Some (MkKeyPerm k__encid b))
      \/ (gks $? k__encid = Some (MkCryptoKey k__encid Encryption AsymKey) /\ ks $? k__encid = Some (MkKeyPerm k__encid true))
      )
    -> gks $? k__signid = Some (MkCryptoKey k__signid Signing kt)
    -> ks $? k__signid = Some k__sign
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> step_user Silent
                (usrs, adv, cs, gks, ks , qmsgs, Decrypt (SignedCiphertext c_id))
                (usrs, adv, cs, gks, ks', qmsgs, Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' gks ks qmsgs (msg : message t) k k_id c_id cipherMsg,
      key_ref k = k_id
    -> ks $? k_id = Some k
    -> has_private_key gks k = true
    -> ~(In c_id cs)
    -> signMessage gks k msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , gks, ks, qmsgs, Sign k msg)
                (usrs, adv, cs', gks, ks, qmsgs, Return (Signature msg c_id))

| StepVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs gks ks qmsgs (msg : message t) k_id k c_id,
    key_ref k = k_id
    (* k is in your key heap *)
    -> ks $? (key_ref k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (SigCipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> step_user Silent
                (usrs, adv, cs, gks, ks, qmsgs, (Verify k (Signature msg c_id)))
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
