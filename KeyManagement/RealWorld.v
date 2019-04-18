From Coq Require Import String Sumbool.

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

(* A master key type *)
Inductive key_type :=
| SymKey
| AsymKey (has_private_access : bool).

Definition key_type_same (kt1 kt2 : key_type) :=
  match (kt1,kt2) with
  | (AsymKey _, AsymKey _) => true
  | (SymKey   , SymKey   ) => true
  | _                      => false
  end.

Lemma key_type_eq_dec :
  forall kt1 kt2 : key_type, { kt1 = kt2 } + { kt1 <> kt2 }.
  decide equality; auto using Bool.bool_dec.
Defined.

Record key := MkCryptoKey { keyId : key_identifier ;
                            keyUsage  : key_usage ;
                            keyType : key_type }.

Lemma key_eq_dec :
  forall k1 k2 : key, { k1 = k2 } + { k1 <> k2 }.
  decide equality; auto using Nat.eq_dec, key_usage_eq_dec, key_type_eq_dec.
Defined.

Notation "x ==kk y" := (key_eq_dec x y) (right associativity, at level 75).
Notation "x ==ku y" := (key_usage_eq_dec x y) (right associativity, at level 75).
Notation "x ==kt y" := (key_type_eq_dec x y) (right associativity, at level 75).

Definition keys_compatible (k1 k2 : key) :=
  if   k1.(keyId) ==n k2.(keyId)
  then if   k1.(keyUsage) ==ku k2.(keyUsage)
       then key_type_same k1.(keyType) k2.(keyType)
       else false
  else false.

Definition keyEq k1 k2 := k1.(keyId) = k2.(keyId).
Notation "x ==k y" := (keyEq x y) (right associativity, at level 75).

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
  | Key => key
  | CipherId => cipher_id
  | Pair t1 t2 => typeDenote t1 * typeDenote t2
  end.

Inductive message : type -> Type :=
(* This will eventually be a message Text, using nat for now *)
| Plaintext (txt : nat) : message Nat
| KeyMessage  (k : key) : message Key

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

Definition queued_messages := list exmsg.
Definition keys            := NatMap.t key.
Definition ciphers         := NatMap.t cipher.

(* Definition adversary_knowledge := keys. *)

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

Definition honest_signing_key (honestk advk : keys) (k : key_identifier) : bool :=
  match honestk $? k with
  | None   => false
  | Some (MkCryptoKey _ Signing SymKey)         =>
    match advk $? k with
    | None   => true
    | Some _ => false
    end
  | Some (MkCryptoKey _ Signing (AsymKey true)) =>
    match advk $? k with
    | None => true
    | Some (MkCryptoKey _ Signing (AsymKey false)) => true
    | _    => false
    end
  | Some _ => false
  end.


Fixpoint msg_pattern_spoofable (honestk advk : keys) (pat : msg_pat) : bool :=
  match pat with
  | Accept                     => true
  | Paired p1 p2               => msg_pattern_spoofable honestk advk p1 || msg_pattern_spoofable honestk advk p2
  | Signed k                   => negb (honest_signing_key honestk advk k)
  | SignedEncrypted k__sign k__enc => negb (honest_signing_key honestk advk k__sign)
  end.

Inductive user_cmd : Type -> Type :=
(* Plumbing *)
| Return {A : Type} (res : A) : user_cmd A
| Bind {A A' : Type} (cmd1 : user_cmd A') (cmd2 : A' -> user_cmd A) : user_cmd A

| Gen : user_cmd nat

(* Messaging *)
| Send {t} (uid : user_id) (msg : message t) : user_cmd unit
| Recv {t} (pat : msg_pat) : user_cmd (message t)

(* Crypto!! *)
| SignEncrypt {t} (k__sign k__enc : key) (msg : message t) : user_cmd (message CipherId)
| Decrypt {t} (msg : message CipherId) : user_cmd (message t)

| Sign    {t} (k : key) (msg : message t) : user_cmd (message t)
| Verify  {t} (k : key) (msg : message t) : user_cmd bool

| GenerateSymKey  (usage : key_usage) : user_cmd key
| GenerateAsymKey (usage : key_usage) : user_cmd key

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
      key_heap : keys
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

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : user_data B
    ; all_ciphers : ciphers
    }.

Definition canonical_key (k1 k2 : key) :=
  match Coq.Init.Nat.compare k1.(keyId) k2.(keyId) with
  | Gt => k1
  | Lt => k2
  | Eq =>
    match (k1.(keyUsage), k2.(keyUsage)) with
    | (Signing, Encryption) => k1
    | (Encryption, Signing) => k2
    | _                     =>
      match (k1.(keyType), k2.(keyType)) with
      | (SymKey, _) => k1
      | (_, SymKey) => k2
      | (AsymKey b1, AsymKey b2) => if b1 then k1 else k2
      end
    end
  end.

Definition add_key (k_id : key_identifier) (k : key) (ks : keys) : keys :=
  match ks $? k_id with
  | None     => ks $+ (k_id, k)
  | Some k'  => if   k ==kk k'
               then ks
               else ks $+ (k_id, canonical_key k k')
               (* else if   keys_compatible k k' *)
               (*      then if   k'.(keyType) ==kt AsymKey true (* private key do nothing *) *)
               (*           then ks *)
               (*           else ks $+ (k_id, k) *)
               (*      (* Don't ever want to go down this branch *)
               (*       * Implemented this way to make the fold work nice. *)
               (*       *) *)
               (*      else ks $+ (k_id, canonical_key k k') *)
  end.

Definition merge_keys (ks ks' : keys) : keys :=
  fold add_key ks ks'.

Notation "m1 $k++ m2" := (merge_keys m2 m1) (at level 50, left associativity).

Fixpoint findKeys {t} (msg : message t) : keys :=
  match msg with
  | Plaintext _        => $0
  | KeyMessage k       => $0 $+ (keyId k, k)
  | MsgPair msg1 msg2  => (findKeys msg1) $k++ (findKeys msg2)
  | SignedCiphertext _ => $0
  | Signature m _      => findKeys m
  end.
  
Definition findUserKeys {A} (us : user_list (user_data A)) : keys :=
  fold (fun u_id u ks => ks $k++ u.(key_heap)) us $0.

Definition addUserKeys {A} (ks : keys) (u : user_data A) : user_data A :=
  {| key_heap := u.(key_heap) $k++ ks ; protocol := u.(protocol) ; msg_heap := u.(msg_heap) |}.

Definition addUsersKeys {A} (us : user_list (user_data A)) (ks : keys) : user_list (user_data A) :=
  map (addUserKeys ks) us.

Definition adv_no_honest_keys (adv honest : keys) : Prop :=
  forall k_id,
    match adv $? k_id with
    | None => True
    | Some (MkCryptoKey _ _ SymKey)            => honest $? k_id = None
    | Some (MkCryptoKey kid kt (AsymKey true)) => honest $? k_id = None
                                               \/ honest $? k_id = Some (MkCryptoKey kid kt (AsymKey false) )
    | _ => False
    end.

Ltac contra_map_lookup :=
  match goal with
  | [ H1 : ?ks $? ?k = Some _, H2 : ?ks $? ?k = None |- _ ] => rewrite H1 in H2; invert H2
  | [ H : ?v1 <> ?v2, H1 : ?ks $? ?k = Some ?v1, H2 : ?ks $? ?k = Some ?v2 |- _ ] => rewrite H1 in H2; invert H2; contradiction
  end.

Ltac split_ands := 
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  
Ltac split_ors :=
  repeat match goal with
         | [ H : _ \/ _ |- _ ] => destruct H
         end.

Section KeyMergeTheorems.

  Lemma merge_keys_notation :
    forall ks1 ks2,
      fold add_key ks2 ks1 = ks1 $k++ ks2.
    unfold merge_keys; trivial.
  Qed.

  Definition keys_good (ks : keys) : Prop :=
    forall k_id k,
      ks $? k_id = Some k
      -> keyId k = k_id.

  Definition key_heaps_compatible (ks1 ks2 : keys) :=
      keys_good ks1
    /\ keys_good ks2
    /\ (forall k_id k k', ks1 $? k_id = Some k -> ks2 $? k_id = Some k' -> keys_compatible k k' = true).

  Lemma canonical_key_one_other :
    forall k1 k2,
        canonical_key k1 k2 = k1
      \/ canonical_key k1 k2 = k2.
  Proof.
    intros; unfold canonical_key.
    destruct k1; destruct k2; simpl.
    cases (keyId0 ?= keyId1);
      cases keyUsage0; cases keyUsage1;
        cases keyType0; cases keyType1; eauto;
          try rewrite Nat.compare_refl; simpl; eauto;
            cases has_private_access; cases has_private_access0; eauto.
  Qed.

  Lemma canonical_key_refl :
    forall k, canonical_key k k = k.
  Proof.
    unfold canonical_key; intros; simpl.
    rewrite Nat.compare_refl.
    cases (keyUsage k); cases (keyType k); simpl; eauto; cases has_private_access; eauto.
  Qed.

  Lemma canonical_key_sym :
    forall k1 k2,
      canonical_key k1 k2 = canonical_key k2 k1.
  Proof.
    intros; destruct k1; destruct k2; unfold canonical_key; simpl.
    cases (keyId0 ?= keyId1).
    - apply Nat.compare_eq in Heq; subst.
      rewrite Nat.compare_refl.
      cases keyUsage0; cases keyUsage1; cases keyType0; cases keyType1; eauto.
      cases has_private_access; cases has_private_access0; eauto.
      cases has_private_access; cases has_private_access0; eauto.

    - rewrite Nat.compare_antisym; rewrite Heq; simpl; auto.
    - rewrite Nat.compare_antisym; rewrite Heq; simpl; auto.
  Qed.

  Lemma canonical_key_assoc :
    forall k1 k2 k3,
      canonical_key k1 (canonical_key k2 k3) = canonical_key (canonical_key k1 k2) k3.
  Proof.
    intros; destruct k1; destruct k2; destruct k3; unfold canonical_key; simpl.

    cases (keyId0 ?= keyId1); cases (keyId1 ?= keyId2).
    - apply Nat.compare_eq in Heq; apply Nat.compare_eq in Heq0; subst. simpl.
      cases keyUsage0; cases keyUsage1; cases keyUsage2;
        cases keyType0; cases keyType1; cases keyType2;
          simpl; eauto;
            try rewrite Nat.compare_refl; eauto;
              cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl;
                try rewrite Nat.compare_refl; eauto.

    - apply Nat.compare_eq in Heq; subst; simpl.
      rewrite Heq0; simpl.
      cases keyUsage0; cases keyUsage1; cases keyUsage2;
        cases keyType0; cases keyType1; cases keyType2;
          simpl; eauto; try rewrite Heq0; simpl; eauto;
            cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl;
              rewrite Heq0; simpl; eauto.

    - apply Nat.compare_eq in Heq; subst; simpl.
      rewrite Nat.compare_refl.
      cases keyUsage0; cases keyUsage1; cases keyUsage2;
        cases keyType0; cases keyType1; cases keyType2;
          simpl; eauto; try rewrite Heq0; simpl; eauto;
            cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl;
              rewrite Heq0; simpl; eauto.

    - apply Nat.compare_eq in Heq0; subst; simpl.
      rewrite Nat.compare_refl; simpl.
      cases keyUsage0; cases keyUsage1; cases keyUsage2;
        cases keyType0; cases keyType1; cases keyType2;
          simpl; eauto; try rewrite Heq; simpl; eauto;
            cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl;
              rewrite Heq; simpl; eauto.

    - simpl. rewrite Heq0.
      pose proof Heq as lt1; pose proof Heq0 as lt2.
      apply nat_compare_lt in lt1; apply nat_compare_lt in lt2.
      pose proof (Nat.lt_trans _ _ _ lt1 lt2). apply nat_compare_lt in H.
      rewrite H; eauto.

    - simpl; rewrite Heq; rewrite Heq0; eauto.

    - apply Nat.compare_eq in Heq0; subst; simpl.
      rewrite Heq; simpl.
      cases keyUsage0; cases keyUsage1; cases keyUsage2;
        cases keyType0; cases keyType1; cases keyType2;
          simpl; eauto; try rewrite Heq; simpl; eauto;
            cases has_private_access; cases has_private_access0; try cases has_private_access1; simpl;
              rewrite Heq; simpl; eauto.

    - simpl. cases (keyId0 ?= keyId2); simpl; eauto.
    - simpl. rewrite Heq.
      pose proof Heq as gt1; pose proof Heq0 as gt2.
      apply nat_compare_gt in gt1; apply nat_compare_gt in gt2.

      pose proof (gt_trans _ _ _ gt1 gt2); apply nat_compare_gt in H.
      rewrite H; simpl; eauto.
  Qed.

  Lemma merge_keys_fold_fn_proper :
      Morphisms.Proper
        (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq)))
        add_key.
  Proof.
    unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst; trivial.
  Qed.

  Lemma merge_keys_fold_fn_proper_flip :
      Morphisms.Proper
        (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful (Basics.flip eq) (Basics.flip eq))))
        add_key.
  Proof.
    unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; unfold Basics.flip in *; subst; trivial.
  Qed.

  Lemma merge_keys_fold_fn_proper_Equal :
    Morphisms.Proper
      (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful Equal Equal)))
      add_key.
  Proof.
    unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst.
    apply map_eq_Equal in H1; subst.
    apply Equal_refl.
  Qed.

  Lemma merge_keys_transpose :
    transpose_neqkey eq add_key.
  Proof.
    unfold transpose_neqkey; intros.
    unfold add_key; simpl.
    case_eq (a $? k); case_eq (a $? k'); intros; subst; simpl.

    Ltac work1 :=
      match goal with
      | [ H : ?x <> ?x |- _ ] => contradiction
      | [ H1 : ?x <> ?y, H2 : ?x = ?y |- _ ] => contradiction
      | [ H : ?a $? ?k  = _ |- context [?a $? ?k]  ] => rewrite H
      | [ H : ?a $? ?k' = _ |- context [?a $? ?k'] ] => rewrite H
      | [ |- context[ ?k1 ==kk ?k2 ] ] => case (k1 ==kk k2); intros; subst
      | [ H : keys_compatible ?k1 ?k2 = _ |- context [ keys_compatible ?k1 ?k2 ]] => rewrite H
      | [ |- context [ keys_compatible ?k1 ?k2 ]] => case_eq (keys_compatible k1 k2); intros
      | [ H : keyType ?k = _ |- context [ keyType ?k ==kt ?kt ]] => rewrite H
      | [ |- context [ keyType ?k ==kt ?kt ]] => case (keyType k ==kt kt); intros
      | [ |- context [ _ $+ (?k1, _) $? ?k1 ]] => rewrite add_eq_o by (trivial || auto)
      | [ |- context [ _ $+ (?k1, _) $? ?k2 ]] => rewrite add_neq_o by auto
      | [ |- context [ _ $- ?k1 $? ?k2 ]] => rewrite remove_neq_o by auto
      end.

    Ltac maps_equal :=
      repeat match goal with
             | [ |- context[find ?k (add ?k _ _) ] ]  => rewrite add_eq_o by auto
             | [ |- context[find ?k (add ?k' _ _) ] ] => rewrite add_neq_o by auto
             | [ |- context[find ?k (remove ?k _) ] ]  => rewrite remove_eq_o by auto
             | [ |- context[find ?k (remove ?k' _) ] ] => rewrite remove_neq_o by auto
             | [ |- _ $+ (?k1,_) $? ?k = _ ] => case (k1 ==n k); intros; subst
             | [ |- _ $- ?k1     $? ?k = _ ] => case (k1 ==n k); intros; subst
             | [ |- add _ _ _ = _ ] => apply map_eq_Equal; unfold Equal; intros ?y
             end.

    repeat work1; eauto;
      apply map_eq_Equal; unfold Equal; intros;
        maps_equal; auto.
    
    repeat work1; eauto;
      apply map_eq_Equal; unfold Equal; intros;
        maps_equal; auto.

    repeat work1; eauto;
      apply map_eq_Equal; unfold Equal; intros;
        maps_equal; auto.

    repeat work1; eauto;
      apply map_eq_Equal; unfold Equal; intros;
        maps_equal; auto.

  Qed.

  Lemma merge_keys_transpose_flip :
    transpose_neqkey (Basics.flip eq) add_key.
  Proof.
    unfold transpose_neqkey, Basics.flip; intros.
    apply merge_keys_transpose; auto.
  Qed.

  Lemma eq_Equal :
    forall {V} (m m' : NatMap.t V),
      m = m'
      -> Equal m m'.
    intros; subst; apply Equal_refl.
  Qed.

  Lemma merge_keys_transpose_Equal :
    transpose_neqkey Equal add_key.
  Proof.
    unfold transpose_neqkey; intros.
    apply eq_Equal.
    apply merge_keys_transpose; auto.
  Qed.

  Hint Resolve merge_keys_fold_fn_proper merge_keys_fold_fn_proper_flip merge_keys_fold_fn_proper_Equal
               merge_keys_transpose merge_keys_transpose_flip merge_keys_transpose_Equal.


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
    end.

  Ltac progress_fold_add1 :=
    match goal with
    | [ H : fold add_key (_ $+ (_,_)) _ $? _ = _ |- _ ] => rewrite fold_add in H
    | [ |- context[  fold add_key (_ $+ (_,_)) _ ] ] => rewrite fold_add
    end.

  Ltac clean_map_lookups :=
    (repeat clean_map_lookups1);
    try discriminate;
    try contra_map_lookup.

  Hint Resolve empty_Empty.
  Hint Extern 1 (~ In _ _) => rewrite not_find_in_iff.

  Lemma merge_keys_left_identity :
    forall ks,
      $0 $k++ ks = ks.
  Proof.
    unfold merge_keys.
    induction ks using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; auto.
    - apply fold_Empty; eauto.
    - rewrite fold_add; clean_map_lookups; eauto.
      rewrite IHks; clear IHks.
      unfold add_key; rewrite H; eauto.
  Qed.
    
  Lemma merge_keys_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_keys; intros; rewrite fold_Empty; eauto.
  Qed.

  Hint Resolve merge_keys_left_identity merge_keys_right_identity.

  Lemma merge_keys_adds_no_new_keys :
    forall ks2 k ks1,
        ks1 $? k = None
      -> ks2 $? k = None
      -> (ks1 $k++ ks2) $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - rewrite merge_keys_right_identity; auto.
    - unfold merge_keys; rewrite fold_add; auto.
      case (x ==n k); intros; subst; clean_map_lookups.
      + rewrite merge_keys_notation; unfold add_key.
        cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases (e ==kk k0); subst; eauto.
        clean_map_lookups. eapply IHks2; auto.
  Qed.

  Lemma merge_keys_no_disappear_keys :
    forall ks2 k ks1,
      (ks1 $k++ ks2) $? k = None
    -> ks1 $? k = None
    /\ ks2 $? k = None.
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - rewrite merge_keys_right_identity in H; eauto.
    - unfold merge_keys in H0. progress_fold_add1; auto.
      rewrite merge_keys_notation in *; clean_map_lookups.
      unfold add_key in H0.
      cases (ks1 $k++ ks2 $? x); clean_map_lookups;
        [cases (e ==kk k0); subst | ];
          case (x ==n k); intros; subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_keys_adds_no_new_keys merge_keys_no_disappear_keys.

  Lemma merge_keys_adds_ks1 :
    forall ks2 ks1 k v ks,
        ks1 $? k = Some v
      -> ks2 $? k = None
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - subst; rewrite fold_Empty; eauto.
    - case (x ==n k); intros; subst; clean_map_lookups; eauto.
      rewrite fold_add; eauto.
      rewrite merge_keys_notation.
      unfold add_key.
      cases ( ks1 $k++ ks2 $? x ); clean_map_lookups; eauto.
      cases ( e ==kk k0 ); eauto.
      clean_map_lookups; eauto.
  Qed.

  Lemma merge_keys_adds_ks2 :
    forall ks2 ks1 k v ks,
        ks1 $? k = None
      -> ks2 $? k = Some v
      -> ks = ks1 $k++ ks2
      -> ks $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - invert H0.
    - subst.
      case (x ==n k); intros; subst; clean_map_lookups; eauto.
      + rewrite fold_add; auto.
        rewrite merge_keys_notation.
        unfold add_key.
        pose proof merge_keys_adds_no_new_keys.
        cases ( ks1 $k++ ks2 $? k); clean_map_lookups; eauto.
        cases ( v ==kk k0 ); subst; clean_map_lookups; eauto.
        specialize (H1 _ _ _ H0 H); contra_map_lookup.

      + rewrite fold_add; auto.
        rewrite merge_keys_notation.
        unfold add_key.
        cases ( ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases ( e ==kk k0 ); eauto.
        clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_keys_adds_ks1 merge_keys_adds_ks2.

  Lemma merge_keys_came_from_somewhere1 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks2 $? k = None
      -> ks1 $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - rewrite fold_Empty in H; auto.

    - case (x ==n k); intros; subst; clean_map_lookups.
      + progress_fold_add1; auto.
        rewrite merge_keys_notation in H0; unfold add_key at 1 in H0.

        cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases ( e ==kk k0 ); subst; clean_map_lookups; eauto.
  Qed.

  Lemma merge_keys_came_from_somewhere2 :
    forall ks2 ks1 k v,
        ks1 $k++ ks2 $? k = Some v
      -> ks1 $? k = None
      -> ks2 $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - rewrite fold_Empty in H; clean_map_lookups; auto.

    - case (x ==n k); intros; subst; clean_map_lookups; progress_fold_add1; auto.
      * pose proof (merge_keys_adds_no_new_keys _ _ _ H1 H).
        rewrite merge_keys_notation in H0; unfold add_key in H0; auto.
        cases (ks1 $k++ ks2 $? k); clean_map_lookups; eauto.

      * rewrite merge_keys_notation in H0; unfold add_key in H0; auto.
        cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases ( e ==kk k0 ); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve merge_keys_came_from_somewhere1 merge_keys_came_from_somewhere2.

  Lemma merge_keys_split :
    forall ks2 k_id k ks1,
      ks1 $k++ ks2 $? k_id = Some k
      -> (ks1 $? k_id = None /\ ks2 $? k_id = Some k)
      \/ (ks1 $? k_id = Some k /\ ks2 $? k_id = None)
      \/ exists k1 k2, ks1 $? k_id = Some k1 /\ ks2 $? k_id = Some k2 /\ k = canonical_key k1 k2.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - rewrite merge_keys_right_identity in H. intuition idtac.
    - rewrite fold_add in H0; auto.
      rewrite merge_keys_notation in H0; unfold add_key in H0; auto.
      case (x ==n k_id); intros; subst; clean_map_lookups.
      + cases (ks1 $k++ ks2 $? k_id); intros; simpl.
        * cases (e ==kk k0); subst.
          ** rewrite Heq in H0; invert H0. eapply merge_keys_came_from_somewhere1 in Heq; auto.
             right; right. do 2 eexists; intuition eauto. rewrite canonical_key_refl; trivial.
          ** clean_map_lookups; eapply merge_keys_came_from_somewhere1 in Heq; auto.
             right; right; do 2 eexists; intuition eauto. rewrite canonical_key_sym; trivial.

        * clean_map_lookups; eauto. eapply merge_keys_no_disappear_keys in Heq; invert Heq.
          intuition idtac.
      + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases (e ==kk k0); auto.
        cases (x ==n k_id); clean_map_lookups; auto.
  Qed.

  Lemma merge_keys_canonicalizes :
    forall ks2 k_id k k1 k2 ks1,
        ks1 $k++ ks2 $? k_id = Some k
      -> ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> k = canonical_key k1 k2.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - invert H1.

    - rewrite fold_add in H0; auto.
      rewrite merge_keys_notation in H0; unfold add_key in H0; auto.
      case (x ==n k_id); intros; subst; clean_map_lookups.
      + cases (ks1 $k++ ks2 $? k_id); intros; simpl.
        * cases (k2 ==kk k0); subst; eauto.
          ** rewrite Heq in H0; invert H0. eapply merge_keys_came_from_somewhere1 in Heq; auto. rewrite Heq in H1; invert H1. rewrite canonical_key_refl; trivial.
          ** clean_map_lookups. eapply merge_keys_came_from_somewhere1 in Heq; auto. rewrite Heq in H1; invert H1. rewrite canonical_key_sym; trivial.

        * clean_map_lookups. eapply merge_keys_no_disappear_keys in Heq; destruct Heq; contra_map_lookup.

      + cases (ks1 $k++ ks2 $? x); clean_map_lookups; eauto.
        cases (e ==kk k0); subst; clean_map_lookups; eauto.
  Qed.

  Lemma merge_keys_canonicalizes' :
    forall ks2 k_id k k1 k2 ks1,
        ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> k = canonical_key k1 k2
      -> ks1 $k++ ks2 $? k_id = Some k.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - invert H0.

    - rewrite fold_add; auto.
      rewrite merge_keys_notation; unfold add_key.
      cases (ks1 $k++ ks2 $? x); case (x ==n k_id); intros; subst; clean_map_lookups.
      + cases (k2 ==kk k0); subst.
        * eapply (merge_keys_came_from_somewhere1) in Heq; auto. rewrite Heq in H0; invert H0. rewrite canonical_key_refl. eapply merge_keys_adds_ks1; eauto.
        * eapply (merge_keys_came_from_somewhere1) in Heq; auto. rewrite Heq in H0; invert H0. rewrite canonical_key_sym. clean_map_lookups; trivial.
      + cases (e ==kk k0); subst; clean_map_lookups; eauto.
      + eapply merge_keys_no_disappear_keys in Heq; invert Heq; contra_map_lookup.
      + eapply IHks2; eauto.
  Qed.

  Lemma add_key_results :
    forall k v ks ks',
      ks' = add_key k v ks
      -> ks' = ks
      \/ ks' = ks $+ (k,v)
      \/ exists k', ks' = ks $+ (k, canonical_key v k').
  Proof.
    unfold add_key; intros.
    cases (ks $? k); auto.
    cases (v ==kk k0); auto.
    intuition eauto.
  Qed.

  Lemma keys_compatible_reflexive :
    forall k,
      keys_compatible k k = true.
  Proof.
    unfold keys_compatible; intros.
    cases (keyId k ==n keyId k); eauto.
    cases (keyUsage k ==ku keyUsage k); eauto.
    unfold key_type_same; cases (keyType k); eauto.
  Qed.

  Lemma keys_compatible_symmetric :
    forall k1 k2,
      keys_compatible k1 k2 = keys_compatible k2 k1.
  Proof.
    unfold keys_compatible; intros.
    cases (keyId k1 ==n keyId k2).
    cases (keyUsage k1 ==ku keyUsage k2).
    cases (key_type_same (keyType k1) (keyType k2)).
    - rewrite e; rewrite e0; cases (keyId k2 ==n keyId k2); cases (keyUsage k2 ==ku keyUsage k2); try contradiction.
      unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto.
    - rewrite e; rewrite e0; cases (keyId k2 ==n keyId k2); cases (keyUsage k2 ==ku keyUsage k2); try contradiction.
      unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto.
    - rewrite e; cases (keyId k2 ==n keyId k2); auto.
      cases (keyUsage k2 ==ku keyUsage k1); auto.
      unfold key_type_same in *; cases (keyType k1); cases (keyType k2); auto.
    - cases (keyId k2 ==n keyId k1); cases (keyUsage k2 ==ku keyUsage k1); try contradiction; auto.
      symmetry in e; contradiction.
  Qed.

  Lemma merge_keys_ok :
    forall ks2 k_id k1 k2 ks ks1,
        ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> ks = ks1 $k++ ks2
      -> ( ks $? k_id = Some k1 /\ k1 = k2)
      \/ ( ks $? k_id = Some (canonical_key k1 k2)).
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - invert H0.

    - subst. progress_fold_add1; clean_map_lookups; eauto.
      rewrite merge_keys_notation.
      case (x ==n k_id); intros; subst; clean_map_lookups.
      + remember (ks1 $k++ ks2) as ks.
        specialize (merge_keys_adds_ks1 _ _ _ H0 H Heqks). intros; subst.
        cases (k2 ==kk k1).
        * unfold add_key; subst. rewrite H1.
          rewrite canonical_key_refl; simpl.
          cases (k1 ==kk k1); try contradiction; eauto.

        * unfold add_key; rewrite H1; simpl. cases (k2 ==kk k1); try contradiction.
          rewrite canonical_key_sym.
          assert (k1 <> k2) by auto.

          clean_map_lookups; intuition idtac.

      + unfold add_key.
        cases (ks1 $k++ ks2 $? x); eauto.
        * cases (e ==kk k); clean_map_lookups; eauto.
        * clean_map_lookups; eauto.
  Qed.

  Lemma merge_keys_symmetric :
    forall ks1 ks2,
      ks1 $k++ ks2 = ks2 $k++ ks1.
  Proof.
    intros.

    apply map_eq_Equal; unfold Equal; subst; intros.

    cases (ks1 $? y); cases (ks2 $? y).
    - remember (ks1 $k++ ks2) as ks12. remember (ks2 $k++ ks1) as ks21.
      pose proof (merge_keys_ok _ _ _ Heq Heq0 Heqks12).
      pose proof (merge_keys_ok _ _ _ Heq0 Heq Heqks21).

      (repeat match goal with
              | [ H : _ /\ _ |- _ ] => destruct H; subst
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ |- context [canonical_key ?k ?k]] => rewrite canonical_key_refl
              | [ H : _ $k++ _ $? _ = Some _ |- _ ] => rewrite H
              | [ H : _ $? _ = Some _ |- _ ] => rewrite H
              end);
        eauto.
      rewrite canonical_key_sym; trivial.

    - erewrite (merge_keys_adds_ks1); eauto.
      erewrite (merge_keys_adds_ks2); eauto.
    - erewrite (merge_keys_adds_ks2); eauto.
      erewrite (merge_keys_adds_ks1); eauto.
    - rewrite merge_keys_adds_no_new_keys; eauto.
      rewrite merge_keys_adds_no_new_keys; eauto.
  Qed.

  Hint Extern 1 (keys_compatible _ _ = _) => eassumption || (rewrite keys_compatible_symmetric; eassumption).

  Lemma merge_keys_inequal_addition_no_impact :
    forall ks1 ks2 k_id k_id' k,
      k_id <> k_id'
      -> ks1 $k++ (ks2 $+ (k_id,k)) $? k_id' = ks1 $k++ ks2 $? k_id'.
  Proof.
    intros.
    cases (ks1 $k++ ks2 $? k_id').
    - apply merge_keys_split in Heq.
      split_ors; split_ands; subst.
      + eapply merge_keys_adds_ks2 with (ks2:=ks2 $+ (k_id, k)); clean_map_lookups; eauto.
      + eapply merge_keys_adds_ks1 with (ks2:=ks2 $+ (k_id, k)); clean_map_lookups; eauto.
      + destruct H0 as [k1 H0]. destruct H0 as [k2 H0]. split_ands.
        remember (ks1 $k++ ks2) as ks.
        specialize (merge_keys_ok _ _ _ H0 H1 Heqks); intros; split_ors; split_ands; subst.
        * rewrite canonical_key_refl.
          eapply merge_keys_canonicalizes' with (ks2:=ks2 $+ (k_id, k)). eauto. clean_map_lookups; eauto. rewrite canonical_key_refl; trivial.
        * eapply merge_keys_canonicalizes' with (ks2:=ks2 $+ (k_id, k)). eauto. clean_map_lookups; eauto. trivial.
    - apply merge_keys_no_disappear_keys in Heq; split_ands.
      eapply merge_keys_adds_no_new_keys; auto.
      clean_map_lookups; auto.
  Qed.

  Lemma merge_keys_assoc :
    forall ks3 ks1 ks2 : keys,
      ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Proof.
    induction ks3 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; eauto.
    - rewrite !merge_keys_right_identity; trivial.
    - apply map_eq_Equal; unfold Equal; subst; intros.
      unfold merge_keys.
      progress_fold_add1; auto. progress_fold_add1; auto.
      rewrite merge_keys_notation with (ks1 := ks1).
      rewrite merge_keys_notation with (ks2 := ks3).
      unfold add_key at 1; unfold add_key at 2.

      (* clean up notation of induction hypothesis *) 
      specialize (IHks3 ks1 ks2); unfold merge_keys in IHks3.
      rewrite merge_keys_notation  with (ks1 := ks1) in IHks3.
      rewrite merge_keys_notation  with (ks1 := ks2) in IHks3.
      rewrite merge_keys_notation  with (ks2 := ks3) in IHks3.
      rewrite merge_keys_notation  with (ks2 := ks2 $k++ ks3) in IHks3.

      rewrite merge_keys_notation with (ks1 := ks2).

      Ltac rewrite123 :=
        match goal with | [ H : _ $k++ _ $k++ _ $? _ = _ |- _ ] => rewrite H end.

      cases (ks1 $k++ ks2 $k++ ks3 $? x);
        intros; subst; clean_map_lookups.

      + cases (ks2 $k++ ks3 $? x).
        * assert (ks1 $k++ ks2 $k++ ks3 $? x = Some k) as S by auto.
          rewrite IHks3 in S; eapply merge_keys_split in S; auto.
          cases (e ==kk k); cases (e ==kk k0); subst.
          ** rewrite merge_keys_notation with (ks2:=ks2$k++ks3); rewrite IHks3; trivial.
          ** rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3 $+ (x, canonical_key k k0)).
             split_ors; split_ands; subst.
             *** rewrite Heq0 in H1; invert H1. contradiction.
             *** contra_map_lookup.
             *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1. symmetry.
                 rewrite <- canonical_key_assoc. rewrite canonical_key_refl.
                 cases (x ==n y); subst.
                   rewrite Heq. eapply merge_keys_canonicalizes'. eassumption. clean_map_lookups. reflexivity. rewrite canonical_key_assoc, canonical_key_refl; trivial.
                   rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption.
          ** rewrite merge_keys_notation with (ks2:=ks2$k++ks3). rewrite <- IHks3.
             split_ors; split_ands; subst.
             *** rewrite Heq0 in H1; invert H1. contradiction.
             *** contra_map_lookup.
             *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1.
                 cases (x ==n y); subst.
                   rewrite canonical_key_sym, <- canonical_key_assoc, canonical_key_refl. clean_map_lookups; rewrite Heq; trivial.
                   clean_map_lookups; trivial.
          ** rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3 $+ (x, canonical_key e k0)).
             split_ors; split_ands; subst.
             *** rewrite Heq0 in H1; invert H1. symmetry.
                 cases (x ==n y); subst; clean_map_lookups.
                   eapply merge_keys_adds_ks2. eauto. 2:reflexivity. clean_map_lookups; trivial.
                   rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption.
             *** contra_map_lookup.
             *** destruct H0 as [k1 H0]. destruct H0 as [k2]. split_ands. rewrite Heq0 in H1; invert H1.
                 symmetry.
                 cases (x ==n y); subst; clean_map_lookups.
                 **** eapply merge_keys_canonicalizes'; clean_map_lookups; eauto.
                      rewrite canonical_key_assoc, canonical_key_sym with (k1:=e), <- canonical_key_assoc; trivial.
                 **** rewrite IHks3. eapply merge_keys_inequal_addition_no_impact; assumption.

        * cases (e ==kk k); subst.
          ** rewrite fold_add; auto. unfold add_key at 1. rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3), <- IHks3. rewrite Heq.
             cases (k ==kk k); simpl; eauto. contradiction.
          ** rewrite fold_add; auto. unfold add_key at 1. rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3), <- IHks3. rewrite Heq.
             cases (e ==kk k); simpl; eauto. contradiction.


      + assert (ks1 $k++ ks2 $k++ ks3 $? x = None) as HH by assumption; rewrite IHks3 in HH; eapply merge_keys_no_disappear_keys in HH; split_ands.
        rewrite H1.
        progress_fold_add1; auto.
        unfold add_key at 1.
        rewrite merge_keys_notation with (ks2:=ks2 $k++ ks3). rewrite <- IHks3. rewrite Heq; clean_map_lookups; trivial.
  Qed.

  Lemma findUserKeys_fold_fn_proper :
    forall {A},
    Morphisms.Proper
      (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq)))
      (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
    unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst; trivial.
  Qed.

  Lemma findUserKeys_fold_fn_proper_Equal :
    forall {A},
    Morphisms.Proper
      (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful Equal Equal)))
      (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
    unfold Morphisms.Proper, Morphisms.respectful; intros.
    apply map_eq_Equal in H1; subst.
    unfold Equal; intros; trivial.
  Qed.

  Lemma findUserKeys_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite merge_keys_symmetric with (ks1 := a).
    rewrite merge_keys_symmetric with (ks1 := a $k++ key_heap e).
    rewrite merge_keys_assoc; trivial.
  Qed.

  Lemma findUserKeys_transpose_Equal :
    forall {A},
      transpose_neqkey Equal (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    unfold Equal; intros.
    rewrite merge_keys_symmetric with (ks1 := a).
    rewrite merge_keys_symmetric with (ks1 := a $k++ key_heap e).
    rewrite merge_keys_assoc; trivial.
  Qed.

  Hint Resolve findUserKeys_fold_fn_proper findUserKeys_fold_fn_proper_Equal findUserKeys_transpose findUserKeys_transpose_Equal.

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

  Lemma find_user_keys_includes_user_keys:
    forall {A} (us : honest_users A) u_id u_d,
      us $? u_id = Some u_d
      -> findUserKeys us = u_d.(key_heap) $k++ findUserKeys (us $- u_id).
  Proof.
    unfold findUserKeys.
    induction us using P.map_induction_bis; intros.
    
    - apply map_eq_Equal in H; subst; eauto.
    - invert H.
    - apply map_eq_Equal; unfold Equal; subst; intros.
      simpl.
      cases (x ==n u_id); intros; subst; clean_map_lookups.
      + rewrite add_remove_eq.
        rewrite fold_add; auto. rewrite remove_not_in_idempotent by assumption.
        rewrite merge_keys_symmetric.
        trivial.
      + rewrite add_remove_neq by assumption.
        rewrite !fold_add; auto.
        rewrite <- merge_keys_assoc.
        erewrite IHus; eauto.
        rewrite not_find_in_iff; rewrite remove_neq_o; auto.
  Qed.

  Lemma find_user_keys_universe_user :
    forall {A B} (U : universe A B) u_id u_d,
        adv_no_honest_keys U.(adversary).(key_heap) (findUserKeys U.(users))
      -> U.(users) $? u_id = Some u_d
      -> key_heaps_compatible U.(adversary).(key_heap) (findUserKeys U.(users))
      -> adv_no_honest_keys U.(adversary).(key_heap) u_d.(key_heap).
  Proof.
  Admitted.

End KeyMergeTheorems.

Definition encryptMessage {t} (k__sign k__enc : key) (m : message t) (c_id : cipher_id) : option cipher :=
  match (k__sign.(keyUsage), k__enc.(keyUsage)) with
  | (Signing, Encryption) =>
    let c := SigEncCipher c_id k__sign.(keyId) k__enc.(keyId) m
    in  match k__sign with
        | MkCryptoKey _ _ SymKey         => Some c
        | MkCryptoKey _ _ (AsymKey true) => Some c
        | _       => None
        end
  | _          => None
  end.

Definition signMessage {t} (k : key) (m : message t) (c_id : cipher_id) : option cipher :=
  match k with
  | MkCryptoKey _ Signing SymKey         => Some (SigCipher c_id k.(keyId) m)
  | MkCryptoKey _ Signing (AsymKey true) => Some (SigCipher c_id k.(keyId) m)
  | _       => None
  end.

Definition canVerifySignature {A} (cs : ciphers)(usrDat : user_data A)(c_id : cipher_id) : Prop :=
  forall t (m : message t) k_id k ,
    cs $? c_id = Some (SigCipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Definition buildUniverse {A B}
           (usrs : honest_users A) (adv : user_data B) (cs : ciphers)
           (u_id : user_id) (userData : user_data A) : universe A B :=
  {| users        := usrs $+ (u_id, userData)
   ; adversary    := adv
   ; all_ciphers  := cs
   |}.

Definition buildUniverseAdv {A B}
           (usrs : honest_users A) (cs : ciphers)
           (userData : user_data B) : universe A B :=
  {| users        := usrs
   ; adversary    := userData
   ; all_ciphers  := cs
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
| Input  t (msg : message t) (pat : msg_pat) (uks : keys)
| Output t (msg : message t)
.

Definition rlabel := @label action.

Definition action_adversary_safe (honestk advk : keys) (a : action) : bool :=
  match a with
  | Input _ pat _ => negb (msg_pattern_spoofable honestk advk pat)
  | Output _      => true
  end.

Definition data_step0 (A B C : Type) : Type :=
  honest_users A * user_data B * ciphers * keys * queued_messages * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B C :=
  (U.(users), U.(adversary), U.(all_ciphers), u_data.(key_heap), u_data.(msg_heap), u_data.(protocol)).

(* Labeled transition system *)
Inductive step_user : forall A B C, rlabel -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {B r r'} (usrs usrs' : honest_users r') (adv adv' : user_data B)
                     lbl cs cs' qmsgs qmsgs' ks ks' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user lbl (usrs, adv, cs, ks, qmsgs, cmd1) (usrs', adv', cs', ks', qmsgs', cmd1')
    -> step_user lbl (usrs, adv, cs, ks, qmsgs, Bind cmd1 cmd2) (usrs', adv', cs', ks', qmsgs', Bind cmd1' cmd2)
| StepBindProceed : forall {B r r'} (usrs : honest_users r) (adv : user_data B) cs ks qmsgs (v : r') (cmd : r' -> user_cmd r),
    step_user Silent (usrs, adv, cs, ks, qmsgs, Bind (Return v) cmd) (usrs, adv, cs, ks, qmsgs, cmd v)

| StepGen : forall {A B} (usrs : honest_users A) (adv : user_data B) cs ks qmsgs n,
    step_user Silent (usrs, adv, cs, ks, qmsgs, Gen) (usrs, adv, cs, ks, qmsgs, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs ks ks' qmsgs qmsgs' (msg : message t) msgs pat newkeys,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> msg_accepted_by_pattern cs pat msg
    -> step_user (Action (Input msg pat ks))
                (usrs, adv, cs, ks , qmsgs , Recv pat)
                (usrs, adv, cs, ks', qmsgs', Return msg)

| StepRecvDrop : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs ks qmsgs qmsgs' (msg : message t) pat msgs,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> ~ msg_accepted_by_pattern cs pat msg
    -> step_user Silent (* Error label ... *)
                (usrs, adv, cs, ks, qmsgs , Recv pat)
                (usrs, adv, cs, ks, qmsgs', Return msg)

(* Augment attacker's keys with those available through messages sent,
 * including traversing through ciphers already known by attacker, etc.
 *)
| StepSend : forall {A B} {t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
               cs ks qmsgs rec_u_id rec_u newkeys (msg : message t),
    findKeys msg = newkeys
    -> adv' = addUserKeys newkeys adv
    -> usrs $? rec_u_id = Some rec_u
    -> usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                  ; protocol := rec_u.(protocol) 
                                  ; msg_heap := rec_u.(msg_heap) ++ [Exm msg]  |})
    -> step_user (Action (Output msg))
                (usrs , adv , cs, ks, qmsgs, Send rec_u_id msg)
                (usrs', adv', cs, ks, qmsgs, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' ks qmsgs (msg : message t) k__sign k__enc k__signid k__encid c_id cipherMsg,
      keyId k__sign = k__signid
    -> keyId k__enc = k__encid
    -> ks $? k__signid = Some k__sign
    -> ks $? k__encid = Some k__enc
    -> ~ In c_id cs
    -> encryptMessage k__sign k__enc msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , ks, qmsgs, SignEncrypt k__sign k__enc msg)
                (usrs, adv, cs', ks, qmsgs, Return (SignedCiphertext c_id))

| StepDecrypt : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs ks ks' qmsgs (msg : message t) k__signid k__sign k__encid c_id newkeys,
      cs $? c_id = Some (SigEncCipher c_id k__signid k__encid msg)
    -> ( ks $? k__encid = Some (MkCryptoKey k__encid Encryption (AsymKey true)) (* check we have access to private key *)
      \/ ks $? k__encid = Some (MkCryptoKey k__encid Encryption SymKey) )
    -> ks $? k__signid = Some k__sign
    (* -> k.(keyId) = k_id *)
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> step_user Silent
                (usrs, adv, cs, ks , qmsgs, Decrypt (SignedCiphertext c_id))
                (usrs, adv, cs, ks', qmsgs, Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs cs' ks qmsgs (msg : message t) k k_id c_id cipherMsg,
      keyId k = k_id
    -> ks $? k_id = Some k
    -> ~(In c_id cs)
    -> signMessage k msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user Silent
                (usrs, adv, cs , ks, qmsgs, Sign k msg)
                (usrs, adv, cs', ks, qmsgs, Return (Signature msg c_id))

| StepVerify : forall {A B} {t} (usrs : honest_users A) (adv : user_data B) cs ks qmsgs (msg : message t) k_id k c_id,
    keyId k = k_id
    (* k is in your key heap *)
    -> ks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (SigCipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> step_user Silent
                (usrs, adv, cs, ks, qmsgs, (Verify k (Signature msg c_id)))
                (usrs, adv, cs, ks, qmsgs, Return true)
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
| StepUser : forall U U' u_id userData usrs adv cs ks qmsgs lbl (cmd : user_cmd A),
    U.(users) $? u_id = Some userData
    -> step_user lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverse usrs adv cs u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U lbl U'
| StepAdversary : forall U U' userData usrs adv cs ks qmsgs lbl (cmd : user_cmd B),
      step_user lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverseAdv usrs cs {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U Silent U'
.
