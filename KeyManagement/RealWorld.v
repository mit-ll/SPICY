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

Definition queued_messages := list exmsg.
Definition keys            := NatMap.t key.
Definition ciphers         := NatMap.t cipher.

Definition adversary_knowledge := keys.

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

Fixpoint msg_pattern_spoofable (advk : adversary_knowledge) (pat : msg_pat) : bool :=
  match pat with
  | Accept => true
  | Paired p1 p2 => msg_pattern_spoofable advk p1 || msg_pattern_spoofable advk p2
  | Signed k =>
    match advk $? k with
    | Some _ => true
    | None   => false
    end
  | SignedEncrypted k__sign K__enc =>
    match advk $? k__sign with
    | Some _ => true
    | None   => false
    end

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

Definition adversaries A  := user_list (user_data A).
Definition honest_users A := user_list (user_data A).

Record universe (A B : Type) :=
  mkUniverse {
      users       : honest_users A
    ; adversary   : adversaries B
    ; all_ciphers : ciphers
    }.

Definition add_key (k_id : key_identifier) (k : key) (ks : keys) : keys :=
  match ks $? k_id with
  | None     => ks $+ (k_id, k)
  | Some k'  => if   k ==kk k'
               then ks
               else if   keys_compatible k k'
                    then if   k'.(keyType) ==kt AsymKey true (* private key do nothing *)
                         then ks
                         else ks $+ (k_id, k)
                    (* Don't ever want to go down this branch
                     * Implemented this way to make the fold work nice.
                     *)
                    else ks $- k_id
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
  
Definition addUserKeys {A} (us : user_list (user_data A)) (ks : keys) : user_list (user_data A) :=
  map (fun u => {| key_heap := u.(key_heap) $k++ ks ; protocol := u.(protocol) ;  msg_heap := u.(msg_heap) |}) us.

Definition adv_no_honest_keys (adv honest : keys) : Prop :=
  forall k_id,
    match adv $? k_id with
    | None => True
    | Some (MkCryptoKey _ _ SymKey)          => honest $? k_id = None
    | Some (MkCryptoKey _ _ (AsymKey true) ) => honest $? k_id = None
    | Some k' =>  honest $? k_id = None
              \/ (exists k, honest $? k_id = Some k /\ keys_compatible k k' = true)
    end.

Section KeyMergeTheorems.

  Definition keys_good (ks : keys) : Prop :=
    forall k_id k,
      ks $? k_id = Some k
      -> keyId k = k_id.

  Definition key_heaps_compatible (ks1 ks2 : keys) :=
      keys_good ks1
    /\ keys_good ks2
    /\ (forall k_id k k', ks1 $? k_id = Some k -> ks2 $? k_id = Some k' -> keys_compatible k k' = true).

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

  Lemma merge_keys_merges :
    forall ks2 k_id k ks ks1,
      ks = ks1 $k++ ks2
      -> ks $? k_id = Some k
      -> ks1 $? k_id = Some k
      \/ ks2 $? k_id = Some k.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst.
      eapply IHks2_1; eauto.

    - rewrite fold_Empty in H; eauto.
      subst; intuition idtac.
      unfold Empty, Raw.Empty, empty, not; simpl. intros. unfold Raw.PX.MapsTo, Raw.empty in H1; invert H1.

    - rewrite fold_add in H0; auto.

      case (x ==n k_id); intros.
      + subst. rewrite add_eq_o by reflexivity.

        remember (fold add_key ks2 ks1) as mks12.
        unfold add_key in H1.
        case_eq (mks12 $? k_id); intros; rewrite H0 in H1.
        * cases (e ==kk k0).
          rewrite H0 in H1; invert H1; auto.
          cases (keys_compatible e k0).
            cases (keyType k0 ==kt AsymKey true).
              specialize (IHks2 _ _ _ _ Heqmks12 H1); invert IHks2; auto. rewrite not_find_in_iff in H. rewrite H in H2; invert H2.
            rewrite add_eq_o in H1; intuition idtac.
            
          rewrite remove_eq_o in H1; invert H1; auto.
        * rewrite add_eq_o in H1 by trivial. intuition idtac.

      + rewrite add_neq_o by auto.
        eapply IHks2; eauto.
        remember (fold add_key ks2 ks1) as mks12.
        unfold add_key in H0.
        rewrite H0 in H1; clear H0.

        case_eq (mks12 $? x); intros; rewrite H0 in H1.
        * cases (e ==kk k0); auto. cases (keys_compatible e k0).
          cases (keyType k0 ==kt AsymKey true); eauto. rewrite add_neq_o in H1; auto.
          rewrite remove_neq_o in H1; auto.
        * rewrite add_neq_o in H1; auto.

  Qed.

  Lemma add_key_results :
    forall k v ks ks',
      ks' = add_key k v ks
      -> ks' = ks
      \/ ks' = ks $+ (k,v)
      \/ ks' = ks $- k.
  Proof.
    unfold add_key; intros.
    cases (ks $? k); auto.
    cases (v ==kk k0); auto.
    cases (keys_compatible v k0); auto.
    cases (keyType k0 ==kt AsymKey true); auto.
  Qed.

  Lemma merge_keys_adds_ks1 :
    forall ks2 ks1 k v ks,
      ks = ks1 $k++ ks2
      -> ks1 $? k = Some v
      -> ks2 $? k = None
      -> ks $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst.
      eapply IHks2_1; eauto.

    - rewrite fold_Empty in H; auto.
      subst; auto. apply empty_Empty.

    - case (x ==n k); intros.
      + rewrite add_eq_o in H2 by assumption; invert H2.
      + rewrite add_neq_o in H2 by assumption.
        rewrite H0. rewrite fold_add; auto.
        remember (fold add_key ks2 ks1) as mks12.
        unfold add_key.
        cases ( mks12 $? x ).
        cases ( e ==kk k0 ). eapply IHks2; eauto.
        cases ( keys_compatible e k0).
        cases (keyType k0 ==kt AsymKey true); try (rewrite add_neq_o by auto); eapply IHks2; eauto.
        rewrite remove_neq_o by auto; eapply IHks2; eauto.
        rewrite add_neq_o by assumption. eapply IHks2; eauto.
  Qed.

  Ltac contra_map_lookup :=
    match goal with
    | [ H1 : ?ks $? ?k = Some _, H2 : ?ks $? ?k = None |- _ ] => rewrite H1 in H2; invert H2
    end.

  Lemma merge_keys_adds_ks2 :
    forall ks2 ks1 k v ks,
      ks = ks1 $k++ ks2
      -> ks1 $? k = None
      -> ks2 $? k = Some v
      -> ks $? k = Some v.
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst.
      eapply IHks2_1; eauto.

    - rewrite fold_Empty in H; auto.
      invert H1. invert H1.

    - case (x ==n k); intros.
      + subst. rewrite add_eq_o in H2 by trivial; invert H2.
        rewrite fold_add; auto.
        remember (fold add_key ks2 ks1) as mks12.
        unfold add_key.
        cases ( mks12 $? k).
        * cases ( v ==kk k0 ); subst; eauto.
          cases (keys_compatible v k0); eauto.
          cases (keyType k0 ==kt AsymKey true); eauto.
          rewrite not_find_in_iff in H; eapply merge_keys_merges in Heq; eauto; destruct Heq; contra_map_lookup.
          rewrite add_eq_o; auto.
          rewrite not_find_in_iff in H; eapply merge_keys_merges in Heq; eauto; destruct Heq; contra_map_lookup.
        * rewrite add_eq_o; auto.

      + subst; rewrite add_neq_o in H2 by assumption; eauto.
        rewrite fold_add; auto.
        remember (fold add_key ks2 ks1) as mks12.
        unfold add_key.
        cases ( mks12 $? x).
        * cases ( e ==kk k0 ); eauto.
          cases (keys_compatible e k0); eauto.
          cases (keyType k0 ==kt AsymKey true); eauto.
          rewrite add_neq_o by assumption; eauto.
          rewrite remove_neq_o by assumption; eauto.
        * rewrite add_neq_o by assumption; eauto.

  Qed.

  Hint Resolve merge_keys_adds_ks1 merge_keys_adds_ks2.

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

  Hint Resolve keys_compatible_reflexive keys_compatible_symmetric.

  Lemma merge_keys_ok :
    forall ks2 k_id k1 k2 ks ks1,
        ks = ks1 $k++ ks2
      -> ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> k1.(keyId) = k_id
      -> k2.(keyId) = k_id
      -> keys_compatible k1 k2 = true
      -> ( ks $? k_id = Some k1 /\ k1 = k2 )
      \/ ( ks $? k_id = Some k1 /\ k1.(keyType) = AsymKey true )
      \/ ( ks $? k_id = Some k2 /\ k1.(keyType) <> AsymKey true ).
  Proof.
    unfold merge_keys.
    induction ks2 using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst.
      eapply IHks2_1; eauto.

    - rewrite empty_o in H1; invert H1.

    - rewrite fold_add in H0; auto.
      remember (fold add_key ks2 ks1) as mks12.
      case (x ==n k_id); intros.
      + rewrite add_eq_o in H2 by assumption. inversion H2. rewrite e0 in *; clear e0. rewrite H7 in *; clear H7.
        clear H2.
        apply not_find_in_iff in H.
        eapply merge_keys_adds_ks1 in Heqmks12; eauto.
        unfold add_key in H0. rewrite Heqmks12 in H0.
        cases (k2 ==kk k1).
        * subst; intuition idtac.
        * rewrite keys_compatible_symmetric in H5. rewrite H5 in H0; cases (keyType k1 ==kt AsymKey true).
          subst; intuition idtac.
          subst. rewrite add_eq_o by trivial. intuition idtac.

      + rewrite add_neq_o in H2 by assumption.
        apply add_key_results in H0.
        intuition idtac;
          subst; ( (rewrite add_neq_o by assumption) || (rewrite remove_neq_o by assumption) || idtac );
            eapply IHks2; eauto.

  Qed.

  Lemma merge_keys_left_identity :
    forall ks,
      $0 $k++ ks = ks.
  Proof.
    unfold merge_keys.
    induction ks using P.map_induction_bis; intros.

    - apply map_eq_Equal in H; subst; auto.
    - apply fold_Empty; eauto using empty_Empty.
    - rewrite fold_add; auto.
      rewrite IHks; clear IHks.
      unfold add_key. apply not_find_in_iff in H. rewrite H; trivial.
  Qed.
    
  Lemma merge_keys_right_identity :
    forall ks,
      ks $k++ $0 = ks.
  Proof.
    unfold merge_keys; intros.
    rewrite fold_Empty; eauto using empty_Empty.
  Qed.

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
      case (x ==n k); intros; subst.
      + rewrite add_eq_o in H1 by trivial; invert H1.
      + rewrite add_neq_o in H1 by auto.
        remember (fold add_key ks2 ks1) as ind.
        unfold add_key.
        cases (ind $? x); eauto.
        * cases (e ==kk k0); subst; eauto.
          cases (keys_compatible e k0); subst; eauto.
            cases (keyType k0 ==kt AsymKey true); eauto. rewrite add_neq_o; eauto.
            rewrite remove_neq_o by auto; eauto.
        * rewrite add_neq_o by assumption; subst; eauto.
  Qed.

  Lemma merge_keys_adds_one_unless_incompatible :
    forall ks2 ks1 k_id k1 k2,
        ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> (ks1 $k++ ks2) $? k_id = Some k1
      \/ (ks1 $k++ ks2) $? k_id = Some k2
      \/ keys_compatible k1 k2 = false.
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; auto.
    - invert H0.
    - unfold merge_keys.
      case (x ==n k_id); intros; subst.
      + rewrite add_eq_o in H1 by trivial; invert H1.
        rewrite fold_add; auto.
        remember (fold add_key ks2 ks1) as ind.
        unfold add_key.
        cases (ind $? k_id); eauto.
        * cases (k2 ==kk k); subst; eauto.
          rewrite not_find_in_iff in H; erewrite merge_keys_adds_ks1 in Heq; eauto; invert Heq.
          cases (keys_compatible k2 k); subst; eauto.
          cases (keyType k ==kt AsymKey true); eauto.
          rewrite !add_eq_o; intuition idtac.
        * rewrite add_eq_o by trivial; intuition idtac.
            
      + rewrite fold_add; eauto.
        rewrite add_neq_o in * by assumption.
        remember (fold add_key ks2 ks1) as ind.
        unfold add_key.
        cases (ind $? x); eauto.
        * cases (e ==kk k); subst; eauto.
          cases (keys_compatible e k); subst; eauto.
            cases (keyType k ==kt AsymKey true); eauto. rewrite !add_neq_o; eauto.
            rewrite remove_neq_o by auto; eauto.
        * rewrite !add_neq_o; subst; eauto.
  Qed.

  Lemma merge_keys_adds_one_unless_incompatible' :
    forall ks2 ks1 ks k_id k1 k2,
        ks1 $? k_id = Some k1
      -> ks2 $? k_id = Some k2
      -> ks = ks1 $k++ ks2
      -> ( ks $? k_id = Some k1 /\ k1 = k2)
      \/ ( ks $? k_id = Some k1 /\ k1 <> k2 /\ keys_compatible k1 k2 = true /\ k1.(keyType) = AsymKey true )
      \/ ( ks $? k_id = Some k2 /\ k1 <> k2 /\ keys_compatible k1 k2 = true /\ k1.(keyType) <> AsymKey true )
      \/ ( ks $? k_id = None /\ keys_compatible k1 k2 = false).
  Proof.
    induction ks2 using P.map_induction_bis; intros.
    - apply map_eq_Equal in H; subst; eauto.
    - invert H0.
    - subst; unfold merge_keys.
      case (x ==n k_id); intros; subst.
      + rewrite add_eq_o in H1 by trivial; invert H1.
        rewrite fold_add; auto.
        remember (fold add_key ks2 ks1) as ind.
        unfold add_key.
        cases (ind $? k_id); eauto.
        * rewrite not_find_in_iff in H; erewrite merge_keys_adds_ks1 in Heq; eauto; invert Heq.
          cases (k2 ==kk k); subst; eauto.
          cases (keys_compatible k2 k); subst; eauto.

          assert (k <> k2) by (unfold not; intros ?SYM; symmetry in SYM; auto).
          rewrite keys_compatible_symmetric in Heq.
          cases (keyType k ==kt AsymKey true); eauto.
            remember (ks1 $k++ ks2) as ks. unfold merge_keys in Heqks. rewrite <- Heqks. eapply merge_keys_adds_ks1 in Heqks; eauto.
            intuition idtac.
            rewrite !add_eq_o; intuition idtac.
            rewrite remove_eq_o by trivial; rewrite keys_compatible_symmetric; intuition idtac.
        * rewrite not_find_in_iff in H; erewrite merge_keys_adds_ks1 in Heq; eauto; invert Heq.
            
      + rewrite fold_add; eauto.
        rewrite add_neq_o in * by assumption.
        remember (fold add_key ks2 ks1) as ind.
        unfold add_key.
        cases (ind $? x); eauto.
        * cases (e ==kk k); subst; eauto.
          cases (keys_compatible e k); subst; eauto.
            cases (keyType k ==kt AsymKey true); eauto. rewrite !add_neq_o; eauto.
            rewrite remove_neq_o by auto; eauto.
        * rewrite !add_neq_o; subst; eauto.
  Qed.

  Lemma merge_keys_symmetric :
    forall ks1 ks2,
      ks1 $k++ ks2 = ks2 $k++ ks1.
  Proof.
    intros.

    apply map_eq_Equal; unfold Equal; subst; intros.

    cases (ks1 $? y); cases (ks2 $? y).
    - remember (ks1 $k++ ks2) as ks12. remember (ks2 $k++ ks1) as ks21.
      pose proof (merge_keys_adds_one_unless_incompatible' _ _ _ Heq Heq0 Heqks12).
      pose proof (merge_keys_adds_one_unless_incompatible' _ _ _ Heq0 Heq Heqks21).

      (repeat match goal with
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H1 : keys_compatible ?k1 ?k2 = false, H2 : keys_compatible ?k2 ?k1 = true |- _ ] =>
                rewrite keys_compatible_symmetric in H1; rewrite H1 in H2; invert H2
              | [ H : keys_compatible ?k ?k = false |- _ ] => idtac k; unfold keys_compatible in H
              end); subst;
        rewrite H;
        rewrite H0;
        eauto.
      
      Ltac discharge_keys_comp_sym_false :=
        repeat match goal with
               | [ H : keys_compatible ?k ?k = false |- _ ] => idtac k; unfold keys_compatible in H
               | [ H : (if ?n ==n ?n then _ else _) = _ |- _ ]    => idtac n; cases (n ==n n); try contradiction
               | [ H : (if ?ku ==ku ?ku then _ else _) = _  |- _ ] => cases (ku ==ku ku); try contradiction
               | [ H : key_type_same _ _ = _ |- _ ] => unfold key_type_same in H
               | [ H : match ?m with _ => _ end = _ |- _ ] => cases m; discriminate
               end.

      discharge_keys_comp_sym_false.

      unfold keys_compatible in H5.
      cases (keyId k ==n keyId k0 ); try discriminate.
      cases (keyUsage k ==ku keyUsage k0); try discriminate.
      unfold key_type_same in H5; cases (keyType k); cases (keyType k0); try discriminate.
      cases has_private_access; cases has_private_access0; try discriminate.
      assert (k = k0); destruct k; destruct k0; simpl in *; subst; eauto.

      unfold keys_compatible in H5.
      cases (keyId k ==n keyId k0 ); try discriminate.
      cases (keyUsage k ==ku keyUsage k0); try discriminate.
      unfold key_type_same in H5; cases (keyType k); cases (keyType k0); try discriminate.
      assert (k = k0); destruct k; destruct k0; simpl in *; subst; eauto.
      cases has_private_access; cases has_private_access0; try discriminate; try contradiction.
      assert (k = k0); destruct k; destruct k0; simpl in *; subst; eauto.

      discharge_keys_comp_sym_false.

    - erewrite (merge_keys_adds_ks1); eauto.
      erewrite (merge_keys_adds_ks2); eauto.
    - erewrite (merge_keys_adds_ks2); eauto.
      erewrite (merge_keys_adds_ks1); eauto.
    - rewrite merge_keys_adds_no_new_keys; eauto.
      rewrite merge_keys_adds_no_new_keys; eauto.
  Qed.

  Lemma merge_keys_transitive :
    forall ks3 ks1 ks2,
      ks1 $k++ ks2 $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Proof.
    induction ks3 using P.map_induction_bis; intros.

    Hint Extern 1 (~ In _ _) => apply not_find_in_iff.

    - apply map_eq_Equal in H; subst; eauto.
    - rewrite !merge_keys_right_identity; trivial.
    - apply map_eq_Equal; unfold Equal; subst; intros.
      unfold merge_keys. rewrite fold_add; auto.
      rewrite fold_add; eauto.
      remember (fold add_key ks2 ks1) as mk12.
      remember (fold add_key ks3 ks2) as mk23.
      remember (fold add_key ks3 mk12) as mk123.
      unfold add_key at 1; unfold add_key at 2.
      specialize (IHks3 ks1 ks2); unfold merge_keys in IHks3. rewrite <- Heqmk12, <- Heqmk23, <- Heqmk123 in IHks3.

      case (y ==n x); intros; cases (mk123 $? x); cases (mk23 $? x); (try (rewrite e0 in *; clear e0)).

      + admit.

      + cases (e ==kk k). rewrite e0 in *; clear e0.
        rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (k ==kk k); eauto. contradiction.
        cases (keys_compatible e k); eauto.
        cases (keyType k ==kt AsymKey true).
        rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); eauto. rewrite Heq1. rewrite e0; simpl. rewrite Heq. trivial.

        rewrite fold_add; eauto; rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); eauto. rewrite e0; clear e0; rewrite add_eq_o; eauto.
        rewrite Heq1. cases (keyType k ==kt AsymKey true); eauto. contradiction.

        rewrite fold_add; eauto; rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); try contradiction. rewrite Heq1. trivial.

      + admit.

      + rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. trivial. 

      + admit.

      + cases (e ==kk k). rewrite e0 in *; clear e0.
        rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (k ==kk k); eauto. contradiction.
        cases (keys_compatible e k); eauto.
        cases (keyType k ==kt AsymKey true).
        rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); eauto. rewrite Heq1. rewrite e0; simpl. trivial.

        rewrite fold_add; eauto; rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); eauto. contradiction.
        rewrite Heq1. cases (keyType k ==kt AsymKey true); eauto. rewrite add_neq_o; eauto.

        rewrite fold_add; eauto; rewrite <- IHks3.
        unfold add_key. rewrite Heq. cases (e ==kk k); try contradiction. rewrite Heq1. trivial.

      + admit.

      + rewrite fold_add; eauto.
        rewrite <- IHks3.
        unfold add_key. rewrite Heq. trivial.

  Admitted.

  Lemma findUserKeys_fold_fn_proper :
    forall {A},
    Morphisms.Proper
      (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq)))
      (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
    unfold Morphisms.Proper, Morphisms.respectful; intros; simpl; subst; trivial.
  Qed.

  Lemma findUserKeys_transpose :
    forall {A},
      transpose_neqkey eq (fun (_ : NatMap.key) (u : user_data A) (ks : keys) => ks $k++ key_heap u).
  Proof.
    unfold transpose_neqkey; intros.
    rewrite merge_keys_symmetric with (ks1 := a).
    rewrite merge_keys_symmetric with (ks1 := a $k++ key_heap e).
  Admitted.


  Lemma compatible_merge_keys_maintains_keys :
    forall ks ks1 ks2,
        key_heaps_compatible ks1 ks2
      -> ks = ks1 $k++ ks2
      -> (forall k_id k,
          ks1 $? k_id = Some k
          -> exists k', ks $? k_id = Some k' /\ keys_compatible k k' = true)
      /\ (forall k_id k,
          ks2 $? k_id = Some k
          -> exists k', ks $? k_id = Some k' /\ keys_compatible k k' = true).
  Proof.
    unfold merge_keys, key_heaps_compatible, keys_good.
    intros.

    Ltac split_ands := 
      repeat match goal with
             | [ H : _ /\ _ |- _ ] => destruct H
             end.

    Ltac split_ors :=
      repeat match goal with
             | [ H : _ \/ _ |- _ ] => destruct H
             end.

    split_ands; split; intros.

    - case_eq (ks2 $? k_id); intros;
        [ eapply merge_keys_ok in H0; eauto | ];
        split_ands; eauto;
          split_ors; split_ands; eauto.

    - case_eq (ks1 $? k_id); intros;
        [ eapply merge_keys_ok in H0; eauto | ];
        split_ands; eauto;
          split_ors; split_ands; eauto.
  Qed.

  (* TODO move to Maps.v *)
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

  Lemma merge_keys_assoc :
    forall ks1 ks2 ks3,
      (ks1 $k++ ks2) $k++ ks3 = ks1 $k++ (ks2 $k++ ks3).
  Admitted.

  Lemma find_user_keys_includes_user_keys :
    forall {A B} (U : universe A B) u_id u_d,
      U.(users) $? u_id = Some u_d
      -> (findUserKeys U.(users)) = u_d.(key_heap) $k++ (findUserKeys (U.(users) $- u_id)).
  Proof.
    unfold findUserKeys; intros.
    generalize H.
    apply P.fold_rec_bis; intros.
    - apply map_eq_Equal in H0; subst; eauto.
    - invert H0.
    - case ( k ==n u_id ); intros.
      + subst. admit.
      + rewrite add_neq_o in H3; eauto.
        rewrite add_remove_neq by assumption.
        rewrite fold_add; auto.
        specialize (H2 H3).

        rewrite <- merge_keys_assoc.
        rewrite H2.
        trivial.

  Admitted.

  Lemma find_user_keys_universe_user :
    forall {A B} (U : universe A B) u_id u_d,
        adv_no_honest_keys (findUserKeys U.(adversary)) (findUserKeys U.(users))
      -> U.(users) $? u_id = Some u_d
      -> key_heaps_compatible (findUserKeys U.(adversary)) (findUserKeys U.(users))
      -> adv_no_honest_keys (findUserKeys U.(adversary)) u_d.(key_heap).
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
  | MkCryptoKey _ _ SymKey         => Some (SigCipher c_id k.(keyId) m)
  | MkCryptoKey _ _ (AsymKey true) => Some (SigCipher c_id k.(keyId) m)
  | _       => None
  end.

Definition canVerifySignature {A} (cs : ciphers)(usrDat : user_data A)(c_id : cipher_id) : Prop :=
  forall t (m : message t) k_id k ,
    cs $? c_id = Some (SigCipher c_id k_id m)
    (*  Make sure that the user has access to the key.  If we are doing asymmetric signatures,
        we only need the public part of the key, so no additional checks necessary! *)
    /\ usrDat.(key_heap) $? k_id = Some k.

Definition buildUniverse {A B}
           (usrs : honest_users A) (advs : adversaries B) (cs : ciphers)
           (u_id : user_id) (userData : user_data A) : universe A B :=
  {| users        := usrs $+ (u_id, userData)
   ; adversary    := advs
   ; all_ciphers  := cs
   |}.

Definition buildUniverseAdv {A B}
           (usrs : honest_users A) (advs : adversaries B) (cs : ciphers)
           (u_id : user_id) (userData : user_data B) : universe A B :=
  {| users        := usrs
   ; adversary    := advs $+ (u_id, userData)
   ; all_ciphers  := cs
   |}.

Definition addAdversaries {A B} (U : universe A B) (advs : adversaries B) :=
  {| users       := U.(users)
   ; adversary   := U.(adversary) $++ advs
   ; all_ciphers := U.(all_ciphers)
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
| Input  t (msg : message t) (pat : msg_pat) (u_id : user_id) (uks : keys)
| Output t (msg : message t) (u_id : user_id)
.

Definition rlabel := @label action.

Definition action_adversary_safe (advk : adversary_knowledge) (a : action) : bool :=
  match a with
  | Input _ pat _ _ => negb (msg_pattern_spoofable advk pat)
  | Output _ _      => true
  end.

Definition data_step0 (A B C : Type) : Type :=
  honest_users A * adversaries B * ciphers * keys * queued_messages * user_cmd C.

Definition build_data_step {A B C} (U : universe A B) (u_data : user_data C) : data_step0 A B C :=
  (U.(users), U.(adversary), U.(all_ciphers), u_data.(key_heap), u_data.(msg_heap), u_data.(protocol)).

(* Labeled transition system *)
Inductive step_user : forall A B C, user_id -> rlabel -> data_step0 A B C -> data_step0 A B C -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {B r r'} u_id (usrs usrs' : honest_users r') (adv adv' : adversaries B)
                     lbl cs cs' qmsgs qmsgs' ks ks' (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user u_id lbl (usrs, adv, cs, ks, qmsgs, cmd1) (usrs', adv', cs', ks', qmsgs', cmd1')
    -> step_user u_id lbl (usrs, adv, cs, ks, qmsgs, Bind cmd1 cmd2) (usrs', adv', cs', ks', qmsgs', Bind cmd1' cmd2)
| StepBindProceed : forall {B r r'} u_id (usrs : honest_users r) (adv : adversaries B) cs ks qmsgs (v : r') (cmd : r' -> user_cmd r),
    step_user u_id Silent (usrs, adv, cs, ks, qmsgs, Bind (Return v) cmd) (usrs, adv, cs, ks, qmsgs, cmd v)

| StepGen : forall {A B} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs n,
    step_user u_id Silent (usrs, adv, cs, ks, qmsgs, Gen) (usrs, adv, cs, ks, qmsgs, Return n)

(* Comms  *)
| StepRecv : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks ks' qmsgs qmsgs' (msg : message t) msgs pat newkeys,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> msg_accepted_by_pattern cs pat msg
    -> step_user u_id (Action (Input msg pat u_id ks))
                (usrs, adv, cs, ks , qmsgs , Recv pat)
                (usrs, adv, cs, ks', qmsgs', Return msg)

| StepRecvDrop : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs qmsgs' (msg : message t) pat msgs,
      qmsgs = Exm msg :: msgs (* we have a message waiting for us! *)
    -> qmsgs' = msgs
    -> ~ msg_accepted_by_pattern cs pat msg
    -> step_user u_id Silent (* Error label ... *)
                (usrs, adv, cs, ks, qmsgs , Recv pat)
                (usrs, adv, cs, ks, qmsgs', Return msg)

(* Augment attacker's keys with those available through messages sent,
 * including traversing through ciphers already known by attacker, etc.
 *)
| StepSend : forall {A B} {t} u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B)
               cs ks qmsgs rec_u_id rec_u newkeys (msg : message t),
    findKeys msg = newkeys
    -> adv' = addUserKeys adv newkeys
    -> usrs $? rec_u_id = Some rec_u
    -> usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                  ; protocol := rec_u.(protocol) 
                                  ; msg_heap := rec_u.(msg_heap) ++ [Exm msg]  |})
    -> step_user u_id (Action (Output msg u_id))
                (usrs , adv , cs, ks, qmsgs, Send rec_u_id msg)
                (usrs', adv', cs, ks, qmsgs, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs cs' ks qmsgs (msg : message t) k__sign k__enc k__signid k__encid c_id cipherMsg,
      keyId k__sign = k__signid
    -> keyId k__enc = k__encid
    -> ks $? k__signid = Some k__sign
    -> ks $? k__encid = Some k__enc
    -> ~ In c_id cs
    -> encryptMessage k__sign k__enc msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user u_id Silent
                (usrs, adv, cs , ks, qmsgs, SignEncrypt k__sign k__enc msg)
                (usrs, adv, cs', ks, qmsgs, Return (SignedCiphertext c_id))

| StepDecrypt : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks ks' qmsgs (msg : message t) k__signid k__sign k__encid c_id newkeys,
      cs $? c_id = Some (SigEncCipher c_id k__signid k__encid msg)
    -> ( ks $? k__encid = Some (MkCryptoKey k__encid Encryption (AsymKey true)) (* check we have access to private key *)
      \/ ks $? k__encid = Some (MkCryptoKey k__encid Encryption SymKey) )
    -> ks $? k__signid = Some k__sign
    (* -> k.(keyId) = k_id *)
    -> findKeys msg = newkeys
    -> ks' = ks $k++ newkeys
    -> step_user u_id Silent
                (usrs, adv, cs, ks , qmsgs, Decrypt (SignedCiphertext c_id))
                (usrs, adv, cs, ks', qmsgs, Return msg)

(* Signing / Verification *)
| StepSign : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs cs' ks qmsgs (msg : message t) k k_id c_id cipherMsg,
      keyId k = k_id
    -> ks $? k_id = Some k
    -> ~(In c_id cs)
    -> signMessage k msg c_id = Some cipherMsg
    -> cs' = cs $+ (c_id, cipherMsg)
    -> step_user u_id Silent
                (usrs, adv, cs , ks, qmsgs, Sign k msg)
                (usrs, adv, cs', ks, qmsgs, Return (Signature msg c_id))

| StepVerify : forall {A B} {t} u_id (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs (msg : message t) k_id k c_id,
    keyId k = k_id
    (* k is in your key heap *)
    -> ks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (SigCipher c_id k_id msg)
    (* -> findKeys msg = newkeys *)
    -> step_user u_id Silent
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
    -> step_user u_id lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverse usrs adv cs u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U lbl U'
| StepAdversary : forall U U' u_id userData usrs adv cs ks qmsgs lbl (cmd : user_cmd B),
    U.(adversary) $? u_id = Some userData
    -> step_user u_id lbl
                (build_data_step U userData)
                (usrs, adv, cs, ks, qmsgs, cmd)
    -> U' = buildUniverseAdv usrs adv cs u_id {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmd |}
    -> step_universe U Silent U'
.
