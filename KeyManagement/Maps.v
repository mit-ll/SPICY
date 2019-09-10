From Coq Require Import
  FSets.FMapList
  FSets.FMapFacts
  Structures.OrderedTypeEx
  Logic.ProofIrrelevance
  Program.Equality
.

Require Import
        MyPrelude
        Tactics.

Module Import NatMap := FMapList.Make(Nat_as_OT).
Module P := WProperties_fun Nat_as_OT NatMap.
Module F := P.F.

Export NatMap P F.

From Coq Require List.

Set Implicit Arguments.

Notation "$0" := (empty _).
Notation "m $+ ( k , v )" := (add k v m) (at level 50, left associativity).
Notation "m $- k" := (remove k m) (at level 50, left associativity).
Notation "m $? k" := (find k m) (at level 50, left associativity).


(* Infix "$<=" := includes (at level 90). *)

Definition merge_maps {V : Type} (m1 m2 : NatMap.t V) : NatMap.t V :=
  fold (fun k v m => m $+ (k,v) ) m1 m2.

Notation "m1 $++ m2" := (merge_maps m2 m1) (at level 50, left associativity).

Module Import OTF := OrderedType.OrderedTypeFacts OrderedTypeEx.Nat_as_OT.
Module Import OMF := FSets.FMapFacts.OrdProperties NatMap.

Ltac clean_map_lookups1 :=
  match goal with
  | [ H : Some _ = None   |- _ ] => invert H
  | [ H : None = Some _   |- _ ] => invert H
  | [ H : Some _ = Some _ |- _ ] => invert H
  | [ H : $0 $? _ = Some _ |- _ ] => invert H
  | [ H : _ $+ (?k,_) $? ?k = _ |- _ ] => rewrite add_eq_o in H by trivial
  | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by auto 2
  | [ H : context [ match _ $+ (?k,_) $? ?k with _ => _ end ] |- _ ] => rewrite add_eq_o in H by trivial
  | [ H : context [ match _ $+ (?k1,_) $? ?k2 with _ => _ end ] |- _ ] => rewrite add_neq_o in H by auto 2
  | [ |- context[_ $+ (?k,_) $? ?k] ] => rewrite add_eq_o by trivial
  | [ |- context[_ $+ (?k1,_) $? ?k2] ] => rewrite add_neq_o by auto
  | [ |- context[_ $- ?k $? ?k] ] => rewrite remove_eq_o by trivial
  | [ |- context[_ $- ?k1 $? ?k2] ] => rewrite remove_neq_o by auto
  | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
  | [ H1 : ?m $? ?k = _ , H2 : ?m $? ?k = _ |- _] => rewrite H1 in H2
  end.

Ltac contra_map_lookup :=
  repeat
    match goal with
    (* | [ H1 : ?ks1 $? ?k = _, H2 : ?ks2 $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2 *)
    | [ H : ?ks $? ?k = ?v -> _, ARG : ?ks $? ?k = ?v |- _ ] => specialize (H ARG)
    | [ H1 : ?ks $? ?k = _, H2 : ?ks $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2
    | [ H : ?ks $? ?k = _ |- context [ ?ks $? ?k <> _] ] => unfold not; intros
    end; try discriminate.

Ltac clean_map_lookups :=
  (repeat clean_map_lookups1);
  try discriminate;
  try contra_map_lookup.

Ltac context_map_rewrites :=
  repeat
    match goal with
    | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H
    | [ H : context [ match ?matchee with _ => _ end ]
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    (* | [ H : match ?matchee with _ => _ end = _ *)
    (*  ,  H1 : ?matchee = _ |- _] => rewrite H1 in H *)
    end.

Section MapLemmas.

  Lemma lookup_split : forall V (m : NatMap.t V) k v k' v',
    (m $+ (k, v)) $? k' = Some v'
    -> (k' <> k /\ m $? k' = Some v') \/ (k' = k /\ v' = v).
  Proof.
    intros.
    case (eq_dec k k').
    - intros.
      subst.
      right; intuition.
      rewrite add_eq_o in H by auto.
      congruence.
    - intros. left.
      intuition.
      rewrite add_neq_o in H by auto.
      exact H.
  Qed.

  Lemma lookup_split' : forall V (m : NatMap.t V) k v,
      m $? k = Some v
      -> fold (fun k' v' p => p \/ (k = k' /\ v = v')) m False.
  Proof.
    intros.
    (* rewrite <- find_mapsto_iff in H. *)
    revert dependent H.
    apply P.fold_rec; intros.
    
    - rewrite <- find_mapsto_iff in H0.
      specialize (H k v). contradiction.
      
    - case (eq_dec k k0).
      + intros. subst.
        right; intuition.
        unfold Add in H1.
        specialize (H1 k0). rewrite H3 in H1.
        symmetry in H1; rewrite <- find_mapsto_iff in H1.
        rewrite add_mapsto_iff in H1.
        destruct H1; intuition.
      + intros. left. apply H2; auto.
        (* rewrite <- find_mapsto_iff in H3. unfold Add in *. *)
        specialize (H1 k). rewrite H3 in H1. symmetry in H1.
        rewrite <- find_mapsto_iff in H1.
        rewrite add_mapsto_iff in H1.
        destruct H1; intuition idtac.
        symmetry in H4; contradiction.
        apply find_mapsto_iff; auto.
  Qed.

  Lemma lookup_some_implies_in : forall V (m : NatMap.t V) k v,
      m $? k = Some v
      -> List.In (k,v) (to_list m).
  Proof.
    intros.

    rewrite <- find_mapsto_iff in H.
    rewrite elements_mapsto_iff in H.
    rewrite InA_alt in H.
    destruct H. destruct H.
    unfold to_list.

    unfold eq_key_elt, Raw.PX.eqke in H; simpl in H.
    destruct H.
    subst.
    rewrite (surjective_pairing x) in H0.
    assumption.
  Qed.

  Lemma map_eq_fields_eq :
    forall {V} (th th' : Raw.t V) s s',
        th = th'
      -> {| this := th ; sorted := s |} = {| this := th' ; sorted := s' |}.
  Proof.
    intros; subst; f_equal; apply proof_irrelevance.
  Qed.

  Lemma map_eq_elements_eq :
    forall {V} (m m' : NatMap.t V),
      elements m = elements m'
      -> m = m'.
  Proof.
    intros. destruct m. destruct m'.
    simpl in *;
      eapply map_eq_fields_eq;
      eauto.
  Qed.

  Lemma Equal_hd_tl :
    forall {V} (m1 m1' m2 m2' : t V) x xs y ys sx sy,
        m1 = {| this := x :: xs ; sorted := sx |}
      -> m2 = {| this := y :: ys ; sorted := sy |}
      -> Equal m1 m2
      -> m1' = m1 $- fst x
      -> m2' = m2 $- fst y
      -> x = y /\ Equal m1' m2'.
  Proof.
    intros.

    destruct x as [n1 v1]; destruct y as [n2 v2]; simpl in *.

    assert ( (n1,v1) = (n2,v2) ).
    - unfold Equal in H1; subst; simpl in *.
      unfold Equal in H1.
      pose proof H1 as HH1; pose proof H1 as HH2.
      specialize (HH1 n1); specialize (HH2 n2).
      unfold find, Raw.find in HH1, HH2; simpl in *.
      
      pose proof (Raw.MX.elim_compare_eq) as EQn1.
      pose proof (Raw.MX.elim_compare_eq) as EQn2.
      specialize (EQn1 n1 n1 (eq_refl n1)); specialize (EQn2 n2 n2 (eq_refl n2)).
      destruct EQn1, EQn2. rewrite H in *; rewrite H0 in *; clear x H x0 H0.

      cases (OrderedTypeEx.Nat_as_OT.compare n1 n2).
      + invert HH1.
      + unfold OrderedTypeEx.Nat_as_OT.eq in e; invert HH1; trivial.
      + cases (OrderedTypeEx.Nat_as_OT.compare n2 n1).
        * invert HH2.
        * unfold OrderedTypeEx.Nat_as_OT.eq in e; invert HH2; trivial. (* hokey proof -- shorter than deriving the contradiction *)
        * unfold OrderedTypeEx.Nat_as_OT.lt in l; unfold OrderedTypeEx.Nat_as_OT.lt in l0.
          assert (LT : n1 < n2) by assumption; apply lt_le in LT; contradiction.

    - constructor; auto.

      subst.

      pose proof (Raw.MX.elim_compare_eq) as EQn2.
      specialize (EQn2 n2 n2 (eq_refl n2)).
      destruct EQn2.
      unfold Equal in *; simpl in *.

      intro k; invert H4.
      case (k ==n n2); intros; subst.
      + rewrite remove_eq_o by apply eq_refl.
        rewrite remove_eq_o by apply eq_refl.
        auto.
      + rewrite remove_neq_o by auto.
        rewrite remove_neq_o by auto.
        specialize (H1 k); assumption.
  Qed.

  Lemma remove_hd :
    forall {V} n (v : V) xs sx hdrel,
      {| this := (n,v) :: xs ; sorted := Sorted.Sorted_cons sx hdrel |} $- n = {| this := xs ; sorted := sx |}.
  Proof.
    intros.
    unfold remove, Raw.remove. simpl.
    eapply map_eq_elements_eq; simpl.

    pose proof (Raw.MX.elim_compare_eq) as EQn; specialize (EQn n n (eq_refl n)); destruct EQn.
    rewrite H; trivial.
  Qed.

  Lemma map_eq_Equal :
    forall {V} (m m' : t V),
      Equal m m'
      -> m = m'.
  Proof.

    intro V.
    intro m.
    destruct m as [l sl].
    generalize dependent l.
    induction l; intros.

    - unfold Equal in H. simpl in *.
      symmetry in H.
      apply map_eq_elements_eq; simpl.

      destruct m'; simpl in *.
      cases this0.
      + trivial.
      + intros. destruct p. specialize (H n).
        unfold find, Raw.find in H; simpl in H.
        (* assert (n = n) by trivial. *)
        
        pose proof (Raw.MX.elim_compare_eq).
        specialize (H0 n n (eq_refl n)).
        destruct H0.
        rewrite H0 in H.
        invert H.

    - simpl.
      destruct m'; cases this0; simpl in *.
      + destruct a as [n v].
        unfold Equal in H; specialize (H n).
        unfold find, Raw.find in H; simpl in H.
        pose proof (Raw.MX.elim_compare_eq) as P; specialize (P n n (eq_refl n)); destruct P.
        rewrite H0 in H; invert H.

      + destruct a as [n1 v1]; destruct p as [n2 v2].
        eapply Equal_hd_tl in H; eauto.
        destruct H; invert H.
        unfold Equal in H0; simpl in *.

        dependent destruction sl.
        dependent destruction sorted0.
        specialize (IHl sl {| this := this0 ; sorted := sorted0 |}).

        assert (tlEQ : Equal {| this := l ; sorted := sl |} {| this := this0 ; sorted := sorted0 |} ).
        * unfold Equal; intro k; specialize (H0 k); do 2 rewrite remove_hd in H0; assumption.
        * specialize (IHl tlEQ).
          dependent destruction IHl.
          eapply map_eq_elements_eq; simpl; f_equal.
  Qed.

  Lemma add_empty_idempotent :
    forall V (m : NatMap.t V),
      m $++ $0 = m.
  Proof.
    intros; unfold merge_maps, fold, Raw.fold; simpl; auto.
  Qed.

  Lemma empty_add_idempotent : 
    forall V (m : NatMap.t V),
      $0 $++ m = m.
  Proof.
    intros; unfold merge_maps.
    apply P.fold_rec.
    - intros.
      apply elements_Empty in H.
      apply map_eq_elements_eq. auto.
      
    - intros. subst.
      apply map_eq_Equal. unfold Equal; intros.
      unfold P.Add in H1. specialize (H1 y). symmetry; auto.
  Qed.

  Lemma empty_Empty :
    forall {V}, Empty (elt:=V) $0.
  Proof.
    intros.
    unfold Empty, Raw.Empty, Raw.PX.MapsTo, not; intros.
    invert H.
  Qed.

  Lemma Empty_eq_empty :
    forall v m,
      Empty (elt:=v) m
      -> $0 = m.
  Proof.
    intros.
    apply elements_Empty in H.
    apply map_eq_elements_eq. auto.
  Qed.

  Lemma map_add_eq :
    forall {V} (m : NatMap.t V) k v1 v2,
      m $+ (k,v1) $+ (k,v2) = m $+ (k,v2).
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros.
    cases (k ==n y); subst.
    - rewrite !add_eq_o; trivial.
    - rewrite !add_neq_o; trivial.
  Qed.

  Lemma map_add_remove_eq :
    forall {V} (m : NatMap.t V) k1 v1,
      m $+ (k1, v1) $- k1 = m $- k1.
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    case (k1 ==n y); intros; subst.
    - rewrite !remove_eq_o; auto.
    - rewrite !remove_neq_o, add_neq_o; auto.
  Qed.

  Lemma map_add_remove_neq :
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

  Lemma map_ne_swap :
    forall {V} (m : NatMap.t V) k v k' v',
      k <> k'
      -> m $+ (k,v) $+ (k',v') = m $+ (k',v') $+ (k,v).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; auto; contradiction.
  Qed.

  Lemma map_remove_not_in_idempotent :
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

  (* Lemma fold_over_empty : *)
  (*   forall {V} (m : NatMap.t V), *)
  (*     fold (fun k v a => *)
  (*             if match v with *)
  (*                | _ => true *)
  (*                end then a $+ (k,v) else a) m $0 = m. *)
  (* Proof. *)

  (*   intros. *)
  (*   apply P.fold_rec. *)
  (*   - intros; simpl. eapply map_eq_Equal; unfold Equal; intros. *)
  (*     rewrite empty_o. admit. *)
  (*   - intros; subst. *)
  (*     apply map_eq_Equal; unfold Equal; intros. *)
  (*     unfold P.Add in H1. specialize (H1 y). symmetry; auto. *)

  (* Admitted. *)

End MapLemmas.

Ltac Equal_eq :=
  repeat
    match goal with
    | [ H : Equal _ _ |- _] => apply map_eq_Equal in H; subst
    end.

Ltac m_equal :=
  repeat match goal with
         (* | [ |- context[find ?k (add ?k' _ _) ] ] => idtac k; idtac k'; case (eq_dec k k'); intro *)
         | [ |- context[find ?k (add ?k _ _) ] ]  =>
           rewrite add_eq_o by (simple apply @eq_refl)
         | [ |- context[find ?k (add ?k' _ _) ] ] =>
           rewrite add_neq_o by ( (unfold not; intros ?SIMPLEQ; invert SIMPLEQ) || intuition idtac )
         | [ |- context[$0 $++ _ ] ] => rewrite empty_add_idempotent
         | [ |- context[_ $++ $0 ] ] => rewrite add_empty_idempotent
         | [ |- (add _ _ _) = _ ] => normalize_set
         | [ |- (add _ _ _) = _ ] => unfold add, Raw.add; simpl
         | [ |- {| this := _ ; sorted := _ |} = _ ] => eapply map_eq_fields_eq
         | [ H : Empty ?m |- $0 = ?m ] => eapply Empty_eq_empty; exact H
         | [ H : Empty ?m |- ?m = $0 ] => symmetry
         | [ |- empty _ = _ ] => unfold empty, Raw.empty, remove, Raw.remove; simpl
         end.

Lemma remove_not_in_map_idempotent :
  forall V (m : NatMap.t V) k,
    m $? k = None
    -> m $- k = m.
Proof.
  intros; apply map_eq_Equal; unfold Equal; intros;
    destruct (k ==n y); subst; context_map_rewrites; clean_map_lookups; trivial.
Qed.

Ltac maps_equal :=
  apply map_eq_Equal; unfold Equal; intros;
  repeat
    match goal with
    | [ |- context [ _ $+ (?k1,?v) $? ?k2 ]] => progress (clean_map_lookups) || destruct (k1 ==n k2); subst
    end; trivial.

Ltac canonicalize_map m :=
  match m with
  | context [ add ?k ?v ?m1 ] =>
    match m1 with
    | context [ add k _ _ ] =>
      assert ( CANON : m = m $- k $+ (k,v) ); [ 
        maps_equal
      | repeat
          (rewrite map_add_remove_eq in CANON by trivial)
        || (rewrite map_add_remove_neq in CANON by eauto)
        || (rewrite remove_not_in_map_idempotent in CANON by eauto)
      ]; rewrite !CANON;
      match type of CANON with
      | _ = ?m' => clear CANON; try canonicalize_map m'
      end
    end
  end.

Lemma canonicalize_map_test1 :
  forall V (m : NatMap.t V) k1 k2 (v1 v2 v3 : V),
    k1 <> k2
    -> m $? k1 = None
    -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) = m $+ (k2,v2) $+ (k1,v3).
Proof.
  intros.
  match goal with
  | [ |- ?m = _ ] => canonicalize_map m
  end; trivial.
Qed.

Lemma canonicalize_map_test2 :
  forall V (m : NatMap.t V) k1 k2 k3 (v1 v2 v3 v4 : V),
    k1 <> k2
    -> k1 <> k3
    -> k2 <> k3
    -> m $? k1 = None
    -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) $+ (k3,v4) = m $+ (k2,v2) $+ (k1,v3) $+ (k3,v4).
Proof.
  intros.
  match goal with
  | [ |- ?m = _ ] => canonicalize_map m
  end; maps_equal.
Qed.

Lemma canonicalize_map_test3 :
  forall V (m : NatMap.t V) k1 k2 k3 (v1 v2 v3 v4 : V),
    k1 <> k2
    -> k1 <> k3
    -> k2 <> k3
    -> m $? k1 = None
    -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) $+ (k2,v4) $+ (k3,v4) = m $+ (k2,v4) $+ (k1,v3) $+ (k3,v4).
Proof.
  intros.
  match goal with
  | [ |- ?m = _ ] => canonicalize_map m
  end; maps_equal.
Qed.

Section MapPredicates.
  Variable V : Type.
  Variable P : V -> Prop.

  Inductive Forall_natmap : NatMap.t V -> Prop :=
  | Empty_Natmap : Forall_natmap $0
  | Add_Natmap k v (m : NatMap.t V) :
      P v
      -> Forall_natmap m
      -> Forall_natmap ( m $+ (k,v)).

  Lemma Forall_natmap_forall :
    forall m,
      Forall_natmap m <-> (forall k v, m $? k = Some v -> P v).
  Proof.
    split.
    - induction 1; contra_map_lookup; intros.
      cases (k ==n k0); intros; subst; clean_map_lookups; eauto.
    - induction m using P.map_induction_bis; intros; Equal_eq; eauto.
      + econstructor.
      + assert (Forall_natmap m).
        eapply IHm; intros.
        apply H0 with (k:=k); eauto.
        cases (x ==n k); subst; clean_map_lookups; eauto.

        econstructor; eauto.
        eapply H0 with (k := x); clean_map_lookups; auto.
  Qed.

  Lemma Forall_natmap_in_prop :
    forall k v m,
      Forall_natmap m
      -> m $? k = Some v
      -> P v.
  Proof.
    intros.
    rewrite Forall_natmap_forall in H; eauto.
  Qed.

  Lemma Forall_natmap_in_prop_add :
    forall k v m,
      Forall_natmap (m $+ (k,v))
      -> P v.
  Proof.
    intros.
    eapply Forall_natmap_in_prop with (k:=k); eauto; clean_map_lookups; trivial.
  Qed.

  Lemma Forall_natmap_split :
    forall k v m,
      Forall_natmap (m $+ (k,v))
      -> ~ In k m
      -> Forall_natmap m
      /\ P v.
  Proof.
    intros.
    rewrite Forall_natmap_forall in *; intros.
    assert (P v) by (eapply H with (k0:=k); clean_map_lookups; trivial).
    split; auto; intros.
    cases (k ==n k0); subst; clean_map_lookups.
    eapply H with (k0:=k0); clean_map_lookups; trivial.
  Qed.

End MapPredicates.

