From Coq Require Import
  FSets.FMapList
  FSets.FMapFacts
  Structures.OrderedTypeEx
  Logic.ProofIrrelevance
  Program.Equality
.

Require Import MyPrelude.

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

  Lemma fold_over_empty :
    forall {V} (m : NatMap.t V),
      fold (fun k v a =>
              if match v with
                 | _ => true
                 end then a $+ (k,v) else a) m $0 = m.
  Proof.

    intros.
    apply P.fold_rec.
    - intros; simpl. eapply map_eq_Equal; unfold Equal; intros.
      rewrite empty_o. admit.
    - intros; subst.
      apply map_eq_Equal; unfold Equal; intros.
      unfold P.Add in H1. specialize (H1 y). symmetry; auto.

  Admitted.

End MapLemmas.

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
