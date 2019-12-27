(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
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

Lemma lookup_empty_none :
  forall {A} k,
    (@empty A) $? k = None.
Proof. unfold find, Raw.find; trivial. Qed.

Ltac context_map_rewrites1 :=
    match goal with
    | [ H : ?m $? ?k = _ |- context[?m $? ?k] ] => rewrite H
    | [ H : context [ match ?matchee with _ => _ end ]
     ,  H1 : ?matchee = _ |- _] => rewrite H1 in H
    end.

Ltac contra_map_lookup1 :=
    match goal with
    | [ H : ?ks $? ?k = ?v -> _, ARG : ?ks $? ?k = ?v |- _ ] => specialize (H ARG)
    | [ H1 : ?ks $? ?k = _, H2 : ?ks $? ?k = _ |- _ ] => rewrite H1 in H2; invert H2
    | [ H : ?ks $? ?k = _ |- context [ ?ks $? ?k <> _] ] => unfold not; intros
    end.

Ltac clean_map_lookups1 :=
  invert_base_equalities1
  || contra_map_lookup1
  || context_map_rewrites1
  || match goal with
    | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
    | [ H : _ $+ (?k,_) $? ?k = _ |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by auto 2
    | [ H : _ $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_eq_o in H by auto 2
    | [ H : context [ match _ $+ (?k,_) $? ?k with _ => _ end ] |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : context [ match _ $+ (?k1,_) $? ?k2 with _ => _ end ] |- _ ] => rewrite add_neq_o in H by auto 2
    | [ H : context [ match _ $+ (?k1,_) $? ?k2 with _ => _ end ] |- _ ] => rewrite add_eq_o in H by auto 2
    | [ |- context[_ $+ (?k,_) $? ?k] ] => rewrite add_eq_o by trivial
    | [ |- context[_ $+ (?k1,_) $? ?k2] ] => rewrite add_neq_o by auto 2
    | [ |- context[_ $+ (?k1,_) $? ?k2] ] => rewrite add_eq_o by auto 2
    | [ |- context[_ $- ?k $? ?k] ] => rewrite remove_eq_o by trivial
    | [ |- context[_ $- ?k1 $? ?k2] ] => rewrite remove_neq_o by auto 2
    | [ |- context[_ $- ?k1 $? ?k2] ] => rewrite remove_eq_o by auto 2
    | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
    | [ |- ~ In _ _ ] => rewrite not_find_in_iff
    | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
    | [ H1 : ?m $? ?k = _ , H2 : ?m $? ?k = _ |- _] => rewrite H1 in H2
    | [ H1 : ?m $? ?k1 = _ , H2 : ?m $? ?k2 = _ |- _] => assert (k1 = k2) as RW by auto 2; rewrite RW in H1; clear RW; rewrite H1 in H2
    | [ H : ?m $? ?k <> None |- _ ] => cases (m $? k); try contradiction; clear H
    | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
    | [ |- context [ MapsTo _ _ _ ] ] => rewrite find_mapsto_iff
    end.

Ltac contra_map_lookup := repeat (invert_base_equalities1 || contra_map_lookup1).
Ltac clean_map_lookups := repeat clean_map_lookups1.
Ltac context_map_rewrites := repeat context_map_rewrites1.

Section MapLemmas.

  Lemma lookup_some_implies_in : forall V (m : NatMap.t V) k v,
      m $? k = Some v
      -> List.In (k,v) (to_list m).
  Proof.
    intros * H.

    rewrite <- find_mapsto_iff, elements_mapsto_iff, InA_alt in H;
      split_ex.
    unfold to_list.

    unfold eq_key_elt, Raw.PX.eqke in H; simpl in H; split_ands; subst.
    rewrite (surjective_pairing x) in *; auto.
  Qed.

  Lemma lookup_split : forall V (m : NatMap.t V) k v k' v',
    (m $+ (k, v)) $? k' = Some v'
    -> (k' <> k /\ m $? k' = Some v') \/ (k' = k /\ v' = v).
  Proof.
    intros;
      case (eq_dec k k'); intros; subst; clean_map_lookups; eauto.
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
    - unfold Equal in *; subst; simpl in *.
      match goal with
      | [ H : forall _, _ |- _ ] => 
        generalize (H n1); generalize (H n2); intros
      end;
        unfold find, Raw.find in *; simpl in *.
      
      pose proof (Raw.MX.elim_compare_eq (eq_refl n1)) as EQn1.
      pose proof (Raw.MX.elim_compare_eq (eq_refl n2)) as EQn2.
      split_ex.
      rewrite H2, H3 in *.

      cases (OrderedTypeEx.Nat_as_OT.compare n1 n2);
        cases (OrderedTypeEx.Nat_as_OT.compare n2 n1);
        try discriminate; subst; repeat invert_base_equalities1; eauto;
          repeat 
            match goal with
            | [ H : OrderedTypeEx.Nat_as_OT.eq _ _ |- _ ] => unfold OrderedTypeEx.Nat_as_OT.eq in H; subst
            end; eauto.
      Nat.order.

    - split; auto; subst.

      pose proof (Raw.MX.elim_compare_eq (eq_refl n2)); split_ex.
      unfold Equal in *; simpl in *.

      intro k; invert H4.
      case (k ==n n2); intros; subst;
        (rewrite !remove_eq_o by auto 2)
      || (rewrite !remove_neq_o by auto 2); eauto.
  Qed.

  Lemma remove_hd :
    forall {V} n (v : V) xs sx hdrel,
      {| this := (n,v) :: xs ; sorted := Sorted.Sorted_cons sx hdrel |} $- n = {| this := xs ; sorted := sx |}.
  Proof.
    intros.
    unfold remove, Raw.remove. simpl.
    eapply map_eq_elements_eq; simpl.

    pose proof (Raw.MX.elim_compare_eq (eq_refl n)); split_ex.
    rewrite H; trivial.
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

  Lemma map_eq_Equal :
    forall {V} (m m' : t V),
      Equal m m'
      -> m = m'.
  Proof.
    destruct m as [l sl].
    generalize dependent l.
    induction l; intros.

    - unfold Equal in H. simpl in *.
      apply map_eq_elements_eq; simpl.
      symmetry in H.

      destruct m'; simpl in *.
      cases this0; trivial.
      exfalso.
      destruct p; specialize (H n).
      unfold find, Raw.find in *; simpl in *.
        
      pose proof (Raw.MX.elim_compare_eq (eq_refl n)); split_ex.
      rewrite H0 in H.
      discriminate.

    - simpl.
      destruct m'; cases this0; simpl in *.
      + destruct a as [n v].
        unfold Equal in H; specialize (H n).
        unfold find, Raw.find in H; simpl in H.
        pose proof (Raw.MX.elim_compare_eq) as P; specialize (P n n (eq_refl n)); destruct P.
        rewrite H0 in H; discriminate.

      + eapply Equal_hd_tl in H; eauto; split_ands; subst.
        unfold Equal in H0; simpl in *.

        dependent destruction sl.
        dependent destruction sorted0.
        specialize (IHl sl {| this := this0 ; sorted := sorted0 |}).

        assert (tlEQ : Equal {| this := l ; sorted := sl |} {| this := this0 ; sorted := sorted0 |} ).
        * destruct p;
            unfold Equal; intro k;
              specialize (H0 k); rewrite !remove_hd in H0; eauto.
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

  Lemma map_add_eq :
    forall {V} (m : NatMap.t V) k v1 v2,
      m $+ (k,v1) $+ (k,v2) = m $+ (k,v2).
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros;
      destruct (k ==n y); subst; clean_map_lookups; eauto.
  Qed.

  Lemma map_add_remove_eq :
    forall {V} (m : NatMap.t V) k v1,
      m $+ (k, v1) $- k = m $- k.
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
      destruct (k ==n y); subst; clean_map_lookups; eauto.
  Qed.

  Lemma map_add_remove_neq :
    forall {V} (m : NatMap.t V) k1 v1 k2,
        k1 <> k2
      -> m $+ (k1, v1) $- k2 = m $- k2 $+ (k1, v1).
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    destruct (k2 ==n y); destruct (k1 ==n y); intros; subst; clean_map_lookups; eauto.
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
    destruct (y ==n k1); subst; clean_map_lookups; eauto.
  Qed.

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

Ltac solve_simple_maps1 :=
  clean_map_lookups1
  || match goal with
    | [ |- context [ _ $+ (?k1,_) $? ?k2 ] ] => destruct (k1 ==n k2); subst
    | [ H : context [ _ $+ (?k1,_) $? ?k2 ] |- _ ] => destruct (k1 ==n k2); subst
    | [ |- context [ match ?m $? ?k with _ => _ end ]] => cases (m $? k)
    | [ H : context [ match ?m $? ?k with _ => _ end ] |- _ ] => cases (m $? k)
    | [ |- context [ ?m $+ (?k,_) $+ (?k,_) ]] => rewrite map_add_eq by trivial
    (* maybe a little too specific? *)
    | [ |- context [ ?m $+ (?k1,_) $+ (?k2,_) = ?m $+ (?k2,_) $+ (?k1,_)]] => rewrite map_ne_swap by auto 2; trivial
    end.

Ltac solve_simple_maps := repeat solve_simple_maps1.

Ltac maps_equal1 :=
  match goal with
  | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros
  | [ |- _ = _ $+ (_,_) ] => apply map_eq_Equal; unfold Equal; intros
  end
  || solve_simple_maps1.

(* TODO -- think of how to eliminate this *)
Ltac maps_equal :=
  apply map_eq_Equal; unfold Equal; intros;
  (repeat solve_simple_maps1); trivial.

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
    - induction 1; intros; solve_simple_maps; eauto.
    - induction m using P.map_induction_bis; intros; Equal_eq; eauto.
      econstructor; solve_simple_maps; eauto.

      assert (Forall_natmap m).
      eapply IHm; intros.
      apply H0 with (k:=k); solve_simple_maps; eauto.

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
    destruct (k ==n k0); subst; clean_map_lookups; eauto.
    eapply H with (k0:=k0); clean_map_lookups; trivial.
  Qed.

End MapPredicates.
