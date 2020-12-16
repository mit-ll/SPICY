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
     Structures.OrderedType
     Structures.OrderedTypeEx
     Logic.ProofIrrelevance
     Program.Equality
.

From Coq Require List.

From SPICY Require Import
     MyPrelude
     Tactics.

Set Implicit Arguments.

Module MyOrderedMap (OT : UsualOrderedType).
  Import OT.

  Module Import Map := FMapList.Make( OT ).
  Definition t := Map.t.

  Module Import P := WProperties_fun OT Map.
  Module Import F := P.F.
  Module Import O := OrdProperties Map.
  Module Import OTF := OrderedType.OrderedTypeFacts OT.

  Local Notation "$0" := (empty _).
  Local Notation "m $+ ( k , v )" := (add k v m) (at level 50, left associativity).
  Local Notation "m $- k" := (remove k m) (at level 50, left associativity).
  Local Notation "m $? k" := (find k m) (at level 50, left associativity).

  Lemma lookup_empty_none : forall V k,
      (@empty V) $? k = None.
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
      | [ H1 : ?m $? ?k1 = _ , H2 : ?m $? ?k2 = _ |- _] =>
        assert (k1 = k2) as RW by auto 2; rewrite RW in H1; clear RW; rewrite H1 in H2
      | [ H : ?m $? ?k <> None |- _ ] => cases (m $? k); try contradiction; clear H
      | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
      | [ |- context [ MapsTo _ _ _ ] ] => rewrite find_mapsto_iff
      end.

  Ltac contra_map_lookup := repeat (invert_base_equalities1 || contra_map_lookup1).
  Ltac clean_map_lookups := repeat clean_map_lookups1.
  Ltac context_map_rewrites := repeat context_map_rewrites1.

  Lemma lookup_some_implies_in : forall V (m : Map.t V) k v,
      m $? k = Some v
      -> List.In (k,v) (to_list m).
  Proof.
    intros * H.

    rewrite <- find_mapsto_iff, elements_mapsto_iff, InA_alt in H.
    split_ex.
    unfold eq_key_elt, Raw.PX.eqke in H; simpl in H.
    destruct x; simpl in *; split_ands; subst; eauto.
  Qed.

  Lemma lookup_split : forall V (m : Map.t V) k v k' v',
      (m $+ (k, v)) $? k' = Some v'
      -> (k' <> k /\ m $? k' = Some v') \/ (k' = k /\ v' = v).
  Proof.
    intros;
      case (eq_dec k k'); intros; subst; clean_map_lookups; eauto.
  Qed.

  Lemma map_eq_fields_eq :
    forall V (th th' : Raw.t V) s s',
      th = th'
      -> {| this := th ; sorted := s |} = {| this := th' ; sorted := s' |}.
  Proof.
    intros; subst; f_equal; apply proof_irrelevance.
  Qed.

  Lemma map_eq_elements_eq :
    forall {V} (m m' : Map.t V),
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

      cases (compare n1 n2);
        cases (compare n2 n1);
        try discriminate; subst; repeat invert_base_equalities1; eauto;
          repeat 
            match goal with
            | [ H : eq _ _ |- _ ] => unfold eq in H; subst
            end; eauto.

      pose proof (lt_trans l0 l) as CONTRA;
        apply lt_not_eq in CONTRA; assert (eq n1 n1) by auto; contradiction.
      
    - split; auto; subst.
      invert H4.
      unfold Equal in *; simpl in *.
      intro k.
      case (eq_dec k n2); intros; subst;
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
    forall {V} m,
      Empty (elt:=V) m
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
      destruct p. specialize (H t0).
      unfold find, Raw.find in *; simpl in *.
      
      pose proof (elim_compare_eq (eq_refl t0)) as RW; destruct RW as [?e RW];
        rewrite RW in *; discriminate.

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

  Lemma empty_Empty :
    forall {V}, Empty (elt:=V) $0.
  Proof.
    intros.
    unfold Empty, Raw.Empty, Raw.PX.MapsTo, not; intros.
    invert H.
  Qed.

  Lemma map_add_eq :
    forall {V} (m : Map.t V) k v1 v2,
      m $+ (k,v1) $+ (k,v2) = m $+ (k,v2).
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros;
      destruct (eq_dec k y); subst; clean_map_lookups; eauto.
  Qed.

  Lemma map_add_remove_eq :
    forall {V} (m : Map.t V) k v1,
      m $+ (k, v1) $- k = m $- k.
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    destruct (eq_dec k y); subst; clean_map_lookups; eauto.
  Qed.

  Lemma map_add_remove_neq :
    forall {V} (m : Map.t V) k1 v1 k2,
      k1 <> k2
      -> m $+ (k1, v1) $- k2 = m $- k2 $+ (k1, v1).
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    destruct (eq_dec k2 y); destruct (eq_dec k1 y); intros; subst; clean_map_lookups; eauto.
  Qed.

  Lemma remove_empty :
    forall V k,
      (@empty V) $- k = $0.
  Proof.
    intros; eapply map_eq_Equal; unfold Equal; intros; eauto.
  Qed.

  Lemma map_ne_swap :
    forall {V} (m : Map.t V) k v k' v',
      k <> k'
      -> m $+ (k,v) $+ (k',v') = m $+ (k',v') $+ (k,v).
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    cases (eq_dec y k); cases (eq_dec y k'); subst; clean_map_lookups; auto; contradiction.
  Qed.

  Lemma map_remove_not_in_idempotent :
    forall {V} (m : Map.t V) k1,
      m $? k1 = None
      -> m $- k1 = m.
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros.
    destruct (eq_dec y k1); subst; clean_map_lookups; eauto.
  Qed.

  Ltac Equal_eq :=
    repeat
      match goal with
      | [ H : Equal _ _ |- _] => apply map_eq_Equal in H; subst
      end.

  Lemma remove_not_in_map_idempotent :
    forall {V} (m : Map.t V) k,
      m $? k = None
      -> m $- k = m.
  Proof.
    intros; apply map_eq_Equal. unfold Equal; intros;
      destruct (eq_dec k y); subst; context_map_rewrites; clean_map_lookups; trivial.
  Qed.

  Ltac solve_simple_maps1 :=
    clean_map_lookups1
    || match goal with
      | [ |- context [ _ $+ (?k1,_) $? ?k2 ] ] => destruct (eq_dec k1 k2); subst
      | [ H : context [ _ $+ (?k1,_) $? ?k2 ] |- _ ] => destruct (eq_dec k1 k2); subst
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

  Local Ltac dupKey k m :=
    match m with
    | add k _ _  => idtac
    | add _ _ ?m' => dupKey k m'
    end.

  Ltac canonicalize_map m :=
    match m with
    | context [ add ?k ?v ?m1 ] =>
      dupKey k m1;
      let CANON := fresh "CANON" in
      assert ( CANON : m = m $- k $+ (k,v) ) by maps_equal; 
      repeat
        (rewrite map_add_remove_eq in CANON by trivial)
      || (rewrite map_add_remove_neq in CANON by eauto)
      || (rewrite remove_not_in_map_idempotent in CANON by eauto)
      ; rewrite !CANON;
      match type of CANON with
      | _ = ?m' => clear CANON; try canonicalize_map m'
      end
      (* match m1 with *)
      (* | context [ add k _ _ ] => *)
      (*   assert ( CANON : m = m $- k $+ (k,v) ); [  *)
      (*     maps_equal *)
      (*   | repeat *)
      (*       (rewrite map_add_remove_eq in CANON by trivial) *)
      (*     || (rewrite map_add_remove_neq in CANON by eauto) *)
      (*     || (rewrite remove_not_in_map_idempotent in CANON by eauto) *)
      (*   ]; rewrite !CANON; *)
      (*   match type of CANON with *)
      (*   | _ = ?m' => clear CANON; try canonicalize_map m' *)
      (*   end *)
      (* end *)
    end.

  Lemma canonicalize_map_test1 :
    forall {V} (m : Map.t V) k1 k2 (v1 v2 v3 : V),
      k1 <> k2
      -> m $? k1 = None
      -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) = m $+ (k2,v2) $+ (k1,v3).
  Proof.
    intros.
    match goal with
    | [ |- ?m = _ ] => canonicalize_map m
    end. maps_equal.
  Qed.

  Lemma canonicalize_map_test2 :
    forall {V} (m : Map.t V) k1 k2 k3 (v1 v2 v3 v4 : V),
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
    forall {V} (m : Map.t V) k1 k2 k3 (v1 v2 v3 v4 : V),
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

  Definition canon_map {V} (m : Map.t V) :=
    of_list (to_list m).

  Lemma canon_map_ok :
    forall {V} (m : Map.t V),
      m = canon_map m.
  Proof.
    intros.
    unfold canon_map.
    pose proof (of_list_3 m).
    apply map_eq_Equal in H.
    rewrite H.
    trivial.
  Qed.

  (* Use if the keys are concrete. Faster and it sorts by key so order is consistent *)
  Definition canonicalize_concrete_map {V} (m : Map.t V) : Map.t V.
    destruct m.
    unfold Raw.t in this0.
    let f := constr:(fun (acc : Map.t V) (cur : OT.t * V) =>
                       let (k, v) := cur
                       in acc $+ (k, v))
    in let m' := (eval simpl in (fold_left f this0 $0))
       in apply m'.
  Defined.

  Ltac canonicalize_concrete_map m :=
    let m' := (eval simpl in (canonicalize_concrete_map m))
    in replace m with m' in * by maps_equal.

  Section MapPredicates.
    Variable V : Type.
    Variable P : V -> Prop.

    Inductive Forall_natmap : Map.t V -> Prop :=
    | Empty_Natmap : Forall_natmap $0
    | Add_Natmap k v (m : Map.t V) :
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
      destruct (eq_dec k k0); subst; clean_map_lookups; eauto.
      eapply H with (k0:=k0); clean_map_lookups; trivial.
    Qed.

  End MapPredicates.

  Export Map F P.

End MyOrderedMap.

Module Export NatMap := MyOrderedMap( Nat_as_OT ).
Module NatMapNotation.
  Notation "$0" := (empty _).
  Notation "m $+ ( k , v )" := (add k v m) (at level 50, left associativity).
  Notation "m $- k" := (remove k m) (at level 50, left associativity).
  Notation "m $? k" := (find k m) (at level 50, left associativity).
End NatMapNotation.

Export NatMapNotation.

Definition merge_maps {V : Type} (m1 m2 : Map.t V) : Map.t V :=
  fold (fun k v m => m $+ (k,v) ) m1 m2.

Notation "m1 $++ m2" := (merge_maps m2 m1) (at level 50, left associativity).

Lemma add_empty_idempotent :
  forall V (m : Map.t V),
    m $++ $0 = m.
Proof.
  intros; unfold merge_maps, Map.fold, Map.Raw.fold; simpl; auto.
Qed.

Lemma empty_add_idempotent : 
  forall {V}(m : Map.t V),
    $0 $++ m = m.
Proof.
  intros; unfold merge_maps.
  apply P.fold_rec.
  - intros.
    apply P.elements_Empty in H; simpl in *.
    apply map_eq_elements_eq; auto.
      
  - intros. subst.
    apply map_eq_Equal. unfold Map.Equal; intros.
    unfold P.Add in H1. specialize (H1 y). symmetry; auto.
Qed.

Ltac m_equal :=
  repeat match goal with
         | [ |- context[_ $+ (?k,_) $? ?k ] ]  =>
           rewrite add_eq_o by (simple apply @eq_refl)
         | [ |- context[_ $+ (?k',_) $? ?k] ] =>
           rewrite add_neq_o by ( (unfold not; intros ?SIMPLEQ; invert SIMPLEQ) || intuition idtac )
         | [ |- context[$0 $++ _ ] ] => rewrite empty_add_idempotent
         | [ |- context[_ $++ $0 ] ] => rewrite add_empty_idempotent
         | [ |- (_ $+ (_,_)) = _ ] => unfold Map.add, Map.Raw.add; simpl
         | [ |- {| Map.this := _ ; Map.sorted := _ |} = _ ] => eapply map_eq_fields_eq
         | [ H : Map.Empty ?m |- $0 = ?m ] => eapply Empty_eq_empty; exact H
         | [ H : Map.Empty ?m |- ?m = $0 ] => symmetry
         | [ |- Map.empty _ = _ ] => unfold Map.empty, Map.Raw.empty, remove, Map.Raw.remove; simpl
         end.

Section ConcreteMaps.

  Definition next_key {V} (m : Map.t V) : nat :=
    match O.max_elt m with
    | None => 0
    | Some (k,v) => S k
    end.

  Lemma next_key_not_in :
    forall {V} (m : Map.t V) k,
      k = next_key m
      -> m $? k = None.
  Proof.
    unfold next_key; intros.
    cases (O.max_elt m); subst.
    - destruct p; simpl.
      cases (m $? S k); eauto.
      exfalso.

      assert (O.Above k (m $- k)) by eauto using O.max_elt_Above.
      specialize (H (S k)).

      assert (In (S k) (m $- k)).
      rewrite in_find_iff; unfold not; intros.
      rewrite remove_neq_o in H0 by eauto; contra_map_lookup.
      specialize (H H0).

      assert (k < S k) by eauto using Nat.lt_succ_diag_r.
      assert (S k < S k) by eauto using Nat.lt_trans.

      assert (~ (S k < S k)) by eauto using OTF.lt_antirefl.
      contradiction.

    - apply O.max_elt_Empty in Heq.
      apply Empty_eq_empty in Heq; subst.
      apply lookup_empty_none.
  Qed.

End ConcreteMaps.


