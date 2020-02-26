From Coq Require Import
     FSets.FMapList
     FSets.FMapFacts
     Structures.OrderedType
     Structures.OrderedTypeEx
     Logic.ProofIrrelevance
     Program.Equality
.

Require Import MyPrelude Tactics.

Inductive channel_id := 
| Single (n : nat)
| Intersection (ch1 ch2 : nat)
.

Module ChannelType <: OrderedType.
  Definition t := channel_id.

  Definition eq ch1 ch2 :=
    match (ch1, ch2) with
    | (Single n, Single n') => n = n'
    | (Intersection n1 n2, Intersection n1' n2') => n1 = n1' /\ n2 = n2'
    | _ => False
    end.

  (*
    Sort by:
         single with lower n < single with higher n
         any intersection < any single
         intersection with lower n1 < intersection with higher n1
         intersection with lower n2 < intersection with higher n2
   *)
  Definition lt ch1 ch2 : Prop :=
    match (ch1, ch2) with
    | (Single n, Single n') => n < n'
    | (Intersection _ _, Single _) => True
    | (Intersection n1 n2, Intersection n1' n2') => (n1 = n1' /\ n2 < n2') \/ n1 < n1'
    | (Single _, Intersection _ _) => False
    end.

  Lemma eq_refl :
    forall x, eq x x.
  Proof.
    intros; unfold eq; destruct x; eauto.
  Qed.
  
  Lemma eq_sym :
    forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; intros; destruct x, y; eauto.
    invert H. eauto.
  Qed.

  Lemma eq_trans :
    forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; intros; destruct x, y, z;
    repeat (match goal with
    | [ H1 : ?n1 = ?n2, H2 : ?n2 = ?n3 |- ?n1 = ?n3 ] => rewrite H1; rewrite H2; trivial
    | [ H : False |- _ ] => inversion H
    | [ H : _ /\ _ |- _ ] => split_ands
    | [ |- _ = _ /\ _ = _ ] => split
    end).
  Qed.

  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros; destruct x, y, z; try Nat.order; try propositional;
      [> left; split | right | right | right ]; Nat.order.
  Qed.

  Lemma lt_not_eq :
    forall x y, lt x y -> ~ eq x y.
  Proof.
    intros; destruct x, y. unfold lt in H. unfold eq. Nat.order.
    unfold eq. eauto. unfold eq; eauto. unfold lt, eq in *.
    split_ands; split_ors; subst; unfold not; intros; split_ands;
      Nat.order.
  Qed.

  Lemma compare :
    forall( x y : t), Compare lt eq x y.
  Proof.
    intros.  destruct x, y. 
    case_eq (Nat.compare n n0); intro. 
    apply EQ. now apply nat_compare_eq.
    apply LT. now apply nat_compare_lt.
    apply GT. now apply nat_compare_gt.
    apply GT. unfold lt. eauto.
    apply LT. unfold lt. eauto.
    case_eq (Nat.compare ch1 ch0); intro.
    case_eq (Nat.compare ch2 ch3); intro.
    apply EQ. unfold eq. split; now apply nat_compare_eq.
    apply LT. unfold lt. left. split. now apply nat_compare_eq.
    now apply nat_compare_lt.
    apply GT. left. split. apply Nat.eq_sym. now apply nat_compare_eq. now apply nat_compare_gt.

    apply LT. unfold lt. right. now apply nat_compare_lt.
    apply GT. unfold lt. right. now apply nat_compare_gt.
  Qed.

  Lemma eq_dec :
    forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq; destruct x, y; try tauto.
    eapply eq_nat_dec.

    cases (ch1 ==n ch0); cases (ch2 ==n ch3); cases (ch1 ==n ch3); cases (ch2 ==n ch0); subst;
      eauto; right; unfold not; intros; split_ors; contradiction.
  Qed.

End ChannelType.

Definition combine (ch1 ch2 : channel_id) :=
  match (ch1, ch2) with
  | (Single n, Single n') => if n <? n'
                            then Some (Intersection n' n)
                            else Some (Intersection n n')
  | _ => None
  end.



Module Import ChMap := FMapList.Make(ChannelType).
Module P := WProperties_fun ChannelType ChMap.
Module F := P.F.
Module O := OrdProperties ChMap.

Export ChMap P F O.

From Coq Require List.

Set Implicit Argruments.

Module ChNotation.
  Notation "#0" := (empty _).
  Notation "m #+ ( k , v )" := (add k v m) (at level 50, left associativity).
  Notation "m #- k" := (remove k m) (at level 50, left associativity).
  Notation "m #? k" := (find k m) (at level 50, left associativity).
End ChNotation.

Import ChNotation.
  
Module Import OTF := OrderedType.OrderedTypeFacts ChannelType.
Module Import OMF := FSets.FMapFacts.OrdProperties ChMap.

Lemma lookup_empty_none :
  forall {A} k,
    (@empty A) #? k = None.
Proof. unfold find, Raw.find; trivial. Qed.

Ltac one_neq_intersection :=
  match goal with
  | [ H : ?ch1 <> ?ch2 |- not (?ch1 = ?ch2 /\ ?ch3 = ?ch4) ]=> unfold not; intros; split_ands; Nat.order
  | [ H : ?ch3 <> ?ch4 |- not (?ch1 = ?ch2 /\ ?ch3 = ?ch4)]  => unfold not; intros; split_ands; Nat.order
  end.

Ltac context_map_rewrites1 :=
  match goal with
  | [ H : ?m #? ?k = _ |- context[?m #? ?k] ] => rewrite H
  | [ H1 : context [match ?m with _ => _ end],
           H2 : ?m = _ |- _ ] => rewrite H2 in H1
  end.

Ltac contra_map_lookup1 :=
  match goal with
  | [ H : ?chs #? ?ch = ?v -> _, ARG : ?ks #? ?k = ?v |- _ ] => specialize (H ARG)
  | [ H1 : ?chs #? ?ch = _, H2 : ?chs #? ?ch = _ |- _ ] => rewrite H1 in H2; invert H2
  | [ H : ?chs #? ?ch = _ |- context [ ?chs #? ?ch <> _ ] ] => unfold not; intros
  end.

Ltac clean_map_lookups1 :=
  invert_base_equalities1
  || contra_map_lookup1
  || context_map_rewrites1
  || match goal with
    | [ H : context [ #0 #? _ ] |- _ ] => rewrite lookup_empty_none in H
    | [ H : _ #? (?ch,_) #? ?ch = _ |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : _ #+ (?ch1,_) #? ?ch2 = _ |- _ ] => rewrite add_neq_o in H by auto 2
    | [ H : _ #+ (?ch1,_) #? ?ch2 = _ |- _ ] => rewrite add_eq_o in H by auto 2
    | [ H : _ #? (?ch,_) #? ?ch = _ |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : _ #+ (?ch1,_) #? ?ch2 = _ |- _ ] => rewrite add_neq_o in H by auto 2
    | [ H : _ #+ (?ch1,_) #? ?ch2 = _ |- _ ] => rewrite add_eq_o in H by auto 2
    | [ H : context [ match _ #+ (?ch,_) #? ?ch with _ => _ end ] |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : context [ match _ #+ (?ch1,_) #? ?ch2 with _ => _ end ] |- _ ] => rewrite add_neq_o in H by auto 2
    | [ H : context [ match _ #+ (?ch1,_) #? ?ch2 with _ => _ end ] |- _ ] => rewrite add_eq_o in H by auto 2
    | [ |- context[_ #+ (?ch,_) #? ?ch] ] => rewrite add_eq_o by trivial
    | [ |- context[_ #+ (?ch1,_) #? ?ch2] ] => rewrite add_neq_o by auto 2
    | [ |- context[_ #+ (?ch1,_) #? ?ch2] ] => rewrite add_eq_o by auto 2
    | [ |- context[_ #- ?ch #? ?ch] ] => rewrite remove_eq_o by trivial
    | [ |- context[_ #- ?ch1 #? ?ch2] ] => rewrite remove_neq_o by auto 2
    | [ |- context[_ #- ?ch1 #? ?ch2] ] => rewrite remove_eq_o by auto 2
    | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
    | [ |- ~ In _ _ ] => rewrite not_find_in_iff
    | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
    | [ H1 : ?m #? ?ch = _ , H2 : ?m #? ?ch = _ |- _] => rewrite H1 in H2
    | [ H1 : ?m #? ?ch1 = _ , H2 : ?m #? ?ch2 = _ |- _] => assert (ch1 = ch2) as RW by auto 2; rewrite RW in H1; clear RW; rewrite H1 in H2
    | [ H : ?m #? ?ch <> None |- _ ] => cases (m #? ch); try contradiction; clear H
    | [ H : MapsTo _ _ _ |- _ ] => rewrite find_mapsto_iff in H
    | [ |- context [ MapsTo _ _ _ ] ] => rewrite find_mapsto_iff
    | [ |- ~False ] => tauto
    | [ H : False |- _] => tauto
    end
.

Ltac contra_chmap_lookup := repeat (invert_base_equalities1 || contra_map_lookup1).
Ltac clean_chmap_lookups := repeat clean_map_lookups1.
Ltac context_chmap_rewrites := repeat context_map_rewrites1.

Section MapLemmas.

  (* Lemma reversed_rewrite : *)
  (*   forall ch1 ch2, *)
  (*     ChannelType.eq (Intersection ch1 ch2) (Intersection ch2 ch1). *)
  (* Proof. *)
  (*   intros. unfold ChannelType.eq; right; split; reflexivity. *)
  (* Qed. *)

  (* Does not work since List.In relies on = not eq *)
  Lemma lookup_some_implies_in :
    forall V (m : ChMap.t V) ch v,
      m #? ch = Some v
      -> List.In (ch, v) (to_list m).
  Proof.
    intros * H. rewrite <- find_mapsto_iff, elements_mapsto_iff, InA_alt in H.
    unfold to_list. split_ex.
    unfold eq_key_elt in H.  unfold Raw.PX.eqke in H. simpl in H; split_ands; subst.

    destruct ch, x, k; split_ex; simpl in *.
    rewrite H. assumption. invert H. invert H. split_ands; rewrite H, H1; assumption.
  Qed.
  

  Lemma lookup_split :
    forall V (m : ChMap.t V) k k' v v',
      (m #+ (k, v)) #? k' = Some v'
      -> (~(ChannelType.eq k' k) /\ m #? k' = Some v') \/ ((ChannelType.eq k' k) /\ v' = v).
  Proof.
    intros.
    cases (eq_dec k k'); intros; subst; clean_chmap_lookups; eauto.
    destruct k, k'. rewrite y. right. split; trivial. invert y. invert y. split_ands.
    rewrite H, H0. right; split; trivial.
    cases (eq_dec k k'); intros; subst; clean_chmap_lookups; eauto.
    destruct k, k'. left. split. unfold not. intro. unfold ChannelType.eq in H0.
    rewrite H0 in n.
    contradiction. trivial. left. split. unfold ChannelType.eq. assumption. trivial.
    left. split. unfold ChannelType.eq. trivial. trivial. left. split. unfold ChannelType.eq.
    unfold not. intro. split_ands. rewrite H1 in n. rewrite H0 in n. unfold not in n. eauto. eauto.
  Qed.

  Lemma map_eq_fields_eq :
    forall {V} (th th' : Raw.t V) s s',
        th = th'
      -> {| this := th ; sorted := s |} = {| this := th' ; sorted := s' |}.
  Proof.
    intros; subst; f_equal; apply proof_irrelevance.
  Qed.

  Lemma map_eq_elements_eq :
    forall {V} (m m' : ChMap.t V),
      elements m = elements m'
      -> m = m'.
  Proof.
    intros. destruct m, m'.
    simpl in *. eapply map_eq_fields_eq; eauto.
  Qed.

  Lemma lt_contra :
    forall x y, ChannelType.lt x y -> ChannelType.lt y x -> False.
  Proof.
    intros. destruct x, y; unfold ChannelType.lt in *. Nat.order. invert H. invert H0.
    split_ands; split_ors; try Nat.order.
  Qed.
  
  Lemma Equal_hd_tl :
    forall {V} (m1 m1' m2 m2' : t V) x xs y ys sx sy,
        m1 = {| this := x  :: xs ; sorted := sx |}
      -> m2 = {| this := y :: ys ; sorted := sy |}
      -> Equal m1 m2
      -> m1' = m1 #- fst x
      -> m2' = m2 #- fst y
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
      
      pose proof (Raw.MX.elim_compare_eq (ChannelType.eq_refl n1)) as EQn1.
      pose proof (Raw.MX.elim_compare_eq (ChannelType.eq_refl n2)) as EQn2.
      split_ex.
      rewrite H2, H3 in *.

      cases (ChannelType.compare n1 n2);
        cases (ChannelType.compare n2 n1);
        try discriminate; subst; repeat invert_base_equalities1; eauto;
          repeat
            match goal with
            | [ H : ChannelType.eq _ _ |- _ ] => unfold ChannelType.eq in H; subst
            end; eauto.
      destruct n1, n2. rewrite e. trivial. invert e. invert e. split_ands. rewrite e0. rewrite e6. trivial.
      destruct n1, n2. rewrite e. trivial. invert e. invert e. split_ands. rewrite e. rewrite e4. trivial.
      destruct n1, n2. rewrite e. trivial. invert e. invert e. split_ands. rewrite e. rewrite e4. trivial.
      clear Heq. eapply lt_contra in l. invert l. assumption.
      
    - split; auto; subst.

      pose proof (Raw.MX.elim_compare_eq (ChannelType.eq_refl n2)); split_ex.
      unfold Equal in *; simpl in *.

      intro k; invert H4. destruct n2, k.
      * case (n ==n n0); intros; subst; (rewrite !remove_eq_o by auto 2) || (rewrite !remove_neq_o by auto 2); eauto.
      * assert (not (ChannelType.eq (Single n) (Intersection ch1 ch2))). unfold ChannelType.eq; eauto.
        (rewrite !remove_neq_o by auto 2); eauto.
      * assert (not (ChannelType.eq (Single n) (Intersection ch1 ch2))). unfold ChannelType.eq; eauto.
        (rewrite !remove_neq_o by auto 2); eauto.
      * cases (ch1 ==n ch0); cases (ch2 ==n ch3).
      + rewrite !remove_eq_o by auto 2; trivial.
      + assert (not (ChannelType.eq (Intersection ch1 ch2) (Intersection ch0 ch3))); unfold ChannelType.eq, not. intro. split_ands. tauto.
        rewrite !remove_neq_o by auto 2; eauto.
      + assert (not (ChannelType.eq (Intersection ch1 ch2) (Intersection ch0 ch3))); unfold ChannelType.eq, not. intro. split_ands. tauto.
        rewrite !remove_neq_o by auto 2; eauto.
      + assert (not (ChannelType.eq (Intersection ch1 ch2) (Intersection ch0 ch3))); unfold ChannelType.eq, not. intro. split_ands. tauto.
        rewrite !remove_neq_o by auto 2; eauto.
  Qed.

  Lemma remove_hd :
    forall {V} n (v : V) xs sx hdrel,
      {| this := (n,v) :: xs ; sorted := Sorted.Sorted_cons sx hdrel |} #- n = {| this := xs ; sorted := sx |}.
  Proof.
    intros. 
    unfold remove. simpl.
    eapply map_eq_elements_eq; simpl.

    pose proof (Raw.MX.elim_compare_eq (ChannelType.eq_refl n)); split_ex.
    rewrite H; trivial.
  Qed.

  Lemma Empty_eq_empty :
    forall v m,
      Empty (elt:=v) m
      -> #0 = m.
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
      destruct p; specialize (H c).
      unfold find, Raw.find in *; simpl in *.
        
      pose proof (Raw.MX.elim_compare_eq (ChannelType.eq_refl c)); split_ex.
      rewrite H0 in H.
      discriminate.

    - simpl.
      destruct m'; cases this0; simpl in *.
      + destruct a as [n v].
        unfold Equal in H; specialize (H n).
        unfold find, Raw.find in H; simpl in H.
        pose proof (Raw.MX.elim_compare_eq) as P; specialize (P n n (ChannelType.eq_refl n)); destruct P.
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
    forall {V}, Empty (elt:=V) #0.
  Proof.
    intros.
    unfold Empty, Raw.Empty, Raw.PX.MapsTo, not; intros.
    invert H.
  Qed.

  Lemma map_add_eq :
    forall {V} (m : ChMap.t V) k v1 v2,
      m #+ (k,v1) #+ (k,v2) = m #+ (k,v2).
  Proof.
    intros; apply map_eq_Equal; unfold Equal; intros. 
        
    destruct k, y; clean_chmap_lookups.
    repeat (match goal with
    | [ |- context[_ #+ (Single ?n, _) #? Single ?n0]] => destruct (n ==n n0); subst; clean_chmap_lookups
    | [ |- context[_ #+ (Single _, _) #? Intersection _ _]] => clean_chmap_lookups; rewrite add_neq_o; rewrite add_neq_o
    (* | [ |- ~ False ] => tauto *)
            end; eauto). eauto. eauto.

    destruct (ch1 ==n ch0), (ch2 ==n ch3). clean_chmap_lookups. eauto. clean_chmap_lookups.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    reflexivity.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    reflexivity.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    reflexivity.
  Qed.

  Lemma map_add_remove_eq :
    forall {V} (m : ChMap.t V) k v1,
      m #+ (k, v1) #- k = m #- k.
  Proof.
    intros. apply map_eq_Equal; unfold Equal; intros.
    destruct k, y; subst; clean_chmap_lookups. destruct (n ==n n0); subst.
    repeat (match goal with
    | [ |- context[_ #- (Single ?n, _) #? Single ?n0]] => destruct (n ==n n0); subst; clean_chmap_lookups
    | [ |- context[_ #- (Single _, _) #? Intersection _ _]] => clean_chmap_lookups; rewrite remove_neq_o; rewrite remove_neq_o
    (* | [ |- ~ False ] => tauto *)
            end; eauto); clean_chmap_lookups; trivial.
  
    rewrite remove_neq_o. rewrite add_neq_o. rewrite remove_neq_o. reflexivity. assumption. assumption. assumption. reflexivity.
    reflexivity.

    destruct (ch1 ==n ch0), (ch2 ==n ch3); subst; clean_chmap_lookups.

    trivial.
    rewrite remove_neq_o by one_neq_intersection.
    rewrite remove_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    trivial.
   
    rewrite remove_neq_o by one_neq_intersection.
    rewrite remove_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    trivial.
    rewrite remove_neq_o by one_neq_intersection.
    rewrite remove_neq_o by one_neq_intersection.
    rewrite add_neq_o by one_neq_intersection.
    trivial.
  Qed.

(*   Lemma map_add_remove_neq : *)
(*     forall {V} (m : ChMap.t V) k1 v1 k2, *)
(*         k1 <> k2 *)
(*       -> m #+ (k1, v1) #- k2 = m #- k2 #+ (k1, v1). *)
(*   Proof. *)
(*     intros. apply map_eq_Equal; unfold Equal; intros. *)

(*     destruct y. *)
(*     destruct (k2 ==n y); destruct (k1 ==n y); intros; subst; clean_map_lookups; eauto. *)
(*   Qed. *)

(*   Lemma map_ne_swap : *)
(*     forall {V} (m : NatMap.t V) k v k' v', *)
(*       k <> k' *)
(*       -> m $+ (k,v) $+ (k',v') = m $+ (k',v') $+ (k,v). *)
(*   Proof. *)
(*     intros. *)
(*     apply map_eq_Equal; unfold Equal; intros. *)
(*     cases (y ==n k); cases (y ==n k'); subst; clean_map_lookups; auto; contradiction. *)
(*   Qed. *)

(*   Lemma map_remove_not_in_idempotent : *)
(*     forall {V} (m : NatMap.t V) k1, *)
(*       m $? k1 = None *)
(*       -> m $- k1 = m. *)
(*   Proof. *)
(*     intros. *)
(*     eapply map_eq_Equal; unfold Equal; intros. *)
(*     destruct (y ==n k1); subst; clean_map_lookups; eauto. *)
(*   Qed. *)

End MapLemmas.

(* (* Ltac Equal_eq := *) *)
(* (*   repeat *) *)
(* (*     match goal with *) *)
(* (*     | [ H : Equal _ _ |- _] => apply map_eq_Equal in H; subst *) *)
(* (*     end. *) *)

(* (* Ltac m_equal := *) *)
(* (*   repeat match goal with *) *)
(* (*          (* | [ |- context[find ?k (add ?k' _ _) ] ] => idtac k; idtac k'; case (eq_dec k k'); intro *) *) *)
(* (*          | [ |- context[find ?k (add ?k _ _) ] ]  => *) *)
(* (*            rewrite add_eq_o by (simple apply @eq_refl) *) *)
(* (*          | [ |- context[find ?k (add ?k' _ _) ] ] => *) *)
(* (*            rewrite add_neq_o by ( (unfold not; intros ?SIMPLEQ; invert SIMPLEQ) || intuition idtac ) *) *)
(* (*          | [ |- context[$0 $++ _ ] ] => rewrite empty_add_idempotent *) *)
(* (*          | [ |- context[_ $++ $0 ] ] => rewrite add_empty_idempotent *) *)
(* (*          (* | [ |- (add _ _ _) = _ ] => normalize_set *) *) *)
(* (*          | [ |- (add _ _ _) = _ ] => unfold add, Raw.add; simpl *) *)
(* (*          | [ |- {| this := _ ; sorted := _ |} = _ ] => eapply map_eq_fields_eq *) *)
(* (*          | [ H : Empty ?m |- $0 = ?m ] => eapply Empty_eq_empty; exact H *) *)
(* (*          | [ H : Empty ?m |- ?m = $0 ] => symmetry *) *)
(* (*          | [ |- empty _ = _ ] => unfold empty, Raw.empty, remove, Raw.remove; simpl *) *)
(* (*          end. *) *)

(* (* Lemma remove_not_in_map_idempotent : *) *)
(* (*   forall V (m : NatMap.t V) k, *) *)
(* (*     m $? k = None *) *)
(* (*     -> m $- k = m. *) *)
(* (* Proof. *) *)
(* (*   intros; apply map_eq_Equal; unfold Equal; intros; *) *)
(* (*     destruct (k ==n y); subst; context_map_rewrites; clean_map_lookups; trivial. *) *)
(* (* Qed. *) *)

(* (* Ltac solve_simple_maps1 := *) *)
(* (*   clean_map_lookups1 *) *)
(* (*   || match goal with *) *)
(* (*     | [ |- context [ _ $+ (?k1,_) $? ?k2 ] ] => destruct (k1 ==n k2); subst *) *)
(* (*     | [ H : context [ _ $+ (?k1,_) $? ?k2 ] |- _ ] => destruct (k1 ==n k2); subst *) *)
(* (*     | [ |- context [ match ?m $? ?k with _ => _ end ]] => cases (m $? k) *) *)
(* (*     | [ H : context [ match ?m $? ?k with _ => _ end ] |- _ ] => cases (m $? k) *) *)
(* (*     | [ |- context [ ?m $+ (?k,_) $+ (?k,_) ]] => rewrite map_add_eq by trivial *) *)
(* (*     (* maybe a little too specific? *) *) *)
(* (*     | [ |- context [ ?m $+ (?k1,_) $+ (?k2,_) = ?m $+ (?k2,_) $+ (?k1,_)]] => rewrite map_ne_swap by auto 2; trivial *) *)
(* (*     end. *) *)

(* (* Ltac solve_simple_maps := repeat solve_simple_maps1. *) *)

(* (* Ltac maps_equal1 := *) *)
(* (*   match goal with *) *)
(* (*   | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros *) *)
(* (*   | [ |- _ = _ $+ (_,_) ] => apply map_eq_Equal; unfold Equal; intros *) *)
(* (*   end *) *)
(* (*   || solve_simple_maps1. *) *)

(* (* (* TODO -- think of how to eliminate this *) *) *)
(* (* Ltac maps_equal := *) *)
(* (*   apply map_eq_Equal; unfold Equal; intros; *) *)
(* (*   (repeat solve_simple_maps1); trivial. *) *)

(* (* Ltac canonicalize_map m := *) *)
(* (*   match m with *) *)
(* (*   | context [ add ?k ?v ?m1 ] => *) *)
(* (*     match m1 with *) *)
(* (*     | context [ add k _ _ ] => *) *)
(* (*       assert ( CANON : m = m $- k $+ (k,v) ); [  *) *)
(* (*         maps_equal *) *)
(* (*       | repeat *) *)
(* (*           (rewrite map_add_remove_eq in CANON by trivial) *) *)
(* (*         || (rewrite map_add_remove_neq in CANON by eauto) *) *)
(* (*         || (rewrite remove_not_in_map_idempotent in CANON by eauto) *) *)
(* (*       ]; rewrite !CANON; *) *)
(* (*       match type of CANON with *) *)
(* (*       | _ = ?m' => clear CANON; try canonicalize_map m' *) *)
(* (*       end *) *)
(* (*     end *) *)
(* (*   end. *) *)

(* (* Lemma canonicalize_map_test1 : *) *)
(* (*   forall V (m : NatMap.t V) k1 k2 (v1 v2 v3 : V), *) *)
(* (*     k1 <> k2 *) *)
(* (*     -> m $? k1 = None *) *)
(* (*     -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) = m $+ (k2,v2) $+ (k1,v3). *) *)
(* (* Proof. *) *)
(* (*   intros. *) *)
(* (*   match goal with *) *)
(* (*   | [ |- ?m = _ ] => canonicalize_map m *) *)
(* (*   end; maps_equal. *) *)
(* (* Qed. *) *)

(* (* Lemma canonicalize_map_test2 : *) *)
(* (*   forall V (m : NatMap.t V) k1 k2 k3 (v1 v2 v3 v4 : V), *) *)
(* (*     k1 <> k2 *) *)
(* (*     -> k1 <> k3 *) *)
(* (*     -> k2 <> k3 *) *)
(* (*     -> m $? k1 = None *) *)
(* (*     -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) $+ (k3,v4) = m $+ (k2,v2) $+ (k1,v3) $+ (k3,v4). *) *)
(* (* Proof. *) *)
(* (*   intros. *) *)
(* (*   match goal with *) *)
(* (*   | [ |- ?m = _ ] => canonicalize_map m *) *)
(* (*   end; maps_equal. *) *)
(* (* Qed. *) *)

(* (* Lemma canonicalize_map_test3 : *) *)
(* (*   forall V (m : NatMap.t V) k1 k2 k3 (v1 v2 v3 v4 : V), *) *)
(* (*     k1 <> k2 *) *)
(* (*     -> k1 <> k3 *) *)
(* (*     -> k2 <> k3 *) *)
(* (*     -> m $? k1 = None *) *)
(* (*     -> m $+ (k1,v1) $+ (k2,v2) $+ (k1,v3) $+ (k2,v4) $+ (k3,v4) = m $+ (k2,v4) $+ (k1,v3) $+ (k3,v4). *) *)
(* (* Proof. *) *)
(* (*   intros. *) *)
(* (*   match goal with *) *)
(* (*   | [ |- ?m = _ ] => canonicalize_map m *) *)
(* (*   end; maps_equal. *) *)
(* (* Qed. *) *)

(* (* Definition canon_map {V} (m : NatMap.t V) := *) *)
(* (*   of_list (to_list m). *) *)

(* (* Lemma canon_map_ok : *) *)
(* (*   forall {V} (m : NatMap.t V), *) *)
(* (*     m = canon_map m. *) *)
(* (* Proof. *) *)
(* (*   intros. *) *)
(* (*   unfold canon_map. *) *)
(* (*   pose proof (of_list_3 m). *) *)
(* (*   apply map_eq_Equal in H. *) *)
(* (*   rewrite H. *) *)
(* (*   trivial. *) *)
(* (* Qed. *) *)

(* (* (* Use if the keys are concrete. Faster and it sorts by key so order is consistent *) *) *)
(* (* Definition canonicalize_concrete_map {v} (m : NatMap.t v) : NatMap.t v. *) *)
(* (*   destruct m. *) *)
(* (*   unfold Raw.t in this0. *) *)
(* (*   let f := constr:(fun (acc : NatMap.t v) (cur : nat * v) => *) *)
(* (*                      let (k, v) := cur *) *)
(* (*                      in acc $+ (k, v)) *) *)
(* (*   in let m' := (eval simpl in (fold_left f this0 $0)) *) *)
(* (*   in apply m'. *) *)
(* (* Defined. *) *)

(* (* Ltac canonicalize_concrete_map m := *) *)
(* (*   let m' := (eval simpl in (canonicalize_concrete_map m)) *) *)
(* (*   in replace m with m' in * by maps_equal. *) *)

(* (* Section MapPredicates. *) *)
(* (*   Variable V : Type. *) *)
(* (*   Variable P : V -> Prop. *) *)

(* (*   Inductive Forall_natmap : NatMap.t V -> Prop := *) *)
(* (*   | Empty_Natmap : Forall_natmap $0 *) *)
(* (*   | Add_Natmap k v (m : NatMap.t V) : *) *)
(* (*       P v *) *)
(* (*       -> Forall_natmap m *) *)
(* (*       -> Forall_natmap ( m $+ (k,v)). *) *)

(* (*   Lemma Forall_natmap_forall : *) *)
(* (*     forall m, *) *)
(* (*       Forall_natmap m <-> (forall k v, m $? k = Some v -> P v). *) *)
(* (*   Proof. *) *)
(* (*     split. *) *)
(* (*     - induction 1; intros; solve_simple_maps; eauto. *) *)
(* (*     - induction m using P.map_induction_bis; intros; Equal_eq; eauto. *) *)
(* (*       econstructor; solve_simple_maps; eauto. *) *)

(* (*       assert (Forall_natmap m). *) *)
(* (*       eapply IHm; intros. *) *)
(* (*       apply H0 with (k:=k); solve_simple_maps; eauto. *) *)

(* (*       econstructor; eauto. *) *)
(* (*       eapply H0 with (k := x); clean_map_lookups; auto. *) *)
(* (*   Qed. *) *)

(* (*   Lemma Forall_natmap_in_prop : *) *)
(* (*     forall k v m, *) *)
(* (*       Forall_natmap m *) *)
(* (*       -> m $? k = Some v *) *)
(* (*       -> P v. *) *)
(* (*   Proof. *) *)
(* (*     intros. *) *)
(* (*     rewrite Forall_natmap_forall in H; eauto. *) *)
(* (*   Qed. *) *)

(* (*   Lemma Forall_natmap_in_prop_add : *) *)
(* (*     forall k v m, *) *)
(* (*       Forall_natmap (m $+ (k,v)) *) *)
(* (*       -> P v. *) *)
(* (*   Proof. *) *)
(* (*     intros. *) *)
(* (*     eapply Forall_natmap_in_prop with (k:=k); eauto; clean_map_lookups; trivial. *) *)
(* (*   Qed. *) *)

(* (*   Lemma Forall_natmap_split : *) *)
(* (*     forall k v m, *) *)
(* (*       Forall_natmap (m $+ (k,v)) *) *)
(* (*       -> ~ In k m *) *)
(* (*       -> Forall_natmap m *) *)
(* (*       /\ P v. *) *)
(* (*   Proof. *) *)
(* (*     intros. *) *)
(* (*     rewrite Forall_natmap_forall in *; intros. *) *)
(* (*     assert (P v) by (eapply H with (k0:=k); clean_map_lookups; trivial). *) *)
(* (*     split; auto; intros. *) *)
(* (*     destruct (k ==n k0); subst; clean_map_lookups; eauto. *) *)
(* (*     eapply H with (k0:=k0); clean_map_lookups; trivial. *) *)
(* (*   Qed. *) *)

(* (* End MapPredicates. *) *)


(* (* Section ConcreteMaps. *) *)

(* (*   Definition next_key {V} (m : NatMap.t V) : nat := *) *)
(* (*     match max_elt m with *) *)
(* (*     | None => 0 *) *)
(* (*     | Some (k,v) => S k *) *)
(* (*     end. *) *)

(* (*   Lemma max_elt_add_ne_recur : *) *)
(* (*     forall {V} (m : NatMap.t V) k1 k2 v1 v2, *) *)
(* (*       m $? k1 = None *) *)
(* (*       -> k1 <> k2 *) *)
(* (*       -> max_elt (m $+ (k1,v1)) = Some (k2,v2) *) *)
(* (*       -> max_elt m = Some (k2,v2). *) *)
(* (*   Proof. *) *)
(* (*     induction m using map_induction_bis; intros; *) *)
(* (*       Equal_eq; eauto. *) *)

(* (*     - unfold max_elt, max_elt_aux in H1; simpl in H1; *) *)
(* (*         clean_map_lookups. *) *)

(* (*     - destruct (x ==n k1); clean_map_lookups; eauto. *) *)
    
(* (*   Admitted. *) *)

(* (*   Lemma max_elt_ge_elements : *) *)
(* (*     forall {V} (m : NatMap.t V) k v, *) *)
(* (*       max_elt m = Some (k,v) *) *)
(* (*       -> forall k' v', m $? k' = Some v' *) *)
(* (*                  -> le k' k. *) *)
(* (*   Proof. *) *)
(* (*     induction m using map_induction_bis; intros; *) *)
(* (*       Equal_eq; clean_map_lookups; eauto. *) *)

(* (*     destruct (x ==n k'); subst; clean_map_lookups; eauto. *) *)
(* (*     - clear IHm. *) *)
(* (*       generalize (max_elt_Above H0); intros MEA. *) *)
(* (*       specialize (MEA k'). *) *)
(* (*       destruct (k ==n k'); subst; clean_map_lookups; eauto. *) *)
(* (*       apply Nat.lt_le_incl. *) *)
(* (*       apply MEA. *) *)
(* (*       rewrite in_find_iff; unfold not; clean_map_lookups. *) *)
      
(* (*     - destruct (x ==n k); subst; eauto using max_elt_add_ne_recur. *) *)
(* (*       apply Nat.lt_le_incl. *) *)
(* (*       generalize (max_elt_Above H0); intros MEA. *) *)
(* (*       apply MEA. *) *)
(* (*       rewrite in_find_iff; unfold not; clean_map_lookups. *) *)
(* (*   Qed. *) *)


(* (*   Lemma next_key_not_in : *) *)
(* (*     forall {V} (m : NatMap.t V) k, *) *)
(* (*       k = next_key m *) *)
(* (*       -> m $? k = None. *) *)
(* (*   Proof. *) *)
(* (*     unfold next_key; intros. *) *)
(* (*     cases (max_elt m); subst. *) *)
(* (*     - destruct p; simpl. *) *)
(* (*       cases (m $? S k); eauto. *) *)
(* (*       exfalso. *) *)

(* (*       assert (Above k (m $- k)) by eauto using max_elt_Above. *) *)
(* (*       specialize (H (S k)). *) *)

(* (*       assert (In (S k) (m $- k)). *) *)
(* (*       rewrite in_find_iff; unfold not; intros. *) *)
(* (*       rewrite remove_neq_o in H0 by eauto; contra_map_lookup. *) *)
(* (*       specialize (H H0). *) *)
(* (*       SearchAbout (_ < _). *) *)
(* (*       assert (k < S k) by eauto using Nat.lt_succ_diag_r. *) *)
(* (*       assert (S k < S k) by eauto using Nat.lt_trans. *) *)
(* (*       SearchAbout (_ < _). *) *)
(* (*       assert (~ (S k < S k)) by eauto using lt_antirefl. *) *)
(* (*       contradiction. *) *)

(* (*     - apply max_elt_Empty in Heq. *) *)
(* (*       apply Empty_eq_empty in Heq; subst. *) *)
(* (*       apply lookup_empty_none. *) *)
(* (*   Qed. *) *)
