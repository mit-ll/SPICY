From Coq Require Import
     Structures.OrderedType
     Structures.OrderedTypeEx
.

Require Import MyPrelude Tactics Maps.

Inductive channel_id := 
| Single (n : nat)
| Intersection (ch1 ch2 : nat)
.

Module ChannelType <: UsualOrderedType.

  (* Module Import Nat_as_OT. *)
  
  Definition t := channel_id.

  Definition eq := @eq t.
    
  Definition lt ch1 ch2 : Prop :=
    match (ch1, ch2) with
    | (Single n, Single n') => n < n'
    | (Intersection _ _, Single _) => True
    | (Intersection n1 n2, Intersection n1' n2') => (n1 = n1' /\ n2 < n2') \/ n1 < n1'
    | (Single _, Intersection _ _) => False
    end.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros; destruct x, y, z; try Nat.order; try propositional;
      [> left; split | right | right | right ]; Nat.order.
  Qed.

  Lemma lt_not_eq :
    forall x y, lt x y -> ~ eq x y.
  Proof.
    intros * H; destruct x, y; unfold lt in H; unfold not, eq;
      intro EQ; invert EQ; split_ors; subst; try Nat.order.
  Qed.

  (* Print Compare. *)
  (* Print lt. *)

  (* Definition compare (x y : t) : Compare lt eq x y := *)
  (*   match (x,y) with *)
  (*   | (Single n, Single n')          => *)
  (*     match Nat_as_OT.compare n n' with *)
  (*     | EQ neq => EQ (eq x y) *)
  (*     | LT nlt => @LT channel_id lt eq x y  *)
  (*     | GT ngt => GT (lt y x) *)
  (*     end *)
  (*   | (Intersection x1 x2, Single s) => LT lt (Intersection x1 x2) (Single s) *)
  (*   | (Intersection n1 n2, Intersection n1' n2') => (n1 = n1' /\ n2 < n2') \/ n1 < n1' *)
  (*   | (Single _, Intersection _ _) => False *)
  (*   end. *)
    



  
  Lemma compare :
    forall( x y : t), Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    case_eq (Nat.compare n n0); intro.
    apply EQ; unfold eq; f_equal; now apply nat_compare_eq.
    apply LT; unfold lt; now apply nat_compare_lt.
    apply GT; unfold lt; now apply nat_compare_gt.
    apply GT; unfold lt; eauto.
    apply LT; unfold lt; eauto.
    case_eq (Nat.compare ch1 ch0).
    case_eq (Nat.compare ch2 ch3); intros.
    apply EQ. unfold eq; f_equal; now apply nat_compare_eq.
    apply LT; unfold lt; f_equal; left.
    split; [ now apply nat_compare_eq
           | now apply nat_compare_lt].
    apply GT; unfold lt; left. split. apply Nat.eq_sym. now apply nat_compare_eq. now apply nat_compare_gt.

    intros; apply LT. unfold lt. right. now apply nat_compare_lt.
    intros; apply GT. unfold lt. right. now apply nat_compare_gt.
  Defined.

  Lemma eq_dec :
    forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq; destruct x, y.
    - destruct (eq_dec n n0); subst; eauto.
      right; intros H; invert H; contradiction.
    - right; unfold not; intros; discriminate.
    - right; unfold not; intros; discriminate.

    - cases (ch1 ==n ch0); cases (ch2 ==n ch3); cases (ch1 ==n ch3); cases (ch2 ==n ch0); subst;
        eauto; right; unfold not; intros H; invert H; contradiction.
  Qed.

End ChannelType.

Definition combine (ch1 ch2 : channel_id) :=
  match (ch1, ch2) with
  | (Single n, Single n') => if n <? n'
                            then Some (Intersection n' n)
                            else Some (Intersection n n')
  | _ => None
  end.

Module Import ChMap := MyOrderedMap( ChannelType ).

Module ChNotation.
  Notation "# x" := (Single x) (at level 50, left associativity).
  Notation "x #& y" := (Intersection x y) (at level 50, left associativity).
End ChNotation. 

Export ChNotation.

Module ChMapNotation.
  Notation "#0" := (empty _).
  Notation "m #+ ( k , v )" := (add k v m) (at level 50, left associativity).
  Notation "m #- k" := (remove k m) (at level 50, left associativity).
  Notation "m #? k" := (find k m) (at level 50, left associativity).
End ChMapNotation.

Export ChMapNotation.
  
Ltac m_equal :=
  repeat match goal with
         | [ |- context[_ #+ (?k,_) #? ?k ] ]  =>
           rewrite add_eq_o by (simple apply @eq_refl)
         | [ |- context[_ #+ (?k',_) #? ?k] ] =>
           rewrite add_neq_o by ( (unfold not; intros ?SIMPLEQ; invert SIMPLEQ) || intuition idtac )
         | [ |- (_ #+ (_,_)) = _ ] => unfold Map.add, Map.Raw.add; simpl
         | [ |- {| Map.this := _ ; Map.sorted := _ |} = _ ] => eapply map_eq_fields_eq
         | [ H : Map.Empty ?m |- #0 = ?m ] => eapply Empty_eq_empty; exact H
         | [ H : Map.Empty ?m |- ?m = #0 ] => symmetry
         | [ |- Map.empty _ = _ ] => unfold Map.empty, Map.Raw.empty, remove, Map.Raw.remove; simpl
         end.

Section ConcreteMaps.

  Definition next_key {V} (m : ChMap.t V) : channel_id :=
    match O.max_elt m with
    | None => Single 0
    | Some (Single k, v) => Single (S k)
    | Some (k1 #& k2, v) => Single 0
    end.

  Lemma next_key_not_in :
    forall {V} (m : ChMap.t V) k,
      k = next_key m
      -> m #? k = None.
  Proof.
    unfold next_key; intros.
    cases (O.max_elt m); subst.
    - destruct p; simpl.
      destruct k.
      + cases (m #? (# S n)); eauto.
        exfalso.
      
        assert (O.Above (# n) (m #- (# n))) by eauto using O.max_elt_Above.
        specialize (H (# S n)).

        assert (In (# S n) (m #- (# n))).
        rewrite in_find_iff; unfold not; intros.
        rewrite remove_neq_o in H0 by eauto; contra_map_lookup.
        specialize (H H0); simpl in H.
        
        assert (n < S n) by eauto using Nat.lt_succ_diag_r.
        Nat.order.

      + cases (m #? (# 0)); eauto.
        exfalso.

        assert (O.Above (ch1 #& ch2) (m #- (ch1 #& ch2))) by eauto using O.max_elt_Above.
        specialize (H (# 0)).
        
        assert (In (# 0) (m #- (ch1 #& ch2))).
        rewrite in_find_iff; unfold not; intros.
        rewrite remove_neq_o in H0 by eauto; contra_map_lookup.
        specialize (H H0); simpl in H; contradiction.

    - apply O.max_elt_Empty in Heq.
      apply Empty_eq_empty in Heq; subst.
      apply lookup_empty_none.
  Qed.

End ConcreteMaps.
