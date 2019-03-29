From Coq Require Import
     List
     Logic.ProofIrrelevance
     Program.Equality.

Require Import MyPrelude.
Require Import Users Common.
Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Section RealLemmas.

  Import RealWorld.

  Lemma real_univ_eq_fields_eq :
    forall {A B} (us us' : honest_users A) (a a' : adversaries B) ud ud',
      us = us'
      -> a = a'
      -> ud = ud'
      -> {| users := us
         ; adversary := a
         ; all_ciphers := ud
        |} =
        {| users := us'
         ; adversary := a'
         ; all_ciphers := ud'
        |}.
  Proof.
    intros; subst; reflexivity.
  Qed.

End RealLemmas.

Module Import OTF := OrderedType.OrderedTypeFacts OrderedTypeEx.Nat_as_OT.
Module Import OMF := FSets.FMapFacts.OrdProperties NatMap.

Section MapLemmas.

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

  Lemma Empty_eq_empty :
    forall v m,
      Empty (elt:=v) m
      -> $0 = m.
  Proof.
    intros.
    apply elements_Empty in H.
    apply map_eq_elements_eq. auto.
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
         | [ |- context[find ?k (add ?k _ _) ] ] => rewrite add_eq_o by (simple apply @eq_refl)
         | [ |- context[find ?k (add ?k' _ _) ] ] => rewrite add_neq_o by ( (unfold not; intros ?SIMPLEQ; invert SIMPLEQ) || intuition idtac )
         | [ |- context[$0 $++ _ ] ] => rewrite empty_add_idempotent
         | [ |- context[_ $++ $0 ] ] => rewrite add_empty_idempotent
         | [ |- (add _ _ _) = _ ] => normalize_set
         | [ |- (add _ _ _) = _ ] => unfold add, Raw.add; simpl
         | [ |- {| this := _ ; sorted := _ |} = _ ] => eapply map_eq_fields_eq
         | [ H : Empty ?m |- $0 = ?m ] => eapply Empty_eq_empty; exact H
         | [ H : Empty ?m |- ?m = $0 ] => symmetry
         | [ |- empty _ = _ ] => unfold empty, Raw.empty, remove, Raw.remove; simpl
         end.

Hint Rewrite add_empty_idempotent empty_add_idempotent : maps.

Ltac smash_universe :=
  unfold RealWorld.buildUniverse, updateUserList;
  repeat (match goal with
          | [ |- {| RealWorld.users := _
                 ; RealWorld.adversary := _
                 ; RealWorld.all_ciphers := _ |} = _
            ] => eapply real_univ_eq_fields_eq
          | [ |- _ = _ ] => reflexivity
          end; m_equal).

Section ExamplarProofs.

  (* User ids *)
  Definition A : user_id   := 0.
  Definition B : user_id   := 1.

  (* Section RealProtocolParams. *)
  (*   Import RealWorld. *)

  (*   Definition KID1 : key_identifier := 0. *)
  (*   Definition KID2 : key_identifier := 1. *)

  (*   Definition KEY1  := MkCryptoKey KID1 Signing. *)
  (*   Definition KEY2  := MkCryptoKey KID2 Signing. *)
  (*   Definition KEY__A  := AsymKey KEY1 true. *)
  (*   Definition KEY__B  := AsymKey KEY2 true. *)
  (*   Definition KEYS  := $0 $+ (KID1, AsymKey KEY1 true) $+ (KID2, AsymKey KEY2 true). *)

  (*   Definition A__keys := $0 $+ (KID1, AsymKey KEY1 true)  $+ (KID2, AsymKey KEY2 false). *)
  (*   Definition B__keys := $0 $+ (KID1, AsymKey KEY1 false) $+ (KID2, AsymKey KEY2 true). *)
  (* End RealProtocolParams. *)

  (* Lemma ex1: forall {AT : Type} cid1 (n : nat) cs, exists qn qcid1 qcs, *)
  (*   (RealWorld.updateUniverse *)
  (*      {| RealWorld.users := $0 $+ (A, *)
  (*         {| RealWorld.key_heap := A__keys; *)
  (*            RealWorld.protocol := *)
  (*              (_  <- RealWorld.Return tt; *)
  (*               m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept); *)
  (*               RealWorld.Return *)
  (*                 match RealWorld.unPair m' with *)
  (*                 | Some (RealWorld.Plaintext n', _) => *)
  (*                   if qn ==n n' then true else false *)
  (*                 | _ => false *)
  (*                 end)%realworld |}) $+ (B, *)
  (*         {| RealWorld.key_heap := B__keys; *)
  (*            RealWorld.protocol := *)
  (*              (m  <- RealWorld.Return (RealWorld.Signature (RealWorld.Plaintext qn) qcid1); *)
  (*               v  <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m; *)
  (*               m' <- match RealWorld.unPair m with *)
  (*                    | Some (p, _) => RealWorld.Sign KEY__B p *)
  (*                    | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1) *)
  (*                    end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |}); *)
  (*         RealWorld.adversary := ($0 : RealWorld.adversaries AT); *)
  (*         RealWorld.univ_data := *)
  (*           {| *)
  (*             RealWorld.users_msg_buffer := $0; *)
  (*             RealWorld.all_keys := KEYS; *)
  (*             RealWorld.all_ciphers := *)
  (*               qcs $+ (qcid1, *)
  (*                       RealWorld.Cipher qcid1 KID1 (RealWorld.Plaintext qn)) |} |} *)
  (*      {| RealWorld.users_msg_buffer := $0; *)
  (*         RealWorld.all_keys := KEYS; *)
  (*         RealWorld.all_ciphers := qcs $+ (qcid1, RealWorld.Cipher qcid1 KID1 (RealWorld.Plaintext qn)) |} $0 A A__keys *)
  (*      (m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept); *)
  (*       RealWorld.Return *)
  (*         match RealWorld.unPair m' with *)
  (*         | Some (RealWorld.Plaintext n', _) => if qn ==n n' then true else false *)
  (*         | _ => false *)
  (*         end)%realworld) =  *)
  (*      {| RealWorld.users := $0 $+ (A, *)
  (*         {| RealWorld.key_heap := A__keys; *)
  (*            RealWorld.protocol := *)
  (*              (m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept); *)
  (*               RealWorld.Return *)
  (*                 match RealWorld.unPair m' with *)
  (*                 | Some (RealWorld.Plaintext n', _) => if n ==n n' then true else false *)
  (*                 | _ => false *)
  (*                 end)%realworld |}) $+ (B, *)
  (*         {| RealWorld.key_heap := B__keys; *)
  (*            RealWorld.protocol := *)
  (*              (m <- RealWorld.Recv (RealWorld.Signed KID1 RealWorld.Accept); *)
  (*               v <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m; *)
  (*               m' <- match RealWorld.unPair m with *)
  (*                    | Some (p, _) => RealWorld.Sign KEY__B p *)
  (*                    | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1) *)
  (*                    end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |}) $+ (B, *)
  (*         {| RealWorld.key_heap := B__keys $++ $0; *)
  (*            RealWorld.protocol := *)
  (*              (m <- RealWorld.Return (RealWorld.Signature (RealWorld.Plaintext n) cid1); *)
  (*               v <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m; *)
  (*               m' <- match RealWorld.unPair m with *)
  (*                    | Some (p, _) => RealWorld.Sign KEY__B p *)
  (*                    | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1) *)
  (*                    end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |}); *)
  (*         RealWorld.adversary := $0; *)
  (*         RealWorld.univ_data := *)
  (*           {| RealWorld.users_msg_buffer := *)
  (*                $0 $+ (B, [Exm (RealWorld.Signature (RealWorld.Plaintext n) cid1)]) $- B; *)
  (*              RealWorld.all_keys := KEYS; *)
  (*              RealWorld.all_ciphers := cs $+ (cid1, RealWorld.Cipher cid1 KID1 (RealWorld.Plaintext n)) |} *)
  (*      |} *)
  (* . *)
  (* Proof. *)
  (*   intros; do 3 eexists. smash_universe. *)
  (* Qed. *)

End ExamplarProofs.
