From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.
Require Import Users Common Simulation.
Require RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Section RealLemmas.

  Lemma real_univ_eq_fields_eq :
    forall {A} (us us' : user_list (RealWorld.user_data A)) a a' ud ud',
      us = us'
      -> a = a'
      -> ud = ud'
      -> {| RealWorld.users := us
         ; RealWorld.adversary := a
         ; RealWorld.univ_data := ud
        |} =
        {| RealWorld.users := us'
         ; RealWorld.adversary := a'
         ; RealWorld.univ_data := ud'
        |}.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma real_ud_eq_fields_eq :
    forall um um' ks ks' cs cs',
        um = um'
      -> ks = ks'
      -> cs = cs'
      -> {| RealWorld.users_msg_buffer := um;
           RealWorld.all_keys         := ks;
           RealWorld.all_ciphers      := cs
        |} =
        {| RealWorld.users_msg_buffer := um';
           RealWorld.all_keys         := ks';
           RealWorld.all_ciphers      := cs'
        |}.
  Proof.
    intros; subst; reflexivity.
  Qed.

End RealLemmas.

Section MapLemmas.

  Lemma map_eq_fields_eq :
    forall {V} (th th' : Raw.t V) s s',
        th = th'
      -> {| this := th ; sorted := s |} = {| this := th' ; sorted := s' |}.
  Proof.
    intros; subst; f_equal; apply proof_irrelevance.
  Qed.
  
  Lemma add_empty_idempotent :
    forall V (m : NatMap.t V),
      m $++ $0 = m.
  Proof.
    intros; unfold merge_maps, fold, Raw.fold; simpl; auto.
  Qed.

End MapLemmas.

Ltac m_equal :=
  repeat match goal with
         (* | [ |- context[find ?k (add ?k' _ _) ] ] => idtac k; idtac k'; case (eq_dec k k'); intro *)
         | [ |- context[find ?k (add ?k _ _) ] ] => rewrite add_eq_o by (simple apply @eq_refl)
         | [ |- context[find ?k (add ?k' _ _) ] ] => rewrite add_neq_o by discriminate
         | [ |- (add _ _ _) = _ ] => normalize_set
         | [ |- (add _ _ _) = _ ] => unfold add, Raw.add; simpl
         | [ |- empty _ = _ ] => unfold empty, Raw.empty, remove, Raw.remove; simpl
         | [ |- {| this := _ ; sorted := _ |} = _ ] => eapply map_eq_fields_eq
         end.

Hint Rewrite add_empty_idempotent : maps.
  
Ltac smash_universe :=
  unfold RealWorld.updateUniverse, updateUserList;
  repeat (match goal with
          | [ |- {| RealWorld.users := _
                   ; RealWorld.adversary := _
                   ; RealWorld.univ_data := _ |} = _
            ] => eapply real_univ_eq_fields_eq
          | [ |- {| RealWorld.users_msg_buffer := _
                   ; RealWorld.all_keys         := _
                   ; RealWorld.all_ciphers      := _ |} = _
            ] => eapply real_ud_eq_fields_eq
          | [ |- _ = _ ] => reflexivity
          end; m_equal).


Section ExamplarProofs.

  (* User ids *)
  Definition A : user_id   := 0.
  Definition B : user_id   := 1.

  Section RealProtocolParams.
    Import RealWorld.

    Definition KID1 : key_identifier := 0.
    Definition KID2 : key_identifier := 1.

    Definition KEY1  := MkCryptoKey KID1 Signing.
    Definition KEY2  := MkCryptoKey KID2 Signing.
    Definition KEY__A  := AsymKey KEY1 true.
    Definition KEY__B  := AsymKey KEY2 true.
    Definition KEYS  := $0 $+ (KID1, AsymKey KEY1 true) $+ (KID2, AsymKey KEY2 true).

    Definition A__keys := $0 $+ (KID1, AsymKey KEY1 true)  $+ (KID2, AsymKey KEY2 false).
    Definition B__keys := $0 $+ (KID1, AsymKey KEY1 false) $+ (KID2, AsymKey KEY2 true).
  End RealProtocolParams.

  Lemma ex1: forall cid1 (n : nat) cs, exists qn qcid1 qcs,
    (RealWorld.updateUniverse
       {| RealWorld.users := $0 $+ (A,
          {| RealWorld.key_heap := A__keys;
             RealWorld.protocol :=
               (_  <- RealWorld.Return tt;
                m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept);
                RealWorld.Return
                  match RealWorld.unPair m' with
                  | Some (RealWorld.Plaintext n', _) =>
                    if qn ==n n' then true else false
                  | _ => false
                  end)%realworld |}) $+ (B,
          {| RealWorld.key_heap := B__keys;
             RealWorld.protocol :=
               (m  <- RealWorld.Return (RealWorld.Signature (RealWorld.Plaintext qn) qcid1);
                v  <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m;
                m' <- match RealWorld.unPair m with
                     | Some (p, _) => RealWorld.Sign KEY__B p
                     | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1)
                     end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |});
          RealWorld.adversary := $0;
          RealWorld.univ_data :=
            {|
              RealWorld.users_msg_buffer := $0;
              RealWorld.all_keys := KEYS;
              RealWorld.all_ciphers :=
                qcs $+ (qcid1,
                        RealWorld.Cipher qcid1 KID1 (RealWorld.Plaintext qn)) |} |}
       {| RealWorld.users_msg_buffer := $0;
          RealWorld.all_keys := KEYS;
          RealWorld.all_ciphers := qcs $+ (qcid1, RealWorld.Cipher qcid1 KID1 (RealWorld.Plaintext qn)) |} $0 A A__keys
       (m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept);
        RealWorld.Return
          match RealWorld.unPair m' with
          | Some (RealWorld.Plaintext n', _) => if qn ==n n' then true else false
          | _ => false
          end)%realworld) = 
       {| RealWorld.users := $0 $+ (A,
          {| RealWorld.key_heap := A__keys;
             RealWorld.protocol :=
               (m' <- @RealWorld.Recv (RealWorld.Pair RealWorld.Nat RealWorld.CipherId) (RealWorld.Signed KID2 RealWorld.Accept);
                RealWorld.Return
                  match RealWorld.unPair m' with
                  | Some (RealWorld.Plaintext n', _) => if n ==n n' then true else false
                  | _ => false
                  end)%realworld |}) $+ (B,
          {| RealWorld.key_heap := B__keys;
             RealWorld.protocol :=
               (m <- RealWorld.Recv (RealWorld.Signed KID1 RealWorld.Accept);
                v <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m;
                m' <- match RealWorld.unPair m with
                     | Some (p, _) => RealWorld.Sign KEY__B p
                     | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1)
                     end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |}) $+ (B,
          {| RealWorld.key_heap := B__keys $++ $0;
             RealWorld.protocol :=
               (m <- RealWorld.Return (RealWorld.Signature (RealWorld.Plaintext n) cid1);
                v <- RealWorld.Verify (RealWorld.AsymKey KEY1 false) m;
                m' <- match RealWorld.unPair m with
                     | Some (p, _) => RealWorld.Sign KEY__B p
                     | None => RealWorld.Sign KEY__B (RealWorld.Plaintext 1)
                     end; _ <- RealWorld.Send A m'; RealWorld.Return v)%realworld |});
          RealWorld.adversary := $0;
          RealWorld.univ_data :=
            {| RealWorld.users_msg_buffer :=
                 $0 $+ (B, [Exm (RealWorld.Signature (RealWorld.Plaintext n) cid1)]) $- B;
               RealWorld.all_keys := KEYS;
               RealWorld.all_ciphers := cs $+ (cid1, RealWorld.Cipher cid1 KID1 (RealWorld.Plaintext n)) |}
       |}
  .
  Proof.
    intros; do 3 eexists. smash_universe.
  Qed.

End ExamplarProofs.
