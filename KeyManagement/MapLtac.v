From Coq Require Import
     List
     Logic.ProofIrrelevance
     Program.Equality.

Require Import MyPrelude Maps Common.
Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Section RealLemmas.

  Import RealWorld.

  Lemma real_univ_eq_fields_eq :
    forall {A B} (us us' : honest_users A) (a a' : user_data B) cs cs' ks ks',
      us = us'
      -> a = a'
      -> cs = cs'
      -> ks = ks'
      -> {| users       := us
         ; adversary   := a
         ; all_ciphers := cs
         ; all_keys    := ks
        |} =
        {| users       := us'
         ; adversary   := a'
         ; all_ciphers := cs'
         ; all_keys    := ks'
        |}.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma real_univ_same_as_fields :
    forall {A B} (U : universe A B) (us : honest_users A) (a : user_data B) cs ks,
        us = U.(users)
      -> a  = U.(adversary)
      -> cs = U.(all_ciphers)
      -> ks = U.(all_keys)
      -> {| users       := us
         ; adversary   := a
         ; all_ciphers := cs
         ; all_keys    := ks
        |} = U.
    intros; destruct U; subst; trivial.
  Qed.

End RealLemmas.

Hint Rewrite add_empty_idempotent empty_add_idempotent : maps.

Ltac smash_universe :=
  unfold RealWorld.buildUniverse;
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
