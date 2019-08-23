From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Keys Simulation MapLtac Tactics Automation AdversaryUniverse ProtocolAutomation.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.
Definition B : user_id   := 1.

Transparent A B.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := 0.
  Definition CH__B2A : channel_id := 1.

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := false; write := true |}) $+ (CH__B2A, {| read := true; write := false |}).
  Definition PERMS__b := $0 $+ (CH__B2A, {| read := false; write := true |}) $+ (CH__A2B, {| read := true; write := false |}).

  Definition mkiU (cv : channels) (p__a p__b : cmd bool): universe bool :=
    {| channel_vector := cv
     ; users := $0
         $+ (A,   {| perms    := PERMS__a ; protocol := p__a |})
         $+ (B,   {| perms    := PERMS__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU ($0 $+ (CH__A2B, { }) $+ (CH__B2A, { }))
         ( n <- Gen
         ; _ <- Send (Content n) CH__A2B
         ; m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- @Recv Nat CH__A2B
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_sent1 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, { }))
         ( _ <- Return tt
         ; m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- @Recv Nat CH__A2B
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_recd1 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, { }))
         ( m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- Return (Content n)
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_sent2 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         ( m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( _ <- Return tt
         ; Return true).

  Definition ideal_univ_recd2 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         ( m <- Return (Content n)
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         (Return true).

  Definition ideal_univ_done n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         (Return true)
         (Return true).

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID1 : key_identifier := 0.
  Definition KID2 : key_identifier := 1.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEY2  := MkCryptoKey KID2 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1) $+ (KID2, KEY2).

  Definition A__keys := $0 $+ (KID1, true) $+ (KID2, false).
  Definition B__keys := $0 $+ (KID1, false) $+ (KID2, true).
End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs1 mycs2 : my_ciphers) (msgs1 msgs2 : queued_messages)
                  (cs : ciphers) (p__a p__b : user_cmd bool) (adv : user_data unit) : universe bool unit :=
    {| users            := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs1 ; c_heap := mycs1 |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b ; msg_heap := msgs2 ; c_heap := mycs2 |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
     |}.

  Definition real_univ_start cs mycs1 mycs2 :=
    mkrU  mycs1 mycs2 [] [] cs
         ( n  <- Gen
         ; m  <- Sign KID1 (Plaintext n)
         ; _  <- Send B m
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent1 n cs mycs1 mycs2 cid1 :=
    mkrU  mycs1 mycs2 [] [existT _ _ (Signature (Plaintext n) KID1 cid1)]
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)
         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_recd1 n cs mycs1 mycs2 cid1 :=
    mkrU mycs1 mycs2 [] []
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- Return (Signature (Plaintext n) KID1 cid1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent2 n cs mycs1 mycs2 cid1 cid2 :=
    mkrU mycs1 mycs2 [existT _ _ (Signature (Plaintext n) KID2 cid2)] []
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)) $+ (cid2, SigCipher KID2 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_recd2 n cs mycs1 mycs2 cid1 cid2 :=
    mkrU mycs1 mycs2 [] [] (cs $+ (cid1, SigCipher KID1 (Plaintext n)) $+ (cid2, SigCipher KID2 (Plaintext n)))
         ( m' <- Return (Signature (Plaintext n) KID2 cid2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_done mycs1 mycs2 cs :=
    mkrU mycs1 mycs2 [] [] cs (Return true) (Return true).

  Inductive RPingPongBase: RealWorld.simpl_universe bool -> IdealWorld.universe bool -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 adv,
        rstepSilent^* (real_univ_start mycs1 mycs2 cs adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) ideal_univ_start

  | Sent1 : forall U__r cs mycs1 mycs2 cid1 n adv,
        rstepSilent^* (real_univ_sent1 n cs mycs1 mycs2 cid1 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_sent1 n)

  | Recd1 : forall U__r cs mycs1 mycs2 cid1 n adv,
        rstepSilent^* (real_univ_recd1 n cs mycs1 mycs2 cid1 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_recd1 n)

  | Sent2 : forall U__r cs mycs1 mycs2 cid1 cid2 n adv,
        rstepSilent^* (real_univ_sent2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_sent2 n)

  | Recd2 : forall U__r cs mycs1 mycs2 cid1 cid2 n adv,
        rstepSilent^* (real_univ_recd2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_recd2 n)

  | Done : forall U__r cs mycs1 mycs2 n adv,
      lameAdv tt adv
      -> U__r = real_univ_done cs mycs1 mycs2 adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_done n)
  .

End RealProtocol.

Hint Constructors RealWorld.msg_accepted_by_pattern.
Hint Constructors RPingPongBase.

Import SimulationAutomation.

Hint Extern 0 (rstepSilent ^* _ _) =>
progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1,
                real_univ_sent2, real_univ_recd2, real_univ_done, mkrU; simpl).
Hint Extern 1 (RPingPongBase (RealWorld.buildUniverse _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.

Hint Extern 1 (IdealWorld.lstep_universe _ _ _) =>
progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1,
                ideal_univ_sent2, ideal_univ_recd2, ideal_univ_done, mkiU; simpl).

Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2.
Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2.
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Section FeebleSimulates.

  Lemma rpingbase_silent_simulates :
    simulates_silent_step (lameAdv tt) RPingPongBase.
  Proof.
    unfold simulates_silent_step.

    time (
        intros;
        invert H;
        try destruct U__r0; try destruct U__r; simpl in *; subst;
        churn; simpl_real_users_context;
        [> eexists; split; swap 1 2; eauto 9 ..]
      ).
  Qed.

  Lemma rpingbase_loud_simulates :
    simulates_labeled_step (lameAdv tt) RPingPongBase.
  Proof.
    unfold simulates_labeled_step.

    time
      (intros;
       invert H;
       try destruct U__r0; try destruct U__r; simpl in *; subst;
       churn;
       simpl_real_users_context;
       (* autorewrite with simpl_univ; *)
       (* simpl; *)
       (do 3 eexists;
        repeat
          match goal with
          | [ |- _ /\ _ ] => split
          end; swap 3 4; swap 1 3; [ .. | admit (* action matches predicate *)];
        eauto; eauto 12)).

  Admitted.

  Lemma rpingbase_univere_ok :
    simulates_universe_ok RPingPongBase.
  Proof.
    unfold simulates_universe_ok; intros.

    time (
        inversion H; clear H; churn; solve_uok; eauto
      ).

  Qed.

  Lemma rpingbase_labeled_simulates_safe :
    simulates_labeled_step_safe RPingPongBase.
  Proof.
    unfold simulates_labeled_step_safe.
    intros.

    assert (RealWorld.findUserKeys U__r.(RealWorld.users) =
            RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.users)))
      by (symmetry; eapply clean_users_no_change_findUserKeys).
    remember (RealWorld.findUserKeys U__r.(RealWorld.users)) as honestk.

    time(
        inversion H; clear H;
        churn;
        [> users_inversion; churn; repeat equality1; solve_adv_safe; eauto .. ]
      ).

  Qed.

  (* Timings:
   *
   * 20190718 (laptop run: directed proof search for rstepSilent ^* goals)
   * Tactic call ran for 50.758 secs (50.693u,0.064s) (success)
   * Tactic call ran for 45.01 secs (44.965u,0.043s) (success)
   * Tactic call ran for 39.41 secs (39.398u,0.012s) (success)
   * Tactic call ran for 29.111 secs (29.076u,0.031s) (success)
   *
   * 20190715 (laptop run: update to simulation statement)
   * Tactic call ran for 1003.739 secs (1003.249u,0.435s) (success)
   * Tactic call ran for 67.14 secs (67.13u,0.008s) (success)
   * Tactic call ran for 51.881 secs (51.877u,0.004s) (success)
   * Tactic call ran for 38.373 secs (38.364u,0.008s) (success)
   *
   * 20190628 (laptop run: inversion lemmas)
   * Tactic call ran for 870.78 secs (870.427u,0.272s) (success)
   * Tactic call ran for 64.791 secs (64.786u,0.004s) (success)
   * Tactic call ran for 38.868 secs (38.868u,0.s) (success)
   *
   * 20190624 (laptop run: block inversion of rstepSilent if don't know start univ -- saving restepping through protocol for adversary)
   * Tactic call ran for 1272.565 secs (1271.919u,0.596s) (success)
   * Tactic call ran for 314.031 secs (314.027u,0.004s) (success)
   * Tactic call ran for 283.061 secs (282.885u,0.148s) (success)
   * --------------------------------------------------------------
   * (no date, desktop run (laptop more like 1700): starting point after refactor)
   * Tactic call ran for 1468.475 secs (1467.238u,1.061s) (success)
   * Tactic call ran for 257.673 secs (257.516u,0.091s) (success)
   * --------------------------------------------------------------
   *)

  Hint Resolve
       rpingbase_silent_simulates
       rpingbase_loud_simulates
       rpingbase_univere_ok
       rpingbase_labeled_simulates_safe.

  Lemma univ_ok_start :
    forall adv,
      lameAdv tt adv
      -> universe_ok (real_univ_start $0 [] [] adv).
  Proof.
    unfold real_univ_start; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start :
    forall adv U__r honestk,
        U__r = real_univ_start $0 [] [] adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv_message_queue_ok honestk adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      -> adv_universe_ok (real_univ_start $0 [] [] adv).
  Proof.
    unfold real_univ_start, adv_universe_ok, adv_no_honest_keys;
      simpl; intuition (subst; eauto).

    - unfold keys_good, KEYS, KID1, KID2, KEY1, KEY2; intros.
      cases (0 ==n k_id); cases (1 ==n k_id); subst; clean_map_lookups; eauto.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

  Qed.

  Hint Resolve
       univ_ok_start
       adv_univ_ok_start.

  Theorem base_pingpong_refines_ideal_pingpong :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv_message_queue_ok honestk adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      (* real_univ_start $0 [] [] adv <| ideal_univ_start / lameAdv tt. *)
      -> refines (lameAdv tt) U__r ideal_univ_start.
  Proof.
    exists RPingPongBase; unfold simulates.
    intuition (subst; eauto).
  Qed.

End FeebleSimulates.
