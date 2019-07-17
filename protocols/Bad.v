From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Keys Simulation MapLtac Tactics Automation ProtocolAutomation AdversaryUniverse.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__B2A : channel_id := 0.

  Definition idealU1 :=
    {| channel_vector := $0 $+ (CH__B2A, {Exm (Content 2)})
       ; users := $0 $+ (A,  {| perms := $0  ; protocol :=
                                                 m <- @Recv Nat CH__B2A ; Return true |})
    |}.

  Definition idealU2 :=
    {| channel_vector := $0 $+ (CH__B2A, { Exm (Content 2) })
       ; users := $0 $+ (A,  {| perms := $0  ; protocol := Return true |})
    |}.

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID1 : key_identifier := 0.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1).
  Definition A__keys := $0 $+ (KID1, true).

End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs : my_ciphers) (msgs : queued_messages)
             (cs : ciphers) (adv : user_data unit) (p__a : user_cmd bool) : universe bool unit :=
    {| users            := $0 $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs ; c_heap := mycs |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
     |}.

  Definition ru1 adv :=
    mkrU [] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2))) adv
         ( c1 <- Sign KID1 (Plaintext 0)
         ; c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 c1
         ).

  Definition ru2 cid1 adv :=
    mkrU [cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         ( c1 <- Return (Signature (Plaintext 0) KID1 cid1)
         ; c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 c1
         ).

  Definition ru3 cid1 adv :=
    mkrU [cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         ( c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru4 cid1 cid2 adv :=
    mkrU [cid2;cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)]
         ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( c2 <- Return (Signature (Plaintext 1) KID1 cid2)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru5 cid1 cid2 adv :=
    mkrU [cid2;cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)]
         ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru6 cid1 cid2 adv :=
    mkrU [5;cid2;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( m <- Return (Signature (Plaintext 2) KID1 5)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru7 cid1 adv :=
    mkrU [5;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         (Verify KID1 (Signature (Plaintext 0) KID1 cid1)).

  Definition ru8 cid1 adv :=
    mkrU [5;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         (Return true).

  Inductive R : RealWorld.simpl_universe bool -> IdealWorld.universe bool -> Prop :=
  | R1 : forall adv,
      lameAdv tt adv
      -> R (peel_adv (ru1 adv)) idealU1
  | R2 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru2 cid1 adv)) idealU1
  | R3 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru3 cid1 adv)) idealU1
  | R4 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru4 cid1 cid2 adv)) idealU1
  | R5 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru5 cid1 cid2 adv)) idealU1
  | R6 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru6 cid1 cid2 adv)) idealU2
  | R7 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru7 cid1 adv)) idealU2
  | R8 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru8 cid1 adv)) idealU2
  .

End RealProtocol.

Import SimulationAutomation SimulationAutomation.T.

Section FeebleSimulates.

  Lemma rpingbase_silent_simulates :
    simulates_silent_step (lameAdv tt) R.
  Proof.
    unfold simulates_silent_step; intros.

    intros; invert H;
      try destruct U__r0; try destruct U__r; simpl in *; subst.

    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R2; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R3; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        simpl.
        eapply R4; eauto.

    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R5; eauto.
    - churn. admit.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R7; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R8; eauto.

End FeebleSimulates.
