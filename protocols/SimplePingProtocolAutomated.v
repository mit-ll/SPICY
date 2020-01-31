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
     List.

Require Import
        MyPrelude
        Maps
        Messages
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.
Definition B : user_id   := 1.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := 0.

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := true; write := true |}). (* writer *)
  Definition PERMS__b := $0 $+ (CH__A2B, {| read := true; write := false |}). (* reader *)

  Definition mkiU (cv : channels) (p__a p__b : cmd (Base Nat)): universe Nat :=
    {| channel_vector := cv
     ; users := $0
         $+ (A,   {| perms    := PERMS__a ; protocol := p__a |})
         $+ (B,   {| perms    := PERMS__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU ($0 $+ (CH__A2B, []))
         (* user A *)
         ( n <- Gen
         ; _ <- Send (Content n) CH__A2B
         ; Return n)
         (* user B *)
         ( m <- @Recv Nat CH__A2B
         ; ret (extractContent m)).

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID1 : key_identifier := 0.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1).

  Definition A__keys := $0 $+ (KID1, true).
  Definition B__keys := $0 $+ (KID1, false).
End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs1 mycs2 : my_ciphers) (froms1 froms2 : recv_nonces)
                  (sents1 sents2 : sent_nonces) (cur_n1 cur_n2 : nat)
                  (msgs1 msgs2 : queued_messages) (cs : ciphers)
                  (p__a p__b : user_cmd (Base Nat)) (adv : user_data Unit) : universe Nat Unit :=
    {| users := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs1 ; c_heap := mycs1
                 ; from_nons := froms1 ; sent_nons := sents1 ; cur_nonce := cur_n1 |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b ; msg_heap := msgs2 ; c_heap := mycs2
                 ; from_nons := froms2 ; sent_nons := sents2 ; cur_nonce := cur_n2 |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
    |}.

  Definition real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 :=
    mkrU mycs1 mycs2 [] [] [] [] cur_n1 cur_n2 [] [] cs
         (* user A *)
         ( n  <- Gen
         ; c  <- Sign KID1 B (message.Content n)
         ; _  <- Send B c
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; ret (if fst v
                then match snd v with
                     | message.Content p => p
                     | _                 => 0
                     end
                else 1)).
  
End RealProtocol.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start mkrU
     ideal_univ_start mkiU : constants.

Import SimulationAutomation.

(* Hint Constructors *)
(*      RSimplePing. *)
(* Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) => *)
(*   simpl; simpl_real_users_context; simpl_ideal_users_context; simpl; *)
(*    ( (eapply Start  ; solve [ eauto ]) *)
(*    || (eapply Recd1' ; solve [ eauto ]) *)
(*    || (eapply Sent1' ; solve [ eauto ]) ). *)

Hint Extern 0 (~^* _ _) =>
 progress(unfold real_univ_start, mkrU; simpl).
(* Hint Extern 1 (RSimplePing (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl. *)

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, mkiU; simpl).

(* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor. *)
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Hint Extern 1 (istepSilent ^* _ _) =>
unfold ideal_univ_start, mkiU; simpl;
  repeat (ideal_single_silent_multistep A);
  repeat (ideal_single_silent_multistep B); solve_refl.


Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Module PD <: ProcDef.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start $0 [] [] 0 0 startAdv.
End PD.

Module G := Gen PD.

Import G PD ModelCheck Invariant Relations.

Definition protos_ok : (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) -> Prop :=
  lift_fst honest_cmds_safe.

Lemma g : invariantFor S protos_ok.
Proof.
  Hint Unfold ru0 iu0 ideal_univ_start mkiU real_univ_start mkrU.
  eapply Invariant.invariant_weaken.

  Import Tacs SetLemmas.

  - apply multiStepClosure_ok; simpl.
    gen1.
    gen1.
    gen1.
    gen1.
    gen1.
    gen1.
    gen1.


    gen1.

  - 
