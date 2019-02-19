From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.

Require Import Common Simulation.
Require IdealWorld RealWorld.

Set Implicit Arguments.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

(* I need to build a proof harness :eyeroll: that takes an adversary's permission set and returns
   a universe in which infinite adversaries with those permissions can be run. Currently this is 
   identical to ping, but ping would be run against adversary with r/w permissions to 0, while in
   this case the adversary has w permission. *)

Section SimpleIdealEncProtocol.
  Import IdealWorld.

  Definition A := 0.
  Definition B := 1.
  Definition adversary := 2.

  Example ideal_enc_universe (adversary_protocol : cmd nat) : universe nat :=
    {| channel_vector := $0 $+ (0, {});
       users := [
               (A, {| perms := $0 $+ (0, {| read := true ; write := true |});
                      protocol := (
                        _ <- Send (Content 2) 0
                      ; Return 1)
                   |});
               (B, {| perms := $0 $+ (0, {| read := true ; write := true |});
                      protocol := (
                        r <- Recv 0
                      ; Return match extractContent r with Some c => c | None => 0 end)
                          
                   |});
               (adversary, {| perms := $0 $+ (0, {| read := false ; write := true |}) ;
                              protocol := adversary_protocol |})
               ]
    |}.
  
  Definition auth_sys (adversary_protocol : cmd nat) :=
    {| Initial := fun U' => U' = ideal_enc_universe adversary_protocol ;
       Step := step_universe |}.

  (* not sure what an appropriate variable would be, final state set inclusion on adversary maybe? *)
End SimpleIdealEncProtocol.

Module Type RealEncPingProtocolParameters.
  Import RealWorld.

  Parameter KEYID : key_identifier.
  Parameter KEY : key.

  Parameter RA : nat.
  Parameter RB : nat.
  Parameter Radversary : nat.

  Parameter uks0 : keys.
  Parameter uks1 : keys.
  Parameter ks   : keys.

End RealEncPingProtocolParameters.

Module RealEncPingProtocol (P : RealEncPingProtocolParameters).
  Import RealWorld.
  Import P.

  Example enc_ping (adversary_protocol : user_cmd nat) : list (user_data nat) := [
    {| usrid    := RA
     ; key_heap := uks0
     ; protocol := (  m <- Encrypt KEY (Plaintext 2)
                    ; _ <- Send RB m
                    ; Return 1)
    |}
    ;
    {| usrid    := RB
     ; key_heap := uks1
     ; protocol := (  cmsg <- Recv (A := cipher_id)
                    ; rec <- Decrypt cmsg
                    ; Return (match extractPlainText rec with
                              | Some msg => msg
                              | None     => 98
                              end))
    |}
    ; 
    {| usrid    := Radversary
     ; key_heap := $0
     ; protocol := adversary_protocol
    |}].

  Example enc_ping_universe (adversary_protocol : user_cmd nat) : universe nat :=
    {|
      users            := map (fun u_d => (u_d.(usrid), u_d)) (enc_ping adversary_protocol)
    ; users_msg_buffer := $0
    ; all_keys         := ks
    ; all_ciphers      := $0
    |}.

End RealEncPingProtocol.

Module EncPingProtocolSimulation (P : RealEncPingProtocolParameters).

  Module RealProtocol := RealEncPingProtocol ( P ).
  Import P RealProtocol.
  Export RealProtocol.

  Definition RUFinal cs :=
        {| RealWorld.users   := ([
               (RA, {| RealWorld.usrid    := RA
                    ; RealWorld.key_heap := uks0
                    ; RealWorld.protocol := RealWorld.Return 1 |} )

             ; (RB, {| RealWorld.usrid    := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := RealWorld.Return 2 |} )
             ; (Radversary, {| RealWorld.usrid    := Radversary
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 0 |} )
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := ks
        ; RealWorld.all_ciphers      := cs
        |}.

  Definition IUFinal :=
    {| IdealWorld.channel_vector := $0 $+ (0, {Exm (IdealWorld.Content 2)});
       IdealWorld.users := [
               (A, {| IdealWorld.perms := $0 $+ (0, {| IdealWorld.read := true ;  IdealWorld.write := true |});
                      IdealWorld.protocol := IdealWorld.Return 1
                   |});
               (B, {| IdealWorld.perms := $0 $+ (0, {|  IdealWorld.read := true ;  IdealWorld.write := true |});
                      IdealWorld.protocol := IdealWorld.Return 2
                   |}) ;
               (adversary, {| IdealWorld.perms := $0 $+ (0, {|  IdealWorld.read := false ;  IdealWorld.write := true |}) ;
                              IdealWorld.protocol := IdealWorld.Return 0 |})
               ]
    |}.

  Inductive RSymEncPing : RealWorld.universe nat -> IdealWorld.universe nat -> Prop :=
  | Start :
      RSymEncPing (enc_ping_universe (RealWorld.Return 0)) (ideal_enc_universe (IdealWorld.Return 0))

  | BeforeReceive : forall RU rcmd0 qmsgs cs,
      RU =
       {|
         RealWorld.users   := ([
               (RA, {| RealWorld.usrid   := RA
                    ; RealWorld.key_heap := uks0
                    ; RealWorld.protocol := rcmd0 |} )

             ; (RB, {| RealWorld.usrid   := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := (
                        cmsg <- RealWorld.Recv (A := RealWorld.cipher_id)
                      ; rec <- RealWorld.Decrypt cmsg
                      ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                          | Some msg => msg
                                          | None     => 98
                                          end)) |})
             ; (Radversary, {| RealWorld.usrid := Radversary
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 0 |} )
                               ])%realworld
        ; RealWorld.users_msg_buffer := qmsgs
        ; RealWorld.all_keys         := ks
        ; RealWorld.all_ciphers      := cs
       |}
      -> (exists cid,
            let ciphertext := RealWorld.Ciphertext cid
            in  cs = $0 $+ (cid, RealWorld.Cipher cid KEYID (RealWorld.Plaintext 2))
              /\ ( (qmsgs = $0
                   /\ ( rcmd0 = ( m <- RealWorld.Return ciphertext ; _ <- RealWorld.Send RB m ; RealWorld.Return 1)
                     \/ rcmd0 = ( _ <- RealWorld.Send RB ciphertext ; RealWorld.Return 1) ))
                \/ (qmsgs = $0 $+ (RB, [Exm ciphertext])
                   /\ ( rcmd0 = ( _ <- RealWorld.Return tt ; RealWorld.Return 1)
                     \/ rcmd0 = ( RealWorld.Return 1) ))
                )
        )%realworld
      -> RSymEncPing RU
        {| IdealWorld.channel_vector := $0 $+ (0, {Exm (IdealWorld.Content 2)})
         ; IdealWorld.users := ([
              (A, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 1
                  |})
            ; (B, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- IdealWorld.Recv 0
                     ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 0 end)
                  |})
            ; (adversary, {| IdealWorld.perms := $0 $+ (0, {|  IdealWorld.read := false ;  IdealWorld.write := true |}) ;
                             IdealWorld.protocol := IdealWorld.Return 0 |})
                               ])%idealworld
        |}
 
  | AfterReceive : forall RU rcmd0 rcmd1 cs,
      RU =
       {|
         RealWorld.users   := ([
               (RA, {| RealWorld.usrid    := RA
                    ; RealWorld.key_heap := uks0
                    ; RealWorld.protocol := rcmd0 |} )

             ; (RB, {| RealWorld.usrid    := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := rcmd1 |} )
             ; (Radversary, {| RealWorld.usrid := Radversary
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 0 |} )
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := ks
        ; RealWorld.all_ciphers      := cs
       |}
      -> (  rcmd0 = ( _ <- RealWorld.Return tt ; RealWorld.Return 1)
         \/ rcmd0 = ( RealWorld.Return 1)
        )%realworld
      -> (exists cid,
            let ciphertext := RealWorld.Ciphertext cid
            in  cs = $0 $+ (cid, RealWorld.Cipher cid KEYID (RealWorld.Plaintext 2))
                /\ ( rcmd1 = (cmsg <- RealWorld.Return ciphertext
                             ; rec <- RealWorld.Decrypt cmsg
                             ; RealWorld.Return (match RealWorld.extractPlainText rec with | Some msg => msg | None => 98 end))
                  \/ rcmd1 = (rec <- RealWorld.Decrypt ciphertext
                             ; RealWorld.Return (match RealWorld.extractPlainText rec with | Some msg => msg | None => 98 end))
                  \/ rcmd1 = (rec <- RealWorld.Return (RealWorld.Plaintext 2)
                             ; RealWorld.Return (match RealWorld.extractPlainText rec with | Some msg => msg | None => 98 end))
                  \/ rcmd1 = RealWorld.Return 2)
        )%realworld
      -> RU <> RUFinal cs
      -> RSymEncPing RU IUFinal

  | SimpleFinish : forall RU IU cs,
        RU = RUFinal cs
      -> IU = IUFinal
      -> (exists cid, cs = $0 $+ (cid, RealWorld.Cipher cid KEYID (RealWorld.Plaintext 2)))
      -> RSymEncPing RU IU
  .

  Hint Extern 1 (IdealWorld.step_universe ^* _ IUFinal) => unfold IUFinal.
  Hint Extern 1 (IdealWorld.step_universe ^* IUFinal _ ) => solve TrcRefl.
    Hint Extern 1 (_ <> RUFinal _) => discriminate.

End EncPingProtocolSimulation.

(* Set up most of the automation *)

Hint Constructors Forall.

Ltac fixcontext1 :=
  match goal with
  | [ H : $0 $? _ = Some _ |- _ ] => apply lookup_empty_not_Some in H; contradiction
  | [ H : (_ $+ (_, _)) $? _ = Some _ |- _ ] => apply lookup_split in H; propositional; subst
  | [ H : (_, _) = (_,_) |- _ ] => invert H
  | [ H : In _ _ |- _ ] => inversion H; clear H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ H : (_ :: _) = _ |- _ ] => invert H
  | [ H : _ \/ _ |- _ ] => invert H
  | [ H : exists _, _ |- _ ] => invert H
  | [ H : Some _ = Some _ |- _ ] => invert H
  | [ H : RealWorld.Cipher _ _ _ = RealWorld.Cipher _ _ _ |- _ ] => invert H
  | [ H : RealWorld.encryptMessage _ _ _ = Some _ |- _ ] => invert H
  end.
    
Ltac rw_step1 :=
  match goal with
  | [ H : RealWorld.step_universe _ _ |- _ ] => invert H
  | [ H : RealWorld.step_user _ _ _ |- _ ] => invert H
  end.
    
Ltac take_step := rw_step1; repeat fixcontext1; simpl in *; repeat fixcontext1.

Ltac final_steps :=
  match goal with
  | [ H : realWorldIsReallyFinalState _ |- _ ] => invert H
  | [ H : exists a , _ |- _ ] => invert H
  | [ H : RealWorld.protocol _ = RealWorld.Return _ |- _ ] => simpl in H; invert H
  | [ H : _ = RealWorld.Return _ |- _ ] => invert H
  | [ H : RealWorld.Return _ = _ |- _ ] => invert H
  | [ H : Forall _ _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ H : _ \/ _ |- _ ] => invert H
  end.
    
Hint Extern 1 (In _ (IdealWorld.users _)) => progress simpl.
Hint Extern 1 (_ \in _ ) => sets.
Hint Extern 1 (IdealWorld.step_user (_, IdealWorld.Bind _ _, _) _) => eapply IdealWorld.StepBindRecur; simplify.
Hint Extern 1 (IdealWorld.step_user (_, IdealWorld.Send _ _, _) _) => eapply IdealWorld.StepSend'; simplify.
Hint Extern 1 (IdealWorld.step_user (IdealWorld.channel_vector _, _, _) _) => progress simpl.
Hint Extern 1 (IdealWorld.protocol _ = _) => progress simpl.

Ltac step_user0 :=
  eapply TrcFront; [  
    eapply IdealWorld.StepUser'; simplify; [ left; reflexivity | | reflexivity ] | ]; simplify.

Ltac step_user1 :=
  eapply TrcFront; [  
    eapply IdealWorld.StepUser'; simplify; [ right; left; reflexivity | | reflexivity ] | ]; simplify.

Hint Extern 1 (IdealWorld.step_universe ^* (ideal_enc_universe _) _) => unfold ideal_enc_universe.
Hint Extern 2 (IdealWorld.step_universe ^* _ _) => (solve TrcRefl) || step_user0.
Hint Extern 2 (IdealWorld.step_universe ^* _ _) => (solve TrcRefl) || step_user1.

Hint Extern 1 (RealWorld.multiMapAdd _ _ _ = _) => unfold RealWorld.multiMapAdd.

Hint Extern 1 (Some _ = Some _) => reflexivity || f_equal.
Hint Extern 1 (RealWorld.Cipher _ _ _ = RealWorld.Cipher _ _ _) => f_equal.
Hint Extern 1 (None = Some _) => contradiction.
Hint Extern 1 (Some _ = None) => contradiction.
    
Hint Extern 1 ( add _ _ _ = _ ) => maps_equal.
Hint Extern 1 ( (RealWorld.updateUniverse _ _ _ _ _ _ _) = _) => reflexivity || (rewrite addRemoveKey; [ reflexivity | trivial ]).

Module Type EncPingProtocolCorrectT (P : RealEncPingProtocolParameters).

  Module Sim := EncPingProtocolSimulation (P).
  Import P Sim.
  Export P Sim.

  Axiom simulation_steps_simulate : 
    forall U1 U2,
      RSymEncPing U1 U2
      -> forall U1',
        RealWorld.step_universe U1 U1'
        -> exists U2',
          IdealWorld.step_universe^* U2 U2'
          /\ RSymEncPing U1' U2'.

  Axiom finalStatesAre :
    forall {U1 : RealWorld.universe nat} {U2 : IdealWorld.universe nat},
      RSymEncPing U1 U2
      -> realWorldIsReallyFinalState U1
      -> U1.(RealWorld.users) = [
               (RA, {| RealWorld.usrid    := RA
                    ; RealWorld.key_heap := uks0
                    ; RealWorld.protocol := RealWorld.Return 1 |} )

             ; (RB, {| RealWorld.usrid    := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := RealWorld.Return 2 |} )
             ; (Radversary, {| RealWorld.usrid    := Radversary
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 0 |} )
                               ]
        /\ U2.(IdealWorld.users) = IUFinal.(IdealWorld.users).
  
  Axiom sim_finishes_correctly :
    forall U1 U2,
      RSymEncPing U1 U2
      -> realWorldIsReallyFinalState U1
      -> idealWorldIsReallyFinalState U2
        /\ realWorldReturnsOf U1 = idealWorldReturnsOf U2.

End EncPingProtocolCorrectT.

Module EncPingProtocolCorrect (P : RealEncPingProtocolParameters) (T : EncPingProtocolCorrectT (P)).

  Import T.
  Section HideHints.

    Hint Constructors RSymEncPing.
    Hint Extern 1 (idealWorldIsReallyFinalState _) => unfold idealWorldIsReallyFinalState; simplify.
    Hint Extern 1 (exists _, _ = _) => eexists; simplify; reflexivity.
    Hint Constructors Forall.
    
    Hint Resolve simulation_steps_simulate sim_finishes_correctly.
    
    Theorem idealSymEncPingRefinesRealSymEncPing :
      enc_ping_universe (RealWorld.Return 0) <| ideal_enc_universe (IdealWorld.Return 0).
    Proof.
      exists RSymEncPing.
      assert (F := sim_finishes_correctly).
      unfold simulates; firstorder; eauto.
    Qed.

    Theorem ping_protocol_ok :
      finalAnswerInclusion (enc_ping_universe (RealWorld.Return 0)) (ideal_enc_universe (IdealWorld.Return 0)).
    Proof.
      apply refines_implies_inclusion.
      apply idealSymEncPingRefinesRealSymEncPing.
    Qed.
  End HideHints.
End EncPingProtocolCorrect.

Module SymmetricU <: RealEncPingProtocolParameters.
  Import RealWorld.

  Definition KEYID := 0.
  Definition KEY   := SymKey (MkCryptoKey KEYID Encryption).

  Definition RA := 0.
  Definition RB := 1.
  Definition Radversary := 2.

  Definition uks0 := $0 $+ (KEYID, KEY).
  Definition uks1 := $0 $+ (KEYID, KEY).
  Definition ks   := $0 $+ (KEYID, KEY).
End SymmetricU.

Module AsymmetricU <: RealEncPingProtocolParameters.
  Import RealWorld.

  Definition KEYID := 0.
  Definition KEY   := AsymKey (MkCryptoKey KEYID Encryption) true.

  Definition RA := 0.
  Definition RB := 1.
  Definition Radversary := 2.

  Definition uks0 := $0 $+ (KEYID, AsymKey (MkCryptoKey KEYID Encryption) false).
  Definition uks1 := $0 $+ (KEYID, KEY).
  Definition ks   := $0 $+ (KEYID, KEY).
End AsymmetricU.

Module SymmetricEncPingProtocolTheory <: EncPingProtocolCorrectT (SymmetricU).

  Module Sim := EncPingProtocolSimulation (SymmetricU).
  Import SymmetricU Sim.

  (* Trap the hints imported from EncPingProtocolCorrect so they get cleaned
   * up after we are done with the proof. *)
  Section HideHints.

    Hint Constructors RSymEncPing.

    Lemma simulation_steps_simulate : 
      forall U1 U2,
        RSymEncPing U1 U2
        -> forall U1',
          RealWorld.step_universe U1 U1'
          -> exists U2',
            IdealWorld.step_universe^* U2 U2'
            /\ RSymEncPing U1' U2'.
    Proof.

      intros.
      Time invert H; unfold enc_ping_universe;
        repeat take_step;
        (eexists; constructor; swap 1 2; [ autorewrite with core | ]; eauto 11).
    Qed.

    Lemma finalStatesAre :
      forall {U1 : RealWorld.universe nat} {U2 : IdealWorld.universe nat},
        RSymEncPing U1 U2
        -> realWorldIsReallyFinalState U1
        -> U1.(RealWorld.users) = [
            (RA, {| RealWorld.usrid    := RA
                  ; RealWorld.key_heap := uks0
                  ; RealWorld.protocol := RealWorld.Return 1 |} )
              
            ; (RB, {| RealWorld.usrid    := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := RealWorld.Return 2 |} )
            ; (Radversary, {| RealWorld.usrid    := Radversary
                            ; RealWorld.key_heap := $0
                            ; RealWorld.protocol := RealWorld.Return 0 |} )
          ]
          /\ U2.(IdealWorld.users) = IUFinal.(IdealWorld.users).
    Proof.
      intros.

      destruct H;
        unfold enc_ping, ideal_enc_universe, IUFinal, RUFinal in *;
        subst;
        repeat final_steps;
        propositional.
    Qed.

    Lemma sim_finishes_correctly :
      forall U1 U2,
        RSymEncPing U1 U2
        -> realWorldIsReallyFinalState U1
        -> idealWorldIsReallyFinalState U2
          /\ realWorldReturnsOf U1 = idealWorldReturnsOf U2.
    Proof.
      intros;
        unfold idealWorldIsReallyFinalState, realWorldReturnsOf, idealWorldReturnsOf;
        (repeat match goal with
                | [ H : RSymEncPing _ _ |- _ ] => eapply finalStatesAre in H; [ | assumption]
                | [ H : _ /\ _ |- _ ] => invert H
                | [ H : RealWorld.users  _ = _ |- _ ] => rewrite H; clear H
                | [ H : IdealWorld.users _ = _ |- _ ] => rewrite H; clear H
                end);
        simpl;
        eauto 12.
    Qed.
  End HideHints.

End SymmetricEncPingProtocolTheory.

Module AsymmetricEncPingProtocolTheory <: EncPingProtocolCorrectT (AsymmetricU).

  Module Sim := EncPingProtocolSimulation (AsymmetricU).
  Import AsymmetricU Sim.

  (* Trap the hints imported from EncPingProtocolCorrect so they get cleaned
   * up after we are done with the proof. *)
  Section HideHints.
    Hint Constructors RSymEncPing.

    Lemma simulation_steps_simulate : 
      forall U1 U2,
        RSymEncPing U1 U2
        -> forall U1',
          RealWorld.step_universe U1 U1'
          -> exists U2',
            IdealWorld.step_universe^* U2 U2'
            /\ RSymEncPing U1' U2'.
    Proof.

      intros.
      Time invert H; unfold enc_ping_universe;
        repeat take_step;
        (eexists; constructor; swap 1 2; [ autorewrite with core | ]; eauto 11).
    Qed.

    Lemma finalStatesAre :
      forall {U1 : RealWorld.universe nat} {U2 : IdealWorld.universe nat},
        RSymEncPing U1 U2
        -> realWorldIsReallyFinalState U1
        -> U1.(RealWorld.users) = [
            (RA, {| RealWorld.usrid    := RA
                  ; RealWorld.key_heap := uks0
                  ; RealWorld.protocol := RealWorld.Return 1 |} )
              
            ; (RB, {| RealWorld.usrid    := RB
                    ; RealWorld.key_heap := uks1
                    ; RealWorld.protocol := RealWorld.Return 2 |} )
            ; (Radversary, {| RealWorld.usrid    := Radversary
                            ; RealWorld.key_heap := $0
                            ; RealWorld.protocol := RealWorld.Return 0 |} )
          ]
          /\ U2.(IdealWorld.users) = IUFinal.(IdealWorld.users).
    Proof.
      intros.

      destruct H;
        unfold enc_ping, ideal_enc_universe, IUFinal, RUFinal in *;
        subst;
        repeat final_steps;
        propositional.
    Qed.

    Lemma sim_finishes_correctly :
      forall U1 U2,
        RSymEncPing U1 U2
        -> realWorldIsReallyFinalState U1
        -> idealWorldIsReallyFinalState U2
          /\ realWorldReturnsOf U1 = idealWorldReturnsOf U2.
    Proof.
      intros;
        unfold idealWorldIsReallyFinalState, realWorldReturnsOf, idealWorldReturnsOf;
        (repeat match goal with
                | [ H : RSymEncPing _ _ |- _ ] => eapply finalStatesAre in H; [ | assumption]
                | [ H : _ /\ _ |- _ ] => invert H
                | [ H : RealWorld.users  _ = _ |- _ ] => rewrite H; clear H
                | [ H : IdealWorld.users _ = _ |- _ ] => rewrite H; clear H
                end);
        simpl;
        eauto 12.
    Qed.
  End HideHints.

End AsymmetricEncPingProtocolTheory.

(* Tie the knot! Both protocols correct. *)
Module SymmetricPingProtocolCorrect := EncPingProtocolCorrect (SymmetricU) (SymmetricEncPingProtocolTheory).
Module AsymmetricPingProtocolCorrect := EncPingProtocolCorrect (AsymmetricU) (AsymmetricEncPingProtocolTheory).
