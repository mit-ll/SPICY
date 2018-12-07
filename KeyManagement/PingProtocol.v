From Coq Require Import List.
(* Require Import Frap Eqdep. *)
Require Import Frap.

Require Import Common.
Require Import Simulation.
Require IdealWorld.
Require RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Section IdealPing.

  Import IdealWorld.

  Example ideal_ping_universe : universe nat :=
    {| channel_vector := $0 $+ (0, { })
     ; users := [
        (0, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := (
                 _ <- (Send (Content 1) 0)
               ; Return 42)
            |})
      ; (1, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := (
                 r <- (Recv 0)
               ; Return match extractContent r with Some c => c | None => 43 end)
            |})
               ]
    |}.

  Check ideal_ping_universe.

End IdealPing.

Section RealPing.

  Import RealWorld.

  Example real_ping : list (user_data nat) :=
    {| usrid    := 0
     ; key_heap := $0
     ; protocol := (  _ <- Send 1 (Plaintext 1)
                    ; Return 42)
    |}
      ::
    {| usrid    := 1
     ; key_heap := $0
     ; protocol := (  rec <- Recv (A := nat)
                    ; Return (match extractPlainText rec with
                              | Some msg => msg
                              | None     => 98
                              end))
    |}
      :: [].

  Example real_ping_universe : universe nat :=
    {|
      users            := map (fun u_d => (u_d.(usrid), u_d)) real_ping
    ; users_msg_buffer := $0
    ; all_keys         := $0
    ; all_ciphers      := $0
    |}.

  Check real_ping_universe.

End RealPing.

(** The correctness theorem for the very simple ping protocol  *)
Section SimplePingProtocolCorrect.

  Inductive R_ping : RealWorld.universe nat -> IdealWorld.universe nat -> Prop :=
  | StartPingProtocol :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := (
                        _ <- RealWorld.Send 1 (RealWorld.Plaintext 1)
                      ; RealWorld.Return 42) |})

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := (
                        rec <- RealWorld.Recv (A := nat)
                      ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                          | Some msg => msg
                                          | None     => 98
                                          end)) |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                        _ <- (IdealWorld.Send (IdealWorld.Content 1) 0)
                     ; IdealWorld.Return 42)
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- (IdealWorld.Recv 0)
                     ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 43 end)
                  |})
                               ])%idealworld
        |}


  | SendPing :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := _ <- RealWorld.Return tt ; RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := (
                        rec <- RealWorld.Recv (A := nat)
                      ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                          | Some msg => msg
                                          | None     => 98
                                          end)) |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0 $+ (1, [RealWorld.Exm (RealWorld.Plaintext 1)])
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := _ <- IdealWorld.Return tt ; IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- (IdealWorld.Recv 0)
                     ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 43 end)
                  |})
                               ])%idealworld
        |}

 
  | SimplAfterSendPing :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := (
                        rec <- RealWorld.Recv (A := nat)
                      ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                          | Some msg => msg
                                          | None     => 98
                                          end)) |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0 $+ (1, [RealWorld.Exm (RealWorld.Plaintext 1)])
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- (IdealWorld.Recv 0)
                     ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 43 end)
                  |})
                               ])%idealworld
        |}


  | ReceivePing :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := _ <- RealWorld.Return tt ; RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := ( rec <- RealWorld.Return (RealWorld.Plaintext 1)
                                            ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                                                | Some msg => msg
                                                                | None     => 98
                                                                end)) |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := _ <- IdealWorld.Return tt ; IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := ( r <- IdealWorld.Return (IdealWorld.Content 1)
                                            ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 43 end)
                  |})
                               ])%idealworld
        |}


  | ReceivePingAfterSimplify :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := ( rec <- RealWorld.Return (RealWorld.Plaintext 1)
                                            ; RealWorld.Return (match RealWorld.extractPlainText rec with
                                                                | Some msg => msg
                                                                | None     => 98
                                                                end)) |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := ( r <- IdealWorld.Return (IdealWorld.Content 1)
                                            ; IdealWorld.Return match IdealWorld.extractContent r with Some c => c | None => 43 end)
                  |})
                               ])%idealworld
        |}

  | SimplifyBindAfterReceive :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := _ <- RealWorld.Return tt ; RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 1 |})
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := _ <- IdealWorld.Return tt ; IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 1
                  |})
                               ])%idealworld
        |}


  | Finish :
      R_ping
        {|
          RealWorld.users   := ([
               (0, {| RealWorld.usrid    := 0
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 42 |} )

             ; (1, {| RealWorld.usrid    := 1
                    ; RealWorld.key_heap := $0
                    ; RealWorld.protocol := RealWorld.Return 1 |} )
                               ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        |}
        {| IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 42
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return 1
                  |})
                               ])%idealworld
        |}
  .

  Hint Constructors R_ping.
  Hint Resolve in_eq in_cons.

  Lemma finalStatesAre : 
    forall {U1 : RealWorld.universe nat} {U2 : IdealWorld.universe nat},
      R_ping U1 U2
      -> realWorldIsReallyFinalState U1
      -> U1 = {|
          RealWorld.users :=
            [(0, {| RealWorld.usrid := 0; RealWorld.key_heap := $0; RealWorld.protocol := RealWorld.Return 42 |});
             (1, {| RealWorld.usrid := 1; RealWorld.key_heap := $0; RealWorld.protocol := RealWorld.Return  1 |})];
          RealWorld.users_msg_buffer := $0;
          RealWorld.all_keys := $0;
          RealWorld.all_ciphers := $0 |}
        /\ U2 = {|
            IdealWorld.channel_vector := $0 $+ (0, {IdealWorld.Exm (IdealWorld.Content 1)});
            IdealWorld.users :=
              [(0, {|
                  IdealWorld.protocol := IdealWorld.Return 42;
                  IdealWorld.perms := $0 $+ (0, {| IdealWorld.read := true; IdealWorld.write := true |}) |});
                 (1, {|
                    IdealWorld.protocol := IdealWorld.Return 1;
                    IdealWorld.perms := $0 $+ (0, {| IdealWorld.read := true; IdealWorld.write := true |}) |})]
          |}.
  Proof.
    intros.

    destruct H;
      (repeat match goal with
              | [ H : realWorldIsReallyFinalState _ |- _ ] => invert H
              | [ H : exists a , _ = RealWorld.Return a |- _ ] => invert H
              | [ H : _ = RealWorld.Return _ |- _ ] => invert H
              | [ H : Forall _ _ |- _ ] => invert H
              end); propositional.
  Qed.

  Hint Resolve finalStatesAre.

  Lemma rping_steps_simulate : 
    forall U1 U2,
      R_ping U1 U2
      -> forall U1',
        RealWorld.step_universe U1 U1'
        -> exists U2',
          IdealWorld.step_universe^* U2 U2'
          /\ R_ping U1' U2'.
  Proof.

    Hint Extern 1 (In _ (IdealWorld.users _)) => progress simpl.
    Hint Extern 1 (_ \in _ ) => sets.
    Hint Extern 1 (IdealWorld.step_user (_, IdealWorld.Bind _ _, _) _) => eapply IdealWorld.StepBindRecur; simplify.
    Hint Extern 1 (IdealWorld.step_user (_, IdealWorld.Send _ _, _) _) => eapply IdealWorld.StepSend'; simplify.
    Hint Extern 1 (IdealWorld.step_user (IdealWorld.channel_vector _, _, _) _) => progress simpl.

    Hint Extern 1 (R_ping (RealWorld.updateUniverse _ _ _ _ _ _ _) _ ) =>
      autorewrite with core; unfold RealWorld.updateUniverse, RealWorld.multiMapAdd; simplify.
    (* Hint Extern 1 (R_ping (RealWorld.updateUniverse _ _ _ _ _ _ _) _ ) => *)
    (*   unfold RealWorld.updateUniverse, RealWorld.multiMapAdd; autorewrite with core; simplify. *)

    intros.

    (* The main idea for solving the generated (existential) goals here is to split apart the
     * conjunction and then solve the second one first.  This works because the second conjuct is
     * the simulation relation constructor, which helps lock down the destsination state and helps
     * determine how many steps are needed to get there in the ideal world. Otherwise, we seem to just
     * pick "take no steps" and get stuck.  *)
    Hint Extern 1 (exists _, _ /\ _) => eexists; constructor; simplify; [ | constructor ].

    invert H; doit; simpl in *; eauto 8;
      (* Question for Adam.  This works, but pulling the rewrite out breaks it.
         despite the fact that the Extern above with the needed rewrite is
         firing.  *)
      autorewrite with core;
      eauto 12.
  Qed.

  Lemma rping_finishes_correctly :
    forall U1 U2,
      R_ping U1 U2
      -> realWorldIsReallyFinalState U1
      -> idealWorldIsReallyFinalState U2
        /\ realWorldReturnsOf U1 = idealWorldReturnsOf U2.
  Proof.
    Hint Extern 1 (exists _, _ = _) => eexists; simplify; reflexivity.
    Hint Extern 1 (idealWorldIsReallyFinalState _) => unfold idealWorldIsReallyFinalState; simplify.
    Hint Constructors Forall.

    firstorder;
      (match goal with
       | [ H : R_ping _ _ |- _ ] => apply finalStatesAre in H
       end); repeat fixcontext; simplify; eauto 8.

  Qed.

  Hint Resolve rping_steps_simulate rping_finishes_correctly.

  Theorem idealPingRefinesRealPing : 
    real_ping_universe <| ideal_ping_universe.
  Proof.
    exists R_ping.
    assert (F := rping_finishes_correctly).
    unfold simulates; firstorder; eauto.

    (* invert H; doit; simpl in *; try contradiction; eexists; *)
    (*   (constructor; [ | simplify; constructor ]; eauto 8; eauto 10). *)
  Qed.

  Theorem ping_protocol_ok :
    finalAnswerInclusion real_ping_universe ideal_ping_universe.
  Proof.
    apply refines_implies_inclusion.
    apply idealPingRefinesRealPing.
  Qed.

End SimplePingProtocolCorrect.
