From Coq Require Import List.
(* Require Import Frap Eqdep. *)
Require Import Frap.

Require Import Common Simulation.
Require IdealWorld.
Require RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Section IdealPing.

  Import IdealWorld.

  Example ideal_ping_universe : universe unit :=
    {| channel_vector := $0 $+ (0, { })
     ; users := [
        (0, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := Send (Content 1) 0
            |})
      ; (1, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := (
                 r <- (Recv (msg_ty := nat) 0)
               ; Return tt)
            |})
               ]
    |}.

  Example ideal_enc_ping_universe : universe unit :=
    {| channel_vector := $0 $+ (0, { })
     ; users := [
        (0, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := Send (Content 1) 0
            |})
      ; (1, {| perms    := $0 $+ (0, {| read := true ; write := true |})
             ; protocol := (
                 r <- (Recv (msg_ty := nat) 0)
               ; Return tt)
            |})
               ]
    |}.

End IdealPing.

Section RealPing.

  Import RealWorld.
  Definition RA := 0.
  Definition RB := 1.

  Definition KEYID := 10.
  Definition KEY   := SymKey (MkCryptoKey KEYID Encryption).
  Definition KEYS  := $0 $+ (KEYID, KEY).

  Example real_ping_universe : universe unit :=
    {|
      users            :=
        [
          (RA, {| key_heap := $0
                ; protocol := Send RB (Plaintext 1)
               |})
        ; (RB, {| key_heap := $0
                ; protocol := (  rec <- Recv (A := nat) (Accept)
                               ; Return tt)
               |})
        ]
    ; users_msg_buffer := $0
    ; all_keys         := $0
    ; all_ciphers      := $0
    ; adversary        := $0
    |}.

End RealPing.

Section SimplePingProtocolCorrectLabeled.

  Definition realUserSilentStep {A} (u_id : user_id) (ds0 ds1 : RealWorld.data_step0 A) :=
    RealWorld.lstep_user u_id Silent ds0 ds1.

  Definition realUniverseSilentStep {A} (U1 U2 : RealWorld.universe A) :=
    RealWorld.lstep_universe U1 Silent U2.

  Definition RUFinal :=
        {| RealWorld.users   := ([
               (RA, {| RealWorld.key_heap := $0
                     ; RealWorld.protocol := RealWorld.Return tt |} )

             ; (RB, {| RealWorld.key_heap := $0
                     ; RealWorld.protocol := RealWorld.Return tt |} )
                                ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        ; RealWorld.adversary        := $0
        |}.

  Definition IUFinal :=
    {| IdealWorld.channel_vector := $0 $+ (0, {Exm (IdealWorld.Content 1)});
       IdealWorld.users := [
               (0, {| IdealWorld.perms := $0 $+ (0, {| IdealWorld.read := true ;  IdealWorld.write := true |});
                      IdealWorld.protocol := IdealWorld.Return tt
                   |})
             ; (1, {| IdealWorld.perms := $0 $+ (0, {|  IdealWorld.read := true ;  IdealWorld.write := true |});
                      IdealWorld.protocol := IdealWorld.Return tt
                   |})
               ]
    |}.

  Inductive RPingL : RealWorld.universe unit -> IdealWorld.universe unit -> Prop :=
  | Start :
      RPingL real_ping_universe ideal_ping_universe

  | BeforeReceive : forall RUSent RU,
      RUSent = {|
        RealWorld.users := ([
            (RA, {| RealWorld.key_heap := $0
                  ; RealWorld.protocol := RealWorld.Return tt
                 |})
          ; (RB, {| RealWorld.key_heap := $0
                  ; RealWorld.protocol := (
                      rec <- RealWorld.Recv (A := nat) (RealWorld.Accept)
                    ; RealWorld.Return tt)
                 |})
                           ])%realworld
        ; RealWorld.users_msg_buffer := $0 $+ (1, [Exm (RealWorld.Plaintext 1)])
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        ; RealWorld.adversary        := $0
      |}
      -> realUniverseSilentStep^* RUSent RU
      -> RPingL RU
        {| IdealWorld.channel_vector := $0 $+ (0, {Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                     ; IdealWorld.protocol := IdealWorld.Return tt
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- IdealWorld.Recv (msg_ty := nat) 0
                     ; IdealWorld.Return tt)
                  |})
                               ])%idealworld
        |}
 
  | AfterReceive : forall RURecd RU,
      RURecd = {|
        RealWorld.users := ([
            (RA, {| RealWorld.key_heap := $0
                  ; RealWorld.protocol := RealWorld.Return tt
                 |})
          ; (RB, {| RealWorld.key_heap := $0
                  ; RealWorld.protocol := (
                      rec <- RealWorld.Return (RealWorld.Plaintext 1)
                    ; RealWorld.Return tt)
                 |})
                           ])%realworld
        ; RealWorld.users_msg_buffer := $0
        ; RealWorld.all_keys         := $0
        ; RealWorld.all_ciphers      := $0
        ; RealWorld.adversary        := $0
      |}
      -> realUniverseSilentStep^* RURecd RU
      -> RU <> RUFinal
      -> RPingL RU
        {| IdealWorld.channel_vector := $0 $+ (0, {Exm (IdealWorld.Content 1)})
         ; IdealWorld.users := ([
              (0, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := IdealWorld.Return tt
                  |})
            ; (1, {| IdealWorld.perms    := $0 $+ (0, {| IdealWorld.read := true ; IdealWorld.write := true |})
                   ; IdealWorld.protocol := (
                       r <- IdealWorld.Return (IdealWorld.Content 1)
                     ; IdealWorld.Return tt)
                  |})
                               ])%idealworld
        |}

  | SimpleFinish : forall RU IU,
        RU = RUFinal
      -> IU = IUFinal
      -> RPingL RU IU
  .

  Hint Constructors RPingL.


  Ltac risky1 :=
    match goal with
    | [ H: realUniverseSilentStep^* _ _ |- _ ] => invert H
    end.

  Ltac churn1 :=
    match goal with
    | [ H: In _ _ |- _ ] => invert H
    | [ H : $0 $? _ = Some _ |- _ ] => apply lookup_empty_not_Some in H; contradiction
    | [ H : (_ $+ (_, _)) $? _ = Some _ |- _ ] => apply lookup_split in H; propositional; subst

    | [ H : (_ :: _) = _ |- _ ] => invert H
    | [ H : (_,_) = (_,_) |- _ ] => invert H
    (* | [ H: _ = _ |- _ ] => progress (invert H) *)

    | [ H : updF _ _ _ = _ |- _ ] => unfold updF; simpl in H

    (* Only take a user step if we have chosen a user *)
    | [ H: RealWorld.lstep_user RA _ _ _ |- _ ] => invert H
    | [ H: RealWorld.lstep_user RB _ _ _ |- _ ] => invert H

    | [ H: rstepSilent _ _ |- _ ] => unfold rstepSilent in H
    | [ H: RealWorld.lstep_universe _ _ _ |- _ ] => invert H

    | [ H: realUniverseSilentStep _ _ |- _ ] => invert H
    | [ H: realUniverseSilentStep^* (RealWorld.updateUniverse _ _ _ _ _ _ _) _ |- _ ] =>
      unfold RealWorld.updateUniverse in H; simpl in H; invert H
    end.

  Ltac rstep_user0 :=
    eapply TrcFront; [
      eapply RealWorld.LStepUser'; simpl; [ left; reflexivity | | reflexivity] |
    ]; simpl.

  Ltac rstep_user1 :=
    eapply TrcFront; [
      eapply RealWorld.LStepUser'; simpl; [ right; left; reflexivity | | reflexivity] |
    ]; simpl.

  Ltac istep_user0 :=
    eapply TrcFront; [
      eapply IdealWorld.LStepUser'; simpl; [ left; reflexivity | | reflexivity] |
    ]; simpl.

  Ltac istep_user1 :=
    eapply TrcFront; [
      eapply IdealWorld.LStepUser'; simpl; [ right; left; reflexivity | | reflexivity] |
    ]; simpl.

  Hint Constructors RealWorld.lstep_user IdealWorld.lstep_user.

  Hint Extern 1 (RPingL (RealWorld.updateUniverse _ _ _ _ _ _ _) _) => unfold RealWorld.updateUniverse; simpl.
  Hint Extern 1 (RealWorld.lstep_universe _ _ _) => eapply RealWorld.LStepUser'.
  Hint Extern 1 (RealWorld.lstep_user _ _ (RealWorld.all_ciphers _, _, _, _, _)) => progress simpl.
  Hint Extern 1 (In _ _) => progress simpl.
  Hint Extern 2 (realUniverseSilentStep ^* _ _) => (solve TrcRefl) || rstep_user0. 
  Hint Extern 2 (realUniverseSilentStep ^* _ _) => (solve TrcRefl) || rstep_user1. 
  Hint Extern 2 (istepSilent ^* _ _) => (solve TrcRefl) || istep_user0. 
  Hint Extern 2 (istepSilent ^* _ _) => (solve TrcRefl) || istep_user1. 
  Hint Extern 1 (_ <> RUFinal) => unfold not, RUFinal; discriminate.

  Lemma rpingl_silent_simulates :
    forall U1 U2,
      RPingL U1 U2
      -> forall U1',
          rstepSilent U1 U1'
          -> exists U2',
              istepSilent ^* U2 U2'
              /\ RPingL U1' U2'.
  Proof.
    unfold real_ping_universe, ideal_ping_universe;
      intros. 

    invert H;
      repeat churn1;
      risky1; repeat (try discriminate; churn1).

    eexists; constructor; swap 1 2; eauto 8.
    risky1; repeat churn1.
  Qed.

  Lemma rpingl_loud_simulates : 
    forall U1 U2,
      RPingL U1 U2
      -> forall a1 U1',
        RealWorld.lstep_universe U1 (Action a1) U1'
        -> exists a2 U2' U2'',
            istepSilent^* U2 U2'
            /\ IdealWorld.lstep_universe U2' (Action a2) U2''
            /\ action_matches a1 a2
            /\ RPingL U1' U2''
            /\ RealWorld.action_adversary_safe U1.(RealWorld.adversary) a1 = true.
  Proof.
    intros.

    invert H; repeat churn1.

    Ltac istep_univ0 :=
      eapply IdealWorld.LStepUser'; simpl; [ left; reflexivity | | reflexivity]; simpl.
    Ltac istep_univ1 :=
      eapply IdealWorld.LStepUser'; simpl; [ right; left; reflexivity | | reflexivity]; simpl.

    Hint Constructors action_matches msg_eq.
    Hint Resolve IdealWorld.LStepSend' IdealWorld.LStepRecv'.

    (* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => eapply IdealWorld.LStepUser'. *)
    Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ0 + istep_univ1.
    (* Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ1. *)

    Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.
    Hint Extern 1 (add _ _ _ = _) => maps_equal.
    Hint Extern 1 (_ \in _) => sets.

    - do 3 eexists.
      propositional;
        swap 1 4; swap 2 4; swap 3 4;
          unfold RealWorld.updateUniverse, RealWorld.multiMapAdd; simplify;
            eauto 8.

    - do 3 eexists.
       propositional;
        swap 1 4; swap 2 4; swap 3 4;
          risky1;
          repeat (try discriminate; churn1);
          match goal with
          | [ H : RB = _ |- _] => rewrite H; clear H
          end;
          unfold RealWorld.updateUniverse; simplify;
            eauto 6.

       admit.

    - risky1; repeat churn1.
      risky1; repeat churn1.
  Admitted.

  (* Theorem is correctly unproveable *)

  Hint Resolve rpingl_silent_simulates rpingl_loud_simulates.

  Theorem idealPingLRefinesRealPing : 
    lrefines real_ping_universe ideal_ping_universe.
  Proof.
    exists RPingL.
    firstorder; eauto.
  Qed.

End SimplePingProtocolCorrectLabeled.
