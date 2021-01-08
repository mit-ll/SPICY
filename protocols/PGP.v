(*
 * © 2020 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     ModelCheck
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse

     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

From Frap Require Import Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Export SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module PGPProtocol.

  (* User ids *)
  Notation USR1 := 0.
  Notation USR2 := 1.

  Section IW.
    Import IdealWorld.

    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).

    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, [])).

    Notation PERMS1 := ($0 $+ (pCH12, owner) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, writer)).

    Definition ideal_users :=
      [
        (mkiUsr USR1 PERMS1 
                ( m1 <- @Recv Access CH21
                  ; m2 <- @Recv Nat (getPerm m1 #& pCH21)
                  ; @Return (Base Nat) (extractContent m2)
        )) ;
      (mkiUsr USR2 PERMS2
              ( chid <- CreateChannel
                ; _ <- Send (sharePerm chid owner) CH21
                ; n <- Gen
                ; _ <- Send (Content n) (chid #& pCH21)
                ; @Return (Base Nat) n
      ))
      ].

    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.
    Import RealWorld.message.

    Notation KID1 := 0.
    Notation KID2 := 1.
    Notation KID3 := 2.

    Notation KEYS := [ skey KID1 ; skey KID2 ; ekey KID3 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, false) $+ (KID3, true)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, true) $+ (KID3, false)).

    Definition real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( c1 <- @Recv Access (SignedEncrypted KID2 KID3 true)
                      ; m1 <- Decrypt c1
                      ; c2 <- @Recv Nat (SignedEncrypted KID2 (getKey m1) true)
                      ; m2 <- Decrypt c2
                      ; @Return (Base Nat) (extractContent m2)) ;

      MkRUserSpec USR2 KEYS2
                  ( kp <- GenerateKey SymKey Encryption
                    ; c1 <- SignEncrypt KID2 KID3 USR1 (sharePrivKey kp)
                    ; _  <- Send USR1 c1
                    ; n  <- Gen
                    ; c2 <- SignEncrypt KID2 (fst kp) USR1 (Content n)
                    ; _  <- Send USR1 c2
                    ; @Return (Base Nat) n )
      ].

    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl).
  
End PGPProtocol.
