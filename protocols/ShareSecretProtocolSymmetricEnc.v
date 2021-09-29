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

     ModelCheck.ProtocolFunctions
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

From Frap Require Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module ShareSecretSymmetricEncProtocol.

  (* User ids *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  
  Section IW_Simple.
    Import IdealWorld.

    Notation perms_CH := 0.
    Notation CH := (Single perms_CH).

    Notation empty_chs := (#0 #+ (CH, [])).

    Definition PERMS := $0 $+ (perms_CH, {| read := true; write := true |}).

    Definition simple_users :=
      [
        (mkiUsr USR1 PERMS 
                (
                  n <- Gen
                  ; _ <- Send (Content n) CH
                  ; @Return (Base Nat) n
        ));
        (mkiUsr USR2 PERMS
                ( m <- @Recv Nat CH
                ; @Return (Base Nat) (extractContent m)))
        ].

    Definition simple_univ_start :=
      mkiU empty_chs simple_users.

  End IW_Simple.

  Section IW.
    Import IdealWorld.

    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).

    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, [])).

    Notation PERMS1 := ($0 $+ (pCH12, owner) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, owner)).

    Notation ideal_users :=
      [
        (mkiUsr USR1 PERMS1 
                ( chid <- CreateChannel
                  ; _ <- Send (sharePerm chid writer) CH12
                  ; m <- @Recv Access (chid #& pCH21)
                  ; n <- Gen
                  ; _ <- Send (Content n) (getPerm m #& pCH12)
                  ; @Return (Base Nat) n
        )) ;
      (mkiUsr USR2 PERMS2
              ( m <- @Recv Access CH12
                ; chid <- CreateChannel
                ; _ <- Send (sharePerm chid owner) (getPerm m #& pCH21)
                ; m <- @Recv Nat (chid #& pCH12)
                ; @Return (Base Nat) (extractContent m)
      ))
      ].

    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.

    Notation KID1 := 0.
    Notation KID2 := 1.

    Notation KEYS := [ skey KID1 ; skey KID2 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, false)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, true)).

    Definition real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( kp <- GenerateKey AsymKey Encryption
                      ; c1 <- Sign KID1 USR2 (sharePubKey kp)
                      ; _  <- Send USR2 c1
                      ; c2 <- @Recv Access (SignedEncrypted KID2 (fst kp) true)
                      ; m  <- Decrypt c2
                      ; n  <- Gen
                      ; c3 <- SignEncrypt KID1 (getKey m) USR2 (message.Content n)
                      ; _  <- Send USR2 c3
                      ; @Return (Base Nat) n) ;

      MkRUserSpec USR2 KEYS2
                  ( c1 <- @Recv Access (Signed KID1 true)
                    ; v  <- Verify KID1 c1
                    ; kp <- GenerateKey SymKey Encryption
                    ; c2 <- SignEncrypt KID2 (getKey (snd v)) USR1 (sharePrivKey kp)
                    ; _  <- Send USR1 c2
                    ; c3 <- @Recv Nat (SignedEncrypted KID1 (fst kp) true)
                    ; m  <- Decrypt c3
                    ; @Return (Base Nat) (extractContent m) )
      ].

    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  #[export] Hint Unfold
       simple_univ_start
       ideal_univ_start
       real_univ_start
    : user_build.

  #[export] Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl) : core.
  
End ShareSecretSymmetricEncProtocol.
