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

From Frap Require Import Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module AvgSalaryProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  Notation USR3 := 2.
  Notation USR4 := 3.

  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH14 := 0.
    Notation pCH24 := 1.
    Notation pCH34 := 2.
    Notation CH14  := (# pCH14).
    Notation CH24  := (# pCH24).
    Notation CH34  := (# pCH34).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0 #+ (CH14, []) #+ (CH24, []) #+ (CH34, [])).

    Notation PERMS1 := ($0 $+ (pCH14, writer)).
    Notation PERMS2 := ($0 $+ (pCH24, writer)).
    Notation PERMS3 := ($0 $+ (pCH34, writer)).
    Notation PERMS4 := ($0 $+ (pCH14, reader) $+ (pCH24, reader) $+ (pCH34, reader)).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        mkiUsr USR1 PERMS1
               ( _ <- Send (Content 1) CH14
                 ; @Return (Base Nat) 1
               )
        ; 

      mkiUsr USR2 PERMS2
             ( _ <- Send (Content 1) CH24
               ; @Return (Base Nat) 1
             )
        ; 

      mkiUsr USR3 PERMS3
             ( _ <- Send (Content 1) CH34
               ; @Return (Base Nat) 1
             )
        ; 

      mkiUsr USR4 PERMS4
             ( m1 <- @Recv Nat CH14
               ; m2 <- @Recv Nat CH24
               ; m3 <- @Recv Nat CH34
               ; @Return (Base Nat) (let c1 := extractContent m1 in
                                     let c2 := extractContent m2 in
                                     let c3 := extractContent m3
                                     in (c1 + c2 + c3) / 3)
             )
      ].

    (* This is where the entire specification universe gets assembled.  It is unlikely anything
     * will need to change here.
     *)
    Definition ideal_univ_start :=
      mkiU empty_chs ideal_users.

  End IW.

  Section RW.
    Import RealWorld.
    Import RealWorld.message.

    (* Key management needs to be bootstrapped.  Since all honest users must only send signed
     * messages, we need some way of initially distributing signing keys in order to be able
     * to begin secure communication.  This is analagous in the real world where we need to 
     * have some sort of trust relationship in order to distribute trusted keys.
     * 
     * Here, each user has a public asymmetric signing key.
     *)
    Notation KID1 := 0.
    Notation KID2 := 1.
    Notation KID3 := 2.
    Notation KID4 := 3.

    Notation KEYS := [ skey KID1 ; skey KID2 ; skey KID3; ekey KID4 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID4, false)).
    Notation KEYS2 := ($0 $+ (KID2, true) $+ (KID4, false)).
    Notation KEYS3 := ($0 $+ (KID3, true) $+ (KID4, false)).
    Notation KEYS4 := ($0 $+ (KID1, false) $+ (KID2, false) $+ (KID3, false) $+ (KID4, true) ).

    Notation real_users :=
      [
        (* User 1 implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      c <- SignEncrypt KID1 KID4 USR4 (Content 1)
                      ; _ <- Send USR4 c
                      ; ret 1
                    )
        ; 

      (* User 2 implementation *)
      MkRUserSpec USR2 KEYS2
                  (
                    c <- SignEncrypt KID2 KID4 USR4 (Content 1)
                    ; _ <- Send USR4 c
                    ; ret 1
                  )
        ; 

      (* User 3 implementation *)
      MkRUserSpec USR3 KEYS3
                  (
                    c <- SignEncrypt KID3 KID4 USR4 (Content 1)
                    ; _ <- Send USR4 c
                    ; ret 1
                  )
        ;
      
      (* Server implementation *)
      MkRUserSpec USR4 KEYS4
                  (
                    salC1 <- @Recv Nat (SignedEncrypted KID1 KID4 true)
                    ; salC2 <- @Recv Nat (SignedEncrypted KID2 KID4 true)
                    ; salC3 <- @Recv Nat (SignedEncrypted KID3 KID4 true)
                    ; sal1 <- Decrypt salC1
                    ; sal2 <- Decrypt salC2
                    ; sal3 <- Decrypt salC3
                    ; ret (let s1 := extractContent sal1 in
                           let s2 := extractContent sal2 in
                           let s3 := extractContent sal3
                           in  (s1 + s2 + s3) / 3 )
                  )
      ].

    (* Here is where we put the implementation universe together.  Like above, it is 
     * unlikely anything will need to change here.
     *)
    Definition real_univ_start :=
      mkrU (mkKeys KEYS) real_users.
  End RW.

  (* These are here to help the proof automation.  Don't change. *)
  #[export] Hint Unfold
       real_univ_start
       ideal_univ_start
    : user_build.

  #[export] Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with user_build; simpl) : core.
  
End AvgSalaryProtocol.
