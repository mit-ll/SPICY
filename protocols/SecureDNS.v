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

From Frap Require Import Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Export SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module SecureDNSProtocol.

  (* Start with two users, as that is the minimum for any interesting protocol *)
  Notation USR1 := 0.
  Notation USR2 := 1.
  Notation USR3 := 2.

  Notation loopN := 10.

  Parameter names : NatMap.t nat.
  
  Section IW.
    Import IdealWorld.

    (* Set up initial communication channels so each user can talk directly to the other *)
    Notation pCH12 := 0.
    Notation pCH21 := 1.
    Notation pCH23 := 2.
    Notation pCH32 := 3.
    Notation CH12  := (# pCH12).
    Notation CH21  := (# pCH21).
    Notation CH23  := (# pCH23).
    Notation CH32  := (# pCH32).

    (* This is the initial channel vector, each channel should be represented and start with 
     * no messages.
     *)
    Notation empty_chs := (#0 #+ (CH12, []) #+ (CH21, []) #+ (CH23, []) #+ (CH32, [])).

    Notation PERMS1 := ($0 $+ (pCH12, writer) $+ (pCH21, reader)).
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, writer) $+ (pCH23, writer) $+ (pCH32, reader)).
    Notation PERMS3 := ($0 $+ (pCH23, reader) $+ (pCH32, writer)).

    (* Fill in the users' protocol specifications here, adding additional users as needed.
     * Note that all users must return an element of the same type, and that type needs to 
     * be one of: ...
     *)
    Notation ideal_users :=
      [
        (* Authorative DNS Server Specification *)
        mkiUsr USR1 PERMS1
               (
                 @idealServer loopN (Base Nat) 1
                              (
                                m <- @Recv Nat CH21
                                ; let ip := match names $? extractContent m with
                                            | None   => 0
                                            | Some a => a
                                            end
                                  in
                                  _ <- Send (Content ip) CH12
                                ; @Return (Base Nat) ip
                              )
               )
        ;

      (* Secure DNS Cache Specification *)
      mkiUsr USR2 PERMS2
             (
               req <- @Recv Nat CH32
               ; _ <- Send (Content (extractContent req)) CH21
               ; ip1 <- @Recv Nat CH12
               ; _ <- Send (Content (extractContent ip1)) CH23
               ; @Return (Base Nat) (extractContent ip1)
             )
        ;

      (* DNS Client Specification *)
      mkiUsr USR3 PERMS3
             (
               _ <- Send (Content 0) CH32
               ; ip1 <- @Recv Nat CH23
               ; @Return (Base Nat) (extractContent ip1)
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
    Notation KID5 := 4.
    Notation KID6 := 5.

    Notation KEYS := [ skey KID1 ; ekey KID2 ; skey KID3 ; ekey KID4 ; skey KID5 ; ekey KID6 ].

    Notation KEYS1 := ($0 $+ (KID1, true) $+ (KID2, true) $+ (KID3, false) $+ (KID4, false)).
    Notation KEYS2 := ($0 $+ (KID1, false) $+ (KID2, false)
                        $+ (KID3, true) $+ (KID4, true)
                        $+ (KID5, false) $+ (KID6, false)).
    Notation KEYS3 := ($0 $+ (KID3, false) $+ (KID4, false) $+ (KID5, true) $+ (KID6, true)).

    Notation real_users :=
      [
        (* Authoritative DNS server implementation *)
        MkRUserSpec USR1 KEYS1
                    (
                      @realServer loopN (Base Nat) 1
                                  ( c <- @Recv Nat (SignedEncrypted KID3 KID2 true)
                                    ; m <- Decrypt c
                                    ; let ip := match names $? (extractContent m) with
                                                | None   => 0
                                                | Some a => a
                                                end
                                      in ipC <- SignEncrypt KID1 KID4 USR2 (message.Content ip)
                                    ; _ <- Send USR2 ipC
                                    ; @Return (Base Nat) ip
                                  )
                    )
        ;

      (* Secure DNS Cache implementation *)
      MkRUserSpec USR2 KEYS2
                  (
                    reqc <- @Recv Nat (SignedEncrypted KID5 KID4 true)
                    ; req <- Decrypt reqc
                    ; c1 <- SignEncrypt KID3 KID2 USR1 (message.Content (extractContent req))
                    ; _ <- Send USR1 c1
                    ; hostC <- @Recv Nat (SignedEncrypted KID1 KID4 true)
                    ; host <- Decrypt hostC
                    ; c2 <- SignEncrypt KID3 KID6 USR3 (message.Content (extractContent host))
                    ; _ <- Send USR3 c2
                    ; @Return (Base Nat) (extractContent host)
                  ) 
        ;

      (* DNS Client implementation *)
      MkRUserSpec USR3 KEYS3
                  (
                    c <- SignEncrypt KID5 KID4 USR2 (message.Content 0)
                    ; _ <- Send USR2 c
                    ; hostC <- @Recv Nat (SignedEncrypted KID3 KID6 true)
                    ; host <- Decrypt hostC
                    ; @Return (Base Nat) (extractContent host)
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
  
End SecureDNSProtocol.
