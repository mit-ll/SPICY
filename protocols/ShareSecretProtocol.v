(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019-2020 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     List.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     Common
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse

     ModelCheck.ModelCheck
     ModelCheck.UniverseEqAutomation
     ModelCheck.ProtocolAutomation
     ModelCheck.SafeProtocol
     ModelCheck.ProtocolFunctions
.

From SPICY Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations
       SimulationAutomation.

From Frap Require Sets.

Module Foo <: Sets.EMPTY.
End Foo.
Module Export SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Open Scope protocol_scope.

Module ShareSecretProtocol.

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
    Notation PERMS2 := ($0 $+ (pCH12, reader) $+ (pCH21, owner)).

    Notation ideal_users :=
      [
        (mkiUsr USR1 PERMS1 
                ( chid <- CreateChannel
                  ; _ <- Send (Permission {| ch_perm := writer ; ch_id := chid |}) CH12
                  ; m <- @Recv Nat (chid #& pCH21)
                  ; @Return (Base Nat) (extractContent m)
        )) ;
      (mkiUsr USR2 PERMS2
              ( m <- @Recv Access CH12
                ; n <- Gen
                ; _ <- let chid := ch_id (extractPermission m)
                      in  Send (Content n) (chid #& pCH21)
                ; @Return (Base Nat) n
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

    Notation real_users :=
      [
        MkRUserSpec USR1 KEYS1
                    ( kp <- GenerateAsymKey Encryption
                      ; c1 <- Sign KID1 USR2 (Permission (fst kp, false))
                      ; _  <- Send USR2 c1
                      ; c2 <- @Recv Nat (SignedEncrypted KID2 (fst kp) true)
                      ; m  <- Decrypt c2
                      ; @Return (Base Nat) (extractContent m) ) ;

      MkRUserSpec USR2 KEYS2
                  ( c1 <- @Recv Access (Signed KID1 true)
                    ; v  <- Verify KID1 c1
                    ; n  <- Gen
                    ; c2 <- SignEncrypt KID2 (fst (extractPermission (snd v))) USR1 (message.Content n)
                    ; _  <- Send USR1 c2
                    ; @Return (Base Nat) n)
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
  
End ShareSecretProtocol.
