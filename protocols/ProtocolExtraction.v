(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily reflect the views of the
 * Department of the Air Force.
 *
 * © 2020 Massachusetts Institute of Technology.
 *
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 *
 * The software/firmware is provided to you on an As-Is basis
 *
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)

From Coq Require
     extraction.Extraction
     extraction.ExtrHaskellBasic
     extraction.ExtrHaskellNatInt
.

Extraction Language Haskell.

Cd "../haskell/src".

From Coq Require Import
     List.
Import ListNotations.

Require Import
        ExampleProtocols.

Section PingProtocol.
  Import SignPingSendProtocol.
  Import RealWorld.
  Import RealWorldNotations.

  Definition akeys := [(KID1, true)].
  Definition bkeys := [(KID1, false)].

  Definition userProto1 : user_cmd (Base Messages.Nat) :=
  (* user A *)
    ( n  <- Gen
    ; c  <- Sign KID1 B (message.Content n)
    ; _  <- Send B c
    ; Return n).

  Definition userProto2 : user_cmd (Base Messages.Nat) :=
  (* user B *)
    ( c  <- @Recv Messages.Nat (Signed KID1 true)
    ; v  <- Verify KID1 c
    ; ret (if fst v
           then match snd v with
                | message.Content p => p
                | _                 => 0
                end
           else 1)).

  Definition simpleSendProto :=
    ( [KEY1]
      , [(akeys, userProto1); (bkeys, userProto2)] ).
End PingProtocol.

Section ShareSecretProtocol.
  Import RealWorld Keys Messages.
  Import RealWorldNotations.

  Notation KID1 := 0.
  Notation KID2 := 1.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEY2  := MkCryptoKey KID2 Signing AsymKey.

  Definition secprotokeysa := [(KID1, true) ; (KID2, false)].
  Definition secprotokeysb := [(KID1, false); (KID2, true)].

  Definition secprotoUsera : user_cmd (Base Nat) :=
    (* user A *)
    ( kp <- GenerateAsymKey Encryption
      ; c1 <- Sign KID1 B (Permission (fst kp, false))
      ; _  <- Send B c1
      ; c2 <- @Recv Nat (SignedEncrypted KID2 (fst kp) true)
      ; m  <- Decrypt c2
      ; @Return (Base Nat) (extractContent m) ).
      
  Definition secprotoUserb : user_cmd (Base Nat) :=
           (* user B *)
           ( c1 <- @Recv Access (Signed KID1 true)
           ; v  <- Verify KID1 c1
           ; n  <- Gen
           ; c2 <- SignEncrypt KID2 (fst (extractPermission (snd v))) A (message.Content n)
           ; _  <- Send A c2
           ; @Return (Base Nat) n).

  Definition shareSecretProto :=
    ( [KEY1 ; KEY2]
      , [(secprotokeysa, secprotoUsera); (secprotokeysb, secprotoUserb)] ).

End ShareSecretProtocol.

Separate Extraction simpleSendProto shareSecretProto.
Separate Extraction SignPingSendProtocol.real_univ_start.
