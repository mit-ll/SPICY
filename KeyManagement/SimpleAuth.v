From Coq Require Import String.
From Coq Require Import Bool.Sumbool.
Require Import Frap.

Require Import Common.
Set Implicit Arguments.
Require IdealWorld.
Require RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Section IdealSimpleAuth.

  Import IdealWorld.

  Definition A := 0.
  Definition B := 1.
  Definition adversary := 2.
    
  Example auth_universe (adversary_protocol : cmd nat) : universe nat :=
    {| channel_vector := $0 $+ (0, {});
       users := [
               (A, {| perms := $0 $+ (0, {| read := true ; write := true |});
                      protocol :=
                        (_ <- (Send (Content 2) 0);
                         Return 1)
                   |});
               (B, {| perms := $0 $+ (0, {| read := true ; write := false |});
                      protocol :=
                        ( r <- (Recv 0);
                            Return match extractContent r with Some c => c | None => 0 end)
                          
                   |});
               (adversary, {| perms := $0 $+ (0, {| read := true ; write := false |});
                              protocol := adversary_protocol |})
               ]
    |}.
  
  Definition auth_sys (adversary_protocol : cmd nat) :=
    {| Initial := fun U' => U' = auth_universe adversary_protocol ;
       Step := IdealWorld.step_universe |}.

(* other proposed invariant: 
   if in final state, A and B answers should be included in non-adversary final state.
   if so then what should be calculated in non-final positions? just always True? *)
  Inductive auth_invariant (auth_U : universe nat) : Prop :=
  | NotPublishedYet : forall s,
      auth_U.(channel_vector) $? 0 = Some s ->
      s = {} ->
      auth_invariant auth_U
  | ValuePublished : forall s,
      auth_U.(channel_vector) $? 0 = Some s ->
      s = {Exm(Content 2)} ->
      auth_invariant auth_U.

  Theorem adversary_unable_to_sign :
    forall (adversary_protocol : cmd nat),
      invariantFor (auth_sys adversary_protocol) (auth_invariant).
  Proof.
    simplify.
    apply invariant_induction; simplify.

    invert H.

    unfold auth_universe. apply NotPublishedYet with {}; simplify; try equality.

    invert H0.
    Admitted.
End IdealSimpleAuth.

Section RealSimpleAuth.
  Import RealWorld.

  Definition KEYID := 0.
  Definition KEY := SymKey (MkCryptoKey KEYID Signing).

  Definition RA := 0.
  Definition RB := 1.
  Definition Radversary := 2.

  Definition uks0 := $0 $+ (KEYID, KEY).
  Definition uks1 := $0 $+ (KEYID, KEY).
  Definition ks   := $0 $+ (KEYID, KEY).

  Example real_enc_ping (adversary_protocol : user_cmd nat) : list (user_data nat) :=
    [{| usrid := RA ;
        key_heap := uks0 ;
        protocol := ( m <- Sign KEY (Plaintext 2) ;
                      _ <- Send RB m ;
                      Return 1)
     |};
       {| usrid    := RB
          ; key_heap := uks1   
          ; protocol := (  cmsg <- Recv (A := cipher_id);
                           rec <- Verify KEY cmsg;
                           Return (if rec then 2 else 98))
    |}
    ; 
    {| usrid    := Radversary
     ; key_heap := $0
     ; protocol := adversary_protocol
    |}].

End RealSimpleAuth.
