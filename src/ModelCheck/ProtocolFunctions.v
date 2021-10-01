(*
 * © 2019 Massachusetts Institute of Technology.
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
     Simulation
     AdversaryUniverse

     ModelCheck.SafeProtocol
.

From SPICY Require
     IdealWorld
     RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* Permissions *)
Notation owner  := {| IdealWorld.read := true; IdealWorld.write := true |}.
Notation reader := {| IdealWorld.read := true; IdealWorld.write := false |}.
Notation writer := {| IdealWorld.read := false; IdealWorld.write := true |}.

Section IdealWorldDefs.
  Import IdealWorld.

  Definition mkiUsr {t} (uid : user_id) (p : permissions) (proto : cmd (Base t)) :=
    (uid, {| perms := p ; protocol := proto |}).

  Definition mkiU {t} (cv : channels) (usrs : list (user_id * user t)) :=
    {| channel_vector := cv;
       users := fold_left (fun us u => us $+ (fst u, snd u)) usrs $0
    |}.

  Definition sharePerm (pid : perm_id) (p : permission) :=
    Permission (construct_access p pid).

  Definition getPerm (m : message Access) : perm_id :=
    ch_id (extractPermission m).
    
  Fixpoint idealServer (n : nat) {t} (r : << t >>) (c : cmd t) : cmd t :=
    match n with
    | 0   => @Return t r
    | S i => (r' <- c ; idealServer i r c)
    end.

  Lemma unroll_idealserver_step : forall n i t r (c : cmd t),
      n = S i
      -> idealServer n r c = IdealWorld.Bind c (fun _ => (idealServer i r c)).
  Proof.
    induct n; intros; try discriminate.
    inversion H; subst.
    unfold idealServer at 1; simpl.
    fold idealServer; eauto.
  Qed.

  Lemma idealserver_done : forall t r (c : cmd t),
      idealServer 0 r c = IdealWorld.Return r.
  Proof.
    eauto.
  Qed.

  #[global] Opaque idealServer.

End IdealWorldDefs.

Section RealWorldDefs.
  Import RealWorld.

  Definition mkrUsr {t} (ks : key_perms) (p : user_cmd (Base t)) :=
    {| key_heap  := ks ;
       protocol  := p ;
       msg_heap  := [] ;
       c_heap    := [] ;
       from_nons := [] ;
       sent_nons := [] ;
       cur_nonce := 0
    |}.

  (* A nice, boring adversary that can be used for protocol proofs. *)
  Definition noAdv := {| key_heap  := $0;
                         protocol  := @Return (Base Unit) tt;
                         msg_heap  := [];
                         c_heap    := [];
                         from_nons := [];
                         sent_nons := [];
                         cur_nonce := 0 |}.

  Record RUserSpec {t} :=
    MkRUserSpec {
        userId    : user_id ;
        userKeys  : key_perms ;
        userProto : user_cmd (Base t)
      }.

  Definition mkrU {t} (gks : keys) (usrs : list (@RUserSpec t)) :=
    let us := fold_left (fun acc u => acc $+ (u.(userId), mkrUsr u.(userKeys) u.(userProto))) usrs $0
    in  {| users       := us ;
           adversary   := noAdv ;
           all_ciphers := $0 ;
           all_keys    := gks
        |}.

  Definition sharePrivKey (kp : key_permission) :=
    Permission (fst kp, true).

  Definition sharePubKey (kp : key_permission) :=
    Permission (fst kp, false).

  Definition getKey (m : message Access) : key_identifier :=
    fst (extractPermission m).

  Fixpoint realServer (n : nat) {t} (r : << t >>) (c : user_cmd t) : user_cmd t :=
    match n with
    | 0   => @Return t r
    | S i => (r' <- c ; realServer i r c)
    end.

  Lemma unroll_realserver_step : forall n i t r (c : user_cmd t),
      n = S i
      -> realServer n r c = RealWorld.Bind c (fun _ => (realServer i r c)).
  Proof.
    induct n; intros; try discriminate.
    inversion H; subst.
    unfold realServer at 1; simpl.
    fold realServer; eauto.
  Qed.

  Lemma realserver_done : forall t r (c : user_cmd t),
      realServer 0 r c = RealWorld.Return r.
  Proof.
    eauto.
  Qed.

  #[global] Opaque realServer.

End RealWorldDefs.

Definition mkKeys (ks : list key) :=
  fold_left (fun ks k => ks $+ (k.(keyId),k)) ks $0.

#[export] Hint Unfold
     mkiU mkiUsr
     sharePerm getPerm
     mkrU mkrUsr
     sharePrivKey sharePubKey getKey
     mkKeys
     noAdv : user_build.

#[export] Hint Unfold
     mkiU mkiUsr
     sharePerm getPerm
     mkrU mkrUsr
     sharePrivKey sharePubKey getKey
     mkKeys
     noAdv : core.

Declare Scope protocol_scope.

Notation "'skey' kid"     := (MkCryptoKey kid Signing AsymKey) (at level 80) : protocol_scope.
Notation "'ekey' kid"     := (MkCryptoKey kid Encryption AsymKey) (at level 80) : protocol_scope.
Notation "'skey_sym' kid" := (MkCryptoKey kid Signing SymKey) (at level 80) : protocol_scope.
Notation "'ekey_sym' kid" := (MkCryptoKey kid Encryption SymKey) (at level 80) : protocol_scope.
