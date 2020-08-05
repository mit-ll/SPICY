(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force 
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed 
 * in this material are those of the author(s) and do not necessarily reflect the views of the 
 * Department of the Air Force.
 * 
 * © 2019 Massachusetts Institute of Technology.
 * 
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the contractor (May 2014)
 * 
 * The software/firmware is provided to you on an As-Is basis
 * 
 * Delivered to the U.S. Government with Unlimited Rights, as defined in DFARS Part 252.227-7013
 * or 7014 (Feb 2014). Notwithstanding any copyright notice, U.S. Government rights in this work are
 * defined by DFARS 252.227-7013 or DFARS 252.227-7014 as detailed above. Use of this work other than
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     List.

Require Import
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
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Notation USR1 := 0.
Notation USR2 := 1.
Notation USR3 := 2.
(* Definition USR1 : user_id   := 0. *)
(* Definition USR2 : user_id   := 1. *)
(* Definition USR3 : user_id   := 2. *)

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

End RealWorldDefs.

Definition mkKeys (ks : list key) :=
  fold_left (fun ks k => ks $+ (k.(keyId),k)) ks $0.

Declare Scope protocol_scope.
Notation "uid 'with' ks >> p" := (MkRUserSpec uid ks p) (at level 80) : protocol_scope.

Notation "'skey' kid"     := (MkCryptoKey kid Signing AsymKey) (at level 80) : protocol_scope.
Notation "'ekey' kid"     := (MkCryptoKey kid Encryption AsymKey) (at level 80) : protocol_scope.
Notation "'skey_sym' kid" := (MkCryptoKey kid Signing SymKey) (at level 80) : protocol_scope.
Notation "'ekey_sym' kid" := (MkCryptoKey kid Encryption SymKey) (at level 80) : protocol_scope.
