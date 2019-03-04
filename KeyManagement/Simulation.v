From Coq Require Import
     List
     Eqdep.

Require Import MyPrelude Users Common. 

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Hint Resolve in_eq in_cons.

Definition rstepSilent {A : Type} (U1 U2 : RealWorld.universe A) :=
  RealWorld.lstep_universe U1 Silent U2.

Definition istepSilent {A : Type} (U1 U2 : IdealWorld.universe A) :=
  IdealWorld.lstep_universe U1 Silent U2.

Inductive chan_key : Set :=
| Public (ch_id : IdealWorld.channel_id)
| Auth (ch_id : IdealWorld.channel_id): forall k,
    k.(RealWorld.keyUsage) = RealWorld.Signing -> chan_key
| Enc  (ch_id : IdealWorld.channel_id) : forall k,
    k.(RealWorld.keyUsage) = RealWorld.Encryption -> chan_key
| AuthEnc (ch_id : IdealWorld.channel_id) : forall k1 k2,
      k1.(RealWorld.keyUsage) = RealWorld.Signing
    -> k2.(RealWorld.keyUsage) = RealWorld.Encryption
    -> chan_key
.

Inductive msg_eq : forall t__r t__i,
    RealWorld.message t__r
    -> IdealWorld.message t__i * IdealWorld.channel_id * IdealWorld.channels * IdealWorld.permissions -> Prop :=

(* Still need to reason over visibility of channel -- plaintext really means everyone can see it *)
| PlaintextMessage' : forall content ch_id cs ps,
    ps $? ch_id = Some (IdealWorld.construct_permission true true) ->
    msg_eq (RealWorld.Plaintext content) (IdealWorld.Content content, ch_id, cs, ps)
.

Definition check_cipher (ch_id : IdealWorld.channel_id)
  :=
    forall A B ch_id k (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs (*do we need these??*) chans perms,
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end.
    
Definition chan_key_ok :=
  forall A B ch_id (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs chan_keys (*do we need these??*) chans perms,
    match chan_keys $? ch_id with
    | None => False
    | Some (Public _)   => msg_eq rm (im,ch_id,chans,perms)
    | Some (Auth _ k _) =>
      (* check_cipher ch_id k im rm cphrs chans perms *)
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end
    | Some (Enc  _ k _) => False
    | Some (AuthEnc _ k1 k2 _ _) => False
    end.


Inductive action_matches :
    RealWorld.action -> IdealWorld.action -> Prop :=
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps p x y z,
      rw = (RealWorld.Input msg1 p x y z)
    -> iw = IdealWorld.Input msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
| Out : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps x,
      rw = RealWorld.Output msg1 x
    -> iw = IdealWorld.Output msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
.

Definition lsimulates {A : Type}
           (R : RealWorld.universe A -> IdealWorld.universe A -> Prop)
           (U__r : RealWorld.universe A) (U__i : IdealWorld.universe A) :=

(*  call spoofable *)

  (forall U__r U__i,
      R U__r U__i
      -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
          /\ R U__r' U__i')

  /\ (forall U__r U__i,
        R U__r U__i
        -> forall a1 U__r',
          RealWorld.lstep_universe U__r (Action a1) U__r' (* excludes adversary steps *)
          -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R U__r' U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.adversary)) a1 = true
    (* and adversary couldn't have constructed message seen in a1 *)
    )

  /\ R U__r U__i.

Definition lrefines {A : Type} (U1 : RealWorld.universe A)(U2 : IdealWorld.universe A) :=
  exists R, lsimulates R U1 U2.

Infix "<|" := lrefines (no associativity, at level 70).


Inductive couldGenerate : forall {A}, RealWorld.universe A -> list RealWorld.action -> Prop :=
| CgNothing : forall {A} (u : RealWorld.universe A),
    couldGenerate u []
| CgSilent : forall {A} {u u' : RealWorld.universe A} tr,
    RealWorld.lstep_universe u Silent u'
    -> couldGenerate u' tr
    -> couldGenerate u tr
| CgAction : forall {A} a (u u' : RealWorld.universe A) tr,
    RealWorld.lstep_universe u (Action a) u'
    -> couldGenerate u' tr
    -> couldGenerate u (a :: tr).
