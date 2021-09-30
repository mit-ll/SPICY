(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     Classical
     Lists.List.

From SPICY Require Import
     MyPrelude
     Maps
     Keys
     Messages
     MessageEq
     Tactics
     Simulation
     RealWorld
     AdversarySafety.

From SPICY Require
     IdealWorld.

From Frap Require Import
     Invariant
.

From Frap Require Sets.
Module Foo <: Sets.EMPTY.
End Foo.
Module Import SN := Sets.SetNotations(Foo).

Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

Definition adversary_is_lame {B : type} (b : << Base B >>) (adv : user_data B) : Prop :=
    adv.(key_heap) = $0
  /\ adv.(msg_heap) = []
  /\ adv.(c_heap) = []
  /\ lameAdv b adv.

Definition universe_starts_sane {A B : type} (b : << Base B >>) (U : universe A B) : Prop :=
  let honestk := findUserKeys U.(users)
  in  (forall u_id u, U.(users) $? u_id = Some u -> u.(RealWorld.msg_heap) = [])
      /\ ciphers_honestly_signed honestk U.(RealWorld.all_ciphers)
      /\ keys_honest honestk U.(RealWorld.all_keys)
      /\ adversary_is_lame b U.(adversary).

Definition ModelState {t__hon t__adv : type} := (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon * bool)%type.

Definition safety {t__hon t__adv} (st : @ModelState t__hon t__adv) : Prop :=
  let '(ru, iu, b) := st
  in  honest_cmds_safe ru.

Definition labels_align {t__hon t__adv} (st : @ModelState t__hon t__adv) : Prop :=
  let '(ru, iu, b) := st
  in  forall uid ru' ra,
      indexedRealStep uid (Action ra) ru ru'
      -> exists ia iu' iu'',
        (indexedIdealStep uid Silent) ^* iu iu'
        /\ indexedIdealStep uid (Action ia) iu' iu''
        /\ action_matches ru.(RealWorld.all_ciphers) ru.(RealWorld.all_keys) (uid,ra) ia.

Definition returns_align {t__hon t__adv} (st : @ModelState t__hon t__adv) : Prop :=
  let '(ru, iu, b) := st
  in (forall uid lbl ru', indexedRealStep uid lbl ru ru' -> False)
     -> forall uid ud__r r__r,
      ru.(RealWorld.users) $? uid = Some ud__r
      -> ud__r.(RealWorld.protocol) = RealWorld.Return r__r
      -> exists (iu' : IdealWorld.universe t__hon) ud__i r__i,
          istepSilent ^* iu iu'
          /\ iu'.(IdealWorld.users) $? uid = Some ud__i
          /\ ud__i.(IdealWorld.protocol) = IdealWorld.Return r__i
          /\ Rret_val_to_val r__r = Iret_val_to_val r__i.

Inductive step {t__hon t__adv : type} :
    @ModelState t__hon t__adv 
  -> @ModelState t__hon t__adv
  -> Prop :=
| RealSilent : forall ru ru' suid iu b,
    RealWorld.step_universe suid ru Silent ru'
    -> step (ru, iu, b) (ru', iu, b)
| BothLoud : forall uid ru ru' iu iu' iu'' ra ia b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> indexedIdealStep uid (Action ia) iu' iu''
    -> action_matches ru.(all_ciphers) ru.(all_keys) (uid,ra) ia
    -> labels_align (ru, iu, b)
    -> step (ru, iu, b) (ru', iu'', b)
| MisalignedCanStep : forall uid ru ru' iu iu' iu'' ra ia b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> indexedIdealStep uid (Action ia) iu' iu''
    -> ~ labels_align (ru, iu, b)
    -> step (ru, iu, b) (ru', iu'', false)
| MisalignedCantStep : forall uid ru ru' iu iu' ra b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> (forall lbl iu'', indexedIdealStep uid lbl iu' iu'' -> False)
    -> ~ labels_align (ru, iu, b)
    -> step (ru, iu, b) (ru', iu, false)
.

Inductive indexedModelStep {t__hon t__adv : type} (uid : user_id) :
    @ModelState t__hon t__adv 
  -> @ModelState t__hon t__adv
  -> Prop :=
| RealSilenti : forall ru ru' iu b,
    indexedRealStep uid Silent ru ru'
    -> indexedModelStep uid (ru, iu, b) (ru', iu, b)
| BothLoudi : forall ru ru' iu iu' iu'' ra ia b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> indexedIdealStep uid (Action ia) iu' iu''
    -> action_matches ru.(all_ciphers) ru.(all_keys) (uid,ra) ia
    -> labels_align (ru, iu, b)
    -> indexedModelStep uid (ru, iu, b) (ru', iu'', b)
| MisalignedCanStepi : forall ru ru' iu iu' iu'' ra ia b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> indexedIdealStep uid (Action ia) iu' iu''
    -> ~ labels_align (ru, iu, b)
    -> indexedModelStep uid (ru, iu, b) (ru', iu'', false)
| MisalignedCantStepi : forall ru ru' iu iu' ra b,
    indexedRealStep uid (Action ra) ru ru'
    -> (indexedIdealStep uid Silent) ^* iu iu'
    -> (forall lbl iu'', indexedIdealStep uid lbl iu' iu'' -> False)
    -> ~ labels_align (ru, iu, b)
    -> indexedModelStep uid (ru, iu, b) (ru', iu, false)
.

Definition alignment {t__hon t__adv} (st : @ModelState t__hon t__adv) : Prop :=
  snd st = true
  /\ labels_align st.

Definition TrS {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) :=
  {| Initial := {(ru0, iu0, true)};
     Step    := @step t__hon t__adv |}.
