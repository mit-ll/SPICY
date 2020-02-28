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
     List
     Logic.ProofIrrelevance
     Program.Equality.

Require Import MyPrelude Maps ChMaps Common.
Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Section RealLemmas.

  Import RealWorld.

  Lemma real_univ_eq_fields_eq :
    forall {A B} (us us' : honest_users A) (a a' : user_data B) cs cs' ks ks',
      us = us'
      -> a = a'
      -> cs = cs'
      -> ks = ks'
      -> {| users       := us
         ; adversary   := a
         ; all_ciphers := cs
         ; all_keys    := ks
        |} =
        {| users       := us'
         ; adversary   := a'
         ; all_ciphers := cs'
         ; all_keys    := ks'
        |}.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma real_univ_same_as_fields :
    forall {A B} (U : universe A B) (us : honest_users A) (a : user_data B) cs ks,
        us = U.(users)
      -> a  = U.(adversary)
      -> cs = U.(all_ciphers)
      -> ks = U.(all_keys)
      -> {| users       := us
         ; adversary   := a
         ; all_ciphers := cs
         ; all_keys    := ks
        |} = U.
    intros; destruct U; subst; trivial.
  Qed.

End RealLemmas.

Section IdealLemmas.
  Import IdealWorld.

  Lemma ideal_univ_eq_fields_eq :
    forall {A} (us us' : user_list (user A)) cv cv',
      us = us'
      -> cv = cv'
      -> {| channel_vector := cv; users := us |}
        = {| channel_vector := cv'; users := us' |}.
    intros; subst; reflexivity. Qed.
                               
  Lemma ideal_universe_same_as_fields :
    forall {A} (U : universe A) us cv,
      us = U.(users)
      -> cv = U.(channel_vector)
      -> {| channel_vector := cv; users := us |} = U.
    intros; destruct U; subst; trivial. Qed.

End IdealLemmas.

(* Hint Rewrite add_empty_idempotent empty_add_idempotent : maps. *)

Ltac smash_universe :=
  unfold RealWorld.buildUniverse;
  repeat (match goal with
          | [ |- {| RealWorld.users := _
                 ; RealWorld.adversary := _
                 ; RealWorld.all_ciphers := _
                 ; RealWorld.all_keys := _ |} = _
            ] => eapply real_univ_eq_fields_eq
          | [ |- {| IdealWorld.users := _;
                   IdealWorld.channel_vector := _ |} = _
            ] => eapply ideal_univ_eq_fields_eq
          | [ |- _ = _ ] => reflexivity
          end).

Section ExamplarProofs.

  Definition uid1 := 1.
  Definition uid2 := 2.

  Section Ideal.
    Import IdealWorld.
    (* Import ChNotation. *)
    Import ChannelType.

    Definition ch1 := (Single 10).
    Definition ch2 := (Single 11).

    (* This needs more of the lemmas in ChMaps *)
    Lemma ideal_test1 :
      forall {A} msgs1 msgs2 msgs3 perms1 perms2 (proto1 proto2 : cmd (Base A)),
      exists perms1' perms2',
        {| channel_vector := #0 #+ (ch1, msgs1) #+ (ch2, msgs2) #+ (ch1, msgs3);
           users := $0 $+ (uid2, {| protocol := proto2; perms := perms2 |})
                     $+ (uid1, {| protocol := proto1; perms := perms1 |}) |}
        =
        {| channel_vector := #0 #+ (ch1, msgs3) #+ (ch2, msgs2) ;
           users := $0 $+ (uid1, {| protocol := proto1; perms := perms1' |})
                     $+ (uid2, {| protocol := proto2; perms := perms2' |}) |}.
    Proof.
      intros. do 2 eexists; smash_universe; Maps.m_equal; ChMaps.m_equal; eauto.
    Qed.

  End Ideal.

  
End ExamplarProofs.
