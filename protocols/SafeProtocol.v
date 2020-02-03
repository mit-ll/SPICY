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
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)

From Coq Require Import
     List.

Require Import
        MyPrelude
        Maps
        Keys
        Messages
        ModelCheck
        Tactics
        Simulation
        RealWorld
        AdversarySafety.

Require Sets IdealWorld.
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

(* 
 * Our definition of a Safe Protocol.  For now, we assume a pretty boring initial
 * adversary state.  The constraints could be relaxed a bit, but it is unclear that
 * there is really any purpose in doing so.
 *)
Module Type SafeProtocol.

  Parameter A B : type.
  Parameter U__i : IdealWorld.universe A.
  Parameter U__r : universe A B.
  Parameter b : << Base B >>.
  Parameter R : simpl_universe A -> IdealWorld.universe A -> Prop.

  Axiom U_good : universe_starts_sane b U__r.

  Axiom R_silent_simulates : simulates_silent_step (lameAdv b) R.
  Axiom R_loud_simulates : simulates_labeled_step (lameAdv b) R.
  Axiom R_honest_actions_safe : honest_actions_safe B R.
  Axiom universe_starts_safe : R (peel_adv U__r) U__i /\ universe_ok U__r /\ adv_universe_ok U__r.

End SafeProtocol.

(*
 * A Functor which lifts any 'SafeProtocol' into the state we really want,
 * namely a universe where there is an adversary executing arbitrary code.
 * This lifting is basically provided by the top level proofs of
 * AdversarySafety.
 *)

Module AdversarySafeProtocol ( Proto : SafeProtocol ).
  Import Proto.

  Hint Resolve
       R_silent_simulates
       R_loud_simulates
       R_honest_actions_safe.

  Lemma proto_lamely_refines :
    refines (lameAdv b) U__r U__i.
  Proof.
    exists R; unfold simulates.
    pose proof universe_starts_safe.
    intuition eauto.
  Qed.

  Hint Resolve proto_lamely_refines.

  Lemma proto_starts_ok : universe_starts_ok U__r.
  Proof.
    pose proof universe_starts_safe.
    pose proof U_good.
    unfold universe_starts_ok; intros.
    unfold universe_ok, adv_universe_ok, universe_starts_sane in *; split_ands.
    intuition eauto.
  Qed.

  Hint Resolve proto_starts_ok.

  Theorem protocol_with_adversary_could_generate_spec :
    forall U__ra advcode acts__r,
      U__ra = add_adversary U__r advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate U__i acts__i
          /\ traceMatches acts__r acts__i.
  Proof.
    intros.
    pose proof U_good as L; unfold universe_starts_sane, adversary_is_lame in L; split_ands.
    eapply refines_could_generate; eauto.
  Qed.
  
End AdversarySafeProtocol.

Section SafeProtocolLemmas.

  Import RealWorld.

  Lemma adversary_is_lame_adv_univ_ok_clauses :
    forall A B (U : universe A B) b,
      universe_starts_sane b U
      -> permission_heap_good U.(all_keys) U.(adversary).(key_heap)
      /\ message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
      /\ adv_cipher_queue_ok U.(all_ciphers) U.(users) U.(adversary).(c_heap)
      /\ adv_message_queue_ok U.(users) U.(all_ciphers) U.(all_keys) U.(adversary).(msg_heap)
      /\ adv_no_honest_keys (findUserKeys U.(users)) U.(adversary).(key_heap).
  Proof.
    unfold universe_starts_sane, adversary_is_lame; intros; split_ands.
    repeat match goal with
           | [ H : _ (adversary _) = _ |- _ ] => rewrite H; clear H
           end.
    repeat (simple apply conj); try solve [ econstructor; clean_map_lookups; eauto ].

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      specialize (H _ _ H2); rewrite H; econstructor.
    - unfold adv_no_honest_keys; intros.
      cases (findUserKeys (users U) $? k_id); eauto.
      destruct b0; eauto.
      right; right; apply conj; eauto.
      clean_map_lookups.

      Unshelve.
      exact (MkCryptoKey 1 Encryption SymKey).
  Qed.

End SafeProtocolLemmas.

Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Inductive step (t__hon t__adv : type) :
  (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> Prop :=
| RealSilent : forall ru ru' iu,
    RealWorld.step_universe ru Silent ru' -> step (ru, iu) (ru', iu)
| BothLoud : forall ru ru' ra ia iu iu' iu'',
    RealWorld.step_universe ru (Action ra) ru'
    -> istepSilent^* iu iu'
    -> IdealWorld.lstep_universe iu' (Action ia) iu''
    -> action_matches ra ru' ia iu'
    -> step (ru, iu) (ru', iu'').

Definition lift_fst {A B C} (f : A -> C) : (A * B) -> C :=
  fun p => f (fst p).

Module Type AutomatedSafeProtocol.

  Parameter t__hon : type.
  Parameter t__adv : type.
  Parameter b : << Base t__adv >>.
  Parameter iu0 : IdealWorld.universe t__hon.
  Parameter ru0 : RealWorld.universe t__hon t__adv.

  Axiom U_good : universe_starts_sane b ru0.
  Axiom universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0.

  Axiom safe_invariant : invariantFor
                           {| Initial := {(ru0, iu0)}; Step := @step t__hon t__adv  |}
                           (lift_fst honest_cmds_safe).

End AutomatedSafeProtocol.

Section RealWorldLemmas.

  Import
    RealWorld
    RealWorldNotations.

  Lemma universe_predicates_preservation :
    forall {A B} (U U' : universe A B) lbl,
      universe_ok U
      -> adv_universe_ok U
      -> honest_cmds_safe U
      -> step_universe U lbl U'
      -> universe_ok U'
        /\ adv_universe_ok U'.
  Proof.
    intros * UOK AUOK HCS STEP.
    destruct lbl;
      intuition eauto.

    unfold adv_universe_ok in *; split_ands; 
      eapply honest_labeled_step_univ_ok;
      eauto using honest_cmds_implies_safe_actions.
  Qed.
End RealWorldLemmas.

Module ProtocolSimulates (Proto : AutomatedSafeProtocol).
  Import Proto Simulation.

  (* Hint Resolve *)
  (*      R_silent_simulates *)
  (*      R_loud_simulates *)
  (*      R_honest_actions_safe. *)

  Inductive R :
    RealWorld.simpl_universe t__hon
    -> IdealWorld.universe t__hon
    -> Prop :=
  | Sil : forall ru ru' iu,
      R (RealWorld.peel_adv ru) iu
      -> RealWorld.step_universe ru Silent ru'
      -> R (@RealWorld.peel_adv _ t__adv ru') iu
  | Loud : forall ru ru' iu iu' iu'' a__r a__i,
      R (RealWorld.peel_adv ru) iu
      -> RealWorld.step_universe ru (Action a__r) ru'
      -> istepSilent^* iu iu'
      -> IdealWorld.lstep_universe iu' (Action a__i) iu''
      -> action_matches a__r ru' a__i iu'
      -> R (@RealWorld.peel_adv _ t__adv ru') iu''.

  Lemma proto_lamely_refines :
    refines (lameAdv b) ru0 iu0.
  Proof.
    eexists; unfold simulates.
    pose proof safe_invariant.
    unfold invariantFor, lift_fst in H; simpl in H.
    assert ( (ru0,iu0) = (ru0,iu0) \/ False ) as ARG by eauto.
    specialize (H _ ARG); clear ARG.

    unfold simulates_silent_step, simulates_labeled_step.
    split; intros.
    
    

    (* pose proof universe_starts_safe. *)
    (* intuition eauto. *)
  Admitted.

  Hint Resolve proto_lamely_refines.

  Lemma proto_starts_ok : universe_starts_ok ru0.
  Proof.
    pose proof universe_starts_safe.
    pose proof U_good.
    unfold universe_starts_ok; intros.
    unfold universe_ok, adv_universe_ok, universe_starts_sane in *; split_ands.
    intuition eauto.
  Qed.

  Hint Resolve proto_starts_ok.

  Theorem protocol_with_adversary_could_generate_spec :
    forall U__ra advcode acts__r,
      U__ra = add_adversary ru0 advcode
      -> rCouldGenerate U__ra acts__r
      -> exists acts__i,
          iCouldGenerate iu0 acts__i
          /\ traceMatches acts__r acts__i.
  Proof.
    intros.
    pose proof U_good as L; unfold universe_starts_sane, adversary_is_lame in L; split_ands.
    eapply refines_could_generate; eauto.
  Qed.

End ProtocolSimulates.
