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
        Messages
        Tactics
        Simulation
        RealWorld
        AdversarySafety.

Require IdealWorld.
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
