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
        Tactics
        Simulation
        RealWorld
        AdversarySafety
        ProtocolAutomation.

Require IdealWorld.

Set Implicit Arguments.

Section RealWorldLemmas.

  Import RealWorld RealWorldNotations.

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

  Inductive UVal (t : user_cmd_type) : Set :=
  | ConcreteVal (v : << t >> )
  | SymbolicVal (* some kind of existential here?? *)
  .

  Inductive syntactically_safe : forall {t}, user_cmd t -> Prop :=
  (* The crux of the matter: *)

  (* | SafeBind : forall {r A} (cmd1 : user_cmd r) (cmd2 : <<r>> -> user_cmd A), *)
  (*     next_cmd_safe honestk cs u_id froms sents cmd1 *)
  (*     -> next_cmd_safe honestk cs u_id froms sents (Bind cmd1 cmd2) *)
  (* | SafeEncrypt : forall {t} (msg : message t) k__sign k__enc msg_to, *)
  (*     honestk $? k__enc = Some true *)
  (*     -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true) *)
  (*     -> next_cmd_safe honestk cs u_id froms sents (SignEncrypt k__sign k__enc msg_to msg) *)
  (* | SafeSign : forall {t} (msg : message t) k msg_to, *)
  (*     (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false) *)
  (*     -> next_cmd_safe honestk cs u_id froms sents (Sign k msg_to msg) *)
  (* | SafeRecv : forall t pat, *)
  (*     msg_pattern_safe honestk pat *)
  (*     -> next_cmd_safe honestk cs u_id froms sents (@Recv t pat) *)
  (* | SafeSend : forall {t} (msg : crypto t) msg_to, *)
  (*       msg_honestly_signed honestk cs msg = true *)
  (*     -> msg_to_this_user cs (Some msg_to) msg = true *)
  (*     -> msgCiphersSignedOk honestk cs msg *)
  (*     -> (exists c_id c, msg = SignedCiphertext c_id *)
  (*               /\ cs $? c_id = Some c *)
  (*               /\ fst (cipher_nonce c) = (Some u_id)  (* only send my messages *) *)
  (*               /\ ~ List.In (cipher_nonce c) sents) *)
  (*     -> next_cmd_safe honestk cs u_id froms sents (Send msg_to msg) *)

  (* Boring Terms *)
  | SafeReturn : forall {A} (a : << A >>), syntactically_safe (Return a)
  | SafeGen : syntactically_safe Gen
  | SafeDecrypt : forall {t} (c : crypto t), syntactically_safe (Decrypt c)
  | SafeVerify : forall {t} k (c : crypto t), syntactically_safe (Verify k c)
  | SafeGenerateSymKey : forall usage, syntactically_safe (GenerateSymKey usage)
  | SafeGenerateAsymKey : forall usage, syntactically_safe (GenerateAsymKey usage)
  .


  (*
   * If we can prove that some simple syntactic symbolic execution implies
   * the honest_cmds_safe predicate...
   *)
  Lemma syntactically_safe_implies_next_cmd_safe :
    forall {A B} (U : universe A B),
      Forall_natmap (fun u => syntactically_safe u.(protocol)) U.(users)
      -> honest_cmds_safe U.
  Proof.
  Admitted.

  Definition rstepSilent {A B} (U U' : universe A B) :=
    step_universe U Silent U'.

  (*
   * And that the syntactic safety predicate is preserved through any
   * silent real world step 
   *)
  Lemma syntactically_safe_preservation' :
    forall {A B} (U U': universe A B),
      Forall_natmap (fun u => syntactically_safe u.(protocol)) U.(RealWorld.users)
      -> step_universe U Silent U'
      -> Forall_natmap (fun u => syntactically_safe u.(protocol)) U'.(RealWorld.users).
  Proof.
  Admitted.

  Lemma syntactically_safe_preservation :
    forall {A B} (U U': universe A B),
      Forall_natmap (fun u => syntactically_safe u.(protocol)) U.(RealWorld.users)
      -> rstepSilent ^* U U'
      -> Forall_natmap (fun u => syntactically_safe u.(protocol)) U'.(RealWorld.users).
  Proof.
  Admitted.

End RealWorldLemmas.

Module Type ProcDef.
  Parameter t__hon : type.
  Parameter t__adv : type.
  Parameter iu0 : IdealWorld.universe t__hon.
  Parameter ru0 : RealWorld.universe t__hon t__adv.
End ProcDef.

Module Gen (PD : ProcDef).
  Import
    PD
    SetLemmas
    ModelCheck
    Invariant
    Relations.

  Definition univ_pr : Type := (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)%type.

  Inductive step : univ_pr -> univ_pr -> Prop :=
  | RealSilent : forall ru ru' iu,
      RealWorld.step_universe ru Silent ru' -> step (ru, iu) (ru', iu)
  | BothLoud : forall ru ru' ra ia iu iu' iu'',
      RealWorld.step_universe ru (Action ra) ru'
      -> istepSilent^* iu iu'
      -> IdealWorld.lstep_universe iu' (Action ia) iu''
      -> action_matches ra ru' ia iu''
      -> step (ru, iu) (ru', iu'').

  (*
   * Can we use the above to silently step as far as possible, then check
   * the ensuing labeled step for the necessary conditions to prove simulation.
   *)
  Lemma check_required_labeled_step :
    forall {A B} (U__r U__r' U__r'' : RealWorld.universe A B) U__i U__i' U__i'' a__r a__i,
      ( rstepSilent ^* U__r U__r' -> U__r = U__r' ) (* no available silent steps *)
      -> Forall_natmap (fun u => syntactically_safe u.(protocol)) U__r'.(RealWorld.users)
      -> RealWorld.step_universe U__r' (Action a__r) U__r''
      -> istepSilent ^* U__i U__i'
      -> IdealWorld.lstep_universe U__i' (Action a__i) U__i''
      -> action_matches a__r U__r' a__i U__i'
      /\ Forall_natmap (fun u => syntactically_safe u.(protocol)) U__r''.(RealWorld.users).
  Proof.
  Admitted.

  (*
   * Now, I want to use all of the above lemmas to prove simulation, essentially converting
   * the whole proof into the above syntactic protocol check, plus some labeled step verification.
   *)
  
End Gen.
