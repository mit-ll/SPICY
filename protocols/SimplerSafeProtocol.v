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

  Definition my_cipher := sigT crypto.
  Definition my_ciphers := NatMap.t my_cipher.
  Definition proto_data := (key_perms * ciphers)%type.

  Inductive syntactically_safe : forall {t}, proto_data -> user_cmd t -> (<<t>> * key_perms * ciphers) -> Prop :=
  (* The crux of the matter: *)

  | SafeBind : forall {r A} (cmd1 : user_cmd r) (cmd2 : <<r>> -> user_cmd A)
                 v1 v2 honestk1 honestk2 honestk3 cs1 cs2 cs3,
        syntactically_safe (honestk1, cs1) cmd1 (v1, honestk2, cs2)
      -> syntactically_safe (honestk2, cs2) (cmd2 v1) (v2, honestk3, cs3)
      -> syntactically_safe (honestk1, cs1) (Bind cmd1 cmd2) (v2, honestk3, cs3)
  | SafeEncrypt : forall {t} (msg : message t) k__sign k__enc msg_to honestk c_id c cs n,
      ~ In c_id cs
      -> c = SigEncCipher k__sign k__enc msg_to n msg
      -> honestk $? k__enc = Some true
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> syntactically_safe (honestk, cs)
                           (SignEncrypt k__sign k__enc msg_to msg)
                           (SignedCiphertext c_id, honestk, cs $+ (c_id,c))
  | SafeSign : forall {t} (msg : message t) k msg_to honestk c_id c cs n,
      ~ In c_id cs
      -> c = SigCipher k msg_to n msg
      -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true /\ kp = false)
      -> syntactically_safe (honestk, cs)
                           (Sign k msg_to msg)
                           (SignedCiphertext c_id, honestk, cs $+ (c_id,c))
  | SafeRecv : forall t pat honestk cs c,
      msg_pattern_safe honestk pat
      -> syntactically_safe (honestk, cs) (@Recv t pat) (c, honestk, cs)
  | SafeSend : forall {t} (msg : crypto t) msg_to honestk cs,
        msg_honestly_signed honestk cs msg = true
      -> msg_to_this_user cs (Some msg_to) msg = true
      -> msgCiphersSignedOk honestk cs msg
      -> (exists c_id c, msg = SignedCiphertext c_id
                /\ cs $? c_id = Some c
                (* /\ fst (cipher_nonce c) = (Some u_id)  (* only send my messages *) *)
                (* /\ ~ List.In (cipher_nonce c) sents *)
        )
      -> syntactically_safe (honestk, cs) (Send msg_to msg) (tt, honestk, cs)

  (* Boring Terms *)
  | SafeReturn : forall {A} (a : << A >>) honestk cs,
      syntactically_safe (honestk, cs) (Return a) (a, honestk, cs)
  | SafeGen : forall honestk cs n,
      syntactically_safe (honestk, cs) Gen (n, honestk, cs)
  | SafeDecrypt : forall {t} (c : crypto t) honestk cs msg,
      syntactically_safe (honestk, cs) (Decrypt c) (msg, honestk, cs)
  | SafeVerify : forall {t} k (c : crypto t) honestk cs pr,
      syntactically_safe (honestk, cs) (Verify k c) (pr, honestk, cs)
  | SafeGenerateSymKey : forall usage k_id honestk cs,
      ~ In k_id honestk
      -> syntactically_safe (honestk, cs) (GenerateSymKey usage) ((k_id,true), honestk $+ (k_id,true), cs)
  | SafeGenerateAsymKey : forall usage k_id honestk cs,
      ~ In k_id honestk
      -> syntactically_safe (honestk, cs) (GenerateAsymKey usage) ((k_id,true), honestk $+ (k_id,true), cs)
  .

  Definition U_syntactically_safe {A B} (U : universe A B) :=
    Forall_natmap (fun u =>
                     exists v honk cs,
                       syntactically_safe
                         (findUserKeys U.(users), U.(all_ciphers)) u.(protocol) (v, honk, cs)
                  ) U.(users).


  Lemma syntactically_safe_implies_next_cmd_safe' :
    forall {t} (p : user_cmd t) t1 t2,
      syntactically_safe t1 p t2
      -> forall honestk cs honestk' cs' v u_id froms sents,
        t1 = (honestk, cs)
        -> t2 = (v, honestk', cs')
        -> next_cmd_safe honestk cs u_id froms sents p.
  Proof.
    induction 1; inversion 1; inversion 1; subst;
      try solve [ econstructor; subst; eauto ].

    econstructor; subst; eauto.
    admit. (* Stupid nonce handling *)

  Admitted.

  (*
   * If we can prove that some simple syntactic symbolic execution implies
   * the honest_cmds_safe predicate...
   *)
  Lemma syntactically_safe_implies_next_cmd_safe :
    forall {A B} (U : universe A B),
      U_syntactically_safe U
      -> honest_cmds_safe U.
  Proof.
    unfold U_syntactically_safe, honest_cmds_safe; intros.
    rewrite Forall_natmap_forall in H.
    specialize (H _ _ H1); split_ex; eauto using syntactically_safe_implies_next_cmd_safe'.
  Qed.

  Definition rstepSilent {A B} (U U' : universe A B) :=
    step_universe U Silent U'.

  (*
   * And that the syntactic safety predicate is preserved through any
   * silent real world step 
   *)
  Lemma syntactically_safe_preservation' :
    forall {A B} (U U': universe A B),
      U_syntactically_safe U
      -> rstepSilent U U'
      -> U_syntactically_safe U'.
  Proof.
    unfold U_syntactically_safe; intros.
    rewrite Forall_natmap_forall in *; intros.
    invert H0.
    - specialize (H _ _ H2); split_ex.



      
    - admit.  (* assume adversary cannot step, in lame world! *)

  Admitted.

  Lemma syntactically_safe_preservation :
    forall {A B} (U U': universe A B),
      U_syntactically_safe U
      -> rstepSilent ^* U U'
      -> U_syntactically_safe U'.
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
    ModelCheck.

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
      -> U_syntactically_safe U__r'
      -> RealWorld.step_universe U__r' (Action a__r) U__r''
      -> istepSilent ^* U__i U__i'
      -> IdealWorld.lstep_universe U__i' (Action a__i) U__i''
      -> action_matches a__r U__r' a__i U__i'
      /\ U_syntactically_safe U__r''.
  Proof.
  Admitted.

  (*
   * Now, I want to use all of the above lemmas to prove simulation, essentially converting
   * the whole proof into the above syntactic protocol check, plus some labeled step verification.
   *)
  
End Gen.
