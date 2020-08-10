(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily reflect the views of the
 * Department of the Air Force.
 *
 * © 2020 Massachusetts Institute of Technology.
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
     Classical
     List.

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     MessagesTheory
     Tactics
     Simulation
     RealWorld
     InvariantsTheory
     SafetyAutomation
     SyntacticallySafe
     AdversarySafety.

From protocols Require Import
     ExampleProtocols
     ProtocolAutomation
     SafeProtocol
     RealWorldStepLemmas
.

Set Implicit Arguments.

Import RealWorldNotations.
Import SimulationAutomation.
Import SafetyAutomation.

Section TestProto.

  Notation KID1 := 0.
  Notation KID2 := 1.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEY2  := MkCryptoKey KID2 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1) $+ (KID2, KEY2).

  Definition A__keys := $0 $+ (KID1, true) $+ (KID2, false).
  Definition B__keys := $0 $+ (KID1, false) $+ (KID2, true).

  Definition real_univ_start :=
    mkrU KEYS A__keys B__keys
         (* user A *)
         ( kp <- GenerateAsymKey Encryption
           ; c1 <- Sign KID1 B (Permission (fst kp, false))
           ; _  <- Send B c1
           ; c2 <- @Recv Nat (SignedEncrypted KID2 (fst kp) true)
           ; m  <- Decrypt c2
           ; @Return (Base Nat) (extractContent m) )

         (* user B *)
         ( c1 <- @Recv Access (Signed KID1 true)
           ; v  <- Verify KID1 c1
           ; n  <- Gen
           ; c2 <- SignEncrypt KID2 (fst (extractPermission (snd v))) A (message.Content n)
           ; _  <- Send A c2
           ; @Return (Base Nat) n).
  
End TestProto.

Hint Constructors
     HonestKey
     syntactically_safe
  : core.

Lemma share_secret_synctactically_safe :
  U_syntactically_safe (real_univ_start startAdv).
Proof.
  unfold U_syntactically_safe, real_univ_start, mkrU, mkrUsr, A__keys, B__keys; simpl; 
    intros; subst.

  destruct (u_id ==n A); destruct (u_id ==n B); subst; clean_map_lookups; simpl.

  - eexists.

    econstructor.
    econstructor.

    intros; econstructor; simpl; eauto.
    econstructor; simpl; eauto.

    intros; destruct (fst a ==n k_id); subst; clean_map_lookups; eauto.
    econstructor; simpl; eauto.
    destruct a; simpl; econstructor; eauto.

    econstructor; simpl; eauto.
    econstructor; simpl; eauto.

    intros; econstructor; subst; eauto.
    econstructor; simpl; eauto 8.

  - eexists.

    econstructor.
    econstructor.
    econstructor; eauto.

    intros; econstructor; simpl.
    econstructor; simpl; eauto 8.

    intros; econstructor; simpl.
    econstructor; simpl; eauto.

    intros; econstructor; simpl; eauto.
    econstructor; simpl; simpl.

    eapply HonestKeyFromMsgVerify; eauto.
    intros; econstructor; simpl; eauto 8.
    intros; clean_map_lookups.

    congruence.
    eauto.
Qed.

Definition no_resends (sents : sent_nonces) :=
  NoDup sents.

Definition no_resends_U {A B} (U : universe A B) :=
  Forall_natmap (fun u => no_resends u.(sent_nons)) U.(users).

Lemma no_resends_user_step :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc u_id,
          suid = Some u_id
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> no_resends sents'
          -> no_resends sents.
Proof.
  induction 1; inversion 1; inversion 1; unfold no_resends; intros; subst; eauto.

  - eapply IHstep_user in H25; eauto.
  - unfold updateSentNonce in H33.
    destruct msg; eauto.
    cases (cs' $? c_id); eauto.
    destruct (rec_u_id ==n cipher_to_user c); subst; eauto.
    invert H33; eauto.
Qed.

Lemma resend_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> no_resends_U (fst (fst st'))
    -> no_resends_U (fst (fst st)).
Proof.
  induction 1; unfold no_resends_U; rewrite !Forall_natmap_forall; destruct ru, v; simpl in *; intros.

  - invert H; unfold build_data_step in *; simpl in *; dismiss_adv.
  
    destruct (u_id ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H1 k); rewrite add_eq_o in H1 by trivial.
      specialize (H1 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H1 k); rewrite add_neq_o in H1 by congruence.
      destruct userData; eapply silent_step_nochange_other_user with (u_id2 := k) in H4; eauto.
      clean_map_lookups; simpl in *.
      specialize (H1 _ H4); eauto.

  - invert H; unfold build_data_step in *; simpl in *.
    destruct (uid ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H5 k); rewrite add_eq_o in H5 by trivial.
      specialize (H5 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H5 k); rewrite add_neq_o in H5 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H7; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H5 _ H7); eauto.
      specialize (H5 _ H7); eauto.

  - invert H; unfold build_data_step in *; simpl in *.
    destruct (uid ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H2 k); rewrite add_eq_o in H2 by trivial.
      specialize (H2 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H2 k); rewrite add_neq_o in H2 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H5; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H2 _ H5); eauto.
      specialize (H2 _ H5); eauto.
Qed.

Lemma resend_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ no_resends_U (fst (fst st))
    -> ~ no_resends_U (fst (fst st')).
Proof.
  unfold not; intros.
  eauto using resend_violation_step'.
Qed.

Lemma resend_violation_steps :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) ^* st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> ~ no_resends_U (fst (fst st))
    -> ~ no_resends_U (fst (fst st')).
Proof.
  induction 1; intros; eauto.

  specialize (adversary_remains_lame_step _ _ _ _ _ H1 H); intros.
  destruct x, y, z; simpl in *.

  generalize H; intros VIOL; eapply resend_violation_step in VIOL; eauto.
Qed.
