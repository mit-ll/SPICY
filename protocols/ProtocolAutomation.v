From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Require Import Common Maps Keys Simulation MapLtac Tactics Automation AdversaryUniverse.

Require IdealWorld RealWorld.

Set Implicit Arguments.

Section RealWorldLemmas.
  Import RealWorld.

  Lemma multiStepSilentInv :
    forall {A B} (U__r U__r': universe A B) b,
        rstepSilent ^* U__r U__r'
      -> U__r.(adversary).(protocol) = Return b
      -> U__r = U__r'
      \/ exists usrs adv cs u_id userData gks ks cmd qmsgs mycs,
            rstepSilent ^* (buildUniverse usrs adv cs gks u_id {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}) U__r'
          /\ users U__r $? u_id = Some userData
          /\ step_user Silent (Some u_id) (RealWorld.build_data_step U__r userData) (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd).
  Proof.
    intros.
    invert H; intuition idtac.
    right. invert H1.
    - repeat eexists; intuition; eauto.
    - exfalso.
      destruct U__r; destruct adversary; simpl in *; subst.
      unfold build_data_step in H; simpl in *.
      invert H.
  Qed.

End RealWorldLemmas.

Ltac equality1 :=
  match goal with
  | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition idtac

  | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
  | [ H : _  $? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : add _ _ _ $? _ = Some ?UD |- _ ] =>
    match type of UD with
    | RealWorld.user_data bool => apply lookup_some_implies_in in H
    | _ => apply lookup_split in H; intuition idtac
    end

  | [ H : _ = {| RealWorld.users := _ ; RealWorld.adversary := _ ; RealWorld.all_ciphers := _ ; RealWorld.all_keys := _ |} |- _ ]
    => inversion H; clear H; subst
  | [ |- RealWorld.protocol (RealWorld.adversary _) = RealWorld.Return _ ] => simpl
  | [ H : lameAdv _ ?adv |- RealWorld.protocol ?adv = _ ] => unfold lameAdv in H; eassumption

  | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => inversion H; clear H
  | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
  | [ H : (_ :: _) = _ |- _ ] => inversion H; clear H
  | [ H : _ = (_ :: _) |- _ ] => inversion H; clear H
  | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H
  | [ H : Action _ = Action _ |- _ ] => inversion H; clear H
  | [ H : RealWorld.Return _ = RealWorld.Return _ |- _ ] => inversion H; clear H
  | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => apply inj_pair2 in H

  | [ H: RealWorld.SigCipher _ _ = RealWorld.SigCipher _ _ |- _ ] => invert H
  | [ H: RealWorld.SigEncCipher _ _ _ = RealWorld.SigEncCipher _ _ _ |- _ ] => invert H
  | [ H: MkCryptoKey _ _ _ = _ |- _ ] => invert H

  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H

  | [ H : keyId _ = _ |- _] => inversion H; clear H
  end.

Module SimulationAutomation.

  Hint Constructors RealWorld.msg_accepted_by_pattern.

  Section InversionPrinciples.
    Import RealWorld.

    (* :flag Keep Proof Equalities. *)

    (* Derive Inversion_clear some_inv with (forall (s1 s2 : Type), Some s1 = Some s2) Sort Prop. *)

    (* Derive Inversion_clear step_user_inv_gen with *)
    (*     (forall (A B : Type) (lbl : rlabel) (u_id : option user_id) (usrs usrs' : honest_users A) *)
    (*        (adv adv' : user_data B) (cs cs' : ciphers) (gks gks' : keys) (ks ks': key_perms) *)
    (*        (qmsgs qmsgs' : queued_messages) (mycs mycs' : my_ciphers) (cmd' : user_cmd nat), *)
    (*         step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Gen) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')) *)
    (*     Sort Prop. *)
    (* Check step_user_inv_gen. *)
    (* Check some_inv. *)

    (* Derive Inversion_clear step_user_inv_bind with *)
    (*     (forall (A B C C': Type) (lbl : rlabel) (u_id : option user_id) (usrs usrs' : honest_users A) *)
    (*        (adv adv' : user_data B) (cs cs' : ciphers) (gks gks' : keys) (ks ks': key_perms) *)
    (*        (qmsgs qmsgs' : queued_messages) (mycs mycs' : my_ciphers) (cmd1 cmd1' : user_cmd C) (cmd : C -> user_cmd C'), *)
    (*         step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind cmd1 cmd) (usrs', adv', cs', gks', ks', qmsgs', mycs', Bind cmd1' cmd)) *)
    (*     Sort Prop. *)

    Lemma step_user_inv_gen :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
          step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Gen) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ lbl = Silent
        /\ exists n, cmd = Return n.
    Proof.
      intros.
      inversion H; repeat equality1; subst; intuition idtac; eauto.
    Qed.

    Lemma step_user_inv_bind :
      forall {A B C C'} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd1 : user_cmd C) (cmd : C -> user_cmd C') (cmd' : user_cmd C'),
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind cmd1 cmd) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
        -> (exists cmd1',
              step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd1) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd1')
            /\ cmd' = Bind cmd1' cmd
          )
        \/ ( usrs = usrs'
          /\ adv = adv'
          /\ cs = cs'
          /\ gks = gks'
          /\ ks = ks'
          /\ qmsgs = qmsgs'
          /\ mycs = mycs'
          /\ lbl = Silent
          /\ exists c, cmd1 = Return c
               /\ cmd' = cmd c).
    Proof.
      intros.
      invert H; intuition eauto.
    Qed.

    Lemma step_user_inv_recv :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd : user_cmd (message t)) pat,
          step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Recv pat) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ exists msg msgs,
            qmsgs = (existT message t msg) :: msgs
          /\ qmsgs' = msgs
          /\ ( ( msg_accepted_by_pattern pat msg
              /\ ks' = ks $k++ findKeys msg
              /\ mycs' = findCiphers msg ++ mycs
              /\ lbl = Action (Input msg pat ks)
              /\ cmd = Return msg)
            \/ ( ~ msg_accepted_by_pattern pat msg
              /\ ks = ks'
              /\ mycs = mycs'
              /\ lbl = Silent
              /\ cmd = Recv pat
              )).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; intuition eauto.
    Qed.

    Lemma step_user_inv_send :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) (msg : message t)
        lbl u_id rec_u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl (Some u_id) (usrs, adv, cs, gks, ks, qmsgs, mycs, Send rec_u_id msg) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ adv' = addUserKeys (findKeys msg) adv
        /\ rec_u_id <> u_id
        /\ lbl = Action (Output msg)
        /\ cmd = Return tt
        /\ exists rec_u,
            usrs $? rec_u_id = Some rec_u
          /\ usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                        ; protocol := rec_u.(protocol)
                                        ; msg_heap := rec_u.(msg_heap) ++ [existT _ _ msg]
                                        ; c_heap   := rec_u.(c_heap) |}).
    Proof.
      intros.
      invert H; intuition idtac.
      eexists; eauto.
    Qed.

    Lemma step_user_inv_enc :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign k__enc (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, SignEncrypt k__sign k__enc msg) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ keys_mine ks (findKeys msg)
        /\ incl (findCiphers msg) mycs
        /\ (exists kt__enc kt__sign kp__enc,
                gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
              /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__enc   = Some kp__enc
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigEncCipher k__sign k__enc msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (SignedCiphertext k__sign k__enc c_id)).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_dec :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign k__enc c_id
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd : user_cmd (message t)),
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Decrypt (SignedCiphertext k__sign k__enc c_id))
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ List.In c_id mycs
        /\ exists (msg : message t) kt__enc kt__sign kp__sign,
            cs $? c_id     = Some (SigEncCipher k__sign k__enc msg)
          /\ gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__enc  = Some true
          /\ ks  $? k__sign = Some kp__sign
          /\ ks' = ks $k++ findKeys msg
          /\ mycs' = findCiphers msg ++ mycs
          /\ cmd = Return msg.
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_sign :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Sign k__sign msg)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ (exists kt__sign,
                gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigCipher k__sign msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (Signature msg k__sign c_id)).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_verify :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign c_id (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Verify k__sign (Signature msg k__sign c_id))
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ lbl = Silent
        /\ cmd = Return true
        /\ List.In c_id mycs
        /\ exists (msg : message t) kt__sign kp__sign,
            cs $? c_id     = Some (SigCipher k__sign msg)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__sign = Some kp__sign.
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma adv_no_step :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) b
        lbl cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        lameAdv b adv
        -> step_user lbl None (usrs, adv, cs, gks, ks, qmsgs, mycs, protocol adv)
                    (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> False.
    Proof.
      unfold lameAdv; destruct adv; simpl; intros;
        match goal with
        | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,?prot) _
          , LAME : ?prot = _ |- _ ] => rewrite LAME in STEP; invert STEP
        end.
    Qed.

  End InversionPrinciples.

  Module T.
    Import RealWorld.

    Ltac churn1 :=
      match goal with

      | [ H : ~ RealWorld.msg_accepted_by_pattern ?pat ?msg |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern pat msg ) by constructor; contradiction

      | [ H : RealWorld.msg_accepted_by_pattern ?pat ?msg -> False |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern pat msg ) by constructor; contradiction

      (* Only take a user step if we have chosen a user *)
      | [ H : RealWorld.step_user _ (Some ?u) _ _ |- _ ] => progress simpl in H
      | [ H : RealWorld.step_user _ (Some ?u) (_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u;
        match cmd with
        | Return _ => invert H
        | Bind _ _ => apply step_user_inv_bind in H; split_ands; split_ors; split_ands; subst; try discriminate
        | Gen => apply step_user_inv_gen in H
        | Send _ _ => apply step_user_inv_send in H
        | Recv _ => apply step_user_inv_recv in H
        | SignEncrypt _ _ _ => apply step_user_inv_enc in H
        | Decrypt _ => apply step_user_inv_dec in H
        | Sign _ _ => apply step_user_inv_sign in H
        | Verify _ _ => apply step_user_inv_verify in H
        | _ => idtac cmd; intuition idtac; subst; (progress (simpl in H) || invert H)
        end

      | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,RealWorld.protocol ?adv) _
        , LAME : lameAdv _ ?adv |- _ ] => pose proof (adv_no_step LAME STEP); contradiction

      | [ H : RealWorld.step_user _ _ (build_data_step _ _) _ |- _ ] => unfold build_data_step in H; simpl in H

      | [ H :rstepSilent ^* (RealWorld.buildUniverse _ _ _ _ _ _) _ |- _] =>
        unfold RealWorld.buildUniverse in H; autorewrite with simpl_univ in H
      | [ |- context [RealWorld.buildUniverse _ _ _ _ _ _] ] =>
        unfold RealWorld.buildUniverse

      | [ S: rstepSilent ^* ?U _ |- _ ] => 
        (* Don't actually multiStep unless we know the state of the starting universe
         * meaning it is not some unknown hypothesis in the context...
         *)
        is_not_var U; eapply multiStepSilentInv in S; split_ors; split_ex; intuition idtac; subst

      | [ H: rstepSilent ?U _ |- _ ] => is_not_var U; invert H
      | [ H: RealWorld.step_universe _ _ _ |- _ ] => invert H

      end.

  End T.

  Import T.
  Export T.

  Ltac churn2 :=
    (repeat equality1); subst; churn1; intuition idtac; split_ex; intuition idtac; subst; try discriminate.

  Ltac churn :=
    repeat churn2.

  Ltac i_single_silent_step :=
      eapply IdealWorld.LStepBindProceed
    || eapply IdealWorld.LStepGen
    || eapply IdealWorld.LStepCreateChannel
  .

  Ltac r_single_silent_step :=
      eapply RealWorld.StepBindProceed
    || eapply RealWorld.StepGen
    (* || eapply RealWorld.StepRecvDrop *)
    || eapply RealWorld.StepEncrypt
    || eapply RealWorld.StepDecrypt
    || eapply RealWorld.StepSign
    || eapply RealWorld.StepVerify
  .

  Ltac pick_user uid :=
    match goal with
    | [ |- _ $? ?euid = Some _ ] => unify euid uid
    end; clean_map_lookups; trivial.

  Ltac istep_univ uid :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..];
      (try eapply @eq_refl); (try f_equal); simpl.
  Ltac rstep_univ uid :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick_user uid | ..]; (try eapply @eq_refl); simpl.

  Ltac isilent_step_univ uid :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
      ((eapply IdealWorld.LStepBindRecur; i_single_silent_step) || i_single_silent_step).
  Ltac rsilent_step_univ uid :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
      ((eapply RealWorld.StepBindRecur; r_single_silent_step) || r_single_silent_step).

  Ltac single_silent_multistep usr_step := eapply TrcFront; [usr_step |]; simpl.

  Ltac real_single_silent_multistep uid := single_silent_multistep ltac:(rsilent_step_univ uid).
  Ltac ideal_single_silent_multistep uid := single_silent_multistep ltac:(isilent_step_univ uid).

  Ltac figure_out_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        does_not_unify usr1 usr2; step_tac u
      end
    end.

  Remove Hints TrcRefl TrcFront.
  Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl.

  Remove Hints eq_sym (* includes_lookup *).
  Remove Hints trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat.

  Hint Constructors action_matches msg_eq.
  Hint Resolve IdealWorld.LStepSend' IdealWorld.LStepRecv'.

  Lemma TrcRefl' :
    forall {A} (R : A -> A -> Prop) x1 x2,
      x1 = x2 ->
      trc R x1 x2.
  Proof.
    intros. subst. apply TrcRefl.
  Qed.

  Ltac solve_refl :=
    solve [
        eapply TrcRefl
      | eapply TrcRefl'; simpl; smash_universe ].

  Ltac simpl_real_users_context :=
    repeat
      match goal with
      | [ |- context [ RealWorld.buildUniverse ] ] => progress (unfold RealWorld.buildUniverse; simpl)
      | [ |- context [ RealWorld.mkUniverse ?usrs _ _ _] ] => canonicalize_map usrs
      end.

  Ltac simpl_ideal_users_context :=
    repeat
      match goal with
      | [ |- context [ IdealWorld.construct_universe _ ?usrs] ] => canonicalize_map usrs
      end.

  Ltac rss_clean uid := real_single_silent_multistep uid; [ solve [eauto 2] .. |].

  Ltac real_silent_multistep :=
    simpl_real_users_context;
    match goal with
    | [ |- rstepSilent ^* ?U1 ?U2 ] =>
      first [
          solve_refl
        | figure_out_user_step rss_clean U1 U2 ]
    end.

  Ltac ideal_silent_multistep :=
    simpl_ideal_users_context;
    match goal with
    | [ |- istepSilent ^* ?U1 ?U2 ] =>
      first [
          solve_refl
        | figure_out_user_step ideal_single_silent_multistep U1 U2 ]
    end.

  Ltac single_step_ideal_universe :=
    simpl_ideal_users_context;
    match goal with
    | [ |- IdealWorld.lstep_universe ?U1 _ ?U2] =>
      match U1 with
      | IdealWorld.construct_universe _ ?usrs1 =>
        match U2 with
        | IdealWorld.construct_universe _ ?usrs2 =>
          figure_out_user_step istep_univ usrs1 usrs2
        end
      end
    end.

  Hint Extern 1 (rstepSilent ^* _ _) => real_silent_multistep.
  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_multistep.
  Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe.

  Hint Extern 1 (List.In _ _) => progress simpl.

  Hint Extern 1 (RealWorld.action_adversary_safe _ _ _ = _) => unfold RealWorld.action_adversary_safe; simplify.
  Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.

  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl.
  Hint Extern 1 (add _ _ _ = _) => m_equal.
  Hint Extern 1 (find _ _ = _) => m_equal.
  Hint Extern 1 (_ \in _) => sets.

End SimulationAutomation.

Import SimulationAutomation.

Section UniverseStep.
  Import RealWorld.

  Definition rewrite_messages {A} (usr : user_data A) (qmsgs : queued_messages) :=
    {| key_heap := usr.(key_heap)
     ; protocol := usr.(protocol)
     ; msg_heap := qmsgs
     ; c_heap   := usr.(c_heap)
    |}.

  Lemma invert_users :
    forall {A} (usrs__ra usrs__r : honest_users A) u_id u,
        usrs__r = clean_users (findUserKeys usrs__ra) usrs__ra
      -> usrs__ra $? u_id = Some u
      -> exists msgs u', usrs__r $? u_id = Some u'
                 /\ u = rewrite_messages u' msgs
                 /\ Forall (fun m => msg_filter (findUserKeys usrs__ra) m = false \/ List.In m u'.(msg_heap)) msgs.
  Proof.
    intros.
    subst; destruct u; simpl in *.
    repeat eexists.
    eapply clean_users_cleans_user; eauto.
    unfold rewrite_messages; simpl; reflexivity.
    rewrite Forall_forall; intros.
    cases (msg_filter (findUserKeys usrs__ra) x); auto.
    right; simpl.
    unfold clean_messages; rewrite filter_In; auto.
  Qed.

  (* Lemma might_as_well_step_til_done : *)
  (*   forall {A B} (U__ra U__ra' U__r U__r' : universe A B) act b, *)
  (*     (rstepSilent U__r U__r' -> False) *)
  (*     -> U__r = strip_adversary_univ U__ra b *)
  (*     -> step_universe U__ra (Action act) U__ra' *)
  (*     -> action_adversary_safe (findUserKeys U__ra.(users)) U__ra.(all_ciphers) act *)
  (*     -> forall U__ra0 U__r0, *)
  (*         rstepSilent ^* U__r0 U__r *)
  (*         -> U__r0 = strip_adversary_univ U__ra0 b *)
  (*         -> action_adversary_safe (findUserKeys U__ra0.(users)) U__ra0.(all_ciphers) act. *)
  (* Proof. *)
  (*   intros. *)

  (* Admitted. *)

End UniverseStep.

Ltac solve_adv_safe :=
  repeat
    match goal with
    | [ |- RealWorld.action_adversary_safe _ _ _] => unfold RealWorld.action_adversary_safe
    | [ |- RealWorld.msg_pattern_safe _ _ ] => econstructor
    | [ |- RealWorld.honest_key _ _ ] => econstructor
    | [ |- RealWorld.honest_keyb _ _ = true ] => rewrite <- RealWorld.honest_key_honest_keyb
    | [ H : RealWorld.findUserKeys ?usrs = _ |- RealWorld.findUserKeys ?usrs $? _ = Some _ ] => rewrite H
    | [ H : _ = clean_users ?honestk ?usrs |- context [ clean_users ?honestk ?usrs ] ] => rewrite <- H
    | [ |- RealWorld.msg_contains_only_honest_public_keys _ _ ] => econstructor
    | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
    | [ |- RealWorld.msgCipherOk _ _ _ ] => unfold RealWorld.msgCipherOk
    | [ |- RealWorld.msg_honestly_signed _ _ = true] => unfold RealWorld.msg_honestly_signed
    | [ |- _ /\ _ ] => split
    | [ H : _ = clean_ciphers ?honk ?cs |- ?cs $? ?cid = Some ?c ] =>
      assert (clean_ciphers honk cs $? cid = Some c) by (rewrite <- H; clean_map_lookups; trivial); clear H
    | [ H : clean_ciphers _ ?cs $? ?cid = Some ?c |- ?cs $? ?cid = Some ?c ] =>
      rewrite <- find_mapsto_iff in H; rewrite clean_ciphers_mapsto_iff in H; split_ands;
      rewrite <- find_mapsto_iff; assumption
    end.

Ltac users_inversion :=
  match goal with
  | [ H : ?usrs $? _ = Some ?u
    , E : _ = clean_users _ _
      |- _ ] =>
    generalize (invert_users _ E H); intros
  end; split_ex; split_ands; subst; simpl in *.

Ltac solve_uok :=
  try match goal with
      | [ |- universe_ok (RealWorld.buildUniverseAdv _ _ _ _ ) ] => solve [ eapply universe_ok_adv_step; eauto ]
      end;
  users_inversion; churn; repeat equality1;
  unfold universe_ok in *;
  simpl;
  autorewrite with find_user_keys;
  try assumption; simpl in *;
  repeat
    match goal with
    | [ H : Forall _ (existT _ _ _ :: _) |- encrypted_ciphers_ok _ _ ] =>
      invert H; split_ors; try contradiction
    | [ H : RealWorld.msg_accepted_by_pattern (RealWorld.Signed _) _ |- _ ] => invert H; simpl in *
    | [ H : RealWorld.honest_keyb ?findUsers _ = false |- _ ] => unfold RealWorld.honest_keyb in H
    | [ H : ?cusrs = clean_users (RealWorld.findUserKeys ?usrs) ?usrs |- _ ] =>
      assert (RealWorld.findUserKeys usrs = RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys usrs) usrs))
        as UKS by (symmetry; eapply clean_users_no_change_findUserKeys);
      rewrite <- H in UKS;
      clear H
    | [ M : match RealWorld.findUserKeys ?usrs $? _ with _ => _ end = _
            , H : RealWorld.findUserKeys ?usrs = _ |- _ ] => rewrite H in M; clear H; simpl in M; try discriminate
    | [ H : RealWorld.Signature _ _ _ = RealWorld.Signature _ _ _ |- _ ] => invert H
    | [ |- encrypted_ciphers_ok _ _ ] => econstructor
    | [ |- encrypted_cipher_ok _ _ _ ] => econstructor
    | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
    | [ |- forall k, RealWorld.findKeys _ $? _ = Some true -> False ] => intros
    | [ H : RealWorld.findKeys _ $? _ = Some true |- False ] => progress simpl in H; invert H
    | [ |- RealWorld.findUserKeys _ $? _ = Some true ] => eapply RealWorld.findUserKeys_has_private_key_of_user
    end.

Hint Resolve encrypted_ciphers_ok_addnl_cipher.

Hint Resolve
     RealWorld.findUserKeys_foldfn_proper
     RealWorld.findUserKeys_foldfn_transpose
     RealWorld.findUserKeys_foldfn_proper_Equal
     RealWorld.findUserKeys_foldfn_transpose_Equal.
