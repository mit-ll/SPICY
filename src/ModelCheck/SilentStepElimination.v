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
     Morphisms
     JMeq
     List
     Lia.

From SPICY Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     Theory.KeysTheory
     Messages
     MessageEq
     Theory.MessageEqTheory
     Tactics
     Simulation
     RealWorld
     Theory.InvariantsTheory
     AdversaryUniverse
     AdversarySafety
     SafetyAutomation
     SyntacticallySafe
     Theory.UsersTheory

     ModelCheck.RealWorldStepLemmas
     ModelCheck.ModelCheck
     ModelCheck.ProtocolFunctions
     ModelCheck.SafeProtocol
     ModelCheck.LabelsAlign
     ModelCheck.NoResends
     ModelCheck.PartialOrderReduction
.

From Frap Require
     Sets.

From SPICY Require
     IdealWorld.

Import SafetyAutomation.

(* For later import of set notations inside sections *)
Module Foo <: Sets.EMPTY.
End Foo.
Module SN := Sets.SetNotations(Foo).

Set Implicit Arguments.

Section NextSteps.

  Inductive nextStepSS {A B} (u_id : user_id) (userData : user_data A)
    : universe A B (* -> universe A B *) -> Prop :=

  | NextSilent : forall U U',
      U.(users) $? u_id = Some userData
      -> indexedRealStep u_id Silent U U'
      -> (forall uid' U', uid' > u_id -> ~ indexedRealStep uid' Silent U U')
      -> nextStepSS u_id userData U

  | NoSilents : forall U U' a,
      U.(users) $? u_id = Some userData

      (* No one can silently step *)
      -> (forall uid' U', ~ indexedRealStep uid' Silent U U')

      -> indexedRealStep u_id (Action a) U U'
      -> nextStepSS u_id userData U.

  Inductive stepSS (t__hon t__adv : type) :
      @ModelState t__hon t__adv
    -> @ModelState t__hon t__adv
    -> Prop :=

  | StepNextSS : forall ru ru' iu iu' u_id ud st st' v v',
      nextStepSS u_id ud ru
      -> st = (ru,iu,v)
      -> st' = (ru',iu',v')
      -> indexedModelStep u_id st st'
      -> stepSS st st'.

End NextSteps.

(* Load the set notations *)
Import SN.

Definition TrSS {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) :=
  {| Initial := {(ru0, iu0, true)};
     Step    := @stepSS t__hon t__adv |}.

Hint Resolve adversary_remains_lame_step : core.
Hint Constructors stepSS nextStepSS : core.

Hint Resolve indexedIdealSteps_ideal_steps : core.
Hint Constructors indexedModelStep indexedIdealStep indexedRealStep : core.
Hint Resolve action_matches_other_user_silent_step_inv : core.


Lemma step_then_step' :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) uid1 ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid1
      -> usrs $? uid1 = Some {| key_heap := ks;
                               protocol := cmdc;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> message_queues_ok cs usrs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> forall usrs'' (adv'' : user_data B) cs'' gks'' ms,
          usrs'' $? uid1 = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs ++ ms;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> (forall uid u, usrs $? uid = Some u -> exists u', usrs'' $? uid = Some u')
          -> (forall cid c, cs $? cid = Some c -> cs'' $? cid = Some c)
          -> (forall cid c, cs'' $? cid = Some c -> cs $? cid = Some c \/ cs $? cid = None)
          -> (forall kid k, gks $? kid = Some k -> gks'' $? kid = Some k)
          -> exists bd'',
              step_user lbl suid
                        (usrs'', adv'', cs'', gks'', ks, qmsgs ++ ms, mycs, froms, sents, cur_n, cmd)
                        bd''.
Proof.
  induction 1; inversion 1; inversion 1
  ; intros
  ; subst
  ; try solve [ eexists; econstructor; eauto ]
  ; clean_context.

  - eapply IHstep_user in H26; eauto.
    split_ex.
    dt x; eexists; econstructor; eauto.

  - rewrite <- app_assoc,
            <- app_comm_cons.
    eexists; econstructor; eauto.
    invert H6;
      [ econstructor 1
      | econstructor 2
      | econstructor 3
      ]; eauto.

    rewrite Forall_forall in H7|- *
    ; intros.

    generalize (H7 _ H)
    ; intros
    ; destruct x
    ; eauto.

    unfold not
    ; intros MAP
    ; apply H0.

    msg_queue_prop.
    apply List.Forall_app in H2
    ; split_ex
    ; rewrite Forall_forall in H2
    ; apply H2 in H
    ; split_ex.

    invert MAP;
      [ econstructor 1
      | econstructor 2
      | econstructor 3
      ]
      ; eauto
      ; specialize (H8 _ eq_refl).

    apply H39 in H11; split_ors; clean_map_lookups; eauto.
    apply H39 in H11; split_ors; clean_map_lookups; eauto.

  - apply H36 in H2; split_ex; eauto.
    eexists; econstructor; eauto.
    unfold keys_mine in H0 |- *; intros.
    apply H0.
    unfold findKeysCrypto in H2 |- *.
    destruct msg; eauto.
    assert (List.In c_id mycs') by eauto.
    user_cipher_queues_prop.
    generalize (H37 _ _  H5); intros; context_map_rewrites; trivial.
    
  - eexists.
    eapply StepEncrypt with (c_id0 := next_key cs''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.

  - eexists.
    eapply StepSign with (c_id0 := next_key cs''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.

  - eexists.
    eapply StepGenerateKey with (k_id0 := next_key gks''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.
    Unshelve.
    auto.
Qed.

Lemma step_then_silent_step :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) uid1 ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid1
      -> usrs $? uid1 = Some {| key_heap := ks;
                               protocol := cmdc;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      (* -> forall ctx styp, syntactically_safe uid1 (compute_ids usrs) ctx cmd styp *)
      (* -> typingcontext_sound ctx usrs cs uid1 *)
      -> message_queues_ok cs usrs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> forall uid2 bd2 bd2',
          step_user Silent (Some uid2) bd2 bd2'

          -> forall cmd2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 usrs'' cmdc' ud2,

            uid1 <> uid2
            -> usrs $? uid2 = Some ud2
            -> bd2 = build_data_step (mkUniverse usrs adv cs gks) ud2
            -> usrs' $? uid2 = Some {| key_heap := ks2;
                                      protocol := cmd2;
                                      msg_heap := qmsgs2;
                                      c_heap   := mycs2;
                                      from_nons := froms2;
                                      sent_nons := sents2;
                                      cur_nonce := cur_n2 |}
            -> usrs'' = usrs' $+ (uid1, {| key_heap := ks';
                                          protocol := cmdc';
                                          msg_heap := qmsgs';
                                          c_heap   := mycs';
                                          from_nons := froms';
                                          sent_nons := sents';
                                          cur_nonce := cur_n' |})
            -> exists bd2'',
                step_user Silent (Some uid2)
                          (usrs'', adv', cs', gks', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                          bd2''
.
Proof.

  Ltac ss :=
    clean_map_lookups
    ; unfold build_data_step in *
    ; simpl in *
    ; eauto
    ; match goal with
      | [ H : step_user Silent (Some ?uid) _ ?bd
          |- exists _, step_user _ (Some ?uid) (?us,_,?cs,?gks,_,_,_,_,_,_,_) _ ] =>
        dt bd
        ; eapply step_then_step' with (ms := []) (usrs'' := us) (cs'' := cs) (gks'' := gks) in H
      end
    ; eauto
    ; try rewrite app_nil_r in *
    ; eauto
    ; try
        match goal with
        | [ |- forall _ _, ?usrs $? _ = Some _ -> exists _, ?usrs $+ (?uid,_) $? _ = Some _ ] =>
          let UID := fresh "UID"
          in intros UID *; destruct (UID ==n uid); subst; eexists; clean_map_lookups; eauto
        end.

  induction 1; inversion 1; inversion 1; intros; subst
  ; try solve [ ss ]; clean_context.

  - destruct (rec_u_id ==n uid2); subst; clean_map_lookups.
    + destruct ud2
      ; clean_map_lookups
      ; unfold build_data_step in *
      ; simpl in *
      ; eauto
      ; match goal with
        | [ H : step_user Silent (Some ?uid) _ ?bd
            |- exists _, step_user _ (Some ?uid) (?us,_,?cs,?gks,_,_,_,_,_,_,_) _ ] =>
          dt bd
          ; eapply step_then_step' with (ms := [existT _ _ msg]) (usrs'' := us) (cs'' := cs) (gks'' := gks) in H
        end
      ; eauto
      ; try rewrite app_nil_r in *
      ; eauto
      ; try
          match goal with
          | [ |- forall _ _, ?usrs $? _ = Some _ -> exists _, ?usrs $+ (?uid,_) $? _ = Some _ ] =>
            let UID := fresh "UID"
            in intros UID *; destruct (UID ==n uid); subst; eexists; clean_map_lookups; eauto
          end.

      intros.
      destruct (uid ==n uid1); destruct (uid ==n uid2); subst; eexists; clean_map_lookups; eauto.

    + ss.
      intros.
      destruct (uid ==n uid1); destruct (uid ==n rec_u_id); subst; eexists; clean_map_lookups; eauto.

  - unfold build_data_step in *
    ; clean_map_lookups
    ; simpl in *.
    
    match goal with
    | [ H : step_user Silent (Some ?uid) _ ?bd
        |- exists _, step_user _ (Some ?uid) (?us,_,?cs,?gks,_,_,_,_,_,_,_) _ ] =>
      dt bd
      ; eapply step_then_step' with (ms := []) (usrs'' := us) (cs'' := cs) (gks'' := gks) in H
    end
    ; try rewrite app_nil_r in *
    ; split_ex; eauto.

    intros.
    destruct (uid ==n uid1); destruct (uid ==n uid2); subst; eexists; clean_map_lookups; eauto.

    intros.
    destruct (c_id ==n cid); subst; clean_map_lookups; eauto.

  - unfold build_data_step in *
    ; clean_map_lookups
    ; simpl in *.
    
    match goal with
    | [ H : step_user Silent (Some ?uid) _ ?bd
        |- exists _, step_user _ (Some ?uid) (?us,_,?cs,?gks,_,_,_,_,_,_,_) _ ] =>
      dt bd
      ; eapply step_then_step' with (ms := []) (usrs'' := us) (cs'' := cs) (gks'' := gks) in H
    end
    ; try rewrite app_nil_r in *
    ; split_ex; eauto.

    intros.
    destruct (uid ==n uid1); destruct (uid ==n uid2); subst; eexists; clean_map_lookups; eauto.

    intros.
    destruct (c_id ==n cid); subst; clean_map_lookups; eauto.

    Unshelve.
    all: eauto.
Qed.

Lemma step_limited_change_other_user_qmsgs :
  forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
    (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs'
    froms froms' sents sents' cur_n cur_n' uid uid' lbl
    ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1,

    usrs $? uid = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
    -> uid <> uid'
    -> usrs $? uid' = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> step_user lbl (Some uid')
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
    -> exists qmsgs1',
        (usrs' $+ (uid', mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n')) $? uid
        = Some (mkUserData ks1 cmd1 qmsgs1' mycs1 froms1 sents1 cur_n1)
        /\ (qmsgs1' = qmsgs1 \/ exists m, qmsgs1' = qmsgs1 ++ [m])
.
Proof.
  intros.
  specialize (user_step_adds_no_users H2 eq_refl eq_refl); intros.
  generalize H2; intros STEP.
  eapply step_limited_change_other_user with (u_id2 := uid) in STEP; eauto; split_ex.
  
  split_ors; split_ex; eauto.
Qed.

Definition useless_summary : summary :=
  {| sending_to := Sets.scomp (fun (n : nat) => True) |}.  

Lemma useless_summary_summarizes :
  forall t cmd,
    @summarize t cmd useless_summary.
Proof.
  induction cmd; econstructor; eauto; simpl.
  unfold Sets.scomp, Sets.In; simpl; trivial.
Qed.

Lemma silent_step_na_commuting :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall s,
          exists t cmd__n,
            @nextAction _ t cmd cmd__n
            /\ commutes cmd__n s.
Proof.
  Hint Constructors nextAction : core.
  induction 1; inversion 1; inversion 1; intros; subst; simpl; try discriminate
  ; try solve [ (do 2 eexists); split; eauto; simpl; trivial ].

  specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl s)
  ; split_ex
  ; (do 2 eexists)
  ; split
  ; [ econstructor |]
  ; eauto.
Qed.

Lemma step_didnt_appear :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) uid1 ks ks' qmsgs qmsgs' mycs mycs' ms
        froms froms' sents sents' cur_n cur_n' cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs ++ ms, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid1
      -> lbl = Silent
      -> usrs $? uid1 = Some {| key_heap := ks;
                               protocol := cmdc;
                               msg_heap := qmsgs ++ ms;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> forall usrs'' (adv'' : user_data B) cs'' gks'',
          usrs'' $? uid1 = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> forall ctx styp, syntactically_safe uid1 (compute_ids usrs'') ctx cmd styp
          -> typingcontext_sound ctx usrs'' cs'' uid1
          -> keys_and_permissions_good gks'' usrs'' adv''.(key_heap)
          -> user_cipher_queues_ok cs'' (findUserKeys usrs'') usrs''
          -> (forall uid u, usrs'' $? uid = Some u -> exists u', usrs $? uid = Some u')
          -> (forall cid c, cs'' $? cid = Some c -> cs $? cid = Some c)
          -> (forall cid c, cs $? cid = Some c -> cs'' $? cid = Some c \/ cs'' $? cid = None)
          -> (forall kid k, gks'' $? kid = Some k -> gks $? kid = Some k)
          -> exists bd'',
              step_user Silent suid
                        (usrs'', adv'', cs'', gks'', ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                        bd''.
Proof.
  induction 1; inversion 1; inversion 1
  ; intros
  ; subst
  ; try discriminate
  ; try solve [ eexists; econstructor; eauto ]
  ; clean_context.

  - invert H28.
    eapply IHstep_user in H27; eauto.
    split_ex.
    dt x; eexists; econstructor; eauto.

  - unfold typingcontext_sound in *
    ; split_ex
    ; invert H38
    ; process_ctx.
    keys_and_permissions_prop.

    generalize (H13 _ _ H9)
    ; generalize (H13 _ _ H10)
    ; intros; split_ex.

    generalize (H45 _ _ H19)
    ; generalize (H45 _ _ H20)
    ; intros
    ; clean_map_lookups.
    
    eapply StepEncrypt with (c_id0 := next_key cs''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.

  - eexists.
    assert (List.In c_id mycs'0) by eauto.
    user_cipher_queues_prop.
    eapply H42 in H; split_ors; clean_map_lookups; eauto.
    keys_and_permissions_prop.

    generalize (H11 _ _ H2)
    ; generalize (H11 _ _ H3)
    ; intros
    ; clean_map_lookups
    ; clear H11.
    
    generalize (H43 _ _ H12)
    ; generalize (H43 _ _ H13)
    ; intros
    ; clean_map_lookups
    ; clear H43.
    
    econstructor; eauto.
    
  - keys_and_permissions_prop.

    generalize (H8 _ _ H0)
    ; intros
    ; clean_map_lookups.

    generalize (H43 _ _ H9)
    ; intros
    ; clean_map_lookups.

    eexists.
    eapply StepSign with (c_id0 := next_key cs''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.

  - keys_and_permissions_prop.
    
    generalize (H7 _ _ H0)
    ; intros
    ; clean_map_lookups.

    generalize (H38 _ _ H8)
    ; intros
    ; clean_map_lookups.

    assert (List.In c_id mycs') by eauto.
    user_cipher_queues_prop.
    eapply H37 in H1; split_ors; clean_map_lookups; eauto.

    eexists. 
    econstructor; eauto.

  - eexists.
    
    eapply StepGenerateKey with (k_id0 := next_key gks''); clean_map_lookups; eauto.
    eapply next_key_not_in; eauto.

    Unshelve.
    auto.
Qed.

Lemma step_then_silent_step_inv :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) uid1 ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid1
      -> usrs $? uid1 = Some {| key_heap := ks;
                               protocol := cmdc;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}

      -> forall uid2 bd2 bd2' cmd2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 usrs'' cmdc' ud2,

          step_user Silent (Some uid2)
                    (usrs'', adv', cs', gks', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                    bd2'
          -> uid1 <> uid2
          -> usrs $? uid2 = Some ud2
          -> bd2 = build_data_step (mkUniverse usrs adv cs gks) ud2
          -> usrs' $? uid2 = Some {| key_heap := ks2;
                                    protocol := cmd2;
                                    msg_heap := qmsgs2;
                                    c_heap   := mycs2;
                                    from_nons := froms2;
                                    sent_nons := sents2;
                                    cur_nonce := cur_n2 |}
          -> usrs'' = usrs' $+ (uid1, {| key_heap := ks';
                                        protocol := cmdc';
                                        msg_heap := qmsgs';
                                        c_heap   := mycs';
                                        from_nons := froms';
                                        sent_nons := sents';
                                        cur_nonce := cur_n' |})
          -> forall ctx styp, syntactically_safe uid2 (compute_ids usrs) ctx cmd2 styp
                        -> typingcontext_sound ctx usrs cs uid2
                        -> keys_and_permissions_good gks usrs adv.(key_heap)
                        -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
                        -> exists bd2'',
                            step_user Silent (Some uid2) bd2 bd2''
.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; clean_context
  ; autorewrite with find_user_keys in *
  ; try solve [
          dt bd2'; clean_map_lookups
          ; eapply step_didnt_appear with (ms := [])
          ; try rewrite app_nil_r
          ; simpl; eauto
          ; intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto ].

  - eapply IHstep_user in H30; eauto.
  - simpl in *.
    destruct (rec_u_id ==n uid2); subst; clean_map_lookups; eauto.

    + dt bd2'; destruct ud2; clean_map_lookups.
      eapply step_didnt_appear with (ms := [existT crypto t0 msg]); simpl in *; eauto.

      intros
      ; destruct (uid1 ==n uid)
      ; destruct (uid2 ==n uid)
      ; subst; clean_map_lookups; eauto.

    + dt bd2'; clean_map_lookups
      ; eapply step_didnt_appear with (ms := [])
      ; try rewrite app_nil_r
      ; simpl in *
      ; eauto.

      intros
      ; destruct (rec_u_id ==n uid)
      ; destruct (uid1 ==n uid)
      ; subst; clean_map_lookups; eauto.
      
  - dt bd2'; clean_map_lookups
    ; eapply step_didnt_appear with (ms := [])
    ; try rewrite app_nil_r
    ; simpl; eauto.
    
    intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.

  - dt bd2'; clean_map_lookups
    ; eapply step_didnt_appear with (ms := [])
    ; try rewrite app_nil_r
    ; simpl; eauto.
    
    intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
Qed.

(* Lemma silent_steps_still_stuck_after_other_step : *)
(*   forall A B uid1 U, *)
(*     (forall uid' U', uid' > uid1 -> ~ @indexedRealStep A B uid' Silent U U') *)
(*     -> forall uid2 lbl U', indexedRealStep uid2 lbl U U' *)
(*     -> uid2 <> uid1  *)
(*     (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent (fst (fst st)) U') *)


Lemma silent_step_commutes_noblock :
  forall t__hon t__adv (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) cs cs' gks gks'
    ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' cmd2 cmd2' uid2,

    usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
    -> step_user Silent (Some uid2)
                (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
    -> forall uid1, uid1 <> uid2
    -> forall (usrs1' : honest_users t__hon) (adv1' : user_data t__adv) cs1' gks1'
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' cmd1 cmd1' lbl1,

        usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
        -> step_user lbl1 (Some uid1)
                  (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                  (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
        -> forall ks2'' qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'',
          usrs1' $? uid2 = Some (mkUserData ks2'' cmd2 qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'')
        -> exists usrs2' adv2' cs2' gks2' ks2''' qmsgs2''' mycs2''' froms2''' sents2''' cur_n2''' cmd2'',
          step_user Silent (Some uid2)
                    (usrs1' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1'),
                     adv1', cs1', gks1', ks2'', qmsgs2'', mycs2'', froms2'', sents2'', cur_n2'', cmd2)
                    (usrs2', adv2', cs2', gks2', ks2''', qmsgs2''', mycs2''', froms2''', sents2''', cur_n2''', cmd2'')
.
Proof.
  intros.

  pose proof (useless_summary_summarizes cmd1).
  generalize H0; intros SS
  ; eapply silent_step_na_commuting with (s := useless_summary) in H0; eauto
  ; split_ex.

  generalize SS; intros STEP
  ; eapply commutes_noblock with (uid1 := uid1) (uid2 := uid2) (summaries := $0 $+ (uid1,useless_summary)) in SS
  ; eauto.
Qed.

Lemma translate_trace_commute :
  forall t__hon t__adv i st st' b,
    @stepsi t__hon t__adv (1 + i) st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> syntactically_safe_U (fst (fst st))
    -> goodness_predicates (fst (fst st))
    -> (forall st'', ~ step st' st'')
    -> forall uid ud, (fst (fst st)).(users) $? uid = Some ud
    (* -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent (fst (fst st)) U') *)
    -> forall bd, step_user Silent (Some uid) (build_data_step (fst (fst st)) ud) bd
    -> exists st0 st0',
          indexedModelStep uid st st0
        /\ stepsi i st0 st0'
        /\ fst st0' = fst st'
        /\ ( snd st0' = snd st' \/ (snd st0' = false /\ snd st' = true) )
.
Proof.
  induct 1; intros; eauto.
  invert H0.

  - clear IHstepsi.
    invert H; simpl in *;
      repeat
        match goal with
        | [ H : ?x = ?x |- _ ] => clear H
        | [ H : step_universe _ _ _ _ |- _ ] => invert H; dismiss_adv
        | [ H : indexedRealStep _ _ _ _ |- _ ] => invert H
        | [ H : Silent = mkULbl ?lbl _ |- _ ] => unfold mkULbl in H; destruct lbl; try discriminate
        end.

    + destruct (uid ==n u_id); subst; clean_map_lookups.

      (* equal *)
      (do 2 eexists); repeat simple apply conj; simpl; try econstructor; eauto 8.

      (* not equal *)

      unfold build_data_step in *
      ; destruct userData, ud
      ; simpl in *
      ; generalize H7; intros STEP
      ; eapply step_limited_change_other_user with (u_id1 := u_id) (u_id2 := uid) in H7
      ; eauto
      ; split_ex
      ; simpl in *.
      
      exfalso.
      unfold goodness_predicates in *; split_ex.
      
      split_ors; split_ex; clean_map_lookups
      ; eapply step_then_silent_step with (uid1 := u_id) (uid2 := uid) in STEP
      ; eauto
      ; split_ex.

      dt x
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id0 := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

      dt x0
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id0 := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

    + destruct (uid ==n uid0); subst; clean_map_lookups.

      (* equal *)
      eapply user_step_label_deterministic in H6; eauto; discriminate.

      (* not equal *) 
      unfold build_data_step in *
      ; destruct userData, ud
      ; dt bd
      ; simpl in *
      ; generalize H11; intros STEP
      ; eapply step_limited_change_other_user with (u_id1 := uid0) (u_id2 := uid) in H11
      ; eauto
      ; split_ex
      ; simpl in *.
      
      exfalso.
      unfold goodness_predicates in *; split_ex.
      
      split_ors; split_ex; clean_map_lookups
      ; eapply step_then_silent_step with (uid1 := uid0) (uid2 := uid) in STEP
      ; eauto
      ; split_ex.

      dt x
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

      dt x0
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

    + destruct (uid ==n uid0); subst; clean_map_lookups.

      (* equal *)
      eapply user_step_label_deterministic in H6; eauto; discriminate.

      (* not equal *) 
      unfold build_data_step in *
      ; destruct userData, ud
      ; dt bd
      ; simpl in *
      ; generalize H10; intros STEP
      ; eapply step_limited_change_other_user with (u_id1 := uid0) (u_id2 := uid) in H10
      ; eauto
      ; split_ex
      ; simpl in *.
      
      exfalso.
      unfold goodness_predicates in *; split_ex.
      
      split_ors; split_ex; clean_map_lookups
      ; eapply step_then_silent_step with (uid1 := uid0) (uid2 := uid) in STEP
      ; eauto
      ; split_ex.

      dt x
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

      dt x0
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

    + destruct (uid ==n uid0); subst; clean_map_lookups.

      (* equal *)
      eapply user_step_label_deterministic in H6; eauto; discriminate.

      (* not equal *) 
      unfold build_data_step in *
      ; destruct userData, ud
      ; dt bd
      ; simpl in *
      ; generalize H10; intros STEP
      ; eapply step_limited_change_other_user with (u_id1 := uid0) (u_id2 := uid) in H10
      ; eauto
      ; split_ex
      ; simpl in *.
      
      exfalso.
      unfold goodness_predicates in *; split_ex.
      
      split_ors; split_ex; clean_map_lookups
      ; eapply step_then_silent_step with (uid1 := uid0) (uid2 := uid) in STEP
      ; eauto
      ; split_ex.

      dt x
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

      dt x0
      ; eapply H4
      ; econstructor 1; eauto
      ; eapply StepUser with (u_id := uid)
      ; unfold build_data_step, buildUniverse; simpl
      ; eauto.

  - assert (LAME: lameAdv b (adversary (fst (fst st)))) by assumption.
    eapply adversary_remains_lame_step in LAME; eauto.

    assert (SS : syntactically_safe_U (fst (fst st'))) by eauto using syntactically_safe_U_preservation_step.

    assert (UNIVS : goodness_predicates (fst (fst st'))).
    eapply goodness_preservation_step; eauto.

    specialize (IHstepsi _ _ eq_refl LAME SS UNIVS H4).
    clear LAME SS UNIVS.

    dt bd; destruct ud; simpl in *.

    invert H; simpl in *;
      repeat
      match goal with
      | [ H : step_universe _ _ _ _ |- _ ] => invert H; dismiss_adv
      | [ H : indexedRealStep _ _ _ _ |- _ ] => invert H
      | [ H : Silent = mkULbl ?lbl _ |- _ ] => unfold mkULbl in H; destruct lbl; try discriminate
      end;
      (* match goal with *)
      (* | [ H : O.max_elt _ = Some _ |- _ ] => *)
      (*   let MAX := fresh "H" *)
      (*   in generalize H; intros MAX; *)
      (*        apply NatMap.O.max_elt_MapsTo in MAX; rewrite find_mapsto_iff in MAX *)
      (* end; *)
      try rename u_id into uid0.

    + destruct (uid ==n uid0); subst; clean_map_lookups.

      (* equal *)
      (do 2 eexists); repeat simple apply conj; eauto.
      econstructor; eauto.
      econstructor; eauto.

      (* not equal *)
      (* assert (LK : users ru $? uid0 = Some userData) by assumption. *)
      (* eapply H8 in LK; eauto; split_ex.     gathers summaries *)

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.
      (* specialize (H5 _ _ x H); split_ex. (* specializes summary *) *)

      generalize H9; intros STEP
      ; eapply step_limited_change_other_user_qmsgs with (uid := uid) (uid' := uid0) in STEP
      ; eauto; split_ex.
      rename x into msg_heap'.

      specialize (IHstepsi _ _ H0); simpl in *.

      eapply silent_step_commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in H6; eauto.
      2: clean_map_lookups; eauto.
      split_ex.

      generalize H6; intros SS; eapply IHstepsi in H6; eauto.
      clear IHstepsi; split_ex; subst.

      Ltac clear_mislabeled_steps :=
        repeat
          match goal with
          | [ H : indexedRealStep _ _ _ _ |- _ ] => invert H
          | [ H1 : step_user (Action _) (Some ?uid) _ _
            , H2 : step_user Silent (Some ?uid) _ _ |- _ ] =>
            unfold build_data_step in *
            ; simpl in *
            ; clean_map_lookups
            ; simpl in *
            ; pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H1 H2)
            ; discriminate
          end.

      invert H6; clear_mislabeled_steps.

      pose proof (useless_summary_summarizes protocol0).
      eapply silent_step_na_commuting with (s := useless_summary) in SS; eauto
      ; split_ex.
      
      eapply commutes_sound with (u_id1 := uid0) (u_id2 := uid) in H14; eauto; simpl.

      split_ex; subst.
      unfold build_data_step in H14; destruct ru.
      dt x14; dt x15; destruct x16; simpl in *.

      (do 2 eexists); repeat simple apply conj; eauto.
      econstructor 1; eauto.
      econstructor; eauto.
      econstructor 1; eauto.
      econstructor 1; eauto.
      
    + destruct (uid ==n uid0); subst; clean_map_lookups; clear_mislabeled_steps.

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.

      generalize H13; intros STEP
      ; eapply step_limited_change_other_user_qmsgs with (uid := uid) (uid' := uid0) in STEP
      ; eauto; split_ex.
      rename x into msg_heap'.

      specialize (IHstepsi _ _ H0); simpl in *.

      eapply silent_step_commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in H6; eauto.
      2: clean_map_lookups; eauto.
      split_ex.

      generalize H6; intros SS; eapply IHstepsi in H6; eauto.
      clear IHstepsi; split_ex; subst.

      invert H6; clear_mislabeled_steps.

      pose proof (useless_summary_summarizes protocol0).
      eapply silent_step_na_commuting with (s := useless_summary) in SS; eauto
      ; split_ex.
      
      eapply commutes_sound with (u_id1 := uid0) (u_id2 := uid) in H18; eauto; simpl.

      split_ex; subst.
      unfold build_data_step in H18; destruct ru.
      dt x14; dt x15; destruct x16; simpl in *.

      destruct (classic (labels_align (buildUniverse usrs2 adv2 cs2 gks2 uid
                {|
                key_heap := ks2;
                protocol := cmd2;
                msg_heap := qmsgs2;
                c_heap := mycs2;
                from_nons := froms2;
                sent_nons := sents2;
                cur_nonce := cur_n2 |}, iu, b0))).

      * (do 2 eexists); repeat simple apply conj; eauto.
        econstructor 1; eauto.
        econstructor; eauto.
        econstructor 2; eauto; simpl in *.
        
        unfold goodness_predicates in *; split_ex; simpl in *.
        specialize (H2 _ _ _ H5 eq_refl); split_ex.
        eapply action_matches_other_user_silent_step; eauto.

      * destruct x11 as [[ru1 iu1] b1].
        (do 2 eexists); repeat simple apply conj;
          [ solve [ econstructor 1; eauto ]
          | econstructor
          | ..
          ].
        econstructor 3; eauto.
        rewrite H25; eapply falsify_trace; eauto.
        eauto.
        destruct st'' as [p b2]; simpl.
        destruct b2; eauto.

    + destruct (uid ==n uid0); subst; clean_map_lookups; clear_mislabeled_steps.

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.

      generalize H12; intros STEP
      ; eapply step_limited_change_other_user_qmsgs with (uid := uid) (uid' := uid0) in STEP
      ; eauto; split_ex.
      rename x into msg_heap'.

      specialize (IHstepsi _ _ H0); simpl in *.

      eapply silent_step_commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in H6; eauto.
      2: clean_map_lookups; eauto.
      split_ex.

      generalize H6; intros SS; eapply IHstepsi in H6; eauto.
      clear IHstepsi; split_ex; subst.

      invert H6; clear_mislabeled_steps.

      pose proof (useless_summary_summarizes protocol0).
      eapply silent_step_na_commuting with (s := useless_summary) in SS; eauto
      ; split_ex.
      
      eapply commutes_sound with (u_id1 := uid0) (u_id2 := uid) in H17; eauto; simpl.

      split_ex; subst.
      unfold build_data_step in H17; destruct ru.
      dt x14; dt x15; destruct x16; simpl in *.

      eapply silent_step_labels_still_misaligned with (b := b0) (b' := b0) in H11; eauto.

      destruct x11 as [[ru1 iu1] b1].
      simpl in *.
      (do 2 eexists); repeat simple apply conj.
      econstructor 1; eauto.
      econstructor; eauto.
      econstructor 3; eauto.
      all: eauto.

    + destruct (uid ==n uid0); subst; clean_map_lookups; clear_mislabeled_steps.

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.

      generalize H12; intros STEP
      ; eapply step_limited_change_other_user_qmsgs with (uid := uid) (uid' := uid0) in STEP
      ; eauto; split_ex.
      rename x into msg_heap'.

      specialize (IHstepsi _ _ H0); simpl in *.

      eapply silent_step_commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in H6; eauto.
      2: clean_map_lookups; eauto.
      split_ex.

      generalize H6; intros SS; eapply IHstepsi in H6; eauto.
      clear IHstepsi; split_ex; subst.

      invert H6; clear_mislabeled_steps.

      pose proof (useless_summary_summarizes protocol0).
      eapply silent_step_na_commuting with (s := useless_summary) in SS; eauto
      ; split_ex.
      
      eapply commutes_sound with (u_id1 := uid0) (u_id2 := uid) in H17; eauto; simpl.

      split_ex; subst.
      unfold build_data_step in H17; destruct ru.
      dt x14; dt x15; destruct x16; simpl in *.

      eapply silent_step_labels_still_misaligned with (b := b0) (b' := b0) in H11; eauto.

      destruct x11 as [[ru1 iu1] b1].
      simpl in *.
      (do 2 eexists); repeat simple apply conj.
      econstructor 1; eauto.
      econstructor; eauto.
      econstructor 4; eauto.
      all: eauto.

Qed.

Hint Constructors indexedRealStep indexedIdealStep : core.

Lemma step_extra_user :
  forall A B C lbl suid bd bd',
    @step_user A B C lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid cmdc,

      suid = Some uid
      -> usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
      -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall uid' ud',
          ~ In uid' usrs
          -> exists bd'',
            step_user lbl (Some uid)
                      (usrs $+ (uid',ud'), adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                      bd''.
Proof.
  induction 1; inversion 3; inversion 1; intros; subst
  ; try solve [ eexists; econstructor; eauto ]
  ; clean_context.

  eapply IHstep_user in H1; eauto.
  split_ex.
  dt x; eexists; econstructor; eauto.

  Unshelve.
  all: auto.
Qed.

Lemma silent_step_minus_user :
  forall A B C lbl suid bd bd',
    @step_user A B C lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid cmdc uid' ud',

      ~ In uid' usrs
      -> suid = Some uid
      -> lbl = Silent
      -> usrs $? uid = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
      -> bd = (usrs $+ (uid',ud'), adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> exists bd'',
          step_user lbl (Some uid)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                    bd''.
Proof.
  induction 1; inversion 5; inversion 1; intros; subst
  ; try discriminate
  ; try solve [ eexists; econstructor; eauto ]
  ; clean_context.

  eapply IHstep_user in H3; eauto.
  split_ex.
  dt x; eexists; econstructor; eauto.

  Unshelve.
  all: auto.
Qed.

Lemma must_be_max_silent_step' :
  forall A B usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd uid bd,
    usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> @step_user A B (Base A) Silent (Some uid) (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) bd
    -> exists uid__max U__max',
        indexedRealStep uid__max Silent
                        {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} U__max'
        /\ (forall uid' U',
              uid' > uid__max ->
              ~ indexedRealStep uid' Silent
                {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} U').
Proof.
  intros A B usrs.
  induction usrs using O.map_induction_max; intros.

  - unfold Empty, Raw.Empty in H.
    rewrite <- find_mapsto_iff in H0.
    unfold MapsTo in H0.
    exfalso.
    eapply H; eauto.

  - unfold Add in H0.

    destruct (x ==n uid); subst; clean_map_lookups; eauto.

    + dt bd.
      clear IHusrs1.
      exists uid; eexists.
      split.
      econstructor; eauto.
      unfold not; intros.
      invert H4; simpl in *.
      unfold O.Above in H.
      specialize (H uid').
      specialize (H0 uid'); clean_map_lookups.
      destruct (uid ==n uid'); subst; try Nat.order.
      clean_map_lookups.
      assert (usrs1 $? uid' <> None) by (clean_map_lookups; eauto).
      rewrite <- in_find_iff in H4.
      apply H in H4; lia.

    + rewrite H0 in H1; clean_map_lookups.
      assert (usrs2 = usrs1 $+ (x,e))
        by (apply map_eq_Equal; unfold Equal; eauto).
      subst.

      unfold O.Above in H.
      destruct ( classic (In x usrs1) ).
      apply H in H3; lia.

      dt bd; pose proof (silent_step_minus_user H2 H3 eq_refl eq_refl H1 eq_refl eq_refl).
      split_ex.
      dt x0.

      generalize H4; intros; eapply IHusrs1 in H4; eauto.
      clear IHusrs1.
      split_ex.

      invert H4; simpl in *.
      destruct (x ==n x0); subst; clean_map_lookups.
      destruct userData
      ; unfold build_data_step in *
      ; simpl in *.

      destruct ( classic ( exists U', indexedRealStep x Silent (mkUniverse (usrs1 $+ (x,e)) adv cs gks) U' )).
      split_ex.

      * exists x; eexists.
        split; eauto.

        unfold not; intros.
        invert H10; simpl in *.
        destruct (x ==n uid'); try lia; clean_map_lookups; eauto.
        assert (usrs1 $? uid' <> None) by (clean_map_lookups).
        rewrite <- in_find_iff in H10.
        apply H in H10; lia.
        
      * eapply step_extra_user in H8; split_ex; eauto.
        dt x1.
        exists x0; eexists.
        split.
        econstructor; unfold build_data_step; simpl; eauto.

        intros.
        destruct (uid' ==n x); subst; clean_map_lookups.
        ** firstorder idtac.
        ** unfold not; intros.
           invert H10.
           destruct userData; unfold build_data_step in *; simpl in *; clean_map_lookups.
           eapply silent_step_minus_user in H12; eauto.
           split_ex; eauto.
           dt x1.
           
           eapply H6 in H9; eauto.

Qed.

Lemma must_be_max_silent_step :
  forall A B uid U U',
    @indexedRealStep A B uid Silent U U'
    -> exists uid__max U__max',
        indexedRealStep uid__max Silent U U__max'
        /\ (forall uid' U',
              uid' > uid__max ->
              ~ indexedRealStep uid' Silent U U').
Proof.
  intros.
  invert H.
  destruct U; destruct userData
  ; simpl in *
  ; eauto using must_be_max_silent_step'.
Qed.

Lemma violations_translate :
  forall t__hon t__adv n st st' b summaries,
    stepsi n st st'
    -> lameAdv b (fst (fst st)).(adversary)
    -> goodness_predicates (fst (fst st))
    -> syntactically_safe_U (fst (fst st))
    -> summarize_univ (fst (fst st)) summaries
    -> (forall st'', step st' st'' -> False)
    -> ~ ( no_resends_U (fst (fst st')) /\ alignment st' /\ returns_align st')
    -> exists st'',
        (@stepSS t__hon t__adv)^* st st''
        /\ ~ (no_resends_U (fst (fst st'')) /\ alignment st'' /\ returns_align st'').
Proof.
  induct n; intros.

  invert H; eexists; split; eauto.

  destruct (
      classic (exists uid U', indexedRealStep uid Silent (fst (fst st)) U')
    ).

  - split_ex.
    
    pose proof (must_be_max_silent_step H6); split_ex; clear x x0 H6.
    invert H7.
    eapply translate_trace_commute in H; eauto.

    split_ex; subst.
    generalize H; intros; eapply progress_predicates in H; eauto; split_ex.

    eapply IHn in H7;
      eauto using model_stuck_carent_alignment_bit,
                  violated_predicates_remain_violated;
      split_ex.

    exists x2; split; eauto.
    eapply TrcFront; eauto.
    destruct st as [[ru iu] v].
    destruct x  as [[ru' iu'] v'].
    simpl in *.

    econstructor.
    2-3: reflexivity.
    econstructor 1; eauto.

    unfold build_data_step in *; simpl in *; eauto.
    
  - invert H.

    generalize H8; intros SS; 
      eapply syntactically_safe_U_preservation_step in SS; eauto.

    assert (SSU : syntactically_safe_U (fst (fst st'0))) by eauto using syntactically_safe_U_preservation_step.
    assert (GOODNESS : goodness_predicates (fst (fst st'0))) by eauto using goodness_preservation_step.

    eapply IHn in H9; eauto.
    repeat match goal with
           | [ H : goodness_predicates _ |- _ ] => clear H
           | [ H : syntactically_safe_U _ |- _ ] => clear H
           end.
    firstorder idtac.
    simpl in *.

    exists x.
    unfold not; split; intros; split_ex; eauto 8.
    eapply TrcFront; eauto.
    destruct st as [[ru iu] v], st'0 as [[ru0' iu0'] v0'].

    generalize H8; intros STEP; invert H8;
      match goal with
      | [ H : step_universe _ _ _ _ |- _ ] => invert H
      | [ H : indexedRealStep _ _ _ _ |- _ ] => invert H
      end.

    + specialize (H5 u_id); firstorder idtac.
      unfold mkULbl in H10; destruct lbl; try discriminate.
      exfalso.
      eapply H5; simpl.
      econstructor; eauto.

    + destruct ru; unfold build_data_step, lameAdv in *; simpl in *.
      rewrite H0 in H6; invert H6.

    + econstructor; eauto.
      econstructor 2; eauto.

    + econstructor; eauto.
      econstructor 2; eauto.

    + econstructor; eauto.
      econstructor 2; eauto.

Qed.

Lemma complete_trace :
  forall t__hon t__adv n' n st b,
    runningTimeMeasure (fst (fst st)) n
    -> n <= n'
    -> lameAdv b (fst (fst st)).(adversary)
    -> exists st',
        (@step t__hon t__adv) ^* st st'
      /\ (forall st'', step st' st'' -> False).

Proof.
  induct n'; intros.
  - invert H; simpl in *.

    exists st; split; intros; eauto.
    destruct st as [[ru iu] v].
    destruct ru; simpl in *; subst.
    destruct n__rt; try lia.

    invert H.
    
    + invert H7; dismiss_adv; simpl in *.
      eapply boundRunningTime_for_element in H2; eauto; split_ex.
      destruct x; try lia.
      invert H2.
      unfold build_data_step in *; rewrite <- H9 in H3; invert H3.

    + invert H6; simpl in *.
      eapply boundRunningTime_for_element in H2; eauto; split_ex.
      destruct x; try lia.
      invert H2.
      unfold build_data_step in *; rewrite <- H12 in H3; invert H3.
    
    + invert H6; simpl in *.
      eapply boundRunningTime_for_element in H2; eauto; split_ex.
      destruct x; try lia.
      invert H2.
      unfold build_data_step in *; rewrite <- H11 in H3; invert H3.

    + invert H6; simpl in *.
      eapply boundRunningTime_for_element in H2; eauto; split_ex.
      destruct x; try lia.
      invert H2.
      unfold build_data_step in *; rewrite <- H11 in H3; invert H3.

  - destruct (classic (exists st', step st st')).
    + split_ex.
      rename x into st'.
      assert (LAME' : lameAdv b (fst (fst st')).(adversary)) by eauto using adversary_remains_lame_step.
      eapply runningTimeMeasure_step in H; eauto; split_ex.

      eapply IHn' in H; try lia; eauto.
      split_ex.
      exists x0; split; intros; eauto.

    + firstorder idtac; simpl in *.
      exists st; split; intros; eauto.
Qed.

Hint Resolve  goodness_preservation_step syntactically_safe_U_preservation_step : core.

Lemma many_steps_stays_lame :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) ^* st st'
    -> lameAdv b (adversary (fst (fst st)))
    -> lameAdv b (adversary (fst (fst st'))).
Proof.
  induction 1;
    intros;
    simpl in *;
    eauto.
Qed.

Lemma many_steps_syntactically_safe :
  forall t__hon t__adv st st',
    (@step t__hon t__adv) ^* st st'
    -> syntactically_safe_U (fst (fst st))
    -> goodness_predicates (fst (fst st))
    -> syntactically_safe_U (fst (fst st')).
Proof.
  induction 1;
    intros;
    simpl in *;
    eauto.
Qed.

Lemma many_steps_stays_good :
  forall t__hon t__adv st st',
    (@step t__hon t__adv) ^* st st'
    -> goodness_predicates (fst (fst st))
    -> syntactically_safe_U (fst (fst st))
    -> goodness_predicates (fst (fst st')).
Proof.
  induction 1;
    intros;
    simpl in *;
    eauto.
Qed.

Hint Resolve many_steps_stays_lame many_steps_syntactically_safe many_steps_stays_good : core.

Theorem step_stepSS' :
  forall {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) b n summaries,
    runningTimeMeasure ru0 n
    -> goodness_predicates ru0
    -> syntactically_safe_U ru0
    -> summarize_univ ru0 summaries
    -> lameAdv b ru0.(adversary)
    -> invariantFor (TrSS ru0 iu0) (fun st => no_resends_U (fst (fst st)) /\ alignment st /\ returns_align st)
    -> invariantFor (TrS ru0 iu0) (fun st => no_resends_U (fst (fst st)) /\ alignment st /\ returns_align st)
.
Proof.
  intros * RUNTIME GOOD SYN_SAFE SUMM LAME INV.

  apply NNPP; unfold not; intros INV'.
  unfold invariantFor in INV'.
  apply not_all_ex_not in INV'; split_ex.
  apply imply_to_and in H; split_ex.
  apply not_all_ex_not in H0; split_ex.
  apply imply_to_and in H0; split_ex.
  simpl in H; split_ors; try contradiction.
  destruct x0 as [[?ru ?iu] ?v].

  subst; simpl in *.

  assert (exists n', runningTimeMeasure (fst (fst (ru, iu, v))) n' /\ n' <= n)
    by eauto using runningTimeMeasure_steps; split_ex.
  
  eapply complete_trace in H; eauto; split_ex.
  specialize (trc_trans H0 H); intros.
  apply steps_stepsi in H4; split_ex.

  unfold invariantFor in INV; simpl in *.
  eapply violations_translate in H4; eauto; split_ex.
  apply INV in H4; eauto; split_ex.

  eapply not_and_or in H1
  ; destruct H1 as [H1 | H1]
  ; [ | eapply not_and_or in H1]
  ; split_ors
  ; simpl
  ; unfold not; intros; split_ex.

  - assert (~ no_resends_U (fst (fst x0)))
      by eauto using resend_violation_steps
    ; contradiction.
  
  - assert (~ alignment x0)
      by eauto using alignment_violation_steps
    ; contradiction.

  - assert (~ returns_align x0)
      by eauto using final_alignment_violation_steps
    ; contradiction.
Qed.

Lemma ss_implies_next_safe :
  forall t (cmd : user_cmd t) uid ctx uids sty cs,
    syntactically_safe uid uids ctx cmd sty
    -> forall A B (usrs usrs' : honest_users A) (adv adv' : user_data B) cmd'
        cs' gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' n n' lbl,
      step_user lbl (Some uid)
                (usrs,adv,cs,gks,ks,qmsgs,mycs,froms,sents,n,cmd)
                (usrs',adv',cs',gks',ks',qmsgs',mycs',froms',sents',n',cmd')
      -> typingcontext_sound ctx usrs cs uid
      -> uids = compute_ids usrs
      -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
      -> (forall r, cmd__n <> Return r)
      -> no_resends sents'
      -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd.
Proof.
  induct cmd;
    unfold next_cmd_safe; intros;
      match goal with
      | [ H : nextAction _ _ |- _ ] => invert H
      end; eauto;
        try solve [ unfold typingcontext_sound in *; split_ex;
                    match goal with
                    | [ H : syntactically_safe _ _ _ _ _ |- _ ] => invert H
                    end; eauto ].

  - invert H0.
    invert H1; eauto.
    invert H4.
    eapply IHcmd in H7; eauto.
    eapply H7 in H11; eauto.

    invert H11; trivial.

  - unfold typingcontext_sound in *; split_ex; invert H.
    apply H2 in H11; split_ex; subst.
    apply H1 in H10.
    unfold msg_honestly_signed, msg_signing_key,
    msg_to_this_user, msg_destination_user,
    msgCiphersSignedOk, honest_keyb;
      context_map_rewrites.
    destruct ( cipher_to_user x0 ==n cipher_to_user x0 ); try contradiction.
    repeat simple apply conj; eauto.
    econstructor; eauto.
    unfold msg_honestly_signed, msg_signing_key, honest_keyb;
      context_map_rewrites;
      trivial.
    (do 2 eexists); repeat simple apply conj; eauto.
    invert H0.
    unfold no_resends, updateSentNonce in H5; context_map_rewrites.
    destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction.
    invert H5; eauto.
    
  - unfold typingcontext_sound in *; split_ex; invert H; eauto.
    intros.
    apply H12 in H; split_ex; subst; eauto.
Qed.

Lemma step_na_recur :
  forall t t__n (cmd : user_cmd t) (cmd__n : user_cmd t__n),
    nextAction cmd cmd__n
    -> forall A B suid lbl bd bd',

      step_user lbl suid bd bd'

      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          cmd__n' ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n',

        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n')
        -> exists bd'',
            step_user lbl suid (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) bd''.
Proof.
  induct 1; intros; subst;
    eauto.

  eapply IHnextAction in H0; eauto. split_ex.
  simpl.

  dt x; eexists; eapply StepBindRecur; eauto.
Qed.

Lemma ss_implies_next_safe_no_model_step :
  forall A B (usrs : honest_users A) (adv : user_data B) cs gks
    cmd uid ctx uids sty,

    uids = compute_ids usrs
    -> forall ks qmsgs mycs froms sents cur_n, usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> forall t__n (cmd__n : user_cmd t__n), nextAction cmd cmd__n
    -> syntactically_safe uid uids ctx cmd sty
    -> typingcontext_sound ctx usrs cs uid
    -> forall ru iu, ru = mkUniverse usrs adv cs gks
    -> (forall ru' iu', indexedModelStep uid (ru,iu,true) (ru',iu',true) -> False)
    -> labels_align (ru,iu,true)
    -> next_cmd_safe (findUserKeys usrs) cs uid froms sents cmd.
Proof.
  intros.
  cases cmd__n;
    unfold next_cmd_safe; intros;
      match goal with
      | [ H1 : nextAction cmd _, H2 : nextAction cmd _ |- _ ] => eapply na_deterministic in H1; eauto
      end; split_ex; subst; trivial.

  Ltac xyz :=
    repeat 
      match goal with
      | [ NA : nextAction _ (Bind _ _) |- _ ] =>
        eapply nextAction_couldBe in NA; contradiction
      | [ SS : syntactically_safe _ _ _ ?cmd _, NA : nextAction ?cmd _ |- _ ] =>
        eapply syntactically_safe_na in SS; eauto; split_ex
      | [ SS : syntactically_safe _ _ _ _ _ |- _ ] =>
        invert SS; unfold typingcontext_sound in *; split_ex; process_ctx
      end.

  all: xyz; eauto.

  - exfalso.

    assert (SEND : exists lbl bd,
               step_user lbl
                         (Some uid)
                         (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, 
                          @Send t0 (cipher_to_user x0) (SignedCiphertext x)) bd).
      (do 2 eexists); econstructor; clean_map_lookups; simpl in *; eauto.
      context_map_rewrites; eauto.
      unfold not; intros INV; invert INV; contradiction.
      split_ex.

      destruct x1.
      invert H4.

      dt x3.
      eapply step_na_recur in H4; eauto; split_ex.
      dt x1.

      assert (exists ru', indexedRealStep uid (Action a)
                                     (mkUniverse usrs adv cs gks)
                                     ru')
        by (eexists; econstructor; eauto). 
      
      split_ex.
      generalize (H6 _ _ _ H8); intros; split_ex.
      eapply H5; clear H5.
      econstructor 2; eauto.

  - eapply H11 in H4; split_ex.
    eapply H in H4; eauto.
Qed.

Theorem step_stepSS :
  forall {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) b n summaries,
    runningTimeMeasure ru0 n
    -> goodness_predicates ru0
    -> syntactically_safe_U ru0
    -> summarize_univ ru0 summaries
    -> lameAdv b ru0.(adversary)
    -> invariantFor (TrS ru0 iu0) (fun st => no_resends_U (fst (fst st)) /\ alignment st /\ returns_align st)
    -> invariantFor (TrS ru0 iu0) (fun st => safety st /\ alignment st /\ returns_align st)
.
Proof.
  unfold invariantFor; intros.
  specialize (H4 _ H5).
  generalize H6; intros STEPS; eapply H4 in H6; eauto.
  split_ex; split; eauto.

  destruct s' as [[ru' iu'] b'].
  simpl in *; split_ex; subst.
  split_ors; try contradiction; subst.

  hnf in H7; split_ex; simpl in H5; subst.
  assert (SS : syntactically_safe_U (fst (fst (ru', iu', true)))) by eauto.
  unfold honest_cmds_safe; intros.

  destruct (classic (exists st, indexedModelStep u_id (ru',iu',true) (st,true))).
  - split_ex.
    destruct x as [ru'' iu''].
    pose proof (indexedModelStep_step H10) as STEP.
    assert (STEPS' : (@step t__hon t__adv) ^* (ru',iu',true) (ru'',iu'',true)) by (eauto using TrcFront).
    pose proof (trc_trans STEPS STEPS') as MORESTEPS.

    specialize (H4 _ MORESTEPS); unfold no_resends_U in H4.
    simpl in *; split_ex.

    unfold syntactically_safe_U in SS;
      specialize (SS _ _ _ H9 eq_refl); split_ex.

    assert (exists lbl, indexedRealStep u_id lbl ru' ru'') by (invert H10; eauto).
    split_ex.
    invert H15.

    unfold build_data_step, buildUniverse in *; simpl in *.
    clean_map_lookups.

    pose proof (na_always_exists (protocol userData)); split_ex.
    destruct (classic (exists r, x3 = Return r)); split_ex; subst; eauto.
    + unfold next_cmd_safe; intros.
      eapply na_deterministic in H5; eauto.
      split_ex; subst; trivial.

    + rewrite Forall_natmap_forall in H4.
      specialize (H4 u_id).
      rewrite add_eq_o in H4 by trivial.
      specialize (H4 _ eq_refl); simpl in H4.
      eapply ss_implies_next_safe;
        eauto.

  - assert (forall st, indexedModelStep u_id (ru',iu',true) (st,true) -> False) by eauto using not_ex_all_not.
    
    subst.
    clear H10.
    unfold syntactically_safe_U in SS.
      specialize (SS _ _ _ H9 eq_refl); split_ex.
    simpl in *.

    pose proof (na_always_exists (protocol u)); split_ex.
    
    destruct ru', u;
      simpl in *;
      eapply ss_implies_next_safe_no_model_step; eauto.

Qed.

Module Type AutomatedSafeProtocolSS.

  Parameter t__hon : type.
  Parameter t__adv : type.
  Parameter b : << Base t__adv >>.
  Parameter iu0 : IdealWorld.universe t__hon.
  Parameter ru0 : RealWorld.universe t__hon t__adv.

  Notation SYS := (TrSS ru0 iu0).

  Axiom U_good : universe_starts_sane b ru0.
  Axiom universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0.

  Axiom safe_invariant : invariantFor
                           SYS
                           (fun st => safety st /\ alignment st /\ returns_align st).

End AutomatedSafeProtocolSS.


Print Assumptions step_stepSS'.
