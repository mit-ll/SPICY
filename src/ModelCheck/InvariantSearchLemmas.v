(*
 * © 2021 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     List
     Lia.

From SPICY Require Import
     MyPrelude
     Maps
     Messages
     Keys
     Tactics
     RealWorld
     SafeProtocol
     SafetyAutomation
     Simulation

     Theory.InvariantsTheory
     Theory.KeysTheory

     ModelCheck.ModelCheck
     ModelCheck.LabelsAlign
     ModelCheck.ProtocolFunctions
     ModelCheck.RealWorldStepLemmas
     ModelCheck.SilentStepElimination
     ModelCheck.SteppingTactics
     ModelCheck.UniverseInversionLemmas
.

Import SafetyAutomation Gen.

Set Implicit Arguments.

Lemma lookup_in_merge_perm :
  forall kid (m m' : key_perms),
    m $k++ m' $? kid = match m $? kid with
                       | Some p => match m' $? kid with
                                  | Some p' => Some (greatest_permission p p')
                                  | None => Some p
                                  end
                       | None => m' $? kid
                       end.
Proof.
  intros; cases (m $? kid); cases (m' $? kid); solve_perm_merges.
Qed.

Section RW.
  Import RealWorld.

  Fixpoint compute_na {t} (cmd: user_cmd t) : sigT user_cmd :=
    match cmd with
    | Bind c _ => compute_na c
    | c => existT _ _ c
    end.

  Lemma compute_na_correct :
    forall t (cmd : user_cmd t) t__n (cmd__n : user_cmd t__n),
      compute_na cmd = existT _ _ cmd__n
      -> nextAction cmd cmd__n.
  Proof.
    induct cmd
    ; try solve [ unfold compute_na; simpl; intros; invert H; econstructor; eauto ].

    intros.
    constructor.
    simpl in H0; eauto.
  Qed.

  Lemma invert_na :
    forall t (cmd : user_cmd t) t__n (cmd__n : user_cmd t__n),
      nextAction cmd cmd__n
      -> compute_na cmd = existT _ _ cmd__n
        /\ projT1 (compute_na cmd) = t__n.
  Proof.

    induct cmd
    ; try solve [ intros; unfold compute_na; invert H; split; eauto ].

    intros; induct H; eauto.
    intros; invert H0; eauto.
  Qed.

End RW.

Inductive NoSilent {A B} (uid : user_id) (U : RealWorld.universe A B) : Prop :=
| Stuck :
    (forall U', ~ indexedRealStep uid Silent U U')
    -> NoSilent uid U.

Definition honest_heaps_sane {A} (usrs : honest_users A) (cs : ciphers) (gks : keys) :=
  forall uid u,
    usrs $? uid = Some u
    -> (forall cid, List.In cid u.(c_heap) -> In cid cs)
    /\ (forall kid kp, u.(key_heap) $? kid = Some kp -> In kid gks)
. 

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
          -> (forall uid u, usrs'' $? uid = Some u -> exists u', usrs $? uid = Some u')
          -> (forall cid c, cs'' $? cid = Some c -> cs $? cid = Some c)
          -> (forall cid c, cs $? cid = Some c -> cs'' $? cid = Some c \/ cs'' $? cid = None)
          -> (forall kid k, gks $? kid = Some k -> gks'' $? kid = Some k \/ gks'' $? kid = None)
          -> (forall kid k, gks'' $? kid = Some k -> gks $? kid = Some k)
          -> honest_heaps_sane usrs'' cs'' gks''
          -> exists bd'',
              step_user Silent suid
                        (usrs'', adv'', cs'', gks'', ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                        bd''.
Proof.
  Local Ltac process_stuff :=
    repeat
      match goal with
      | [ H : honest_heaps_sane ?usrs ?cs ?gks, USR : ?usrs $? _ = Some _ |- _ ] =>
        specialize (H _ _ USR)
        ; simpl in H
        ; destruct H
      | [ H : ?m $? _ = Some _, FN : (forall _ _, ?m $? _ = Some _ -> _) |- _ ] =>
        apply FN in H
      | [ H : List.In _ ?l, FN : (forall _, List.In _ ?l -> _) |- _ ] =>
        apply FN in H
      end
    ; split_ors
    ; clean_map_lookups
    ; trivial.
  
  induction 1; inversion 1; inversion 1
  ; intros
  ; subst
  ; try discriminate
  ; try solve [ eexists; econstructor; eauto ]
  ; eauto.

  - eapply IHstep_user in H27; eauto.
    split_ex; eauto.
    dt x.
    eexists; econstructor; eauto.
  - eexists; eapply StepEncrypt with (c_id0 := next_key cs''); eauto using Maps.next_key_not_in
    ; process_stuff.
    
  - eexists; econstructor; trivial.
    process_stuff; split_ors; clean_map_lookups; eauto.
    process_stuff; split_ors; clean_map_lookups; eauto.
    process_stuff; split_ors; clean_map_lookups; eauto.
    all: eauto.
  - eexists; eapply StepSign with (c_id0 := next_key cs''); eauto using Maps.next_key_not_in
    ; process_stuff.
  - eexists; econstructor; eauto
    ; process_stuff.
  - eexists; eapply StepGenerateKey with (k_id0 := next_key gks''); eauto using Maps.next_key_not_in.

    Unshelve.
    auto.
Qed.

Lemma silent_step_then_silent_step_inv :
  forall {A B} suid lbl bd bd',

    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd (Base A)) uid1 ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' cmdc,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid1
      -> lbl = Silent
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
          -> honest_heaps_sane usrs cs gks
          -> exists bd2'',
              step_user Silent (Some uid2) bd2 bd2''
.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst
  ; autorewrite with find_user_keys in *
  ; try discriminate
  ; try solve [
          dt bd2'; clean_map_lookups
          ; eapply step_didnt_appear with (ms := [])
          ; try rewrite app_nil_r
          ; simpl; eauto
          ; intros
          ; clean_map_lookups
          ; trivial
          ; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto].

  - eapply IHstep_user in H28; eauto.
      
  - dt bd2'; clean_map_lookups
    ; eapply step_didnt_appear with (ms := [])
    ; try rewrite app_nil_r
    ; simpl; eauto.

    clean_map_lookups; trivial.
    
    intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.

  - dt bd2'; clean_map_lookups
    ; eapply step_didnt_appear with (ms := [])
    ; try rewrite app_nil_r
    ; simpl; eauto.
    
    clean_map_lookups; trivial.
    
    intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.
    intros; destruct (c_id ==n cid); subst; clean_map_lookups; eauto.

  - dt bd2'; clean_map_lookups
    ; eapply step_didnt_appear with (ms := [])
    ; try rewrite app_nil_r
    ; simpl; eauto.
    
    clean_map_lookups; trivial.
    
    intros; destruct (uid1 ==n uid); subst; clean_map_lookups; eauto.
    intros; destruct (k_id ==n kid); subst; clean_map_lookups; eauto.
    intros; destruct (k_id ==n kid); subst; clean_map_lookups; eauto.
Qed.

Lemma NoSilent_no_indexed_silent_step :
  forall A B uid (U : RealWorld.universe A B), 
    NoSilent uid U
    -> forall U',
      ~ indexedRealStep uid Silent U U'.
Proof.
  invert 1; intros; eauto.
Qed.

Definition propNoSilent {A B} (U U' : RealWorld.universe A B) :=
  forall uid, NoSilent uid U -> NoSilent uid U'.

Lemma all_users_NoSilent_no_indexed_silent_step :
  forall A B uid (U : RealWorld.universe A B),
    (forall uid ud, U.(RealWorld.users) $? uid = Some ud -> NoSilent uid U)
    -> forall U',
      ~ indexedRealStep uid Silent U U'.
Proof.
  intros.
  unfold not; intros.
  generalize H0; invert H0.
  apply H in H1.
  eapply NoSilent_no_indexed_silent_step; eauto.
Qed.

Lemma silent_step_nochange_other_user_inv :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc u_id1 u_id2 ud2,
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs' $? u_id2 = Some ud2
          -> usrs $? u_id2 = Some ud2.
Proof.
  induction 1; inversion 1; inversion 1
  ; intros; subst
  ; try discriminate
  ; try solve [ clean_map_lookups; trivial ]
  ; eauto.
Qed.

Lemma propNoSilent_silent_step :
  forall A B (U U': RealWorld.universe A B) uid,
    indexedRealStep uid Silent U U'
    -> honest_heaps_sane U.(users) U.(all_ciphers) U.(all_keys)
    -> propNoSilent U U'.
Proof.
  unfold propNoSilent; intros.
  invert H1.
  constructor; unfold not; intros.

  destruct (uid ==n uid0); subst.

  apply H2 in H; auto.

  invert H; invert H1.
  destruct U, userData, userData0.
  unfold build_data_step, buildUniverse in *; simpl in *; clean_map_lookups.

  pose proof (silent_step_then_silent_step_inv H4).
  pose proof (silent_step_nochange_other_user_inv H4).

  specialize (H6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl).
  specialize (H6 _ _ _ _ eq_refl n H3 H).
  
  specialize (H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl H3).
  specialize (H1 _ _ _ _ _ _ _ _ _ _ _ _ _ H5 n H6 eq_refl H eq_refl).

  specialize (H1 H0).

  split_ex.
  dt x.
  eapply H2.
  econstructor; simpl; eauto.
Qed.

Lemma ssteps_inv_silent :
  forall A B st st',
    (@stepSS A B) ^* st st'
    -> forall (U U' : RealWorld.universe A B) uid U__i b,
      st = (U,U__i,b)
      -> indexedRealStep uid Silent U U'
      -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent U U')
      -> exists U__r,
          indexedRealStep uid Silent U U__r
          /\ (  st' = (U,U__i,b)
               \/  (stepSS (t__adv := B) ^* (U__r,U__i,b) st')
            )
          /\ ( honest_heaps_sane U.(users) U.(all_ciphers) U.(all_keys)
            -> propNoSilent U U__r ).
Proof.
  intros.
  subst; invert H.
  - eexists; eauto 8 using propNoSilent_silent_step.
  - invert H0; repeat equality1.
    invert H.
    + apply indexedModelStep_user_step in H6; split_ex; split_ors; subst.
      * destruct ( uid ==n u_id ); subst.
        clear H1 H4.
        
        eexists; repeat simple apply conj; eauto using propNoSilent_silent_step.
        exfalso.

        destruct (le_gt_dec u_id uid).
        assert (uid > u_id) by lia.
        eapply H5; eauto.
        eapply H2; eauto.
        
      * invert H; invert H4.
        exfalso.
        clean_map_lookups
        ; pose proof (user_step_label_deterministic _ _ _ _ _ _ _ _ _ H7 H8); discriminate.

    + eapply H4 in H1; contradiction.
Qed.

Lemma ssteps_inv_labeled :
  forall A B st st' ru,
    (forall uid U', ~ @indexedRealStep A B uid Silent ru U')
    -> (@stepSS A B) ^* st st'
    -> labels_align st
    -> forall iu b,
        st = (ru,iu,b)
        -> st = st'
          \/ exists uid ru' iu0 iu' ra ia,
            indexedRealStep uid (Action ra) ru ru'
            /\ (indexedIdealStep uid Silent) ^* iu iu0
            /\ indexedIdealStep uid (Action ia) iu0 iu'
            /\ action_matches (RealWorld.all_ciphers ru) (RealWorld.all_keys ru) (uid,ra) ia
            /\ (@stepSS A B) ^* (ru',iu',b) st'.
Proof.
  intros; subst.
  invert H0; clear_mislabeled_steps; eauto.
  right.

  invert H2; repeat equality1.
  invert H0.
  - exfalso; eapply H; eauto.
  - invert H6; try contradiction.
    clear_mislabeled_steps.
    eauto 12.
Qed.
