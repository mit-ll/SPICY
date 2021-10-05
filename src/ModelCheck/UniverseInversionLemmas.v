(*
 * © 2019 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)
From Coq Require Import
     Classical
     List.

From SPICY Require Import
     MyPrelude
     Maps
     ChMaps
     Messages
     Keys
     Automation
     Tactics
     Simulation
     AdversaryUniverse
     Theory.KeysTheory

     ModelCheck.ModelCheck
.

From SPICY Require
     IdealWorld
     RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Section RealWorldLemmas.
  Import RealWorld.

  Lemma invert_return :
    forall (t : user_cmd_type) (r1 r2 : denote t),
      Return r1 = Return r2 -> r1 = r2.
  Proof. intros * H; invert H; trivial. Qed.

  Lemma invert_bind_eq :
    forall t1  t3 (cmd1 : user_cmd t1) (cmd2 : << t1 >> -> user_cmd t3)
      (cmd1' : user_cmd t1) (cmd2' : << t1 >> -> user_cmd t3),
      Bind cmd1 cmd2 = Bind cmd1' cmd2'
      -> cmd1 = cmd1'
      /\ forall (tv1 : << t1 >>), cmd2 tv1 = cmd2' tv1.
  Proof.
    intros.
    induction cmd1; invert H; eauto.
  Qed.

  Lemma input_act_eq_inv :
    forall t m m' p p' f f', @Input t m p f = Input m' p' f' -> m = m' /\ p = p' /\ f = f'.
  Proof. intros * H; invert H; auto. Qed.

  Lemma output_act_eq_inv :
    forall t m m' su1 su1' su2 su2' s s',
      @Output t m su1 su2 s = Output m' su1' su2' s'
      -> m = m' /\ su1 = su1' /\ su2 = su2' /\ s = s'.
  Proof. intros * H; invert H; auto. Qed.

  Lemma ct_eq_inv :
    forall t cid cid', @SignedCiphertext t cid = SignedCiphertext cid' -> cid = cid'.
  Proof. intros * H; invert H; auto. Qed.

  Import JMeq.
      
  Lemma sigcphr_eq_inv :
    forall t t' m m' kid kid' uid uid' seq seq',
      @SigCipher t kid uid seq m = @SigCipher t' kid' uid' seq' m'
      -> t = t' /\ kid = kid' /\ uid = uid' /\ seq = seq' /\ JMeq m m'.
  Proof. intros * H; invert H; auto. Qed.

  Lemma enccphr_eq_inv :
    forall t t' m m' kid kid' kid2 kid2' uid uid' seq seq',
      @SigEncCipher t kid kid2 uid seq m = @SigEncCipher t' kid' kid2' uid' seq' m'
      -> t = t' /\ kid = kid' /\ kid2 = kid2' /\ uid = uid' /\ seq = seq' /\ JMeq m m'.
  Proof. intros * H; invert H; auto 6. Qed.

  Lemma message_match_not_match_pattern_different :
    forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) cs suid froms pat,
      ~ msg_accepted_by_pattern cs suid froms pat msg1
      -> msg_accepted_by_pattern cs suid froms pat msg2
      -> existT _ _ msg1 <> existT _ _ msg2.
  Proof.
    intros.
    unfold not; intros.
    generalize (projT1_eq H1); intros EQ; simpl in EQ; subst.
    eapply inj_pair2 in H1; subst.
    contradiction.
  Qed.

  Lemma message_queue_split_head :
    forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) qmsgs qmsgs1 qmsgs2
      cs suid froms pat,

      existT _ _ msg2 :: qmsgs = qmsgs1 ++ existT _ _ msg1 :: qmsgs2
      -> msg_accepted_by_pattern cs suid froms pat msg1
      -> ~ msg_accepted_by_pattern cs suid froms pat msg2
      -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs suid froms pat msg') qmsgs1
      -> exists qmsgs1',
          qmsgs1 = (existT _ _ msg2) :: qmsgs1'.
  Proof.
    intros.
    destruct qmsgs1.
    - rewrite app_nil_l in H.
      eapply message_match_not_match_pattern_different in H0; eauto.
      invert H; contradiction.

    - rewrite <- app_comm_cons in H.
      invert H; eauto.
  Qed.

  Lemma message_queue_solve_head :
    forall t1 t2 (msg1 : crypto t1) (msg2 : crypto t2) qmsgs qmsgs1 qmsgs2
      cs suid froms pat,

      existT _ _ msg2 :: qmsgs = qmsgs1 ++ existT _ _ msg1 :: qmsgs2
      -> msg_accepted_by_pattern cs suid froms pat msg1
      -> msg_accepted_by_pattern cs suid froms pat msg2
      -> Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs suid froms pat msg') qmsgs1
      -> qmsgs1 = []
        /\ qmsgs2 = qmsgs
        /\ existT _ _ msg1 = existT _ _ msg2.
  Proof.
    intros.
    subst.
    destruct qmsgs1.

    rewrite app_nil_l in H
    ; invert H
    ; eauto.

    exfalso.
    rewrite <- app_comm_cons in H.
    invert H; eauto.
    invert H2; contradiction.
  Qed.

  #[local] Hint Resolve findUserKeys_foldfn_proper findUserKeys_foldfn_transpose : core.

  Lemma findUserKeys_add_reduce :
    forall {A} (usrs : honest_users A) u_id ks p qmsgs mycs froms sents cur_n,
      ~ In u_id usrs
      -> findUserKeys (usrs $+ (u_id, {| key_heap := ks;
                                        protocol := p;
                                        msg_heap := qmsgs;
                                        c_heap := mycs;
                                        from_nons := froms;
                                        sent_nons := sents;
                                        cur_nonce := cur_n |})) = findUserKeys usrs $k++ ks.
  Proof.
    intros.
    unfold findUserKeys.
    rewrite fold_add; eauto.
  Qed.

  Lemma findUserKeys_empty_is_empty :
    forall A, @findUserKeys A $0 = $0.
  Proof. trivial. Qed.  

End RealWorldLemmas.

Section OtherInvLemmas.
  Lemma nil_not_app_cons :
    forall A (l1 l2 : list A) e,
      [] = l1 ++ e :: l2
      -> False.
  Proof.
    intros.
    destruct l1.
    rewrite app_nil_l in H; invert H.
    rewrite <- app_comm_cons in H; invert H.
  Qed.

  Lemma action_eq_inv :
    forall t a1 a2, @Action t a1 = Action a2 -> a1 = a2.
  Proof. intros * H; invert H; auto.  Qed.

  Lemma key_eq_inv :
    forall kid kid' ku ku' kt kt', MkCryptoKey kid ku kt = MkCryptoKey kid' ku' kt' -> kid = kid' /\ ku = ku' /\ kt = kt'.
  Proof. intros * H; invert H; auto.  Qed.

  Lemma remove_empty :
    forall k V, (@empty V) $- k = $0.
  Proof.
    intros.
    eapply map_eq_Equal; unfold Equal; intros; eauto.
  Qed.

  Lemma map_sym : forall {v} (m : NatMap.t v) k1 k2 v1 v2,
      k1 <> k2
      -> m $+ (k1, v1) $+ (k2, v2) = m $+ (k2, v2) $+ (k1, v1).
  Proof. intros; maps_equal. Qed.

  Lemma in_empty_map_contra : (forall {t} x, Map.In (elt := t) x $0 -> False).
  Proof. propositional. invert H. invert H0. Qed.

  Lemma incl_empty_empty : (forall {t}, @incl t [] []).
  Proof. cbv; auto. Qed.


  Lemma TrcRefl' :
    forall {A} (R : A -> A -> Prop) x1 x2,
      x1 = x2 ->
      trc R x1 x2.
  Proof.
    intros. subst. apply TrcRefl.
  Qed.

  Lemma Trc3Refl' :
    forall {A B} (R : A -> B -> A -> Prop) x1 x2 P,
      x1 = x2 ->
      trc3 R P x1 x2.
  Proof.
    intros. subst. apply Trc3Refl.
  Qed.
  
End OtherInvLemmas.

Section InversionPrinciples.
  Import RealWorld.

  Lemma step_user_inv_ret :
    forall {A B C} (usrs usrs' : honest_users A) (adv adv' : user_data B)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd C) (r : <<C>>),
      step_user lbl u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Return r)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> False.
  Proof.
    intros * STEP; inversion STEP.
  Qed.

  Lemma step_user_inv_gen :
    forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      step_user lbl u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Gen)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ lbl = Silent
        /\ exists n, cmd = Return n.
  Proof.
    intros * H.
    inversion H; repeat invert_base_equalities1; subst; intuition idtac; eauto.
  Qed.

  Lemma step_user_inv_bind :
    forall {A B C C'} (usrs usrs' : honest_users A) (adv adv' : user_data B)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n'
      (cmd1 : user_cmd C) (cmd : <<C>> -> user_cmd C') (cmd' : user_cmd C'),
      step_user lbl u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Bind cmd1 cmd)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd')
      -> (exists cmd1',
            step_user lbl u_id
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, cmd1)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd1')
            /\ cmd' = Bind cmd1' cmd
        )
        \/ ( usrs = usrs'
            /\ adv = adv'
            /\ cs = cs'
            /\ gks = gks'
            /\ ks = ks'
            /\ qmsgs = qmsgs'
            /\ mycs = mycs'
            /\ froms = froms'
            /\ tos = tos'
            /\ cur_n = cur_n'
            /\ lbl = Silent
            /\ exists c, cmd1 = Return c
                   /\ cmd' = cmd c).
  Proof.
    intros * H.
    invert H; intuition eauto.
  Qed.

  Lemma step_user_inv_recv :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd (Crypto t)) pat,
      step_user lbl u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Recv pat)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ gks = gks'
        /\ exists msg msgs1 msgs2,
            qmsgs = msgs1 ++ (existT crypto t msg) :: msgs2
            /\ qmsgs' = msgs1 ++ msgs2
            /\ Forall (fun '(existT _ _ msg') => ~ msg_accepted_by_pattern cs u_id froms pat msg' ) msgs1
            /\ ( ( msg_accepted_by_pattern cs u_id froms pat msg
                  /\ ks' = ks $k++ findKeysCrypto cs msg
                  /\ mycs' = findCiphers msg ++ mycs
                  /\ froms' = updateTrackedNonce u_id froms cs msg
                  /\ lbl = Action (Input msg pat froms)
                  /\ cmd = @Return (Crypto t) msg)
              ).
  Proof.
    intros * H.
    invert H; intuition idtac; repeat eexists; intuition eauto.
  Qed.

  Lemma step_user_inv_send :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) (msg : crypto t)
      lbl u_id rec_u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      step_user lbl
                (Some u_id)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Send rec_u_id msg)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ froms = froms'
        /\ tos' = updateSentNonce (Some rec_u_id) tos cs msg
        /\ cur_n = cur_n'
        /\ mycs = mycs'
        /\ keys_mine ks (findKeysCrypto cs msg)
        /\ incl (findCiphers msg) mycs
        /\ adv' = 
          {| key_heap  := adv.(key_heap) $k++ findKeysCrypto cs msg
             ; protocol  := adv.(protocol)
             ; msg_heap  := adv.(msg_heap) ++ [existT _ _ msg]
             ; c_heap    := adv.(c_heap)
             ; from_nons := adv.(from_nons)
             ; sent_nons := adv.(sent_nons)
             ; cur_nonce := adv.(cur_nonce) |}
        /\ rec_u_id <> u_id
        /\ lbl = Action (Output msg (Some u_id) (Some rec_u_id) tos)
        /\ cmd = @Return (Base Unit) tt
        /\ exists rec_u,
            usrs $? rec_u_id = Some rec_u
            /\ usrs' = usrs $+ (rec_u_id, {| key_heap  := rec_u.(key_heap)
                                            ; protocol  := rec_u.(protocol)
                                            ; msg_heap  := rec_u.(msg_heap) ++ [existT _ _ msg]
                                            ; c_heap    := rec_u.(c_heap)
                                            ; from_nons := rec_u.(from_nons)
                                            ; sent_nons := rec_u.(sent_nons)
                                            ; cur_nonce := rec_u.(cur_nonce) |}).
  Proof.
    intros * H.
    invert H; intuition eauto.
  Qed.
  
  Lemma step_user_inv_enc :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign k__enc (msg : message t)
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n'
      msg_to cmd,
      step_user lbl
                u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, SignEncrypt k__sign k__enc msg_to msg)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n' = 1 + cur_n
        /\ keys_mine ks (findKeysMessage msg)
        /\ (exists kt__enc kt__sign kp__enc,
              gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
              /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__enc   = Some kp__enc
              /\ ks $? k__sign  = Some true
              /\ lbl = Silent)
        /\ (exists c_id msg_nonce, 
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigEncCipher k__sign k__enc msg_to msg_nonce msg)
              /\ (u_id <> None -> msg_nonce = (u_id, cur_n))
              /\ mycs' = c_id :: mycs
              /\ cmd = @Return (Crypto t) (SignedCiphertext c_id)).
  Proof.
    intros * H.
    invert H; intuition eauto 12.
  Qed.

  Lemma step_user_inv_dec :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) m
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd (Message t)),
      step_user lbl
                u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Decrypt m)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ qmsgs = qmsgs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ lbl = Silent
        /\ exists (msg : message t) k__sign k__enc kt__enc kt__sign kp__sign msg_to nonce c_id,
            cs $? c_id     = Some (SigEncCipher k__sign k__enc msg_to nonce msg)
            /\ m = SignedCiphertext c_id
            /\ List.In c_id mycs
            /\ gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
            /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
            /\ ks  $? k__enc  = Some true
            /\ ks  $? k__sign = Some kp__sign
            /\ ks' = ks $k++ findKeysMessage msg
            /\ mycs' = (* findCiphers msg ++ *) mycs
            /\ cmd = @Return (Message t) msg.
  Proof.
    intros * H.
    invert H; intuition eauto 20.
  Qed.

  Lemma step_user_inv_sign :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign (msg : message t) msg_to 
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      step_user lbl
                u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Sign k__sign msg_to msg)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n' = 1 + cur_n
        /\ keys_mine ks (findKeysMessage msg)
        /\ lbl = Silent
        /\ (exists kt__sign,
              gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id msg_nonce,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigCipher k__sign msg_to msg_nonce msg)
              /\ (u_id <> None -> msg_nonce = (u_id, cur_n))
              /\ mycs' = c_id :: mycs
              /\ cmd = @Return (Crypto t) (SignedCiphertext c_id)).
  Proof.
    intros * H.
    invert H; intuition eauto 12.
  Qed.

  Lemma step_user_inv_verify :
    forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign m
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      step_user lbl
                u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Verify k__sign m)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ lbl = Silent
        /\ exists (msg : message t) kt__sign kp__sign msg_to nonce c_id,
            cs $? c_id     = Some (SigCipher k__sign msg_to nonce msg)
            /\ m = SignedCiphertext c_id
            /\ List.In c_id mycs
            /\ cmd = @Return (UPair (Base Bool) (Message t)) (true,msg)
            /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
            /\ ks  $? k__sign = Some kp__sign.
  Proof.
    intros * H.
    invert H; intuition eauto 12.
  Qed.

  Lemma step_user_inv_genkey :
    forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) usage kt
      lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      step_user lbl
                u_id
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, GenerateKey kt usage)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ froms = froms'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ lbl = Silent
        /\ exists k_id k,
            gks $? k_id = None
            /\ k = MkCryptoKey k_id usage kt
            /\ gks' = gks $+ (k_id, k)
            /\ ks' = add_key_perm k_id true ks
            /\ cmd = @Return (Base Access) (k_id,true).
  Proof.
    intros * H.
    invert H; intuition eauto 12.
  Qed.

  Lemma adv_no_step :
    forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) b
      lbl cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
      lameAdv b adv
      -> step_user lbl None (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, protocol adv)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
      -> False.
  Proof.
    unfold lameAdv; destruct adv; simpl; intros;
      match goal with
      | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,?prot) _
                 , LAME : ?prot = _ |- _ ] => rewrite LAME in STEP; invert STEP
      end.
  Qed.

End InversionPrinciples.

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

  Lemma split_real_univ_fields :
    forall {A B} (us us' : honest_users A) (a a' : user_data B) cs cs' ks ks',
      {| users       := us
         ; adversary   := a
         ; all_ciphers := cs
         ; all_keys    := ks
      |} =
      {| users       := us'
         ; adversary   := a'
         ; all_ciphers := cs'
         ; all_keys    := ks'
      |}
      -> us = us'
        /\  a =  a'
        /\ cs = cs'
        /\ ks = ks'.
  Proof.
    intros * H; invert H; eauto.
  Qed.

  Lemma split_real_user_data_fields :
    forall t ks ks' (p p' : user_cmd (Base t)) msgs msgs' cheap cheap' froms froms' sents sents' n n',
      {| key_heap := ks;
         protocol := p;
         msg_heap := msgs;
         c_heap := cheap;
         from_nons := froms;
         sent_nons := sents;
         cur_nonce := n
      |} =
      {| key_heap := ks';
         protocol := p';
         msg_heap := msgs';
         c_heap := cheap';
         from_nons := froms';
         sent_nons := sents';
         cur_nonce := n' |}
      -> ks = ks'
        /\ p = p'
        /\ msgs = msgs'
        /\ cheap = cheap'
        /\ froms = froms'
        /\ sents = sents'
        /\ n = n'.
  Proof.
    intros * H; invert H; eauto 8.
  Qed.

  Lemma map_eq_fields_eq :
    forall V (m m' : NatMap.t V) k v,
      m $+ (k,v) = m'
      -> m' $? k = Some v
        /\ m $- k = m' $- k.
  Proof.
    intros; subst.
    clean_map_lookups; eauto.
    rewrite map_add_remove_eq; eauto.
  Qed.

End RealLemmas.

Section IdealLemmas.
  Import IdealWorld.

  Lemma ideal_univ_eq_fields_eq :
    forall {A} (us us' : NatMap.t (user A)) cv cv',
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

Section StepInversions.
  Import RealWorld.

  #[local] Hint Constructors indexedRealStep : core.
  
  Lemma inv_univ_silent_step :
    forall t__hon t__adv ru ru' suid b,
      lameAdv b ru.(adversary)
      -> @step_universe t__hon t__adv suid ru Silent ru'
      -> exists uid ud usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
          ru.(users) $? uid = Some ud
          /\ step_user Silent (Some uid)
                      (build_data_step ru ud)
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          /\ ru' = buildUniverse usrs adv cs gks uid {| key_heap    := ks
                                                       ; msg_heap  := qmsgs
                                                       ; protocol  := cmd
                                                       ; c_heap    := mycs
                                                       ; from_nons := froms
                                                       ; sent_nons := sents
                                                       ; cur_nonce := cur_n |}.
  Proof.
    intros * LAME STEP
    ; invert STEP.

    - unfold mkULbl in H2
      ; destruct lbl
      ; try discriminate
      ; eauto 20.

    - unfold lameAdv in LAME.
      unfold build_data_step in H
      ; rewrite LAME in H
      ; invert H.
  Qed.

  Lemma inv_univ_labeled_step :
    forall t__hon t__adv ru ru' suid uid a,
      @step_universe t__hon t__adv suid ru (Action (uid,a)) ru'
      -> exists ud usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
        ru.(users) $? uid = Some ud
        /\ suid = Some uid
        /\ step_user (@Action action a) (Some uid)
                    (build_data_step ru ud)
                    (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        /\ ru' = buildUniverse usrs adv cs gks uid {| key_heap    := ks
                                                     ; msg_heap  := qmsgs
                                                     ; protocol  := cmd
                                                     ; c_heap    := mycs
                                                     ; from_nons := froms
                                                     ; sent_nons := sents
                                                     ; cur_nonce := cur_n |}.
  Proof.
    intros * STEP
    ; invert STEP.

    unfold mkULbl in H2
    ; destruct lbl
    ; try discriminate.

    invert H2; eauto 20.
  Qed.

  Lemma label_align_step_split :
    forall t__hon t__adv st st',
      @step t__hon t__adv st st'
      -> labels_align st
      -> forall ru ru' iu iu' b b' a,
          st = (ru,iu,b)
          -> st' = (ru',iu',b')
          -> lameAdv a ru.(adversary)
          -> b = b'
            /\ exists uid,
              ( indexedRealStep uid Silent ru ru' /\ iu = iu' )
              \/ exists iu0 ra ia, 
                indexedRealStep uid (Action ra) ru ru'
                /\ (indexedIdealStep uid Silent) ^* iu iu0
                /\ indexedIdealStep uid (Action ia) iu0 iu'
                /\ action_matches (all_ciphers ru) (all_keys ru) (uid,ra) ia.
  Proof.
    intros.
    subst; invert H; try contradiction.

    - invert H2;
        try 
          match goal with
          | [ H : Silent = mkULbl ?lbl _ |- _ ] => unfold mkULbl in H; destruct lbl; try discriminate
          end;
        split; eexists; left; eauto.
      unfold build_data_step in *; unfold lameAdv in H3; rewrite H3 in *.
      invert H.
    - split; eexists; right; eauto 10.

      Unshelve.
      auto.
  Qed.

  Lemma label_align_indexedModelStep_split :
    forall t__hon t__adv st st' uid,
      @indexedModelStep t__hon t__adv uid st st'
      -> labels_align st
      -> forall ru ru' iu iu' b b' a,
          st = (ru,iu,b)
          -> st' = (ru',iu',b')
          -> lameAdv a ru.(adversary)
          -> b = b'
            /\ ( (indexedRealStep uid Silent ru ru' /\ iu = iu')
                \/ (exists iu0 ra ia, 
                      indexedRealStep uid (Action ra) ru ru'
                      /\ (indexedIdealStep uid Silent) ^* iu iu0
                      /\ indexedIdealStep uid (Action ia) iu0 iu'
                      /\ action_matches (all_ciphers ru) (all_keys ru) (uid,ra) ia)).
  Proof.
    intros;
      subst; invert H; try contradiction; eauto 12.
  Qed.

  Lemma upper_users_cant_step_rewrite :
    forall A B (U : universe A B) uid,
      (forall uid' ud' U', U.(users) $? uid' = Some ud' -> uid' > uid -> ~ indexedRealStep uid' Silent U U')
      -> (forall uid' U', uid' > uid -> ~ indexedRealStep uid' Silent U U').
  Proof.
    intros * H * INEQ.
    unfold not; intros IRS.
    invert IRS; eauto.
    eapply H; eauto.
  Qed.

  Lemma indexedModelStep_user_step :
    forall t__hon t__adv uid ru ru' iu iu' b b',
      @indexedModelStep t__hon t__adv uid (ru,iu,b) (ru',iu',b')
      -> (indexedRealStep uid Silent ru ru' /\ iu = iu' /\ b = b')
        \/ (exists a, indexedRealStep uid (Action a) ru ru')
  .
  Proof.
    induct 1; eauto 8.
  Qed.

End StepInversions.

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
