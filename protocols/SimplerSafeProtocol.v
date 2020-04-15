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

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     Messages
     Tactics
     Simulation
     RealWorld
     AdversarySafety.

From protocols Require Import
     SafeProtocol
     ProtocolAutomation.

From protocols Require Sets.

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

  (* Partial order reduction *)

  Record summary := { sending_to : Sets.set user_id }.

  Inductive summarize : forall {t}, user_cmd t -> summary -> Prop :=
  | SumReturn : forall t r s,
      summarize (@Return t r) s
  | SumGen : forall s,
      summarize Gen s
  | SumSend : forall {t} (msg : crypto t) uid s,
      Sets.In uid s.(sending_to)
      -> summarize (Send uid msg) s
  | SumRecv : forall t pat s,
      summarize (@Recv t pat) s
  | SumSignEncrypt : forall t k__s k__e u_id (msg : message t)s ,
      summarize (SignEncrypt k__s k__e u_id msg) s
  | SumDecrypt : forall t (msg : crypto t) s,
      summarize (Decrypt msg) s
  | SumSign : forall t k u_id (msg : message t) s,
      summarize (Sign k u_id msg) s
  | SumVerify : forall t k (msg : crypto t) s,
      summarize (Verify k msg) s
  | SumGenSymKey : forall usg s,
      summarize (GenerateSymKey usg) s
  | SumGenAsymKey : forall usg s,
      summarize (GenerateAsymKey usg) s
  | SumBind : forall t1 t2 (c1 : user_cmd t1) (c2 : << t1 >> -> user_cmd t2) s,
      summarize c1 s
      -> (forall r__v, summarize (c2 r__v) s)
      -> summarize (Bind c1 c2) s
  .

  Definition commutes {t} (cmd : user_cmd t) (s : summary) : Prop :=
    match cmd with
    | Return _ => True
    | Gen => True
    | Send uid _ => False (* figure out sends/receives commuting condition *)
    | Recv _ => False  (* ~ Sets.In me s.(sending_to) *)
    | SignEncrypt _ _ _ _ => True
    | Decrypt _ => True
    | Sign _ _ _ => True
    | Verify _ _ => True
    | GenerateSymKey _ => True
    | GenerateAsymKey _ => True
    | Bind _ _ => False
    end.

  Lemma step_na_return :
    forall {A B C D} suid lbl bd bd',

      step_user lbl suid bd bd'

      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n' r,

        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> @nextAction C D cmd (Return r)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ froms = froms'
        /\ sents = sents'
        /\ cur_n = cur_n'
        /\ (forall cs'' (usrs'': honest_users A) (adv'' : user_data B) gks'' ks'' qmsgs'' mycs'' froms'' sents'' cur_n'',
              step_user lbl suid
                        (usrs'', adv'', cs'', gks'', ks'', qmsgs'', mycs'', froms'', sents'', cur_n'', cmd)
                        (usrs'', adv'', cs'', gks'', ks'', qmsgs'', mycs'', froms'', sents'', cur_n'', cmd')).
  Proof.
    induction 1; inversion 1; inversion 1; intros; subst;
      match goal with
      | [ H : nextAction _ _ |- _ ] => invert H
      end; eauto.

    - eapply IHstep_user in H5; eauto; intuition (subst; eauto).
      econstructor; eauto.

    - invert H4.
      intuition idtac.
      econstructor.
  Qed.

  Lemma step_na_not_return :
    forall {A B C D} suid lbl bd bd',

      step_user lbl suid bd bd'

      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd cmd' : user_cmd C) (cmd__n : user_cmd D) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n',

        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> nextAction cmd cmd__n
        -> (forall r, cmd__n <> Return r)
        -> exists f cmd__n',
            step_user lbl suid
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n')
            /\ cmd = f cmd__n
            /\ cmd' = f cmd__n'
            /\ forall lbl1 suid1 (usrs1 usrs1' : honest_users A) (adv1 adv1' : user_data B)
                cs1 cs1' gks1 gks1'
                ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' (cmd__n'' : user_cmd D)
                froms1 froms1' sents1 sents1' cur_n1 cur_n1',

                step_user lbl1 suid1
                          (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n)
                          (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n'')
                -> step_user lbl1 suid1
                            (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, f cmd__n)
                            (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', f cmd__n'').
  Proof.
    Hint Constructors step_user.

    induction 1; inversion 1; inversion 1; invert 1; intros.

    - eapply IHstep_user in H28; eauto.
      split_ex.
      exists (fun CD => x <- x CD; cmd2 x).
      eexists; subst; split; eauto.
    - invert H27.
      unfold not in *; exfalso; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
    - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  Qed.

  Hint Constructors nextAction : core.
  Definition data_step_no_cmd A B : Type :=
    honest_users A * user_data B * ciphers * keys * key_perms * queued_messages * my_ciphers * recv_nonces * sent_nonces * nat.

  Lemma step_implies_na :
    forall {A B C} suid lbl bd bd',

      step_user lbl suid bd bd'

      -> forall (bd__x bd__x' : data_step_no_cmd A B)  (cmd cmd' : user_cmd C),
          bd = (bd__x, cmd)
        -> bd' = (bd__x', cmd')
        -> (exists R (r : <<R>>), @nextAction C R cmd (Return r))
        \/ (exists D f (cmd__n cmd__n' : user_cmd D),
              nextAction cmd cmd__n
            /\ cmd = f cmd__n
            /\ cmd' = f cmd__n'
            /\ forall (bd__x1 bd__x1' : data_step_no_cmd A B),
                 step_user lbl suid
                          (bd__x1, cmd__n)
                          (bd__x1', cmd__n')
                -> step_user lbl suid
                            (bd__x1, f cmd__n)
                            (bd__x1', f cmd__n')

          ).
  Proof.
    induction 1; inversion 1; inversion 1;
      intros; subst; try solve [ right; eexists; exists (fun x => x); eauto 6]; eauto.

    - specialize (IHstep_user _ _ _ _ eq_refl eq_refl).
      split_ors; split_ex; subst.
      + left; eauto 8.
      + right; eexists; exists (fun CMD => x <- x0 CMD; cmd2 x);
          (do 2 eexists); repeat simple apply conj; eauto; intros.
        do 9 destruct bd__x1 as [bd__x1 ?x].
        do 9 destruct bd__x1' as [bd__x1' ?x].
        eapply StepBindRecur; eauto 12.
  Qed.

  (* need to know that msg, if cipher, is in cs *)
  Lemma findKeysCrypto_addnl_cipher :
    forall {t} (msg : crypto t) cs c_id c,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> findKeysCrypto cs msg = findKeysCrypto (cs $+ (c_id,c)) msg.
  Proof.
    intros.
    unfold findKeysCrypto.
    destruct msg; eauto.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    simpl in *.
    specialize (H0 _ eq_refl); contradiction.
  Qed.
  
  Lemma merge_findKeysCrypto_addnl_cipher :
    forall {t} (msg : crypto t) cs c_id c ks,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> ks $k++ findKeysCrypto cs msg = ks $k++ findKeysCrypto (cs $+ (c_id,c)) msg.
  Proof.
    intros.
    erewrite findKeysCrypto_addnl_cipher; trivial.
  Qed.

  Lemma msg_signed_addressed_addnl_cipher :
    forall {t} (msg : crypto t) cs c_id c honestk suid,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> msg_signed_addressed honestk cs suid msg =
        msg_signed_addressed honestk (cs $+ (c_id,c)) suid msg.
  Proof.
    intros.
    match goal with
    | [ |- msg_signed_addressed ?honk ?cs ?suid ?msg = _ ] =>
      case_eq (msg_signed_addressed honk cs suid msg)
    end; intros; symmetry; eauto using msg_signed_addressed_nochange_addnl_cipher.
  Qed.

  Lemma msg_signed_addressed_nochange_addnl_honest_key :
    forall {t} (msg : crypto t) (gks : keys) honestk cs suid k_id tf,
      ~ In k_id honestk
      -> gks $? k_id = None
      -> (forall k, msg_signing_key cs msg = Some k ->
              gks $? k <> None /\
              (honest_key honestk k ->
               message_no_adv_private honestk cs msg /\ msgCiphersSignedOk honestk cs msg))
      -> msg_signed_addressed honestk cs suid msg = tf
      -> msg_signed_addressed (honestk $+ (k_id,true)) cs suid msg = tf.
  Proof.
    destruct tf; eauto using msg_signed_addressed_addnl_honest_key; intros.
    unfold msg_signed_addressed in *; intros.
    rewrite andb_false_iff in *; split_ors; eauto.
    left.
    unfold msg_honestly_signed in *.
    destruct (msg_signing_key cs msg); eauto.
    unfold honest_keyb in *.
    destruct (k_id ==n k); subst; clean_map_lookups; eauto.
    specialize (H1 _ eq_refl); split_ands; contradiction.
  Qed.

  Lemma honestk_merge_new_msgs_keys_same :
    forall honestk cs  {t} (msg : crypto t),
      message_no_adv_private honestk cs msg
      -> (honestk $k++ findKeysCrypto cs msg) = honestk.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    solve_perm_merges; eauto;
      specialize (H _ _ Heq0); clean_map_lookups; eauto.
  Qed.

  Lemma honestk_merge_new_msgs_keys_dec_same :
    forall honestk {t} (msg : message t),
      (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
      -> (honestk $k++ findKeysMessage msg) = honestk.
  Proof.
    intros.
    apply map_eq_Equal; unfold Equal; intros.
    solve_perm_merges; eauto;
      specialize (H _ _ Heq0); clean_map_lookups; eauto.
  Qed.

  (* need to know that msg, if cipher, is in cs *)
  Lemma updateTrackedNonce_addnl_cipher :
    forall suid nons cs {t} (msg : crypto t) c_id c,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> updateTrackedNonce suid nons cs msg =
        updateTrackedNonce suid nons (cs $+ (c_id, c)) msg.
  Proof.
    intros.
    unfold updateTrackedNonce.
    destruct msg; eauto.
    destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
    specialize (H0 _ eq_refl); contradiction.
  Qed.

  Lemma msg_not_accepted_pattern_addnl_cipher :
    forall {t} (msg : crypto t) cs suid froms pat c_id c,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> ~ msg_accepted_by_pattern cs suid froms pat msg
      -> ~ msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg.
  Proof.
    intros.
    unfold not.
    destruct pat; intros; eauto;
      repeat
        match goal with
        | [ H : msg_accepted_by_pattern _ _ _ _ _ |- _ ] => invert H
        | [ H : _ $+ (?cid1,_) $? ?cid2 = _ |- _ ] => destruct (cid1 ==n cid2); subst; clean_map_lookups
        | [ H : ?cs $? ?cid = None,
                H1 : (forall c_id, _ = Some c_id -> ?cs $? c_id <> None) |- _ ] => simpl in H1; specialize (H1 _ eq_refl); contradiction
        | [ H : ~ msg_accepted_by_pattern ?cs ?to ?froms ?pat ?m |- _ ] =>
          assert (msg_accepted_by_pattern cs to froms pat m) by (econstructor; eauto); contradiction
        end.
  Qed.

  Lemma msg_accepted_pattern_addnl_cipher :
    forall {t} (msg : crypto t) cs suid froms pat c_id c,
      ~ In c_id cs
      -> msg_accepted_by_pattern cs suid froms pat msg
      -> msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg.
  Proof.
    intros * NOTIN H; invert H; eauto.
  Qed.


  Lemma msg_accepted_pattern_addnl_cipher_inv :
    forall {t} (msg : crypto t) cs suid froms pat c_id c,
      ~ In c_id cs
      -> (forall cid, msg_cipher_id msg = Some cid -> cs $? cid <> None)
      -> msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg
      -> msg_accepted_by_pattern cs suid froms pat msg.
  Proof.
    intros * NOTIN INCS H; invert H; eauto;
      destruct (c_id ==n c_id0); subst;
        clean_map_lookups; eauto;
          simpl in INCS; specialize (INCS _ eq_refl);
            contradiction.
  Qed.

  Lemma findKeysCrypto_addnl_cipher' :
    forall cs cid1 c cid2 t,
      cid1 <> cid2
      -> @findKeysCrypto t (cs $+ (cid1, c)) (SignedCiphertext cid2) =
        @findKeysCrypto t cs (SignedCiphertext cid2).
  Proof.
    intros.
    unfold findKeysCrypto in *; clean_map_lookups; eauto.
  Qed.

  Lemma updateTrackedNonce_addnl_cipher' :
    forall cs cid1 c cid2 t nons suid,
      cid1 <> cid2
      -> @updateTrackedNonce t suid nons cs (SignedCiphertext cid2) =
        @updateTrackedNonce t suid nons (cs $+ (cid1, c)) (SignedCiphertext cid2).
  Proof.
    intros.
    unfold updateTrackedNonce; clean_map_lookups; eauto.
  Qed.

  Hint Resolve
       findKeysCrypto_addnl_cipher
       merge_findKeysCrypto_addnl_cipher
       updateTrackedNonce_addnl_cipher
       updateTrackedNonce_addnl_cipher'
       msg_signed_addressed_addnl_cipher
       msg_signed_addressed_nochange_addnl_honest_key
       msg_accepted_pattern_addnl_cipher
       msg_accepted_pattern_addnl_cipher_inv
       msg_not_accepted_pattern_addnl_cipher
       : core.

  Import SimulationAutomation.
  Import AdversarySafety.Automation.

  Ltac step_usr uid :=
    match goal with
    | [ H : RealWorld.step_user _ (Some uid) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
      match cmd with
      | Return _ => apply step_user_inv_ret in H; contradiction
      | Bind _ _ => apply step_user_inv_bind in H; split_ands; split_ors; split_ands; subst; try discriminate
      | Gen => apply step_user_inv_gen in H
      | Send _ _ => apply step_user_inv_send in H
      | Recv _ => apply step_user_inv_recv in H
      | SignEncrypt _ _ _ _ => apply step_user_inv_enc in H
      | Decrypt _ => apply step_user_inv_dec in H
      | Sign _ _ _ => apply step_user_inv_sign in H
      | Verify _ _ => apply step_user_inv_verify in H
      | GenerateSymKey _ => apply step_user_inv_gensym in H
      | GenerateAsymKey _ => apply step_user_inv_genasym in H
      | _ => idtac "***Missing inversion: " cmd; invert H
      end
    end; split_ex; split_ors; split_ex; subst.

  Definition buildUniverse_step {A B} (ds : data_step0 A B (Base A)) (uid : user_id) : universe A B  :=
    let '(usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) := ds
    in  buildUniverse usrs adv cs gks uid
                      (mkUserData ks cmd qmsgs mycs froms sents cur_n).

  Lemma commutes_sound' :
    forall {A B C D} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B C),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall (bd2 bd2' : data_step0 A B D) lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs cs1 cs' (usrs1 usrs1' usrs2 usrs2' : honest_users A) (adv adv1 adv' : user_data B) gks gks1 gks'
              ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2'
              cmdc1 cmdc1' cmdc2 qmsgs2'' s,

              bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2'', mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
              (* allow protocol to freely vary, since we won't be looking at it *)
              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs1 $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs1' $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2'' mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1')
              -> encrypted_ciphers_ok (findUserKeys usrs1) cs gks
              -> message_queues_ok cs usrs1 gks
              -> keys_and_permissions_good gks usrs1 adv.(key_heap)
              -> user_cipher_queues_ok cs (findUserKeys usrs1) usrs1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2
                                  
              (* no recursion *)
              -> nextAction cmd1 cmd1

              -> nextAction cmd2 cmd2
              -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n <> Send x m)

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                      step_user lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl4 suid1 bd4 bd4'
                      /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') = 
                          usrs2' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs2' mycs2' froms2' sents2' cur_n2') )
  .
  Proof.
    intros
    ; cases cmd1; cases cmd2
    ; subst
    ; repeat
        match goal with
        | [ ARG : nextAction (Send ?u ?msg) (Send ?u ?msg) , H : (forall c _ _ _, nextAction (Send ?u ?msg) c -> c <> _) |- _ ] =>
          specialize (H _ u _ msg ARG); contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : ?uid1 <> ?uid2 , USRS : _ $+ (?uid1,_) $? ?uid2 = _ |- _ ] => rewrite add_neq_o in USRS by congruence
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; contradiction
        end
    ; step_usr u_id1; step_usr u_id2
    ; try match goal with
      | [ NA : nextAction (Recv _) _ ,
          OK : message_queues_ok ?cs ?us ?gks ,
          US1 : ?us $? _ = Some _ ,
          US2 : ?us $? _ = Some _
          |- _ ] =>
        generalize (Forall_natmap_in_prop _ OK US1)
        ; generalize (Forall_natmap_in_prop _ OK US2)
        ; simpl; intros
      end.

    Ltac process_next_cmd_safe :=
      match goal with
      | [ H : next_cmd_safe _ _ _ _ _ ?c |- _] =>
        let NA := fresh "NA" in 
        match c with
        | (Bind (Return ?r) ?c2) =>
          assert (nextAction c (Return r)) as NA by (repeat econstructor)
        | _ =>
          assert (nextAction c c) as NA by econstructor
        end
        ; specialize (H _ _ NA)
        ; simpl in H
        ; split_ex
      end.

    Ltac solver1 :=
      match goal with
      | [ H : msg_accepted_by_pattern _ _ _ ?pat _ |- step_user _ _ (_,_,_,_,_,_,_,_,_,_,Recv ?pat) _ ] =>
        eapply StepRecv
      | [ H : ~ msg_accepted_by_pattern _ _ _ ?pat _ |- step_user _ _ (_,_,_,_,_,_,_,_,_,_,Recv ?pat) _ ] =>
        eapply StepRecvDrop
      | [ |- step_user _ _ _ _ ] => econstructor
      | [ |- _ = _ ] => reflexivity

      | [ |- context [ findUserKeys (_ $+ (_,_)) ]] => autorewrite with find_user_keys
      | [ |- context [ findKeysCrypto (_ $+ (_,_)) _ ]] => 
        erewrite <- findKeysCrypto_addnl_cipher by eauto
      | [ |- context [ updateTrackedNonce _ _ (_ $+ (_,_)) _ ]] => 
        erewrite <- updateTrackedNonce_addnl_cipher by eauto
      | [ H : message_queue_ok _ _ (_ :: _) _ |- _ ] => invert H; split_ex
      | [ |- context [ msg_signed_addressed (?honk $+ (_,true)) _ _ _ ]] =>
        erewrite msg_signed_addressed_nochange_addnl_honest_key
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- ?m $? ?k2 = _ ] =>
        (progress clean_map_lookups)
         || (destruct (k1 ==n k2); subst)

      | [ KPG : keys_and_permissions_good ?gks ?usrs _, GKS : ?gks $? ?kid = None, KS : ?ks $? ?kid = Some _ |- _ ] =>
        keys_and_permissions_prop; permission_heaps_prop
      | [ H : ~ In ?cid1 (?cs $+ (?cid2,_)) |- ~ In ?cid1 ?cs ] =>
        rewrite not_find_in_iff in H; destruct (cid1 ==n cid2); subst; clean_map_lookups
      | [ |- (if ?fi then _ else _) = (if ?fi then _ else _) ] =>
        destruct fi

      | [ H : (forall _, msg_signing_key ?cs ?m = Some _ -> _) ,
          MHS : msg_honestly_signed _ _ ?m = true
          |- _ ] =>
        generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ex;
        eapply msg_honestly_signed_signing_key_honest in MHS; eauto;
        specialize_simply

      | [ H : msg_accepted_by_pattern ?cs _ _ ?pat ?m , SAFE : next_cmd_safe ?honk _ _ _ _ (Recv ?pat) |- _ ] =>
        repeat process_next_cmd_safe;
        assert (msg_honestly_signed honk cs m = true) by eauto
                                                           
      | [ H : message_no_adv_private _ ?cs ?msg |- context [ _ $k++ findKeysCrypto ?cs ?msg ]] =>
        rewrite honestk_merge_new_msgs_keys_same by eassumption
                 
      | [ |- context [ if msg_signed_addressed ?honk (?cs $+ (_,_)) ?suid ?m then _ else _ ]] =>
        erewrite <- msg_signed_addressed_addnl_cipher by eauto; 
        destruct (msg_signed_addressed honk cs suid m); subst

      | [ |- context [ _ $k++ findKeysMessage _ ]] =>
        (do 2 user_cipher_queues_prop); encrypted_ciphers_prop;
        rewrite honestk_merge_new_msgs_keys_dec_same by eassumption

      | [ H : keys_and_permissions_good _ ?usrs _ |- ~ In ?kid (findUserKeys ?usrs) ] =>
        keys_and_permissions_prop; clean_map_lookups;
        case_eq (findUserKeys usrs $? kid); intros
                                                                                
      | [ GOOD : permission_heap_good ?gks ?ks ,
          NIN : ?gks $? ?kid = None ,
          FK : ?ks $? ?kid = Some _
        |- _ ] =>
        specialize (GOOD _ _ FK); split_ex; contra_map_lookup

      | [ |- None = Some _ ] => exfalso
      | [ |- Some _ = None ] => exfalso

      | [ |- _ $+ (?u_id1,_) = _ $+ (?u_id2,_) ] =>
        apply map_eq_Equal; unfold Equal;
        let y := fresh "y"
        in intros y; destruct (y ==n u_id1); destruct (y ==n u_id2); subst; clean_map_lookups; trivial

      | [ |- False ] =>
        solve [ user_cipher_queues_prop; user_cipher_queues_prop ]
      end.
    
    all: solve [ (do 12 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; eauto ].
  Qed.

  Lemma commutes_sound_send :
    forall {A B D} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B (Base Unit)),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall (bd2 bd2' : data_step0 A B D) lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs cs1 cs' (usrs1 usrs1' usrs2 usrs2' : honest_users A) (adv adv1 adv' : user_data B) gks gks1 gks'
              ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2'
              cmdc1 cmdc1' cmdc2 u {t} (m : crypto t) s qmsgs2'',

              bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> cmd1 = Send u m
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                         
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2'', mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
              (* allow protocol to freely vary, since we won't be looking at it *)
              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs1 $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs1' $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2'' mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1')
              -> encrypted_ciphers_ok (findUserKeys usrs1) cs gks
              -> message_queues_ok cs usrs1 gks
              -> keys_and_permissions_good gks usrs1 adv.(key_heap)
              -> user_cipher_queues_ok cs (findUserKeys usrs1) usrs1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2
                                  
              (* no recursion *)
              (* -> nextAction cmd1 cmd1 *)
              -> nextAction cmd2 cmd2
              (* -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n = Send x m) *)

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                    step_user lbl3 suid2 bd3 bd3'
                    /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                    /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                    /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                    /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                    /\ step_user lbl4 suid1 bd4 bd4'
                    /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') =
                        usrs2' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs2' mycs2' froms2' sents2' cur_n2') )
  .
  Proof.
    intros
    ; cases cmd2
    ; repeat
        match goal with
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction
        end
    ; subst
    ; destruct (u ==n u_id2); subst
    ; step_usr u_id1; step_usr u_id2.

    all: clean_map_lookups; subst.

    Ltac stuff :=
      repeat
        match goal with
        | [ H : next_cmd_safe _ _ _ _ _ (Send _ _) |- _ ] => process_next_cmd_safe; subst
        | [ |- context [ findKeysCrypto (_ $+ (?cid1,_)) (SignedCiphertext ?cid2) ]] =>
          destruct (cid1 ==n cid2); subst; clean_map_lookups; rewrite findKeysCrypto_addnl_cipher'
        | [ |- context [ updateTrackedNonce _ _ (_ $+ (?cid1,_)) (SignedCiphertext ?cid2) ]] =>
          destruct (cid1 ==n cid2); subst; clean_map_lookups; eauto
        | [ |- exists _, _ /\ _ ] =>
          solve [ try unfold add_key_perm
                  ; eexists; simpl; split; [ clean_map_lookups; simpl; eauto | maps_equal ]]
        end; eauto.

    all :
      try
        solve [
          (do 12 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; try congruence; eauto; stuff ] .
  Qed.

  Lemma commutes_sound_recur_cmd1' :
    forall {A B C D} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B C),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall (bd2 bd2' : data_step0 A B D) lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs cs1 cs' (usrs1 usrs1' usrs2 usrs2' : honest_users A) (adv adv1 adv' : user_data B) gks gks1 gks'
              ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2'
              cmdc1 cmdc1' cmdc2 qmsgs2'' s,

              bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2'', mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
              (* allow protocol to freely vary, since we won't be looking at it *)
              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs1 $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs1' $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2'' mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1')
              -> encrypted_ciphers_ok (findUserKeys usrs1) cs gks
              -> message_queues_ok cs usrs1 gks
              -> keys_and_permissions_good gks usrs1 adv.(key_heap)
              -> user_cipher_queues_ok cs (findUserKeys usrs1) usrs1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2
                                  
              (* no recursion *)
              (* -> nextAction cmd1 cmd1 *)
              -> nextAction cmd2 cmd2
              (* -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n <> Send x m) *)

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                      step_user lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl4 suid1 bd4 bd4'
                      /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmdc1' qmsgs1' mycs1' froms1' sents1' cur_n1') = 
                          usrs2' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs2' mycs2' froms2' sents2' cur_n2') )
  .
  Proof.
    induction 1; inversion 5; inversion 1
    ; intros
    ; repeat
        match goal with
        | [ ARG : nextAction (Send ?u ?msg) (Send ?u ?msg) , H : (forall c _ _ _, nextAction (Send ?u ?msg) c -> c <> _) |- _ ] =>
          specialize (H _ u _ msg ARG); contradiction
        | [ H : nextAction (Recv _) _  |- _ ] => msg_queue_prop; msg_queue_prop; clear H
        (* | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction *)
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction
        end
    ; subst; eauto.

    Hint Extern 1 (forall _ _ _ _, nextAction _ _ -> _ <> _ ) => intros * NA; invert NA; congruence : core.

    all : try solve [ eapply commutes_sound'; clean_map_lookups; eauto; econstructor; eauto ].

    - specialize (IHstep_user eq_refl).
      clean_context.
      specialize (IHstep_user _ _ _ _ _ H1 eq_refl H3).
      specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                              _ _ _ _ _ _ _ _ _ _ _ _ cmdc1' _ _ s
                              eq_refl eq_refl eq_refl eq_refl H30 H31).
      specialize_simply.
      apply next_action_next_cmd_safe_bind in H38.
      invert H41.
      specialize_simply.
      specialize (IHstep_user _ cmdc2' eq_refl).
      split_ex; subst.
      (do 12 eexists); repeat simple apply conj; eauto.
      econstructor; eauto.

    - cases cmd2;
        repeat 
        match goal with
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction
        end; step_usr u_id2
        ; (do 12 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; eauto.

    - simpl.
      eapply commutes_sound_send; eauto.
      econstructor; eauto.

  Qed.

  Lemma step_no_depend_other_usrs_program :
    forall {A B C} suid u_id1 lbl bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id1

      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n',

          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

          -> forall cmdc cmdc' u_id2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2,
              u_id1 <> u_id2
              -> usrs $? u_id2 = Some (mkUserData ks2 cmdc qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> exists ks2' qmsgs2' mycs2' froms2' sents2' cur_n2',
                  usrs' $? u_id2 = Some (mkUserData ks2' cmdc qmsgs2' mycs2' froms2' sents2' cur_n2')
                  /\ step_user lbl (Some u_id1)
                              (usrs $+ (u_id2, mkUserData ks2 cmdc' qmsgs2 mycs2 froms2 sents2 cur_n2)
                               , adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                              (usrs' $+ (u_id2, mkUserData ks2' cmdc' qmsgs2' mycs2' froms2' sents2' cur_n2')
                               , adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd').
  Proof.
    induct 1; inversion 2; inversion 1; intros; subst; clean_map_lookups.

    - specialize (IHstep_user eq_refl).
      specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _
                              _ _ _ _ _ _ _ _ _ _ _
                              eq_refl eq_refl).
      specialize (IHstep_user _ cmdc' _ _ _ _ _ _ _
                              H14 H26).
      clean_context.
      split_ex.
      (do 6 eexists); split; eauto.
      econstructor; eauto.

    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
      autorewrite with find_user_keys; trivial.
    - destruct (u_id2 ==n rec_u_id); subst; clean_map_lookups; simpl in *.
      (do 6 eexists); split; [ | econstructor]; try congruence; eauto.
      (do 6 eexists); split; [ | econstructor]; try congruence; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
    - (do 6 eexists); split; [ | econstructor]; eauto.
  Qed.

  Lemma commutes_sound_recur' :
    forall {A B} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B (Base A)),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall (bd2 bd2' : data_step0 A B (Base A)) lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs cs1 cs' (usrs1 usrs1' usrs2 usrs2' : honest_users A) (adv adv1 adv' : user_data B) gks gks1 gks'
              ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' cmd1 cmd1' froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' s qmsgs2'',

              bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              (* allow protocol to freely vary, since we won't be looking at it *)
              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs1 $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs1' $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2'' mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2'', mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
              -> encrypted_ciphers_ok (findUserKeys usrs1) cs gks
              -> message_queues_ok cs usrs1 gks
              -> keys_and_permissions_good gks usrs1 adv.(key_heap)
              -> user_cipher_queues_ok cs (findUserKeys usrs1) usrs1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1
              -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2

              -> forall E (cmd__i2 : user_cmd E),
                  nextAction cmd2 cmd__i2
                  -> summarize cmd1 s
                  -> commutes cmd__i2 s

                  -> forall bd3,
                      bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                      -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                        step_user lbl3 suid2 bd3 bd3'
                        /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                        /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmd2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                        /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                        /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                        /\ step_user lbl4 suid1 bd4 bd4'
                        /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1') =
                            usrs2' $+ (u_id2, mkUserData ks2' cmd2' qmsgs2' mycs2' froms2' sents2' cur_n2') )
  .
  Proof.
    intros; subst; clean_map_lookups.

    specialize (nextAction_couldBe H18).
    cases cmd__i2; intros; try contradiction; clean_context.

    - eapply step_na_return in H18; eauto; split_ands; subst.
      eapply step_no_depend_other_usrs_program in H; eauto; split_ex.
      (do 12 eexists); repeat simple apply conj; eauto.
      maps_equal; eauto.

      Ltac setup uid cmd1 :=
        match goal with
        | [ NA : nextAction ?c2 ?c
          , STEP : step_user _ (Some uid) _ _
          , NCS : next_cmd_safe _ _ _ _ _ ?c2 |- _ ] => 
          let NACMD2 := fresh "NACMD2" in
          generalize NA; intros NACMD2
        ; eapply step_na_not_return in NA; eauto; split_ex; subst; try congruence
        ; eapply commutes_sound_recur_cmd1' with (cmd2 := cmd1) (cmd3 := c) in STEP; eauto
        ; specialize (NCS _ _ NACMD2); simpl in NCS
        end.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      unfold next_cmd_safe; intros * NCSNA; invert NCSNA; eauto.
      
  Qed.

  Lemma impact_from_other_user_step :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
    
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
      u_id1 u_id2 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C),
    
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid1 = Some u_id1
      -> u_id1 <> u_id2
      -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
          usrs $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
          -> exists m,
            usrs' $? u_id2 = Some (mkUserData ks2 cmd2 (qmsgs2 ++ m) mycs2 froms2 sents2 cur_n2).
  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end;
      clean_map_lookups;
      try solve [ exists []; rewrite app_nil_r; trivial ];
      eauto.

    destruct (rec_u_id ==n u_id2); subst; clean_map_lookups;
      repeat simple apply conj; trivial; eauto.
    exists []; rewrite app_nil_r; trivial.
  Qed.

  Lemma impact_from_other_user_step_commutes :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
    
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
      u_id1 u_id2 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C) s,
    
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid1 = Some u_id1
      -> u_id1 <> u_id2
      -> forall D (cmd'' : user_cmd D),
          nextAction cmd cmd''
          -> commutes cmd'' s
          -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
              usrs $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs' $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2).
  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end; eauto.

    - invert H16.
      eapply IHstep_user; eauto.
    - invert H23; eauto.
    
  Qed.

  Lemma step_addnl_msgs :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
    
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
          u_id1 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C) ms,
    
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> suid1 = Some u_id1
        -> step_user lbl suid1
                    (usrs, adv, cs, gks, ks, qmsgs ++ ms, mycs, froms, sents, cur_n, cmd)
                    (usrs', adv', cs', gks', ks', qmsgs' ++ ms, mycs', froms', sents', cur_n', cmd').

  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end;
      clean_map_lookups;
      eauto.

    rewrite <- app_comm_cons; eauto.
    rewrite <- app_comm_cons; eauto.
    econstructor; eauto.
    congruence.
  Qed.

  Hint Resolve step_addnl_msgs : core.

  Lemma commutes_sound :
    forall {A B} (U__r : universe A B) lbl1 u_id1 u_id2 userData1 userData2 bd1,
      U__r.(users) $? u_id1 = Some userData1
      -> U__r.(users) $? u_id2 = Some userData2
      -> honest_cmds_safe U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> step_user lbl1 (Some u_id1) (build_data_step U__r userData1) bd1
      -> forall U__r' lbl2 bd1' userData2',
          U__r' = buildUniverse_step bd1 u_id1
          -> u_id1 <> u_id2
          -> U__r'.(users) $? u_id2 = Some userData2'
          -> step_user lbl2 (Some u_id2) (build_data_step U__r' userData2') bd1'
          -> forall C (cmd__n : user_cmd C) s,
              nextAction userData2.(protocol) cmd__n
              -> summarize userData1.(protocol) s
              -> commutes cmd__n s

          -> exists U__r'' lbl3 lbl4 bd3 bd3' userData1',
                step_user lbl3 (Some u_id2) (build_data_step U__r userData2) bd3
              /\ U__r'' = buildUniverse_step bd3 u_id2
              /\ U__r''.(users) $? u_id1 = Some userData1'
              /\ step_user lbl4 (Some u_id1) (build_data_step U__r'' userData1') bd3'
              /\ buildUniverse_step bd3' u_id1 = buildUniverse_step bd1' u_id2
  .
  Proof.
    intros.
    destruct U__r; destruct U__r'; simpl in *.
    destruct userData1; destruct userData2; destruct userData2'; simpl in *.
    unfold universe_ok, adv_universe_ok in *; split_ands.
    unfold build_data_step, buildUniverse_step, buildUniverse in *; simpl in *.

    Ltac dt bd :=
      destruct bd as [[[[[[[[[[?usrs ?adv] ?cs] ?gks] ?ks] ?qmsgs] ?mycs] ?froms] ?sents] ?cur_n] ?cmd].

    dt bd1; dt bd1'.
    clean_context; subst.
    
    repeat 
      match goal with
      | [ H : {| users := _ |} = _ |- _ ] => invert H; clean_map_lookups
      | [ H : honest_cmds_safe _ , US1 : _ $? u_id1 = _ , US2 : _ $? u_id2 = _ |- _ ] =>
        generalize (H _ _ _ eq_refl US1)
        ; generalize (H _ _ _ eq_refl US2)
        ; clear H; intros; simpl in *
      end.

    specialize (impact_from_other_user_step H4 eq_refl eq_refl eq_refl H6 H0); intros; split_ex; clean_map_lookups.
    assert (u_id2 <> u_id1) as UNE by congruence.

    eapply commutes_sound_recur' in H8; try reflexivity; try eassumption; split_ex; subst.
    (do 6 eexists); repeat simple apply conj; simpl; eauto.
    specialize (impact_from_other_user_step_commutes H8 s eq_refl eq_refl eq_refl UNE H9 H11 H); intros; eauto.
    all: simpl; clean_map_lookups; eauto.
    simpl; rewrite H24; eauto.
  Qed.

  (* rather than just running last user, need some computation that finds next available person to run 
   * 
   * does this really do what I want it to?
   *)

  Require Import Classical.

  Lemma has_user_step {A B} (U : universe A B) (u_id : user_id) :
    forall u_d,
      U.(users) $? u_id = Some u_d
      -> (exists lbl U', step_user lbl (Some u_id) (build_data_step U u_d) U')
        \/ (forall lbl U', ~ step_user lbl (Some u_id) (build_data_step U u_d) U').
  Proof.
    intros.

    remember (forall p, let '(lbl,U') := p in ~ step_user lbl (Some u_id) (build_data_step U u_d) U') as PRED.
    specialize (classic PRED); intros.
    split_ors; subst.
    - right; intros.
      remember (lbl,U') as p.
      specialize (H0 p); destruct p; invert Heqp; eauto.

    - left.
      apply not_all_ex_not in H0; split_ex.
      destruct x; eauto.
      apply NNPP in H0; eauto.
  Qed.

  (* Inductive nextStep {A B} (U : universe A B) : *)
  (*   forall (usrs : list (user_id * user_data A)), (forall uid ud, List.In (uid,ud) usrs -> U.(users) $? uid = Some ud) -> Prop := *)

  (* | Here : forall us us' mapIn lbl bd' u_id userData, *)
  (*     us = (u_id,userData) :: us' *)
  (*     -> step_user lbl (Some u_id) (build_data_step U userData) bd' *)
  (*     -> nextStep U us mapIn *)

  (* | There : forall us us' mapIn mapIn' u_id userData, *)
  (*     us = (u_id,userData) :: us' *)
  (*     -> (forall lbl bd', ~ step_user lbl (Some u_id) (build_data_step U userData) bd') *)
  (*     -> nextStep U us' mapIn' *)
  (*     -> nextStep U us mapIn *)
  (* . *)

  Definition summarize_univ {A B} (U : universe A B) (summaries : NatMap.t summary) : Prop :=
    forall u_id u_d s,
      U.(users) $? u_id = Some u_d
      -> summaries $? u_id = Some s
      /\ summarize u_d.(protocol) s.

  Inductive nextStep {A B} (U : universe A B) :
    list (user_id * user_data A) -> Prop :=

  | Here : forall us us' lbl bd' u_id userData,
      us = (u_id,userData) :: us'
      -> step_user lbl (Some u_id) (build_data_step U userData) bd'
      -> nextStep U us

  | There : forall us us' u_id userData summaries,
      us = (u_id,userData) :: us'
      -> summarize_univ U summaries
      -> (forall lbl bd', ~ step_user lbl (Some u_id) (build_data_step U userData) bd')
      \/ (exists u_id2 userData2, u_id <> u_id2
                          /\ U.(users) $? u_id2 = Some userData2
                          /\ forall t (cmd__n : user_cmd t) s,
                              nextAction userData2.(protocol) cmd__n
                              -> summaries $? u_id = Some s
                              -> commutes cmd__n s
                              -> False)
      -> nextStep U us'
      -> nextStep U us
  .
  
  Lemma elements_in {V} (m : NatMap.t V) :
    forall uid ud,
      List.In (uid,ud) (elements m)
      -> m $? uid = Some ud.
  Proof.
    intros.
    rewrite <- find_mapsto_iff, elements_mapsto_iff.
    rewrite SetoidList.InA_alt;
      exists (uid,ud); split; eauto.
    econstructor; eauto.
  Qed.

  Definition nextStepU {A B} (U : universe A B) := nextStep U (elements U.(users)).

  Inductive step_universeC {A B} :
    universe A B -> rlabel -> universe A B -> Prop :=
    
  | StepNext : forall U U' (u_id : user_id) us userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd lbl,
      nextStep U ((u_id,userData) :: us)
      -> step_user lbl (Some u_id)
                  (build_data_step U userData)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> U' = buildUniverse usrs adv cs gks u_id {| key_heap  := ks;
                                                   msg_heap  := qmsgs;
                                                   protocol  := cmd;
                                                   c_heap    := mycs;
                                                   from_nons := froms;
                                                   sent_nons := sents;
                                                   cur_nonce := cur_n; |}
      -> step_universeC U lbl U'. 

  (* Definition universeStepCommutes {A B} (U U' : universe A B) : Prop := *)
  (*   forall lbl1 lbl2 U'' u_id1 u_id2 ud1 ud2 bd1 bd2 summaries, *)
  (*     step_universe U lbl1 U' *)
  (*     -> step_universe U' lbl2 U'' *)
  (*     -> U.(users) $? u_id1 = Some ud1 *)
  (*     -> step_user lbl1 (Some u_id1) (build_data_step U ud1) bd1 *)
  (*     -> U'.(users) $? u_id2 = Some ud2 *)
  (*     -> step_user lbl2 (Some u_id2) (build_data_step U' ud2) bd2 *)
  (*     -> u_id1 <> u_id2 *)
  (*     -> summarize_univ U summaries *)
  (*     -> (forall C (cmd__n : user_cmd C) s, *)
  (*         nextAction ud2.(protocol) cmd__n *)
  (*         -> forall uid ud, *)
  (*           uid <> u_id2 *)
  (*           -> U.(users) $? uid = Some ud *)
  (*           -> summarize ud.(protocol) s *)
  (*           -> commutes cmd__n s) *)
  (*     -> True. *)

  (* Lemma commutes_sound_universe : *)
  (*   forall {A B} (U U' U'' : universe A B) lbl1 lbl2, *)
  (*     step_universe U lbl1 U' *)
  (*     -> step_universe U' lbl2 U'' *)
  (*     -> universeStepCommutes U U' *)
  (*     -> exists U''' lbl3 lbl4, *)
  (*         step_user lbl3 (Some u_id2) (build_data_step U__r userData2) bd3 *)
  (*             /\ U__r'' = buildUniverse_step bd3 u_id2 *)
  (*             /\ U__r''.(users) $? u_id1 = Some userData1' *)
  (*             /\ step_user lbl4 (Some u_id1) (build_data_step U__r'' userData1') bd3' *)
  (*             /\ buildUniverse_step bd3' u_id1 = buildUniverse_step bd1' u_id2 *)

  
  
End RealWorldLemmas.
                    

Inductive stepC (t__hon t__adv : type) :
    (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> Prop :=
| RealSilentC : forall ru ru' iu,
    step_universeC ru Silent ru'
    -> stepC (ru, iu) (ru', iu)
| BothLoud : forall ru ru' ra ia iu iu' iu'',
    step_universeC ru (Action ra) ru'
    -> istepSilent^* iu iu'
    (* step silently as far as we can *)
    -> (forall iu''', istepSilent iu iu''' -> False)
    -> IdealWorld.lstep_universe iu' (Action ia) iu''
    -> action_matches ra ru ia iu'
    -> stepC (ru, iu) (ru', iu'').

From protocols
     Require Import
     Sets
     ModelCheck.

Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Definition TrC {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) :=
  {| Initial := {(ru0, iu0)};
     Step    := @stepC t__hon t__adv |}.


Lemma safety_violation_step :
  forall t__hon t__adv st st',
    @step t__hon t__adv st st'
    -> ~ safety st
    -> ~ safety st'.
Proof.
  induct 1; unfold safety; simpl; intros.

Admitted.

Lemma safety_violation_steps :
  forall t__hon t__adv st st',
    (@step t__hon t__adv)^* st st'
    -> ~ safety st
    -> ~ safety st'.
Proof.
  induct 1; eauto using safety_violation_step.
Qed.

Definition almostEqual {A}  (ud ud' : user_data A) :=
  ud = ud' \/
  (exists msg, ud = 
  {|
  key_heap := key_heap ud';
  protocol := protocol ud';
  msg_heap := msg_heap ud' ++ [msg];
  c_heap := c_heap ud';
  from_nons := from_nons ud';
  sent_nons := sent_nons ud';
  cur_nonce := cur_nonce ud' |}).

Lemma non_stepped_ud_almost_equal :
  forall { A B C } suid lbl bd1 bd2,
    step_user lbl suid bd1 bd2
    -> forall (users1 users2 : honest_users A) (adv1 adv2 : user_data B) cs1 cs2 gks1 gks2
        stepper ks1 ks2 qmsgs1 qmsgs2 mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2
        (cmdc1 cmdc2 : user_cmd C) cmd1,
      bd1 = (users1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1)
      -> bd2 = (users2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2)
      -> suid = Some stepper
    -> users1 $? stepper = Some {| key_heap := ks1
                               ; protocol := cmd1
                               ; msg_heap := qmsgs1
                               ; c_heap := mycs1
                               ; from_nons := froms1
                               ; sent_nons := sents1
                               ; cur_nonce := cur_n1 |}
    -> (forall uid ud1 ud2,
          uid <> stepper
          -> users1 $? uid = Some ud1
          -> users2 $? uid = Some ud2
          -> almostEqual ud2 ud1).
Proof.
  induct 1; inversion 1; inversion 1; intros; subst; clean_context; clean_map_lookups; eauto;
    unfold almostEqual; eauto.
  
  destruct (rec_u_id ==n uid); subst; clean_map_lookups; eauto.
Qed.

Lemma different_steps_must_be_by_different_users :
  forall { A B C } (bd1 bd2 bd__other : data_step0 A B C ) lbl1 lbl2 u_id1 u_id2,
    (* lameAdv b bd1.(adversary) *)
    step_user lbl1 (Some u_id1) bd1 bd2
    -> step_user lbl2 (Some u_id2) bd1 bd__other
    -> lbl1 <> lbl2
    -> u_id1 <> u_id2.
Proof.
  (* inversion 2; inversion 1; intros; subst; eauto. *)

  (* destruct ru1.  unfold build_data_step in *. destruct userData. destruct userData0. simpl in *. *)
  (* clean_map_lookups. *)
  (* destruct ru1. destruct adversary. simpl in *. unfold build_data_step in *. simpl in *. *)
  (* rewrite H in H8. invert H8. admit. admit. *)
Admitted.



        (* relation between ru__other ru'' : only A and global state are different *)
(* Definition only_global_or_single_user_state_changed {A B C} (bd1 bd2 : data_step0 A B C) (u_id : user_id) := *)
(*   forall u_id' u_d1 u_d2 ru1 ru2, *)
(*     ru1.(users) $? u_id' = Some u_d1 *)
(*     -> bd1 = build_data_step ru1 u_d1 *)
(*     -> ru2.(users) $? u_id' = Some u_d2 *)
(*     -> u_id' <> u_id *)
(*     -> u_d1 = u_d2. *)

(* Lemma silent_leading_step_preserves_action_matches : *)
(*   forall {A B C} (* (ru ru' ru__other : RealWorld.universe A B) *) ra u_id1 u_id2 (bd bd' bd__other : data_step0 A B C), *)
(*     (* ru = buildUniverse_step bd u_id1 *) *)
(*      step_user Silent (Some u_id1) bd bd' *)
(*      (* -> step_universe ru Silent ru' *) *)
(*      (* -> bd = build_data_step  *) *)
(*     -> step_user (Action ra) (Some u_id2) bd bd__other *)
(*     -> forall (users1 users2 : honest_users A) (adv1 adv2 : user_data B) cs1 cs2 gks1 gks2 *)
(*          ks1 ks2 qmsgs1 qmsgs2 mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2 *)
(*         (cmdc1 cmdc2 : user_cmd C), *)
(*       bd = (users1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1) *)
(*       -> bd' = (users2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2) *)
(*     -> exists bd'' , *)
(*         step_user (Action ra) (Some u_id2) bd' bd'' *)
(*         -> only_global_or_single_user_state_changed bd__other bd'' u_id1. *)
(*         (* -> action_matches (buildUniverse_step bd') ra iu ia = action_matches (buildUniverse_step bd'') ra iu ia. *) *)
(* Proof. *)
(*   induction 1; inversion 2; inversion 1; intros; subst; eauto. *)
(*   clear H1. clear H2. eexists.  *)
  
  
Lemma silent_step_blah :     
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc cmdc' u_id1 u_id2 ud2 usrs'',
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> usrs $? u_id2 = Some ud2
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> usrs'' $? u_id2 = Some ud2.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst;
      try discriminate;
      try solve [ clean_map_lookups; trivial ].
  specialize (IHstep_user _ _ _ _ _ _ _ _ _ _ _
                          _ _ _ _ _ _ _ _ _ _ _
                          eq_refl eq_refl eq_refl).
  specialize (IHstep_user cmdc cmdc').
  specialize (IHstep_user _ _ _ _ eq_refl H26 H27 H28 eq_refl).
  clean_map_lookups; eauto.
Qed.

Lemma silent_step_message_eq : 
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> forall cmdc cmdc' u_id1 usrs'' t (m__rw : crypto t) m__iw iu ch_id,
          suid = Some u_id1
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> MessageEq.message_eq
              m__rw
              {| users := usrs $+ (u_id1,
                                   {| key_heap := ks;
                                      protocol := cmdc;
                                      msg_heap := qmsgs;
                                      c_heap := mycs;
                                      from_nons := froms;
                                      sent_nons := sents;
                                      cur_nonce := cur_n |});
                 adversary := adv;
                 all_ciphers := cs;
                 all_keys := gks |} m__iw iu ch_id
          -> usrs'' = usrs' $+ (u_id1, {| key_heap := ks';
                                         protocol := cmdc';
                                         msg_heap := qmsgs';
                                         c_heap   := mycs';
                                         from_nons := froms';
                                         sent_nons := sents';
                                         cur_nonce := cur_n' |})
          -> MessageEq.message_eq
              m__rw
              {| users := usrs'' ;
                 adversary := adv';
                 all_ciphers := cs';
                 all_keys := gks' |} m__iw iu ch_id.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst;
    try discriminate;
    try solve [ clean_map_lookups; trivial ]; eauto.
  - invert H26; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; intros; clean_map_lookups;
      autorewrite with find_user_keys in *; simpl in *; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * (* autorewrite with find_user_keys in *.  simpl. *)
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto. 
      (* destruct data__rw. *)
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := ks';
                            protocol := cmdc;
                            msg_heap := qmsgs';
                            c_heap := mycs';
                            from_nons := froms';
                            sent_nons := sents';
                            cur_nonce := cur_n' |}) .
      clean_map_lookups; eauto. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto. eapply H11; eauto.
    * autorewrite with find_user_keys in *.  simpl.
      destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto.
      destruct data__rw.
      specialize (H11 u).
      eapply H11 with (data__rw :=
                         {| key_heap := key_heap;
                            protocol := cmdc;
                            msg_heap := msg_heap;
                            c_heap := c_heap;
                            from_nons := from_nons;
                            sent_nons := sent_nons;
                            cur_nonce := cur_nonce |}) .
      clean_map_lookups; eauto. assumption. assumption. assumption.
      
      specialize (H11 u). rewrite add_neq_o in H11 by auto.
      eapply H11 with (data__rw :=
                         {| key_heap := key_heap;
                            protocol := protocol;
                            msg_heap := msg_heap;
                            c_heap := c_heap;
                            from_nons := from_nons;
                            sent_nons := sent_nons;
                            cur_nonce := cur_nonce |}); eauto.
     
      eapply H
    autorewrite with find_user_keys in *. destruct data__rw. simpl.
    specialize (H11 u).
    destruct (u_id1 ==n u); subst; clean_map_lookups; simpl in * ; eauto.
    eapply H11 with (data__rw :=
    {| key_heap := key_heap;
    protocol := cmdc;
    msg_heap := msg_heap;
    c_heap := c_heap;
    from_nons := from_nons;
    sent_nons := sent_nons;
    cur_nonce := cur_nonce |}) .
    clean_map_lookups; eauto. assumption. assumption.
Admitted.

Lemma silent_step_then_labeled_step : 
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) u_id1 cmdc cmdc'
        ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' suid2 lbl2,
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Silent
      -> usrs $? u_id1 = Some {| key_heap := ks;
                                protocol := cmdc;
                                msg_heap := qmsgs;
                                c_heap   := mycs;
                                from_nons := froms;
                                sent_nons := sents;
                                cur_nonce := cur_n |}
      -> forall D bd2 bd2',
          step_user lbl2 suid2 bd2 bd2'
          -> forall cmdc2 u_id2 ru ia iu ra
              (cmd2 cmd2' : user_cmd D) ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              froms2 froms2' sents2 sents2' cur_n2 cur_n2',
            suid = Some u_id1
            -> suid2 = Some u_id2
            -> lbl2 = Action ra
            -> bd2 = (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
            -> bd2' = (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
            -> u_id1 <> u_id2
            -> ru = buildUniverse usrs adv cs gks u_id1 {| key_heap  := ks
                                                          ; msg_heap  := qmsgs
                                                          ; protocol  := cmdc
                                                          ; c_heap    := mycs
                                                          ; from_nons := froms
                                                          ; sent_nons := sents
                                                          ; cur_nonce := cur_n |}
            -> action_matches ra ru ia iu
            -> usrs $? u_id2 = Some {| key_heap := ks2;
                                      protocol := cmdc2;
                                      msg_heap := qmsgs2;
                                      c_heap   := mycs2;
                                      from_nons := froms2;
                                      sent_nons := sents2;
                                      cur_nonce := cur_n2 |}
            -> forall ru',
                  (* step_user (Action ra) (Some u_id2) *)
                  (*           (usrs'', adv', cs', gks', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2) *)
                  (*           bd2'' *)
                  ru' = buildUniverse usrs' adv' cs' gks' u_id1 {| key_heap  := ks'
                                                                     ; msg_heap  := qmsgs'
                                                                     ; protocol  := cmdc'
                                                                     ; c_heap    := mycs'
                                                                     ; from_nons := froms'
                                                                     ; sent_nons := sents'
                                                                     ; cur_nonce := cur_n' |}
                  ->  action_matches ra ru' ia iu.
Proof.
  induction 6; inversion 4; inversion 1; intros; subst; try discriminate; clean_context.
  - specialize (IHstep_user _ _ H).
    specialize (IHstep_user _ _ _ _ _ cmdc' eq_refl eq_refl H3).
    specialize (IHstep_user _ _ _ _ _ _ _ _ _ _
                            _ _ _ _ _ _ _ _ _ _
                            eq_refl eq_refl eq_refl eq_refl eq_refl H21 eq_refl H34 H35).
    eapply IHstep_user; eauto.
  - generalize H; intros STEP1.
    eapply silent_step_blah in H; eauto.
    clean_map_lookups.
    invert H41; eauto.
    econstructor; eauto.
    invert H1.
    unfold buildUniverse in *; simpl in *.
    eapply silent_step_message_eq with (u_id3 := u_id1); eauto.
  - generalize H; intros STEP1.
    eapply silent_step_blah in H; eauto.
    clean_map_lookups.
    invert H41; eauto.
    eapply Out; eauto.
    invert H2.
    unfold buildUniverse in *; simpl in *.
    eapply silent_step_message_eq with (u_id3 := u_id1); eauto.
    Unshelve.
    all: try discriminate; eauto.
Qed.



(*   inversion 1;  intros; subst; eauto; simpl in *. *)
(*   (* inversion 3; inversion 2;  intros; subst; eauto; simpl in *.  *) *)
(*   (* eexists. destruct (nextStep cmd). *) *)
(*   (* invert H13. destruct iu; simpl in *. econstructor. *) *)
(*   (* eauto. eauto. eauto.  *) *)
(* Admitted. *)


Lemma alignment_preservation_step :
  forall t__hon t__adv st st',
    @step t__hon t__adv st st'
    (* -> lameAdv b (fst st).(adversary) *)
    -> labels_align st'
    -> labels_align st.
Proof.


  induct 1; unfold labels_align.
  - intros.  eapply silent_leading_step_preserves_action_matches in H. eexists. eexists. eexists.
    
  (*   eapply silent_leading_step_preserves_action_matches; eauto.  *)
  (*   eapply silent_leading_step_preserves_action_matches in H. *)
  (*   invert H. invert H1. shelve. shelve. *)
  (* - intros. invert H. *)

  (*   invert H. invert H0. *)

 (*   specialize (H0 _ ra). admit. *)
  (* - intros. *)
  (*   eapply H0. invert H1. invert H. eapply H0. specialize (H0 _ _ H1). *)


  (*   intro. intro ru''. intros. specialize (H0 ru'' ra). invert H.    admit. admit. *)
          
  (* - intro. intro ru''. intro ra'. specialize (H3 ru'' ra').  *)
Admitted.


Lemma alignment_perservation_steps :
  forall t__hon t__adv st st' ,
    (@step t__hon t__adv)^* st st'
    (* -> lameAdv b (fst st).(adversary) *)
    -> labels_align st'
    -> labels_align st.
(* a user either has only changed in that it has new messages or a user already had label alignment in st *)
Proof.
  induct 1; eauto using alignment_preservation_step.
Qed.



(*       intros. eapply IHtrc in H1. invert H. destruct z as (ru'', iu''). *)
(*     eauto using alignment_preservation_step. *)

(* Admitted. *)


(* Will probably need to add indexed step relation here for induction 
 * i.e., perform bounded running time analysis and update step to stepi
 * 
 *)

Lemma safety_violations_translate :
  forall t__hon t__adv st st',
    (@step t__hon t__adv)^* st st'
    -> (forall st'', step st' st'' -> False)
    -> ~ safety st'
    -> exists st'',
        (@stepC t__hon t__adv)^* st st''
        /\ ~ safety st''.
Proof.
Admitted.

Lemma alignment_violations_translate :
  forall t__hon t__adv st st',
    (@step t__hon t__adv)^* st st'
    -> (forall st'', step st' st'' -> False)
    -> ~ labels_align st'
    -> exists st'',
        (@stepC t__hon t__adv)^* st st''
        /\ ~ labels_align st''.
Proof.
Admitted.

Theorem step_stepC :
  forall {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon),
  (* summarizeThreads c cs *)
    (* -> boundRunningTime c n *)
    invariantFor (TrC ru0 iu0) (fun st => safety st /\ labels_align st)
    -> invariantFor (S ru0 iu0) (fun st => safety st /\ labels_align st)
.
Proof.
  intros * INV.
  unfold invariantFor in *; intros * INIT.
  simpl in *.
  specialize (INV _ INIT); intros.

  



    


    

  
  
                                  
  Lemma silent_commutes :
    forall {A B} (U__r U__r' : universe A B) (U__i : IdealWorld.universe A) b,
      step_universe U__r Silent U__r'
      -> lameAdv b U__r.(adversary)
      -> labels_align (U__r',U__i)
      -> labels_align (U__r ,U__i).
  Proof.
    intros.
    invert H; destruct U__r; simpl in *.
    - destruct userData; simpl in *.
      eapply silent_commutes'; eauto.
      reflexivity.
      unfold buildUniverse; simpl.
      f_equal.
      maps_equal.

    - unfold lameAdv, build_data_step in *; simpl in *.
      rewrite H0 in *.
      invert H2.
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
  Admitted
       

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
