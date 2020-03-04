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
     List
     JMeq.

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
     (* Sets *)
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

  Inductive nextAction : forall {A B}, user_cmd A -> user_cmd B -> Prop :=
  | NaReturn : forall A (a : << A >>),
      nextAction (Return a) (Return a)
  | NaGen :
      nextAction Gen Gen
  | NaSend : forall t uid (msg : crypto t),
      nextAction (Send uid msg) (Send uid msg)
  | NaRecv : forall t pat,
      nextAction (@Recv t pat) (@Recv t pat)
  | NaSignEncrypt : forall t k__s k__e u_id (msg : message t),
      nextAction (SignEncrypt k__s k__e u_id msg) (SignEncrypt k__s k__e u_id msg)
  | NaDecrypt : forall t (msg : crypto t),
      nextAction (Decrypt msg) (Decrypt msg)
  | NaSign : forall t k u_id (msg : message t),
      nextAction (Sign k u_id msg) (Sign k u_id msg)
  | NaVerify : forall t k (msg : crypto t),
      nextAction (Verify k msg) (Verify k msg)
  | NaGenSymKey : forall usg,
      nextAction (GenerateSymKey usg) (GenerateSymKey usg)
  | NaGenAsymKey : forall usg,
      nextAction (GenerateAsymKey usg) (GenerateAsymKey usg)
  | NaBind : forall A B r (c : user_cmd B) (c1 : user_cmd r) (c2 : << r >> -> user_cmd A),
      nextAction c1 c
      -> nextAction (Bind c1 c2) c
  .

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
    | Send uid _ => False (* For now, be imprecise ~ uid \in s.(sending_to) *)
    | Recv _ => True
    | SignEncrypt _ _ _ _ => True
    | Decrypt _ => True
    | Sign _ _ _ => True
    | Verify _ _ => True
    | GenerateSymKey _ => True
    | GenerateAsymKey _ => True
    | Bind _ _ => False
    end.

  Definition hstep {A B} (lbl : rlabel) (suid : option user_id) (bd bd' : data_step0 A B (Base A)) :=
    step_user lbl suid bd bd'.

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
        /\ cur_n = cur_n'.

  Proof.
    induction 1; inversion 1; inversion 1; intros; subst;
      match goal with
      | [ H : nextAction _ _ |- _ ] => invert H
      end; eauto.

    intuition idtac.
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

  Lemma nextAction_couldBe :
    forall {A B} (c1 : user_cmd A) (c2 : user_cmd B),
      nextAction c1 c2
      -> match c2 with
        | Return _ => True
        | Gen => True
        | Send _ _ => True
        | Recv _ => True
        | SignEncrypt _ _ _ _ => True
        | Decrypt _ => True
        | Sign _ _ _ => True
        | Verify _ _ => True
        | GenerateAsymKey _ => True
        | GenerateSymKey _ => True
        | Bind _ _ => False
        end.
  Proof.
    induction 1; eauto.
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

  (* Lemma msg_no_adv_private_findKeysCrypto_addnl_cipher : *)
  (*   forall {t} (msg : crypto t) honestk cs c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> message_no_adv_private honestk cs msg *)
  (*     -> findKeysCrypto cs msg = findKeysCrypto (cs $+ (c_id,c)) msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold findKeysCrypto. *)
  (*   destruct msg; eauto. *)
  (*   destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto. *)
  (*   unfold message_no_adv_private in H0. *)
  (*   simpl in *. *)
  (*   specialize (H0 _ eq_refl); contradiction. *)
  (* Qed. *)
  
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

  (* Lemma msg_signed_addressed_new_msgs_keys_same : *)
  (*   forall honestk cs suid {t1 t2} (msg1 : crypto t1) (msg2 : crypto t2), *)
  (*     message_no_adv_private honestk cs msg1 *)
  (*     -> msg_signed_addressed (honestk $k++ findKeysCrypto cs msg1) cs suid msg2 = *)
  (*       msg_signed_addressed honestk cs suid msg2. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold msg_signed_addressed; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ |- context [ _ && true ]] => rewrite andb_true_r *)
  (*       | [ |- context [ _ && false ]] => rewrite andb_false_r *)
  (*       | [ |- (_ && ?a) = (_ && ?a) ] => destruct a; subst *)
  (*       end; eauto. *)
  (*   unfold msg_honestly_signed. *)
  (*   destruct (msg_signing_key cs msg2); eauto. *)
  (*   unfold honest_keyb. *)
  (*   solve_perm_merges; eauto; *)
  (*     specialize (H _ _ H1); clean_map_lookups; eauto. *)
  (* Qed. *)

  (* Lemma msg_signed_addressed_new_msgs_keys_dec_same : *)
  (*   forall honestk cs suid {t1 t2} (msg1 : message t1) (msg2 : crypto t2), *)
  (*     (forall k_id kp, findKeysMessage msg1 $? k_id = Some kp -> honestk $? k_id = Some true) *)
  (*     -> msg_signed_addressed (honestk $k++ findKeysMessage msg1) cs suid msg2 = *)
  (*       msg_signed_addressed honestk cs suid msg2. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold msg_signed_addressed; *)
  (*     repeat *)
  (*       match goal with *)
  (*       | [ |- context [ _ && true ]] => rewrite andb_true_r *)
  (*       | [ |- context [ _ && false ]] => rewrite andb_false_r *)
  (*       | [ |- (_ && ?a) = (_ && ?a) ] => destruct a; subst *)
  (*       end; eauto. *)
  (*   unfold msg_honestly_signed. *)
  (*   destruct (msg_signing_key cs msg2); eauto. *)
  (*   unfold honest_keyb. *)
  (*   solve_perm_merges; eauto; *)
  (*     specialize (H _ _ H1); clean_map_lookups; eauto. *)
  (* Qed. *)

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

  Hint Resolve
       findKeysCrypto_addnl_cipher
       merge_findKeysCrypto_addnl_cipher
       updateTrackedNonce_addnl_cipher
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
      | Return _ => invert H
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
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' cmdc1 cmdc1' cmdc2 s,

              bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
              (* allow protocol to freely vary, since we won't be looking at it *)
              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmdc1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs1 $? u_id2 = Some (mkUserData ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2)
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

              -> forall bd3 cmd2'',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4 usrs4',
                      step_user lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmd2'' qmsgs2' mycs2' froms2' sents2' cur_n2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl4 suid1 bd4 bd4'
  .
  Proof.
    intros
    ; cases cmd1; cases cmd2
    ; repeat
        match goal with
        | [ ARG : nextAction (Send ?u ?msg) (Send ?u ?msg) , H : (forall c _ _ _, nextAction (Send ?u ?msg) c -> c <> _) |- _ ] =>
          specialize (H _ u _ msg ARG); contradiction
        | [ H : nextAction (Recv _) _  |- _ ] => msg_queue_prop; msg_queue_prop; clear H
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        (* | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction *)
        end
    ; subst
    ; step_usr u_id1; step_usr u_id2.

    Ltac s1 :=
      match goal with
      | [ |- step_user _ _ _ _ ] => econstructor
      | [ |- context [ findUserKeys (_ $+ (_,_)) ]] => autorewrite with find_user_keys
      | [ H : message_queue_ok _ _ (_ :: _) _ |- context [ findKeysCrypto (_ $+ (_,_)) _ ]] =>
        invert H; split_ands
      | [ H : message_queue_ok _ _ (_ :: _) _ |- context [ updateTrackedNonce _ _ (_ $+ (_,_)) _ ]] =>
        invert H; split_ands
      | [ H : message_queue_ok _ _ (_ :: _) _ |- ~ msg_accepted_by_pattern (_ $+ (_,_)) _ _ _ _ ] =>
        invert H; split_ands
      | [ |- context [ if msg_signed_addressed ?honk ?cs ?suid ?m then _ else _ ]] =>
        erewrite <- msg_signed_addressed_addnl_cipher by eauto; 
        destruct (msg_signed_addressed honk cs suid m); subst
      | [ H : message_queue_ok _ _ (_ :: _) _ |- context [ msg_signed_addressed (?honk $+ (_,true)) _ _ _ ]] =>
        invert H; split_ands;
        erewrite msg_signed_addressed_nochange_addnl_honest_key
      | [ H : keys_and_permissions_good _ ?usrs _ |- ~ In ?kid (findUserKeys ?usrs) ] =>
        keys_and_permissions_prop; unfold not; let IN := fresh "IN" in intro IN; rewrite in_find_iff in IN;
        case_eq (findUserKeys usrs $? kid); intros; try contradiction
      | [ H : permission_heap_good ?gks ?ks, ARG : ?ks $? ?k = Some _, CONT : ?gks $? ?k = None  |- _ ] =>
        specialize (H _ _ ARG); split_ex; contra_map_lookup
      | [ GOOD : keys_and_permissions_good ?gks ?usrs _ ,
          NIN : ?gks $? ?kid = None ,
          IN : ?ks $? ?kid = Some _ ,
          US : _ $? _ = Some (  mkUserData ?ks _ _ _ _ _ _ )
          |- False ] =>
        progress (keys_and_permissions_prop; repeat permission_heaps_prop)
      | [ GOOD : permission_heap_good ?gks ?ks ,
          NIN : ?gks $? ?kid = None ,
          IN : ?ks $? ?kid = Some _ 
          |- False ] =>
        specialize (GOOD _ _ IN); split_ex; contra_map_lookup
      | [ H : ~ In ?cid1 (?cs $+ (?cid2,_)) |- ~ In ?cid1 ?cs ] =>
        rewrite not_find_in_iff in H; destruct (cid1 ==n cid2); subst; clean_map_lookups
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- ?m $? ?k2 = _ ] =>
        (progress clean_map_lookups)
         || (destruct (k1 ==n k2); subst)
      | [ OK : user_cipher_queues_ok ?cs ?honk ?usrs, IN : List.In ?cid _ , CS : ?cs $? ?cid = None |- False ] =>
        progress user_cipher_queues_prop
      | [ |- None = Some _ ] => exfalso
      | [ |- Some _ = None ] => exfalso
      end.

    all: try solve [ do 11 eexists; (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; eauto ].

    Ltac foo :=
      repeat 
        match goal with
        | [ |- context [ _ $k++ findKeysMessage _ ]] =>
          (do 2 user_cipher_queues_prop); encrypted_ciphers_prop;
          rewrite honestk_merge_new_msgs_keys_dec_same by eassumption
        | [ H : message_queue_ok _ _ (existT _ _ ?m :: _) _ |- msg_accepted_by_pattern _ _ _ _ ?m ] =>
          invert H; split_ex

        | [ H : message_no_adv_private _ ?cs ?msg |- context [ _ $k++ findKeysCrypto ?cs ?msg ]] =>
          rewrite honestk_merge_new_msgs_keys_same by eassumption
        | [ H : (honest_key _ ?k -> _) ,
                ARG : honest_key _ ?k
            |- _ ] =>
          specialize (H ARG); split_ands
        | [ H : (forall _, msg_signing_key ?cs ?m = Some _ -> _) ,
                ARG : msg_signing_key ?cs ?m = Some ?k ,
                      ARG2 : honest_key _ ?k
            |- _ ] =>
          specialize (H _ ARG); split_ands
        | [ MQOK : message_queue_ok _ _ (existT _ _ ?msg :: _) _ ,
                   MHS : msg_honestly_signed _ _ ?msg = true
            |- context [ _ $k++ findKeysCrypto _ ?msg ]] =>
          invert MQOK;
          generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ex;
          eapply msg_honestly_signed_signing_key_honest in MHS; eauto
        | [ H : msg_accepted_by_pattern ?cs _ _ ?pat ?msg ,
                NCS : next_cmd_safe ?honk ?cs _ _ _ (Recv ?pat)
            |- context [ _ $k++ findKeysCrypto _ ?msg ]] =>
          invert NCS; assert (msg_honestly_signed honk cs msg = true) by eauto
        | [ |- (if ?fi then _ else _) = (if ?fi then _ else _) ] =>
          destruct fi
        | [ |- _ = _ ] => solve [ eauto | symmetry; eauto ]
        end.

    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
    (do 11 eexists); (repeat simple apply conj); try reflexivity; repeat s1; eauto; repeat s1; foo; eauto.
  Qed.




  
  Lemma commutes_sound' :
    forall {A B C} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B C),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall bd2 bd2' lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs1 cs1' cs1'' (usrs1 usrs1': honest_users A) (adv1 adv1' adv1'' : user_data B) gks1 gks1' gks1''
              (cmd__n1 cmd__n1' : user_cmd C) ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1'
              (cmd1 cmd1' cmd2 cmd2': user_cmd (Base A))
              froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              usrs2 usrs2' ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              (* (cmd__n2 cmd__n2' : user_cmd D) *)
              froms2 froms2' sents2 sents2' cur_n2 cur_n2' s,

                bd1 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n1)
              -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n1')
              -> bd2 = (usrs2, adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv1'', cs1'', gks1'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

              (* build link to overall user command *)
              -> nextAction cmd1 cmd__n1
              -> (forall r, cmd__n1 <> Return r)
              -> (exists f, cmd1 = f cmd__n1
                    /\ cmd1' = f cmd__n1'
                     /\ forall lbl5 suid5 (usrs5 usrs5' : honest_users A) (adv5 adv5' : user_data B)
                        cs5 cs5' gks5 gks5'
                        ks5 ks5' qmsgs5 qmsgs5' mycs5 mycs5' (cmd__n'' : user_cmd C)
                        froms5 froms5' sents5 sents5' cur_n5 cur_n5',

                        step_user lbl5 suid5
                                  (usrs5, adv5, cs5, gks5, ks5, qmsgs5, mycs5, froms5, sents5, cur_n5, cmd__n1)
                                  (usrs5', adv5', cs5', gks5', ks5', qmsgs5', mycs5', froms5', sents5', cur_n5', cmd__n'')
                        -> step_user lbl5 suid5
                                    (usrs5, adv5, cs5, gks5, ks5, qmsgs5, mycs5, froms5, sents5, cur_n5, f cmd__n1)
                                    (usrs5', adv5', cs5', gks5', ks5', qmsgs5', mycs5', froms5', sents5', cur_n5', f cmd__n'')

                )
              -> step_user lbl1 suid1
                          (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n1)
                          (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n1')

              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs2 $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 ks3 qmsgs3 mycs3 froms3 sents3 cur_n3,
                  bd3 = (usrs1, adv1, cs1, gks1, ks3, qmsgs3, mycs3, froms3, sents3, cur_n3, cmd2)
                  -> usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                  
                  -> exists bd3' lbl3 lbl4 bd4 bd4'
                      cs3' (usrs3': honest_users A)
                      (adv3' : user_data B) gks3'
                      ks3' qmsgs3' mycs3' froms3' sents3' cur_n3'
                      usrs4 usrs4' ks4 ks4' qmsgs4 qmsgs4' mycs4 mycs4'
                      froms4 froms4' sents4 sents4' cur_n4 cur_n4',

                      hstep lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv3', cs3', gks3', ks3', qmsgs3', mycs3', froms3', sents3', cur_n3', cmd2')
                      /\ bd4 = (usrs4, adv3', cs3', gks3', ks4, qmsgs4, mycs4, froms4, sents4, cur_n4, cmd1)
                      /\ bd4' = (usrs4', adv1'', cs1'', gks1'', ks4', qmsgs4', mycs4', froms4', sents4', cur_n4', cmd1')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks3' cmd2' qmsgs3' mycs3' froms3' sents3' cur_n3')
                      /\ usrs4 $? u_id1 = Some (mkUserData ks4 cmd1 qmsgs4 mycs4 froms4 sents4 cur_n4)
                      /\ hstep lbl4 suid1 bd4 bd4'
  .
  Proof.

    Ltac p :=
      match goal with
      | [ |- _ /\ _ ] => simple apply conj
      | [ |- _ = _ ] => reflexivity
      | [ |- step_user _ _ _ _ ] => solve [ econstructor; repeat p; eauto ]
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k2;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 1
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $+ (?k2,_) $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k1;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 2
      | [ |- (_,_) = _ ] => f_equal
      | [ |- _ $+ (_,_) = _ ] => maps_equal
      | [ |- _ $+ (_,_) $? _ = _ ] => clean_map_lookups
      end.

    Ltac simpl_solve uid :=
      split_ex; subst;
      match goal with
      | [ H : step_user _ (Some uid) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups;
      do 29 eexists;
         repeat p;
         eauto;
         repeat
           match goal with
           | [ |- hstep _ _ _ _ ] => solve [ econstructor; eauto ]
           | [ H : forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, step_user _ _ _ _  -> step_user _ _ _ _ |- hstep _ _ _ _ ] =>
             solve [ eapply H; eauto ] 
           end.
         
    induction 1; inversion 5; inversion 1; intros;
      clean_context;
      repeat 
        match goal with
        | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
        | [ H : commutes _ _ |- _ ] => unfold commutes in H; try contradiction
        end; clean_context; try (solve [ simpl_solve u_id2 ] ).


    - apply nextAction_couldBe in H30; contradiction.
    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
             reflexivity.
      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
           reflexivity.

      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
           reflexivity.

    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + do 29 eexists; repeat p; eauto.
           econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.

    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + do 29 eexists; repeat p; eauto.
           econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
  Qed.


  Lemma commutes_sound'' :
    forall {A B C} suid1 u_id1 lbl1 (bd1 bd1' : data_step0 A B C),

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall bd2 bd2' lbl2 suid2 u_id2,

          step_user lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs1 cs1' cs1'' (usrs1 usrs1': honest_users A) (adv1 adv1' adv1'' : user_data B) gks1 gks1' gks1''
              (cmd__n1 cmd__n1' : user_cmd C) ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1'
              (cmd1 cmd1' cmd2 cmd2': user_cmd (Base A))
              froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              usrs2 usrs2' ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              (* (cmd__n2 cmd__n2' : user_cmd D) *)
              froms2 froms2' sents2 sents2' cur_n2 cur_n2' s,

                bd1 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n1)
              -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n1')
              -> bd2 = (usrs2, adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv1'', cs1'', gks1'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

              (* build link to overall user command *)
              -> nextAction cmd1 cmd__n1
              -> (forall r, cmd__n1 <> Return r)
              -> (exists f, cmd1 = f cmd__n1
                    /\ cmd1' = f cmd__n1'
                    /\ forall lbl5 suid5 (usrs5 usrs5' : honest_users A) (adv5 adv5' : user_data B)
                        cs5 cs5' gks5 gks5'
                        ks5 ks5' qmsgs5 qmsgs5' mycs5 mycs5' (cmd__n'' : user_cmd C)
                        froms5 froms5' sents5 sents5' cur_n5 cur_n5',

                        step_user lbl5 suid5
                                  (usrs5, adv5, cs5, gks5, ks5, qmsgs5, mycs5, froms5, sents5, cur_n5, cmd__n1)
                                  (usrs5', adv5', cs5', gks5', ks5', qmsgs5', mycs5', froms5', sents5', cur_n5', cmd__n'')
                        -> step_user lbl5 suid5
                                    (usrs5, adv5, cs5, gks5, ks5, qmsgs5, mycs5, froms5, sents5, cur_n5, f cmd__n1)
                                    (usrs5', adv5', cs5', gks5', ks5', qmsgs5', mycs5', froms5', sents5', cur_n5', f cmd__n'')

                )
              -> step_user lbl1 suid1
                          (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n1)
                          (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n1')

              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs2 $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 ks3 qmsgs3 mycs3 froms3 sents3 cur_n3,
                  bd3 = (usrs1, adv1, cs1, gks1, ks3, qmsgs3, mycs3, froms3, sents3, cur_n3, cmd2)
                  -> usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                  
                  -> exists bd3' lbl3 lbl4 bd4 bd4'
                      cs3' (usrs3': honest_users A)
                      (adv3' : user_data B) gks3'
                      ks3' qmsgs3' mycs3' froms3' sents3' cur_n3'
                      usrs4 usrs4' ks4 ks4' qmsgs4 qmsgs4' mycs4 mycs4'
                      froms4 froms4' sents4 sents4' cur_n4 cur_n4',

                      hstep lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv3', cs3', gks3', ks3', qmsgs3', mycs3', froms3', sents3', cur_n3', cmd2')
                      /\ bd4 = (usrs4, adv3', cs3', gks3', ks4, qmsgs4, mycs4, froms4, sents4, cur_n4, cmd1)
                      /\ bd4' = (usrs4', adv1'', cs1'', gks1'', ks4', qmsgs4', mycs4', froms4', sents4', cur_n4', cmd1')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks3' cmd2' qmsgs3' mycs3' froms3' sents3' cur_n3')
                      /\ usrs4 $? u_id1 = Some (mkUserData ks4 cmd1 qmsgs4 mycs4 froms4 sents4 cur_n4)
                      /\ hstep lbl4 suid1 bd4 bd4'
  .
  Proof.

    intros.

    Ltac p :=
      match goal with
      | [ |- _ /\ _ ] => simple apply conj
      | [ |- _ = _ ] => reflexivity
      | [ |- step_user _ _ _ _ ] => solve [ econstructor; repeat p; eauto ]
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k2;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 1
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $+ (?k2,_) $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k1;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 2
      | [ |- (_,_) = _ ] => f_equal
      | [ |- _ $+ (_,_) = _ ] => maps_equal
      | [ |- _ $+ (_,_) $? _ = _ ] => clean_map_lookups
      end.

    Ltac simpl_solve uid :=
      split_ex; subst;
      match goal with
      | [ H : step_user _ (Some uid) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups;
      do 29 eexists;
         repeat p;
         eauto;
         repeat
           match goal with
           | [ |- hstep _ _ _ _ ] => solve [ econstructor; eauto ]
           | [ H : forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, step_user _ _ _ _  -> step_user _ _ _ _ |- hstep _ _ _ _ ] =>
             solve [ eapply H; eauto ] 
           end.
         
    induction 1; inversion 5; inversion 1; intros;
      clean_context;
      repeat 
        match goal with
        | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
        | [ H : commutes _ _ |- _ ] => unfold commutes in H; try contradiction
        end; clean_context; try (solve [ simpl_solve u_id2 ] ).


    - apply nextAction_couldBe in H30; contradiction.
    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
             reflexivity.
      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
           reflexivity.

      + destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; simpl in *.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
        * do 29 eexists; repeat p; eauto.
             econstructor; eauto.
             eapply H5; eauto.
             invert H40.
             econstructor; eauto.
             clean_map_lookups.
           reflexivity.

    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + do 29 eexists; repeat p; eauto.
           econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.

    - split_ex; subst.
      match goal with
      | [ H : step_user _ (Some u_id2) _ _ |- _ ] => invert H; try contradiction
      end; clean_map_lookups.
      + do 29 eexists; repeat p; eauto.
           econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
      + do 29 eexists; repeat p; eauto.
           destruct (k_id ==n k_id0); subst; econstructor; eauto.
           eapply H2; eauto.
  Qed.







  Require Import Coq.Program.Equality.
  
  Lemma commutes_sound' :
    forall {A B} suid1 u_id1 lbl1 bd1 bd1',

      hstep lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall bd2 bd2' lbl2 suid2 u_id2,

          hstep lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs1 cs1' cs1'' (usrs1 usrs1': honest_users A) (adv1 adv1' adv1'' : user_data B) gks1 gks1' gks1''
              cmd1 cmd1' ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1'
              froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              usrs2 usrs2' cmd2 cmd2' ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              froms2 froms2' sents2 sents2' cur_n2 cur_n2' s,

                bd1 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2 = (usrs2, adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv1'', cs1'', gks1'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs2 $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 ks3 qmsgs3 mycs3 froms3 sents3 cur_n3,
                  bd3 = (usrs1, adv1, cs1, gks1, ks3, qmsgs3, mycs3, froms3, sents3, cur_n3, cmd2)
                  -> usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                  
                  -> exists bd3' lbl3 lbl4 bd4 bd4'
                      cs3' (usrs3': honest_users A)
                      (adv3' : user_data B) gks3'
                      ks3' qmsgs3' mycs3' froms3' sents3' cur_n3'
                      usrs4 usrs4' ks4 ks4' qmsgs4 qmsgs4' mycs4 mycs4'
                      froms4 froms4' sents4 sents4' cur_n4 cur_n4',

                      hstep lbl3 suid2 bd3 bd3'
                      /\ usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                      /\ bd3' = (usrs3', adv3', cs3', gks3', ks3', qmsgs3', mycs3', froms3', sents3', cur_n3', cmd2')
                      /\ bd4 = (usrs4, adv3', cs3', gks3', ks4, qmsgs4, mycs4, froms4, sents4, cur_n4, cmd1)
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks3' cmd1' qmsgs3' mycs3' froms3' sents3' cur_n3')
                      /\ usrs4 $? u_id1 = Some (mkUserData ks4 cmd1 qmsgs4 mycs4 froms4 sents4 cur_n4)
                      /\ hstep lbl4 suid1 bd4 bd4'
                      /\ bd4' = (usrs4', adv1'', cs1'', gks1'', ks4', qmsgs4', mycs4', froms4', sents4', cur_n4', cmd1')
  .
  Proof.
    unfold hstep.

    Hint Constructors step_user : core.
    Hint Extern 1 (_ /\ _) => split : core.
    Hint Extern 1 (_ = _) => reflexivity : core.

    intros * STEP.
    dependent induction STEP;
      intros;
      clean_context;
      repeat 
        match goal with
        | [ H : (_,_,_,_,_,_,_,_,_,_,_) = _ |- _ ] => invert H
        | [ H : commutes _ _ |- _ ] => unfold commutes in H; try contradiction
        end.

    Ltac p :=
      match goal with
      | [ |- _ /\ _ ] => simple apply conj
      | [ |- _ = _ ] => reflexivity
      | [ |- step_user _ _ _ _ ] => solve [ econstructor; repeat p; eauto ]
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k2;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 1
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $+ (?k2,_) $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k1;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 2
      | [ |- (_,_) = _ ] => f_equal
      | [ |- _ $+ (_,_) = _ ] => maps_equal
      | [ |- _ $+ (_,_) $? _ = _ ] => clean_map_lookups
      end.

    shelve.
    - clean_map_lookups.
      invert H0. admit. admit. admit. admit. admit.

    all : match goal with
          | [ H : step_user _ _ _ _ |- _ ] => invert H; try contradiction
          end; clean_map_lookups; do 29 eexists; repeat p.

    Unshelve.

    clean_map_lookups.
    invert H10.

    eapply IHSTEP in H0; clear IHSTEP; eauto.
    shelve.
    clear IHstep_user.
    





  

  Lemma commutes_sound' :
    forall {A B} suid1 u_id1 lbl1 bd1 bd1',

      hstep lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> forall bd2 bd2' lbl2 suid2 u_id2,

          hstep lbl2 suid2 bd2 bd2'
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2

          -> forall cs1 cs1' cs1'' (usrs1 usrs1': honest_users A) (adv1 adv1' adv1'' : user_data B) gks1 gks1' gks1''
              cmd1 cmd1' ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1'
              froms1 froms1' sents1 sents1' cur_n1 cur_n1'
              usrs2 usrs2' cmd2 cmd2' ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2'
              froms2 froms2' sents2 sents2' cur_n2 cur_n2' s,

                bd1 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2 = (usrs2, adv1', cs1', gks1', ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv1'', cs1'', gks1'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

              -> usrs1 $? u_id1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
              -> usrs2 $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
              -> usrs2 = usrs1' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 ks3 qmsgs3 mycs3 froms3 sents3 cur_n3,
                  bd3 = (usrs1, adv1, cs1, gks1, ks3, qmsgs3, mycs3, froms3, sents3, cur_n3, cmd2)
                  -> usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                  
                  -> exists bd3' lbl3 lbl4 bd4 bd4'
                      cs3' (usrs3': honest_users A)
                      (adv3' : user_data B) gks3'
                      ks3' qmsgs3' mycs3' froms3' sents3' cur_n3'
                      usrs4 usrs4' ks4 ks4' qmsgs4 qmsgs4' mycs4 mycs4'
                      froms4 froms4' sents4 sents4' cur_n4 cur_n4',

                      hstep lbl3 suid2 bd3 bd3'
                      /\ usrs1 $? u_id2 = Some (mkUserData ks3 cmd2 qmsgs3 mycs3 froms3 sents3 cur_n3)
                      /\ bd3' = (usrs3', adv3', cs3', gks3', ks3', qmsgs3', mycs3', froms3', sents3', cur_n3', cmd2')
                      /\ bd4 = (usrs4, adv3', cs3', gks3', ks4, qmsgs4, mycs4, froms4, sents4, cur_n4, cmd1)
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks3' cmd1' qmsgs3' mycs3' froms3' sents3' cur_n3')
                      /\ usrs4 $? u_id1 = Some (mkUserData ks4 cmd1 qmsgs4 mycs4 froms4 sents4 cur_n4)
                      /\ hstep lbl4 suid1 bd4 bd4'
                      /\ bd4' = (usrs4', adv1'', cs1'', gks1'', ks4', qmsgs4', mycs4', froms4', sents4', cur_n4', cmd1')
  .
  Proof.
    unfold hstep.

    Hint Constructors step_user : core.
    Hint Extern 1 (_ /\ _) => split : core.
    Hint Extern 1 (_ = _) => reflexivity : core.

    intros * STEP.
    dependent induction STEP;
      intros;
      clean_context;
      repeat 
        match goal with
        | [ H : (_,_,_,_,_,_,_,_,_,_,_) = _ |- _ ] => invert H
        | [ H : commutes _ _ |- _ ] => unfold commutes in H; try contradiction
        end.

    Ltac p :=
      match goal with
      | [ |- _ /\ _ ] => simple apply conj
      | [ |- _ = _ ] => reflexivity
      | [ |- step_user _ _ _ _ ] => solve [ econstructor; repeat p; eauto ]
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k2;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 1
      | [ H : ?m $+ (?k1,_) $? ?k2 = None |- ?m $+ (?k2,_) $? ?k3 = None ] =>
        match type of m with
        | keys => idtac
        | ciphers => idtac
        end;
        is_not_evar k1; is_not_evar k2; is_evar k3; unify k3 k1;
          destruct (k1 ==n k2); subst; clean_map_lookups; idtac 2
      | [ |- (_,_) = _ ] => f_equal
      | [ |- _ $+ (_,_) = _ ] => maps_equal
      | [ |- _ $+ (_,_) $? _ = _ ] => clean_map_lookups
      end.

    shelve.
    
    all : match goal with
          | [ H : step_user _ _ _ _ |- _ ] => invert H; try contradiction
          end; clean_map_lookups; do 29 eexists; repeat p.

    Unshelve.

    clean_map_lookups.
    invert H10.

    eapply IHSTEP in H0; clear IHSTEP; eauto.
    shelve.
    clear IHstep_user.
    
  Admitted.



  
  Lemma commutes_sound' :
    forall {A B C}
      suid1 u_id1 cs1 cs1' (usrs1 usrs1': honest_users A) (adv1 adv1' : user_data B) gks1 gks1' lbl1
      ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' bd1 bd1',

      step_user lbl1 suid1 bd1 bd1'
      -> suid1 = Some u_id1
      -> bd1 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
      -> bd1' = (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                     
      -> forall suid2 u_id2 cs2 (usrs2 : honest_users A) (adv2 : user_data B) gks2 lbl2
          ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 bd2 s,

          -> step_user lbl2 suid2 bd1' bd2
          -> suid2 = Some u_id2
          -> u_id1 <> u_id2
          -> bd2 = (usrs2, adv2, cs2, gks2, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)

          -> forall cmdu1 cmdu2,
              usrs1 $? u_id1 = Some {| key_heap  := ks1;
                                       protocol  := cmdu1;
                                       msg_heap  := qmsgs1;
                                       c_heap    := mycs1;
                                       from_nons := froms1;
                                       sent_nons := sents1;
                                       cur_nonce := cur_n1 |}
              -> usrs1' $? u_id2 = Some {| key_heap  := ks1;
                                          protocol  := cmdu1;
                                          msg_heap  := qmsgs1;
                                          c_heap    := mycs1;
                                          from_nons := froms1;
                                          sent_nons := sents1;
                                          cur_nonce := cur_n1 |}

          -> summarize cmd1 s
          -> commutes cmd2 s
          -> exists cs3 (usrs3 : honest_users A) (adv3 : user_data B) gks3 lbl3
              ks3 qmsgs3 mycs3 froms3 sents3 cur_n3 bd3,
              step_usr lbl3 suid2 bd3 bd3'
              -> bd3 = (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)





  


  Lemma silent_commutes_nobind' :
    forall {A B C} suid u_id cs cs' (usrs usrs': honest_users A)
      (adv adv' : user_data B) gks gks' lbl
      ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',

      step_user lbl suid bd bd'
      -> lbl = Silent
      -> suid = Some u_id
      -> forall (cmd cmd' : user_cmd C),
          (* usrs $? u_id = Some {| key_heap  := ks; *)
          (*                        protocol  := cmd; *)
          (*                        msg_heap  := qmsgs; *)
          (*                        c_heap    := mycs; *)
          (*                        from_nons := froms; *)
          (*                        sent_nons := sents; *)
          (*                        cur_nonce := cur_n |} *)

            bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> forall U__r U__r' U__i ud,
              labels_align (U__r', U__i)
              -> usrs $? u_id = Some ud
              -> U__r = buildUniverse usrs adv cs gks u_id ud
              -> U__r' = buildUniverse usrs' adv' cs' gks' u_id
                                    {| key_heap  := ks';
                                       protocol  := cmd';
                                       msg_heap  := qmsgs';
                                       c_heap    := mycs';
                                       from_nons := froms';
                                       sent_nons := sents';
                                       cur_nonce := cur_n' |}
              -> labels_align (U__r,U__i).
  Proof.
    induction 1.


  
  Infix "==" := JMeq (at level 70, no associativity).

  Lemma silent_commutes' :
    forall {A B C} suid u_id cs cs' (usrs usrs': honest_users A)
      (adv adv' : user_data B) gks gks' lbl
      ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',

      step_user lbl suid bd bd'
      -> lbl = Silent
      -> suid = Some u_id
      -> forall (cmdc cmdc' : user_cmd C) cmd cmd',
          usrs $? u_id = Some {| key_heap  := ks;
                                 protocol  := cmd;
                                 msg_heap  := qmsgs;
                                 c_heap    := mycs;
                                 from_nons := froms;
                                 sent_nons := sents;
                                 cur_nonce := cur_n |}

          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
          -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
          (* -> (C = Base A /\ cmdc = cmd) *)
          -> (cmd == cmdc \/ exists cmdcc, cmd = Bind cmdc cmdcc)
          -> forall U__r U__r' U__i ud,
              labels_align (U__r', U__i)
              -> usrs $? u_id = Some ud
              -> U__r = buildUniverse usrs adv cs gks u_id ud
              -> U__r' = buildUniverse usrs' adv' cs' gks' u_id
                                    {| key_heap  := ks';
                                       protocol  := cmd';
                                       msg_heap  := qmsgs';
                                       c_heap    := mycs';
                                       from_nons := froms';
                                       sent_nons := sents';
                                       cur_nonce := cur_n' |}
              -> labels_align (U__r,U__i).
  Proof.
    induction 1; inversion 4; inversion 1; intros; subst; intros;
      try discriminate;
      clean_context;
      eauto 8.

    admit.
    admit.

    split_ors.
    inversion H.
    generalize (JMeq_eq H).
    
    
    
  Admitted.
                                  
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
