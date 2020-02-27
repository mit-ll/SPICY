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
     ProtocolAutomation
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

      (* -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
      (*     (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs' *)
      (*     froms froms' sents sents' cur_n cur_n', *)
        (*   bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
        (* -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
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
  (* Lemma findKeysCrypto_addnl_cipher : *)
  (*   forall {t} (msg : crypto t) ks cs c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> keys_mine ks (findKeysCrypto cs msg) *)
  (*     -> findKeysCrypto cs msg = findKeysCrypto (cs $+ (c_id,c)) msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold findKeysCrypto in *. *)
  (*   destruct msg; eauto. *)
  (*   destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto. *)
  (*   unfold keys_mine in H0. *)

  (* need to know that msg, if cipher, is in cs *)
  (* Lemma updateTrackedNonce_addnl_cipher : *)
  (*   forall suid nons cs {t} (msg : crypto t) c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> updateTrackedNonce suid nons cs msg = *)
  (*       updateTrackedNonce suid nons (cs $+ (c_id, c)) msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold updateTrackedNonce. *)
  (*   destruct msg; eauto. *)
  (*   destruct (c_id ==n c_id0); subst; clean_map_lookups.  *)

  (* Lemma msg_not_accepted_pattern_addnl_cipher : *)
  (*   forall {t} (msg : crypto t) cs suid froms pat c_id c, *)
  (*     ~ In c_id cs *)
  (*     -> ~ msg_accepted_by_pattern cs suid froms pat msg *)
  (*     -> ~ msg_accepted_by_pattern (cs $+ (c_id, c)) suid froms pat msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold not. *)
  (*   destruct pat; intros; eauto. *)
  (*   - invert H1. *)

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
              ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' cmd2 cmd2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' s,

                bd1  = (usrs1,  adv,  cs,  gks,  ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              -> bd1' = (usrs1', adv1, cs1, gks1, ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
              -> bd2  = (usrs2,  adv1, cs1, gks1, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              -> bd2' = (usrs2', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')

              (* no recursion *)
              -> nextAction cmd1 cmd1
              -> nextAction cmd2 cmd2
              -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n <> Send x m)

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 (usrs3 usrs4 : honest_users A),
                  bd3 = (usrs3,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' lbl3 lbl4 adv2 cs2 gks2 usrs3' usrs4',
                      step_user lbl3 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl4 suid1 bd4 bd4'
  .
  Proof.
    intros;
      cases cmd1; cases cmd2;
      subst;
      repeat
        match goal with
         | [ ARG : nextAction (Send ?u ?msg) (Send ?u ?msg) , H : (forall c _ _ _, nextAction (Send ?u ?msg) c -> c <> _) |- _ ] =>
           specialize (H _ u _ msg ARG); contradiction
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : step_user _ _ _ _ |- _ ] => invert H
        end; subst;
        churn;
        try solve [ do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto ].

    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
         admit.

    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit. admit. admit. admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit. admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit. admit. admit. 
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
         (* ~ msg_accepted_by_pattern cs1 (Some u_id1) froms1 pat msg0 *)
         (*   ===================== *)
         (*   ~ msg_accepted_by_pattern (cs1 $+ (c_id, SigEncCipher k__sign k__enc msg_to (Some u_id2, cur_n2) msg)) (Some u_id1) froms1 pat msg0 *)
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit. admit. admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit. admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
    - do 10 eexists; (repeat simple apply conj); try reflexivity; try econstructor; eauto; eauto.
         admit.
       


    
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
