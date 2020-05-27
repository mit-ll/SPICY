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
     List.

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     Tactics
     Simulation
     RealWorld
     AdversarySafety.

From protocols Require Import
     ExampleProtocols
     ModelCheck
     ProtocolAutomation
     SafeProtocol
     SyntacticallySafe
     (* LabelsAlign *)
     RealWorldStepLemmas.

From protocols Require Sets.

(* For later import of set notations inside sections *)
Module Foo <: Sets.EMPTY.
End Foo.
Module SN := Sets.SetNotations(Foo).

Require IdealWorld.

Set Implicit Arguments.

Ltac dt bd :=
  destruct bd as [[[[[[[[[[?usrs ?adv] ?cs] ?gks] ?ks] ?qmsgs] ?mycs] ?froms] ?sents] ?cur_n] ?cmd].

Section CommutationLemmas.

  Import RealWorldNotations.

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
            (* /\ (forall ctx sty uid, suid = Some uid -> syntactically_safe uid ctx cmd sty -> syntactically_safe uid ctx cmd__n sty) *)
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
    Hint Constructors step_user syntactically_safe : core.

    induction 1; inversion 1; inversion 1; invert 1; intros.

    - eapply IHstep_user in H28; eauto.
      split_ex.
      exists (fun CD => x <- x CD; cmd2 x).
      eexists; subst; repeat simple apply conj; eauto.
      
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
              (* -> forall ctx1 styp1, syntactically_safe u_id1 ctx1 cmd1 styp1 *)
              (* -> typingcontext_sound ctx1 (findUserKeys usrs1) cs u_id1 *)
              (* -> forall ctx2 styp2, syntactically_safe u_id2 ctx2 cmd2 styp2 *)
              (* -> typingcontext_sound ctx2 (findUserKeys usrs2) cs1 u_id2 *)
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1 *)
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2 *)
                                  
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
              -> forall ctx1 styp1, syntactically_safe u_id1 ctx1 cmd1 styp1
              -> typingcontext_sound ctx1 (findUserKeys usrs1) cs u_id1
              -> forall ctx2 styp2, syntactically_safe u_id2 ctx2 cmd2 styp2
              -> typingcontext_sound ctx2 (findUserKeys usrs2) cs1 u_id2
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1 *)
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2 *)
                                  
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
        | [ H : syntactically_safe _ _ _ _ |- _ ] => invert H
        | [ H : typingcontext_sound _ _ _ _ |- _ ] => unfold typingcontext_sound in H
        end
    ; subst
    ; destruct (u ==n u_id2); subst
    ; step_usr u_id1; step_usr u_id2.

    all: clean_map_lookups; subst.

    Ltac stuff :=
      repeat
        match goal with
        (* | [ H : next_cmd_safe _ _ _ _ _ (Send _ _) |- _ ] => process_next_cmd_safe; subst *)
        | [ H : List.In {| cmd_type := Crypto ?t ; cmd_val := ?msg ; safetyTy := TyMyCphr _ _ |} ?ctx,
                FN : (forall _ _ _ _, List.In {| cmd_type := Crypto _ |} ?ctx -> _)
            |- context [ ?msg ] ] => specialize (FN _ _ _ _ H); split_ex; subst
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
              -> forall ctx1 styp1, syntactically_safe u_id1 ctx1 cmd1 styp1
              -> typingcontext_sound ctx1 (findUserKeys usrs1) cs u_id1
              -> forall ctx2 styp2, syntactically_safe u_id2 ctx2 cmd2 styp2
              -> typingcontext_sound ctx2 (findUserKeys usrs2) cs1 u_id2
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1 *)
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2 *)
                                  
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
      invert H38.
      specialize (IHstep_user _ _ H8 H39 _ _ H40 H41).
      (* apply next_action_next_cmd_safe_bind in H38. *)
      invert H43.
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
              -> forall ctx1 styp1, syntactically_safe u_id1 ctx1 cmd1 styp1
              -> typingcontext_sound ctx1 (findUserKeys usrs1) cs u_id1
              -> forall ctx2 styp2, syntactically_safe u_id2 ctx2 cmd2 styp2
              -> typingcontext_sound ctx2 (findUserKeys usrs2) cs1 u_id2
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id1 froms1 sents1 cmd1 *)
              (* -> next_cmd_safe (findUserKeys usrs1) cs u_id2 froms2 sents2 cmd2 *)

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

    specialize (nextAction_couldBe H20).
    cases cmd__i2; intros; try contradiction; clean_context.

    - eapply step_na_return in H20; eauto; split_ands; subst.
      eapply step_no_depend_other_usrs_program in H; eauto; split_ex.
      (do 12 eexists); repeat simple apply conj; eauto.
      maps_equal; eauto.

      Ltac setup uid cmd1 :=
        match goal with
        | [ NA : nextAction ?c2 ?c
          , STEP : step_user _ (Some uid) _ _
          , SS : syntactically_safe _ _ ?c2 _
          (* , NCS : next_cmd_safe _ _ _ _ _ ?c2 *)
            |- _ ] => 
          let NACMD2 := fresh "NACMD2" in
          generalize NA; intros NACMD2
        ; eapply step_na_not_return in NA; eauto; split_ex; subst; try congruence
        ; eapply syntactically_safe_na in SS; eauto; split_ex
        ; eapply commutes_sound_recur_cmd1' with (cmd2 := cmd1) (cmd3 := c) in STEP; eauto
        (* ; specialize (NCS _ _ NACMD2); simpl in NCS *)
        end.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      
    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.

    - setup u_id1 cmd1; split_ex; subst.
      (do 12 eexists); repeat simple apply conj; try reflexivity; eauto.
      
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
  Hint Resolve typingcontext_sound_other_user_step : core.

  Lemma commutes_sound :
    forall {A B} (U__r : universe A B) lbl1 u_id1 u_id2 userData1 userData2 bd1,
      U__r.(users) $? u_id1 = Some userData1
      -> U__r.(users) $? u_id2 = Some userData2
      (* -> honest_cmds_safe U__r *)
      -> syntactically_safe_U U__r
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

    dt bd1; dt bd1'.
    clean_context; subst.
    
    repeat 
      match goal with
      | [ H : {| users := _ |} = _ |- _ ] => invert H; clean_map_lookups
      | [ H : syntactically_safe_U _ , US1 : _ $? u_id1 = _ , US2 : _ $? u_id2 = _ |- _ ] =>
        generalize (H _ _ US1)
        ; generalize (H _ _ US2)
        ; clear H; intros; simpl in *; split_ex
      end.

    specialize (impact_from_other_user_step H4 eq_refl eq_refl eq_refl H6 H0); intros; split_ex; clean_map_lookups.
    assert (u_id2 <> u_id1) as UNE by congruence.

    eapply commutes_sound_recur' in H8; try reflexivity; try eassumption; split_ex; subst; eauto.
    (do 6 eexists); repeat simple apply conj; simpl; eauto.
    specialize (impact_from_other_user_step_commutes H8 s eq_refl eq_refl eq_refl UNE H9 H11 H); intros; eauto.
    all: simpl; clean_map_lookups; eauto.
    simpl; rewrite H26; eauto.
  Qed.
  
End CommutationLemmas.

Section TimeMeasures.
  
  Inductive boundRunningTime : forall {A}, user_cmd A -> nat -> Prop :=
  | BrtReturn : forall t (r : <<t>>) n,
      boundRunningTime (Return r) n
  | BrtGen : forall n,
      boundRunningTime Gen (2 + n)
  | BrtSend : forall {t} (msg : crypto t) uid n,
      boundRunningTime (Send uid msg) (2 + n)
  | BrtRecv : forall t pat n,
      boundRunningTime (@Recv t pat) (2 + n)
  | BrtSignEncrypt : forall t k__s k__e u_id (msg : message t) n,
      boundRunningTime (SignEncrypt k__s k__e u_id msg) (2 + n)
  | BrtDecrypt : forall t (msg : crypto t) n,
      boundRunningTime (Decrypt msg) (2 + n)
  | BrtSign : forall t k u_id (msg : message t) n,
      boundRunningTime (Sign k u_id msg) (2 + n)
  | BrtVerify : forall t k (msg : crypto t) n,
      boundRunningTime (Verify k msg) (2 + n)
  | BrtGenSymKey : forall usg n,
      boundRunningTime (GenerateSymKey usg) (2 + n)
  | BrtGenAsymKey : forall usg n,
      boundRunningTime (GenerateAsymKey usg) (2 + n)
  | BrtBind : forall t1 t2 (c1 : user_cmd t1) (c2 : << t1 >> -> user_cmd t2) n1 n2,
      boundRunningTime c1 n1
      -> (forall t, boundRunningTime (c2 t) n2)
      -> boundRunningTime (Bind c1 c2) (2 + (n1 + n2)).

  Hint Constructors boundRunningTime : core.

  Hint Extern 1 (_ < _) => Omega.omega : core.
  Hint Extern 1 (_ <= _) => Omega.omega : core.

  Definition queues_size {A} (usrs : honest_users A) : nat :=
    fold (fun uid ud acc => acc + length ud.(msg_heap)) usrs 0.

  Lemma queues_size_proper :
    forall {A},
      Proper (eq ==> eq ==> eq ==> eq) (fun (_ : Map.key) (u : user_data A) (acc : nat) => acc + length (msg_heap u)).
  Proof.
    solve_proper.
  Qed.

  Lemma queues_size_transpose_neqkey :
    forall {A},
      transpose_neqkey eq (fun (_ : Map.key) (u : user_data A) (acc : nat) => acc + length (msg_heap u)).
  Proof.
    unfold transpose_neqkey; intros; Omega.omega.
  Qed.

  Hint Resolve queues_size_proper queues_size_transpose_neqkey : core.

  Lemma queues_size_readd_user_same_queue_idem :
    forall A (usrs usrs' : honest_users A) uid ud ud',
      usrs $? uid = Some ud
      -> usrs' = usrs $+ (uid, ud')
      -> ud'.(msg_heap) = ud.(msg_heap)
      -> queues_size usrs = queues_size usrs'.
  Proof.
    induction usrs using map_induction_bis;
      intros; Equal_eq; subst; clean_map_lookups; eauto.

    destruct (x ==n uid); subst; clean_map_lookups; eauto.
    - rewrite map_add_eq; unfold queues_size.
      rewrite !fold_add; eauto.
      rewrite H2; trivial.
    - unfold queues_size.
      rewrite map_ne_swap by eauto.
      progress (rewrite !fold_add by eauto).
      specialize (IHusrs _ _ _ _ H0 eq_refl H2).
      unfold queues_size in IHusrs.
      rewrite IHusrs.
      trivial.
  Qed.

  Lemma queues_size_readd_user_addnl_msg :
    forall A (usrs usrs' : honest_users A) uid ud ud' m,
      usrs $? uid = Some ud
      -> usrs' = usrs $+ (uid, ud')
      -> ud'.(msg_heap) = ud.(msg_heap) ++ [m]
      -> queues_size usrs' = 1 + queues_size usrs.
  Proof.
    induction usrs using map_induction_bis;
      intros; Equal_eq; subst; clean_map_lookups; eauto.

    destruct (x ==n uid); subst; clean_map_lookups; eauto.
    - rewrite map_add_eq; unfold queues_size.
      rewrite !fold_add; eauto.
      rewrite H2.
      rewrite app_length; simpl; Omega.omega.
      
    - unfold queues_size.
      rewrite map_ne_swap by eauto.
      progress (rewrite !fold_add by eauto).
      specialize (IHusrs _ _ _ _ _ H0 eq_refl H2).
      unfold queues_size in IHusrs.
      rewrite IHusrs.
      rewrite fold_add by eauto.
      trivial.
  Qed.

  Lemma queues_size_readd_user_popped_msg :
    forall A (usrs usrs' : honest_users A) uid ud ud' m,
      usrs $? uid = Some ud
      -> usrs' = usrs $+ (uid, ud')
      -> ud.(msg_heap) = m :: ud'.(msg_heap)
      -> queues_size usrs = 1 + queues_size usrs'.
  Proof.
    induction usrs using map_induction_bis;
      intros; Equal_eq; subst; clean_map_lookups; eauto.

    destruct (x ==n uid); subst; clean_map_lookups; eauto.
    - rewrite map_add_eq; unfold queues_size.
      rewrite !fold_add; eauto.
      rewrite H2; simpl; Omega.omega.
      
    - unfold queues_size.
      rewrite map_ne_swap by eauto.
      rewrite !fold_add by eauto.
      specialize (IHusrs _ _ _ _ _ H0 eq_refl H2).
      unfold queues_size in IHusrs.
      rewrite IHusrs.
      trivial.
  Qed.
  
  Hint Resolve queues_size_readd_user_same_queue_idem : core.

  Lemma boundRunningTime_step :
    forall C (cmd : user_cmd C) n,
      boundRunningTime cmd n

      -> forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n' lbl cmda cmda' uid,
        
        step_user lbl (Some uid)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> usrs $? uid = Some (mkUserData ks cmda qmsgs mycs froms sents cur_n)

        -> exists n',
          boundRunningTime cmd' n'
          /\ n' + queues_size (usrs' $+ (uid, mkUserData ks' cmda' qmsgs' mycs' froms' sents' cur_n' ))
            < n + queues_size usrs.
  Proof.
    induction 1;
      invert 1;
      intros;
      try solve [ exists n; simpl; erewrite <- queues_size_readd_user_same_queue_idem by eauto; split; eauto ].

    - assert (uid <> uid0) by (unfold not; intros RW; rewrite RW in *; contradiction).
      rewrite map_ne_swap by eauto.

      erewrite queues_size_readd_user_addnl_msg with (uid := uid).
      3: reflexivity.
      2: clean_map_lookups; reflexivity.
      2: simpl; reflexivity.
      
      erewrite <- queues_size_readd_user_same_queue_idem by eauto.

      exists n; split; eauto.
      
    - exists (n + 1); split; eauto.
      rewrite <- plus_assoc.
      erewrite <- queues_size_readd_user_popped_msg; eauto; eauto.
      simpl; eauto.
      
    - exists (2 + n); split; eauto.

      rewrite <- plus_assoc.
      rewrite plus_comm with (n := n).
      rewrite plus_assoc.
      rewrite <- plus_assoc with (n := 1).
      erewrite <- queues_size_readd_user_popped_msg; eauto; eauto.
      simpl; eauto.

    - eapply IHboundRunningTime in H9; split_ex; eauto.
      eexists; split; eauto.
      rewrite plus_comm with (n := x).
      rewrite plus_comm with (n := n1).
      rewrite !plus_assoc.
      rewrite <- plus_assoc.
      rewrite <- plus_assoc with (m := n1).
      apply Nat.add_lt_mono_l; eauto.
      
    - erewrite <- queues_size_readd_user_same_queue_idem by eauto.
      eexists; split; eauto.
      
  Qed.

  Inductive boundRunningTimeUniv {A} : honest_users A -> nat -> Prop :=
  | BrtEmpty : boundRunningTimeUniv $0 0
  | BrtRecur : forall uid u us n n',
      boundRunningTime u.(protocol) n
      -> us $? uid = Some u
      -> boundRunningTimeUniv (us $- uid) n'
      -> boundRunningTimeUniv us (n + n')
  .

  Hint Constructors boundRunningTimeUniv : core.

  Lemma boundRunningTime_for_element :
    forall A (usrs : honest_users A) n__rt,
      boundRunningTimeUniv usrs n__rt
      -> forall uid u,
        usrs $? uid = Some u
        -> exists n,
          boundRunningTime u.(protocol) n
        /\ boundRunningTimeUniv (usrs $- uid) (n__rt - n)
        /\ n <= n__rt.
  Proof.
    induction 1; intros; clean_map_lookups; eauto.
    destruct (uid ==n uid0); subst; clean_map_lookups; eauto.
    - eexists; repeat simple apply conj; eauto.
      rewrite plus_comm. rewrite <- Nat.add_sub_assoc by Omega.omega.
      rewrite Nat.sub_diag, Nat.add_0_r; auto.

    - assert (us $- uid $? uid0 = Some u0) by (clean_map_lookups; trivial).
      eapply IHboundRunningTimeUniv in H3; split_ex; eauto.
      eexists; repeat simple apply conj; eauto.
      rewrite <- Nat.add_sub_assoc by Omega.omega.
      eapply BrtRecur with (uid1 := uid); eauto.

      assert (RW : us $- uid0 $- uid = us $- uid $- uid0).
      apply map_eq_Equal; unfold Equal; intros.
      destruct (y ==n uid); destruct (y ==n uid0); subst; clean_map_lookups; eauto.
      rewrite RW; auto.
  Qed.

  Lemma map_no_entries_empty :
    forall A (usrs : honest_users A),
      (forall uid u, usrs $? uid = Some u -> exists u', False /\ u.(protocol) = u'.(protocol))
      -> usrs = $0.
  Proof.
    induction usrs using map_induction_bis;
      intros; Equal_eq; subst; clean_map_lookups; eauto.

    exfalso.
    assert (LKP : usrs $+ (x, e) $? x = Some e) by (clean_map_lookups; trivial).
    specialize (H0 _ _ LKP); split_ex; contradiction.
  Qed.

  Lemma boundedRunningTimeUniv_generalize' :
    forall A (usrs : honest_users A) n,
      boundRunningTimeUniv usrs n
      -> forall usrs',
        (forall uid u, usrs' $? uid = Some u -> exists u', usrs $? uid = Some u' /\ u.(protocol) = u'.(protocol))
        -> (forall uid u, usrs $? uid = Some u -> exists u', usrs' $? uid = Some u' /\ u.(protocol) = u'.(protocol))
        -> boundRunningTimeUniv usrs' n.
  Proof.
    induction 1; intros; subst.

    - assert (usrs' = $0).
      apply map_no_entries_empty; intros; eauto.
      apply H in H1; split_ex; clean_map_lookups.

      subst; eauto.

    - generalize (H3 _ _ H0); intros; split_ex.

      assert (ARG : (forall uid0 u,
                        usrs' $- uid $? uid0 = Some u ->
                        exists u' : user_data A, us $- uid $? uid0 = Some u' /\ protocol u = protocol u')).
      intros; destruct (uid ==n uid0); subst; clean_map_lookups; eauto.
      rewrite remove_eq_o in H6 by congruence; discriminate.
      rewrite remove_neq_o in H6 by congruence; eauto.

      specialize (IHboundRunningTimeUniv _ ARG); clear ARG.

      eapply BrtRecur with (uid0 := uid) (u0 := x); try assumption.
      rewrite <- H5; assumption.
      eapply IHboundRunningTimeUniv; intros; eauto.

      destruct (uid ==n uid0); subst.
      rewrite remove_eq_o in H6 by congruence; discriminate.
      rewrite remove_neq_o in * by congruence.
      eapply H3 in H6; split_ex.
      
      eexists; split; eauto.
  Qed.

  Lemma user_step_removes_no_users_keeps_proto :
    forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl u_id bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> forall cmd',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> forall u_id' u_d,
            usrs $? u_id' = Some u_d
            -> exists u_d',
              usrs' $? u_id' = Some u_d'
            /\ u_d.(protocol) = u_d'.(protocol).
  Proof.
    induction 1; inversion 1; inversion 1; intros; subst; eauto.

    case (u_id' ==n rec_u_id); intro; subst; unfold not; intros; clean_map_lookups; eauto.
  Qed.

  Lemma user_step_adds_no_users_keeps_proto :
    forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl u_id bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> forall cmd',
          bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
          -> forall u_id' u_d,
            usrs' $? u_id' = Some u_d
            -> exists u_d',
              usrs $? u_id' = Some u_d'
            /\ u_d.(protocol) = u_d'.(protocol).
  Proof.
    induction 1; inversion 1; inversion 1; intros; subst; eauto.

    case (u_id' ==n rec_u_id); intro; subst; unfold not; intros; clean_map_lookups; eauto.
  Qed.

  Lemma user_step_boundRunningTimeUniv_impact :
    forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
      (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs'
      froms froms' sents sents' cur_n cur_n' lbl uid,
        
      step_user lbl (Some uid)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
                
      -> forall n,
          boundRunningTimeUniv usrs n
          -> boundRunningTimeUniv usrs' n.
  Proof.
    intros * STEP USR1 * BRT.
    generalize (user_step_removes_no_users_keeps_proto STEP eq_refl eq_refl); intros.
    generalize (user_step_adds_no_users_keeps_proto STEP eq_refl eq_refl); intros.
    eapply boundedRunningTimeUniv_generalize'; eauto.
  Qed.

  Lemma user_step_boundRunningTimeUniv_impact_minus_stepped :
    forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
      (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs'
      froms froms' sents sents' cur_n cur_n' lbl uid,
        
      step_user lbl (Some uid)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
                
      -> forall n,
          boundRunningTimeUniv (usrs $- uid) n
          -> boundRunningTimeUniv (usrs' $- uid) n.
  Proof.
    intros * STEP USR1 * BRT.
    generalize (user_step_removes_no_users_keeps_proto STEP eq_refl eq_refl); intros.
    generalize (user_step_adds_no_users_keeps_proto STEP eq_refl eq_refl); intros.
    eapply boundedRunningTimeUniv_generalize'; eauto.

    - intros; destruct (uid ==n uid0); subst.
      rewrite remove_eq_o in H1 by congruence; discriminate.
      rewrite remove_neq_o in * by congruence; eauto.
    
    - intros; destruct (uid ==n uid0); subst.
      rewrite remove_eq_o in H1 by congruence; discriminate.
      rewrite remove_neq_o in * by congruence; eauto.
  Qed.

  Lemma boundRunningTime_univ_step :
    forall A B (U U' : universe A B) lbl b n__rt n__qs,
      step_universe U lbl U'
      -> lameAdv b U.(adversary)
      -> boundRunningTimeUniv U.(users) n__rt
      -> queues_size U.(users) = n__qs
      -> exists n',
          boundRunningTimeUniv U'.(users) n'
        /\ n' + queues_size U'.(users) < n__rt + n__qs.
  Proof.
    invert 1; intros.
    - unfold buildUniverse; unfold users.

      destruct U; destruct userData; unfold build_data_step in *; simpl in *.
      generalize (user_step_boundRunningTimeUniv_impact H1 H0 H2); intros.
      generalize (boundRunningTime_for_element H2 _ H0); simpl; intros; split_ex.
      generalize (boundRunningTime_step H5 cmd H1 H0); intros; split_ex.

      eexists; split.

      eapply BrtRecur with (uid := u_id); simpl; eauto.
      simpl; eauto.
      eapply user_step_boundRunningTimeUniv_impact_minus_stepped in H1; eauto.

      rewrite map_add_remove_eq; eauto.

      Omega.omega.
      
    - unfold lameAdv, build_data_step in *; destruct U; destruct adversary; simpl in *; rewrite H in *.
      invert H0.
  Qed.

  Inductive runningTimeMeasure {A B} (U : universe A B) : nat -> Prop :=
  | Measure : forall n__qs n__rt,
        boundRunningTimeUniv U.(users) n__rt
      -> queues_size U.(users) = n__qs
      -> runningTimeMeasure U (n__rt + n__qs).

  Hint Constructors runningTimeMeasure : core.

  Lemma runningTimeMeasure_stepU :
    forall A B (U U' : universe A B) lbl b n,
      step_universe U lbl U'
      -> lameAdv b U.(adversary)
      -> runningTimeMeasure U n
      -> exists n',
          runningTimeMeasure U' n'
          /\ n' < n.
  Proof.
    inversion 3; subst; eauto.
    eapply boundRunningTime_univ_step in H; eauto; split_ex; eauto.
  Qed.

  Notation "R ^ P ^^*" := (trc3 R P) (at level 0).

  Definition ign_lbl : rlabel -> Prop :=
    fun _ => True.

  Lemma adversary_remains_lame :
    forall A B (U U' : universe A B) b lbl,
      lameAdv b U.(adversary)
      -> step_universe U lbl U'
      -> lameAdv b U'.(adversary).
  Proof.
    unfold lameAdv; invert 2; subst; simpl in *; subst; 
      unfold build_data_step, buildUniverse, buildUniverseAdv in *; simpl in *.

    - destruct lbl.
      + simpl in *; eapply honest_silent_step_nochange_adversaries in H2; eauto.
        subst; auto.
      + simpl in *; eapply honest_labeled_step_nochange_adversary_protocol in H2; eauto.
        rewrite <- H2; auto.
        
    - rewrite H in H1; invert H1.
  Qed.

  Lemma adversary_remains_lame_step :
    forall t__hon t__adv st st' b,
      lameAdv b (fst st).(adversary)
      -> (@step t__hon t__adv) st st'
      -> lameAdv b (fst st').(adversary).
  Proof.
    invert 2; simpl in *; eauto using adversary_remains_lame.
  Qed.

  Lemma runningTimeMeasure_step :
    forall A B (st st' : RealWorld.universe A B * IdealWorld.universe A) b n,
      step st st'
      -> lameAdv b (fst st).(adversary)
      -> runningTimeMeasure (fst st) n
      -> exists n',
          runningTimeMeasure (fst st') n'
          /\ n' < n.
  Proof.
    destruct st; destruct st'; simpl;
      inversion 3; subst; eauto.
    invert H; eauto using runningTimeMeasure_stepU.
  Qed.
  
  Lemma runningTimeMeasure_steps :
    forall A B (st st' : RealWorld.universe A B * IdealWorld.universe A),
      (@step A B) ^* st st'
      -> forall b n,
        lameAdv b (fst st).(adversary)
        -> runningTimeMeasure (fst st) n
        -> exists n',
            runningTimeMeasure (fst st') n'
          /\ n' <= n.
  Proof.
    induction 1; intros; eauto.
    generalize H; intros STEP.
    eapply runningTimeMeasure_step in H; eauto; split_ex.

    assert (lameAdv b (adversary (fst y))).
    invert STEP;
      eapply adversary_remains_lame; eauto.

    specialize (IHtrc _ _ H4 H); split_ex; eauto.
  Qed.

  Inductive rstepsi {A B} :
    nat -> universe A B  -> universe A B -> Prop :=
  | RStepsiO : forall U,
      rstepsi O U U
  | RStepsiS : forall lbl U U' U'' i,
      step_universe U lbl U'
      -> rstepsi i U' U''
      -> rstepsi (1 + i) U U''.

  Hint Constructors rstepsi : core.

  Lemma rsteps_rstepsi :
    forall A B pr (U U' : universe A B),
      trc3 step_universe pr U U'
      -> exists i, rstepsi i U U'.
  Proof.
    induction 1; split_ex; eauto.
  Qed.

  Inductive stepsi {t__hon t__adv} :
    nat 
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> Prop :=
  | StepsiO : forall st,
      stepsi O st st
  | StepsiS : forall st st' st'' i,
      step st st' 
      -> stepsi i st' st''
      -> stepsi (1 + i) st st''.

  Hint Constructors step stepsi : core.
    
  Lemma steps_stepsi :
    forall t__hon t__adv st st',
      (@step t__hon t__adv) ^* st st'
      -> exists i, stepsi i st st'.
  Proof.
    induction 1; split_ex; eauto.
  Qed.

End TimeMeasures.

Section NextSteps.

  Lemma user_step_or_not {A B} (U : universe A B) (u_id : user_id) :
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

  Definition summarize_univ {A B} (U : universe A B) (summaries : NatMap.t summary) : Prop :=
    forall u_id u_d s,
      U.(users) $? u_id = Some u_d
      -> summaries $? u_id = Some s
        /\ summarize u_d.(protocol) s.

  Inductive nextStep {A B} (* (us : honest_users A) *)
            (u_id : user_id) (userData : user_data A)
    : universe A B -> rlabel -> universe A B  -> Prop :=

  | Here : forall U U' lbl usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,

      NatMap.O.max_elt U.(users) = Some (u_id, userData)
      (* NatMap.O.max_elt us = Some (u_id, userData) *)
      -> U' = buildUniverse usrs adv cs gks u_id {| key_heap  := ks
                                                   ; msg_heap  := qmsgs
                                                   ; protocol  := cmd
                                                   ; c_heap    := mycs
                                                   ; from_nons := froms
                                                   ; sent_nons := sents
                                                   ; cur_nonce := cur_n |}
      (* -> U.(users) $? u_id = Some userData *)
      -> step_user lbl (Some u_id) (build_data_step U userData)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> nextStep (* us *) u_id userData U lbl U'

  | There : forall (U U' : universe A B) lbl summaries u_id' userData'
              usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,

      NatMap.O.max_elt U.(users) = Some (u_id', userData')
      (* NatMap.O.max_elt us = Some (u_id', userData') *)
      -> summarize_univ U summaries
      -> (forall lbl bd', ~ step_user lbl (Some u_id') (build_data_step U userData') bd')
      \/ (exists u_id2 userData2, u_id' <> u_id2
                          /\ U.(users) $? u_id2 = Some userData2
                          /\ (forall t (cmd__n : user_cmd t) s bd' lbl,
                                step_user lbl (Some u_id2) (build_data_step U userData2) bd'
                                -> nextAction userData2.(protocol) cmd__n
                                -> summaries $? u_id' = Some s
                                -> commutes cmd__n s
                                -> False))
      -> u_id <> u_id'
      -> U' = buildUniverse usrs adv cs gks u_id {| key_heap  := ks
                                                   ; msg_heap  := qmsgs
                                                   ; protocol  := cmd
                                                   ; c_heap    := mycs
                                                   ; from_nons := froms
                                                   ; sent_nons := sents
                                                   ; cur_nonce := cur_n |}
      -> U.(users) $? u_id = Some userData
      -> step_user lbl (Some u_id) (build_data_step U userData)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      (* -> nextStep (us $- u_id') u_id userData U lbl U' *)
      -> nextStep (* us *) u_id userData U lbl U'.

  Inductive stepC (t__hon t__adv : type) :
    (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
    -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
    -> Prop :=

  | StepNextC : forall ru ru' rlbl iu iu' u_id ud st st',
      nextStep (* ru.(users) *) u_id ud ru rlbl ru'
      -> st = (ru,iu)
      -> st' = (ru',iu')
      -> step  st st'
      -> stepC st st'.
  

End NextSteps.

(* Load the set notations *)
Import SN.

Definition TrC {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) :=
  {| Initial := {(ru0, iu0)};
     Step    := @stepC t__hon t__adv |}.


Lemma resend_violation_translate :
  forall t__hon t__adv n st st' b,
    stepsi n st st'
    -> lameAdv b (fst st).(adversary)
    -> (forall st'', step st' st'' -> False)
    -> ~ no_resends_U (fst st')
    -> exists st'',
        (@stepC t__hon t__adv)^* st st''
        /\ ~ no_resends_U (fst st'').
Proof.
Admitted.

Lemma alignment_violation_translate :
  forall t__hon t__adv st st' n b,
    stepsi n st st'
    -> lameAdv b (fst st).(adversary)
    -> (forall st'', step st' st'' -> False)
    -> ~ labels_align st'
    -> exists st'',
        (@stepC t__hon t__adv)^* st st''
        /\ ~ labels_align st''.
Proof.
Admitted.

(* Lemma translate_trace_commute : *)
(*   forall i h l c1 c2 h' l' c', *)
(*     stepsi (S i) (h, l, c1 || c2) (h', l', c') *)
(*     -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False) *)
(*     -> forall s, summarize c2 s *)
(*     -> forall x, nextAction c1 x *)
(*     -> commutes x s *)
(*     -> forall x0 x1 x2, step (h, l, c1) (x0, x1, x2) *)
(*     -> exists h'' l'', step (h, l, c1) (h'', l'', x2) *)
(*                        /\ stepsi i (h'', l'', x2 || c2) (h', l', c'). *)
(* Proof. *)
(*   induct 1; simplify. *)
(*   invert H0. *)
  
(*   invert H. *)

(*   eapply nextAction_det in H5; try eapply H6; eauto; propositional; subst. *)
(*   eauto 10. *)

(*   eapply commutes_noblock in H3; eauto. *)
(*   first_order. *)
(*   exfalso; eauto. *)

(*   invert H. *)

(*   eapply nextAction_det in H5; try eapply H12; eauto; propositional; subst. *)
(*   eauto 10. *)

(*   assert (Hnext : nextAction c1 x) by assumption. *)
(*   eapply commutes_noblock in Hnext; eauto. *)
(*   first_order. *)
(*   eapply IHstepsi in H; clear IHstepsi; eauto using summarize_step. *)
(*   first_order. *)
(*   eapply commutes_sound with (c1 := c1) (c2 := c2) (c0 := x) in H; eauto. *)
(*   first_order. *)
(*   eauto 10. *)
(* Qed. *)

(* Lemma translate_trace_commute : *)
(*   forall t__hon t__adv st st' n, *)
(*     @stepsi t__hon t__adv (1 + n) st st' *)
(*     -> (forall st'', step st' st'' -> False) *)
(*     -> forall summaries, summarize_univ (fst st) summaries. *)

(*     -> forall x, nextAction c1 x *)
(*     -> commutes x s *)
(*     -> forall x0 x1 x2, step (h, l, c1) (x0, x1, x2) *)
(*     -> exists h'' l'', step (h, l, c1) (h'', l'', x2) *)
(*                        /\ stepsi i (h'', l'', x2 || c2) (h', l', c'). *)
(* Proof. *)
(*   induct 1; simplify. *)
(*   invert H0. *)
  
(*   invert H. *)

(*   eapply nextAction_det in H5; try eapply H6; eauto; propositional; subst. *)
(*   eauto 10. *)

(*   eapply commutes_noblock in H3; eauto. *)
(*   first_order. *)
(*   exfalso; eauto. *)

(*   invert H. *)

(*   eapply nextAction_det in H5; try eapply H12; eauto; propositional; subst. *)
(*   eauto 10. *)

(*   assert (Hnext : nextAction c1 x) by assumption. *)
(*   eapply commutes_noblock in Hnext; eauto. *)
(*   first_order. *)
(*   eapply IHstepsi in H; clear IHstepsi; eauto using summarize_step. *)
(*   first_order. *)
(*   eapply commutes_sound with (c1 := c1) (c2 := c2) (c0 := x) in H; eauto. *)
(*   first_order. *)
(*   eauto 10. *)
(* Qed. *)


Lemma fold_Equal :
  forall V (m1 m2 : NatMap.t V),
    (forall y, m1 $? y = m2 $? y)
    -> Equal m1 m2.
  unfold Equal; intros; eauto. Qed.

Lemma eqlistA_eq :
  forall e (l1 l2 : list (nat * e)),
    SetoidList.eqlistA (O.O.eqke (elt:=e)) l1 l2
    -> l1 = l2.
  induct 1; subst; eauto.
  unfold O.O.eqke in H; destruct x , x'; simpl in *; split_ands; subst; eauto.
Qed.

Lemma add_above_max_elt :
  forall V (m1 : NatMap.t V) k,
    O.Above k m1
    -> forall m2 v,
      Add k v m1 m2
      -> NatMap.O.max_elt m2 = Some (k, v).
Proof.
  intros.

  pose proof (NatMap.O.elements_Add_Above H H0).
  apply eqlistA_eq in H1.
  unfold O.max_elt, O.max_elt_aux.
  rewrite H1.
  fold O.max_elt.


  unfold Add in H0.
  apply fold_Equal in H0.
  apply map_eq_Equal in H0.

  generalize (elements m1).
  induction l; eauto.
  rewrite <- app_comm_cons.
  destruct a.
  destruct l; eauto.
Qed.

(* Lemma no_stepC_no_step' : *)
(*     forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' *)
(*       (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs' *)
(*       froms froms' sents sents' cur_n cur_n' lbl uid U summaries, *)
        
(*       step_user lbl (Some uid) *)
(*                 (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
(*                 (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
(*       -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n) *)
(*       -> U = mkUniverse usrs adv cs gks *)
(*       -> summarize_univ U summaries *)
(*       -> forall us, *)
(*           us $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n) *)
(*           -> (forall uid' ud', us $? uid' = Some ud' -> usrs $? uid' = Some ud') *)
(*           -> exists uid' ud' lbl' U', *)
(*             nextStep us uid' ud' U lbl' U'. *)
(* Proof. *)
(*   induction us using NatMap.O.map_induction_max; *)
(*     intros; Equal_eq. *)

(*   - eapply Empty_eq_empty in H3; subst; clean_map_lookups. *)
(*   - destruct (x ==n uid). *)
(*     + rewrite e0 in *; clear e0; clear x. *)
(*       generalize H4; intros ADD. *)
(*       specialize (H4 uid); rewrite add_eq_o in H4 by auto; clean_map_lookups. *)
(*       unfold Add in ADD; apply fold_Equal in ADD; apply map_eq_Equal in ADD; subst. *)
(*       (do 4 eexists). *)
(*       eapply Here with (u_id := uid); eauto. *)

(*       eapply add_above_max_elt; eauto. *)
(*       unfold Add; intros. *)
(*       destruct (uid ==n y); clean_map_lookups; eauto. *)

(*     + pose proof (user_step_or_not U). *)

(*       generalize H4; intros ADD; unfold Add in ADD; apply fold_Equal in ADD; apply map_eq_Equal in ADD. *)
(*       assert (us2 $? x = Some e) as USX by *)
(*             (rewrite ADD; clean_map_lookups; trivial). *)
      
(*       generalize (H6 _ _ USX); intros USERX. *)
(*       rewrite H1 in H7; simpl in H7; eapply H7 in USERX; split_ors. *)

(*       * rewrite H1. *)
(*         dt x1. *)
(*         (do 4 eexists). *)
(*         eapply Here. *)
(*         eapply add_above_max_elt; eauto. *)
(*         eauto. *)
(*         simpl; eauto. *)
(*         eauto. *)

(*       * generalize H4; intros. *)
(*         unfold Add in H4. specialize (H4 uid). rewrite add_neq_o in H4 by auto. *)
(*         rewrite <- H4 in IHus1. *)
(*         apply IHus1 in H5; split_ex; eauto 8. *)

(*         assert (us1 $? x = None). *)
(*         cases (us1 $? x); eauto. *)
(*         exfalso. *)
(*         assert (us1 $? x <> None) as NOTNONE by (unfold not; intros; clean_map_lookups). *)
(*         rewrite <- in_find_iff in NOTNONE. *)
(*         eapply H3 in NOTNONE; Omega.omega. *)

(*         assert (us1 = us2 $- x). *)
(*         apply map_eq_Equal; unfold Equal; intros. *)
(*         destruct (x ==n y); subst; clean_map_lookups; eauto. *)

(*         (do 4 eexists). *)
(*         eapply There. *)
(*         eapply add_above_max_elt; eauto. *)
(*         eassumption. *)
(*         rewrite H1; left; intros; eauto. *)

(*         rewrite <- H11; eassumption. *)

(*         intros. *)
(*         eapply H6; subst. *)
(*         destruct (x ==n uid'); subst; clean_map_lookups; eauto. *)
(*         assert (us1 $? uid' <> None) by (unfold not; intros; clean_map_lookups). *)
(*         rewrite <- in_find_iff in H1; eapply H3 in H1; Omega.omega. *)
(* Qed. *)
       
(* Lemma no_stepC_no_step : *)
(*   forall t__hon t__adv st summaries, *)
(*     (forall st', ~ @stepC t__hon t__adv st st') *)
(*     -> summarize_univ (fst st) summaries *)
(*     -> forall st'', step st st'' -> False. *)
(* Proof. *)
(*   intros. *)
(*   invert H1. *)
  
(*   - invert H2. admit. *)
(*     destruct userData, ru; simpl in *. *)
(*     eapply no_stepC_no_step' in H3; eauto; simpl in *; split_ex. *)
(*     destruct x1. *)
    
(*     + eapply H. *)
(*       econstructor; simpl; eauto. *)
(*       econstructor; eauto. *)
(*     + eapply H. *)
(*       econstructor 2; simpl; eauto. *)
(*       econstructor; eauto. *)

      
(*       eapply no_stepC_no_step'. *)
  
(*   econstructor; eauto. *)

Hint Resolve adversary_remains_lame_step : core.

(* Lemma no_stepC_no_step : *)
(*   forall t__hon t__adv st st', *)
    
(*     @step t__hon t__adv st st' *)
(*     -> (forall st'', ~ stepC st st'') *)
(*     -> False. *)
(* Proof. *)
(* Admitted. *)

Hint Constructors stepC nextStep : core.

Lemma summarize_step_other :
  forall A B C suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid

      -> forall uid__s ud__s summaries s,
          usrs $? uid__s = Some ud__s
          -> uid <> uid__s
          -> summaries $? uid__s = Some s
          -> summarize ud__s.(protocol) s
          -> exists ud'__s,
              usrs' $? uid__s = Some ud'__s
              /\ summarize ud'__s.(protocol) s.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto.
  destruct (rec_u_id ==n uid__s); subst; clean_map_lookups; eauto.
Qed.

Lemma summarize_user_step' :
  forall A B C suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' uid,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some uid

      -> forall s,
          summarize cmd s
          -> summarize cmd' s.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst;
    match goal with
    | [ H : summarize _ _ |- _ ] => invert H
    end;
    try solve [ econstructor; eauto ]; eauto.
Qed.

Lemma summarize_user_step :
  forall A B cs (usrs : honest_users A) (adv : user_data B) gks cmd  ks qmsgs mycs froms sents cur_n uid ud U lbl,

    step_user lbl (Some uid)
              (build_data_step U ud)
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
    -> U.(users) $? uid = Some ud
    -> forall s,
        summarize ud.(protocol) s
        -> summarize cmd s.
Proof.
  intros.
  destruct U, ud; unfold build_data_step in *; simpl in *.
  eapply summarize_user_step'; eauto.
Qed.

Lemma summarize_univ_step :
  forall t__hon t__adv st st' summaries b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> summarize_univ (fst st) summaries
    -> summarize_univ (fst st') summaries.
Proof.
  inversion 1; subst; unfold summarize_univ; simpl in *; intros;
    match goal with
    | [ H : step_universe _ _ _ |- _ ] => invert H; dismiss_adv
    end.

  - unfold buildUniverse in H3; simpl in H3.
    destruct (u_id ==n u_id0); subst; clean_map_lookups.
    specialize (H2 _ _ s H4); split_ex.
    split; simpl; eauto using summarize_user_step.

    destruct ru, userData, u_d; unfold build_data_step in *; simpl in *.
    eapply step_back_into_other_user with (u_id2 := u_id) in H5; eauto.
    split_ors; clean_map_lookups; eauto.
    specialize (H2 _ _ s H0); simpl in *; eauto.
    specialize (H2 _ _ s H5); simpl in *; eauto.

  - unfold buildUniverse in *; simpl in *.
    destruct (u_id ==n u_id0); subst; clean_map_lookups.
    specialize (H5 _ _ s H7); split_ex.
    split; simpl; eauto using summarize_user_step.

    destruct ru, userData, u_d; unfold build_data_step in *; simpl in *.
    eapply step_back_into_other_user with (u_id2 := u_id) in H7; eauto.
    split_ors; clean_map_lookups; eauto.
    specialize (H5 _ _ s H0); simpl in *; eauto.
    specialize (H5 _ _ s H7); simpl in *; eauto.
Qed.

Hint Resolve summarize_univ_step : core.

Lemma max_element_some :
  forall V (m : NatMap.t V) k v,
    m $? k = Some v
    -> exists k' v',
      NatMap.O.max_elt m = Some (k',v').
Proof.
  intros.
  cases (O.max_elt m).
  destruct p; eauto.

  apply NatMap.O.max_elt_Empty in Heq.
  unfold Empty, Raw.Empty in Heq.
  specialize (Heq k v).
  rewrite <- find_mapsto_iff in H.
  contradiction.
Qed.

Lemma commutes_noblock :
  forall t t__n2 (cmd2 : user_cmd (Base t)) (cmd__n2 : user_cmd t__n2),
    nextAction cmd2 cmd__n2
  -> forall t__adv (usrs usrs' : honest_users t) (adv adv' : user_data t__adv) cs cs' gks gks'
      ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' cmd2' uid2 lbl2,
      
      usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
    -> step_user lbl2 (Some uid2)
              (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
    -> forall (cmd1 : user_cmd (Base t)) s1, summarize cmd1 s1
    -> forall uid1 summaries, summaries $? uid1 = Some s1
    -> commutes cmd__n2 s1
    -> uid1 <> uid2
    -> forall (usrs1' : honest_users t) (adv1' : user_data t__adv) cs1' gks1'
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' cmd1' lbl1,

        usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
        -> step_user lbl1 (Some uid1)
                  (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                  (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
        -> forall ks2'' qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'',
          usrs1' $? uid2 = Some (mkUserData ks2'' cmd2 qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'')
        -> exists usrs2' adv2' cs2' gks2' lbl2' ks2''' qmsgs2''' mycs2''' froms2''' sents2''' cur_n2''',
          step_user lbl2' (Some uid2)
                    (usrs1' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1'),
                     adv1', cs1', gks1', ks2'', qmsgs2'', mycs2'', froms2'', sents2'', cur_n2'', cmd2)
                    (usrs2', adv2', cs2', gks2', ks2''', qmsgs2''', mycs2''', froms2''', sents2''', cur_n2''', cmd2')
.
Proof.
Admitted.

Inductive model_step_user (t__hon t__adv : type) (uid : user_id) :
  (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon)
  -> Prop :=
| MSSilent :
    forall ru ru' iu userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd,
      ru.(users) $? uid = Some userData
    -> step_user Silent (Some uid)
                (build_data_step ru userData)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
    -> ru' = buildUniverse usrs adv cs gks uid {| key_heap  := ks
                                               ; msg_heap  := qmsgs
                                               ; protocol  := cmd
                                               ; c_heap    := mycs
                                               ; from_nons := froms
                                               ; sent_nons := sents
                                               ; cur_nonce := cur_n |}
    -> model_step_user uid (ru, iu) (ru', iu)
| MSLoud :
    forall ru ru' iu iu' iu'' userData usrs adv cs gks ks qmsgs mycs froms sents cur_n cmd ra ia,
      ru.(users) $? uid = Some userData
    -> step_user (Action ra) (Some uid)
                (build_data_step ru userData)
                (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
    -> ru' = buildUniverse usrs adv cs gks uid {| key_heap  := ks
                                               ; msg_heap  := qmsgs
                                               ; protocol  := cmd
                                               ; c_heap    := mycs
                                               ; from_nons := froms
                                               ; sent_nons := sents
                                               ; cur_nonce := cur_n |}
    -> istepSilent^* iu iu'
    -> IdealWorld.lstep_universe iu' (Action ia) iu''
    -> action_matches ra ru ia iu'
    -> model_step_user uid (ru, iu) (ru', iu'')
.

Lemma step_implies_model_step_user :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> exists uid,
        model_step_user uid st st'.
Proof.
  invert 1; intros; subst; simpl in *.

  invert H0; dismiss_adv; unfold buildUniverse, build_data_step in *; simpl in *.
  eexists; econstructor 1; eauto.

  invert H0; dismiss_adv; unfold buildUniverse, build_data_step in *; simpl in *.
  eexists; econstructor 2; eauto.
Qed.

Lemma model_step_user_implies_step :
  forall t__hon t__adv st st' uid,
    @model_step_user t__hon t__adv uid st st'
    -> step st st'.
Proof.
  invert 1.
  econstructor 1; econstructor 1; eauto.

  econstructor 2; eauto.
  econstructor; eauto.
Qed.
      
Lemma translate_trace_commute :
  forall t__hon t__adv i st st' b,
    @stepsi t__hon t__adv (1 + i) st st'
    -> lameAdv b (fst st).(adversary)
    -> (forall st'', ~ step st' st'')
    -> forall summaries, summarize_univ (fst st) summaries
    -> forall uid ud, NatMap.O.max_elt (fst st).(users) = Some (uid,ud)
    -> (forall u_id2 userData2,
          uid <> u_id2
          -> users (fst st) $? u_id2 = Some userData2
          -> forall bd' lbl, step_user lbl (Some u_id2) (build_data_step (fst st) userData2) bd'
          -> exists t (cmd__n : user_cmd t) s,
              nextAction (protocol userData2) cmd__n
              /\ summaries $? uid = Some s
              /\ commutes cmd__n s)
    -> forall lbl bd, step_user lbl (Some uid) (build_data_step (fst st) ud) bd
    -> exists lbl' bd' iu st0,
          step_user lbl' (Some uid) (build_data_step (fst st) ud) bd'
          /\ st0 = (buildUniverse_step bd' uid, iu)
          /\ step st st0
          /\ stepsi i st0 st'.
Proof.
  induct 1; intros; eauto.

  invert H0.

  - clear IHstepsi.
    invert H; simpl in *.

    + invert H0; dismiss_adv.
      destruct (uid ==n u_id); subst; clean_map_lookups.
      admit.

      assert (LK : users ru $? u_id = Some userData) by assumption.
      eapply H5 in LK; eauto; split_ex.

      apply NatMap.O.max_elt_MapsTo in H4;
        rewrite find_mapsto_iff in H4.
      destruct userData, ud; unfold build_data_step in *; simpl in *.

      specialize (H3 _ _ x1 H4); split_ex.
      dt bd.

      generalize H6; intros STEP.
      eapply step_limited_change_other_user in STEP; eauto; split_ex.
      split_ors; clean_map_lookups; eauto.

      eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in H0; eauto; split_ex.
      unfold buildUniverse in H2.

      destruct x6;
        exfalso; eapply H2.
      * econstructor 1.
        unfold buildUniverse.
        clear H7.
        eapply StepUser with (u_id0 := u_id); eauto.

        unfold buildUniverse; simpl; clean_map_lookups; eauto.

        admit.

      * admit.
      * admit.

    + admit.

  - assert (LAME: lameAdv b (adversary (fst st))) by assumption.
    eapply adversary_remains_lame_step in LAME; eauto.

    assert (SUMMARIES : summarize_univ (fst st) summaries) by assumption.
    eapply summarize_univ_step in SUMMARIES; eauto.

    specialize (IHstepsi _ _ eq_refl LAME H2 _ SUMMARIES).
  
Admitted.

Lemma resend_violation_translate' :
  forall t__hon t__adv n st st' b summaries,
    stepsi n st st'
    -> lameAdv b (fst st).(adversary)
    -> summarize_univ (fst st) summaries
    -> (forall st'', step st' st'' -> False)
    -> ~ no_resends_U (fst st')
    -> exists st'',
        (@stepC t__hon t__adv)^* st st''
        /\ ~ no_resends_U (fst st'').
Proof.
  induct n; intros.

  invert H; eexists; split; eauto.
  econstructor.

  destruct (
      classic (
          exists uid ud,
            NatMap.O.max_elt (fst st).(users) = Some (uid,ud)
          /\ (exists lbl bd, step_user lbl (Some uid) (build_data_step (fst st) ud) bd)
          /\ (forall u_id2 userData2,
                uid <> u_id2
              -> (fst st).(users) $? u_id2 = Some userData2
              -> forall bd lbl, step_user lbl (Some u_id2) (build_data_step (fst st) userData2) bd
              -> exists t (cmd__n : user_cmd t) s,
                  nextAction userData2.(protocol) cmd__n
                /\ summaries $? uid = Some s
                /\ commutes cmd__n s))).

  - firstorder idtac.

    eapply translate_trace_commute in H; eauto.
    firstorder idtac.
    eapply IHn in H9; eauto.
    firstorder idtac.

    exists x7; split; eauto.
    eapply TrcFront; eauto.
    destruct st; econstructor; eauto.
    dt x4; simpl in *; econstructor 1; eauto.
    
  - invert H.
    eapply IHn in H7; eauto.
    firstorder idtac.
    simpl in *.

    exists x.
    split; eauto.
    eapply TrcFront; eauto.
    destruct st, st'0.

    generalize H6; intros STEP; invert H6;
      match goal with
      | [ H : step_universe _ _ _ |- _ ] => invert H
      end.

    + pose proof (max_element_some _ _ H6); firstorder idtac.
      specialize (H4 x0); firstorder idtac.
      specialize (H4 x1); simpl in H4; split_ands.
      eapply not_and_or in H4; split_ors; try contradiction.
      eapply not_and_or in H4.

      destruct (x0 ==n u_id); subst; clean_map_lookups.
      * generalize (O.max_elt_MapsTo H8); intros MT.
        rewrite find_mapsto_iff in MT.
        clean_map_lookups.
        econstructor; eauto.

      * econstructor; eauto.
        econstructor 2; eauto.
        split_ors.
        left; unfold not; intros; eauto.
        right; intros.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.

        apply imply_to_and in H4; split_ands.
        apply imply_to_and in H9; split_ands.
        apply not_all_ex_not in H10; split_ex.
        apply not_all_ex_not in H10; split_ex.
        apply imply_to_and in H10; split_ands.
        firstorder idtac; simpl in *.
        exists x2; exists x3; repeat simple apply conj; eauto; intros; simpl in *.
        eapply H11; eauto.

    + destruct u; unfold build_data_step, lameAdv in *; simpl in *.
      rewrite H0 in H6; invert H6.

    + pose proof (max_element_some _ _ H6); firstorder idtac.
      specialize (H4 x0); firstorder idtac.
      specialize (H4 x1); simpl in H4; split_ands.
      eapply not_and_or in H4; split_ors; try contradiction.
      eapply not_and_or in H4.

      destruct (x0 ==n u_id); subst; clean_map_lookups.
      * generalize (O.max_elt_MapsTo H8); intros MT.
        rewrite find_mapsto_iff in MT.
        clean_map_lookups.
        econstructor; eauto.

      * econstructor; eauto.
        econstructor 2; eauto.
        split_ors.
        left; unfold not; intros; eauto.
        right; intros.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.

        apply imply_to_and in H4; split_ands.
        apply imply_to_and in H9; split_ands.
        apply not_all_ex_not in H10; split_ex.
        apply not_all_ex_not in H10; split_ex.
        apply imply_to_and in H10; split_ands.
        firstorder idtac; simpl in *.
        exists x2; exists x3; repeat simple apply conj; eauto; intros; simpl in *.
        eapply H11; eauto.
Qed.
  
Lemma complete_trace :
  forall t__hon t__adv n' n st b,
    runningTimeMeasure (fst st) n
    -> n <= n'
    -> lameAdv b (fst st).(adversary)
    -> exists st',
        (@step t__hon t__adv) ^* st st'
        /\ (forall st'', step st' st'' -> False).

Proof.
  induct n'; intros.
  - invert H; simpl in *.

    exists st; split; intros; eauto.
    destruct st.
    destruct u; simpl in *; subst.
    destruct n__rt; try Omega.omega.
    
    invert H.

    invert H6; dismiss_adv; simpl in *.
    eapply boundRunningTime_for_element in H2; eauto; split_ex.
    destruct x; try Omega.omega.
    invert H2.
    unfold build_data_step in *; rewrite <- H8 in H3; invert H3.
    
    invert H5; simpl in *.
    eapply boundRunningTime_for_element in H2; eauto; split_ex.
    destruct x; try Omega.omega.
    invert H2.
    unfold build_data_step in *; rewrite <- H11 in H3; invert H3.

  - destruct (classic (exists st', step st st')).
    + split_ex.
      rename x into st'.
      generalize H2; intros STEP; invert H2; simpl in *.

      * eapply runningTimeMeasure_stepU in H; eauto.
        split_ex.
        eapply adversary_remains_lame in H1; eauto.

        specialize (IHn' x (ru',iu)).
        simpl in IHn'.
        eapply IHn' in H; try Omega.omega; eauto.
        split_ex.

        exists x0; split; intros; eauto.
        eapply TrcFront; eauto.

      * eapply runningTimeMeasure_stepU in H; eauto.
        split_ex.
        eapply adversary_remains_lame in H1; eauto.

        specialize (IHn' x (ru',iu'')).
        simpl in IHn'.
        eapply IHn' in H; try Omega.omega; eauto.
        split_ex.

        exists x0; split; intros; eauto.
        eapply TrcFront; eauto.


    + assert (forall st', ~ step st st') by eauto using not_ex_all_not.
      exists st; split; intros; eauto.
Qed.

Lemma many_steps_stays_lame :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) ^* st st'
    -> lameAdv b (adversary (fst st))
    -> lameAdv b (adversary (fst st')).
Proof.
  induction 1;
    intros;
    simpl in *;
    eauto.
Qed.

Hint Resolve many_steps_stays_lame : core.

Theorem step_stepC :
  forall {t__hon t__adv} (ru0 : RealWorld.universe t__hon t__adv) (iu0 : IdealWorld.universe t__hon) b n,
    syntactically_safe_U ru0
    -> runningTimeMeasure ru0 n
    -> lameAdv b ru0.(adversary)
    -> invariantFor (TrC ru0 iu0) (fun st => no_resends_U (fst st) /\ labels_align st)
    -> invariantFor (S ru0 iu0) (fun st => no_resends_U (fst st) /\ labels_align st)
.
Proof.
  intros * SYN_SAFE RUNTIME LAME INV.

  apply NNPP; unfold not; intros INV'.
  unfold invariantFor in INV'.
  apply not_all_ex_not in INV'; split_ex.
  apply imply_to_and in H; split_ex.
  apply not_all_ex_not in H0; split_ex.
  apply imply_to_and in H0; split_ex.
  simpl in H; split_ors; try contradiction.
  destruct x0 as [?ru ?iu].

  subst; simpl in *.

  assert (exists n', runningTimeMeasure (fst (ru, iu)) n' /\ n' <= n)
    by eauto using runningTimeMeasure_steps; split_ex.
  
  eapply complete_trace in H; eauto; split_ex.
  specialize (trc_trans H0 H); intros.
  apply steps_stepsi in H4; split_ex.

  apply not_and_or in H1; split_ors.
  - assert (~ no_resends_U (fst x0))
      by eauto using resend_violation_steps, many_steps_stays_lame.

    unfold invariantFor in INV; simpl in *.
    eapply resend_violation_translate in H4; eauto; split_ex.
    apply INV in H4; eauto; split_ex.
    contradiction.
    
  - assert (~ labels_align x0) by admit.
      (* by eauto using labels_align_violation_steps, many_steps_stays_lame. *)

    unfold invariantFor in INV; simpl in *.
    eapply alignment_violation_translate in H4; eauto; split_ex.
    apply INV in H4; eauto; split_ex.
    contradiction.

Admitted.
