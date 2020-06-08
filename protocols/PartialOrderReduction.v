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

  Definition buildUniverse_step {A B} (ds : data_step0 A B (Base A)) (uid : user_id) : universe A B  :=
    let '(usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) := ds
    in  buildUniverse usrs adv cs gks uid
                      (mkUserData ks cmd qmsgs mycs froms sents cur_n).

  Lemma commutes_sound_no_recur' :
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
                                  
              (* no recursion *)
              -> nextAction cmd1 cmd1

              -> nextAction cmd2 cmd2
              -> (forall cmd__n x t (m : crypto t), nextAction cmd1 cmd__n -> cmd__n <> Send x m)

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' (* lbl3 lbl4 *) adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                      step_user lbl2 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl1 suid1 bd4 bd4'
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
    
    all: solve [ (do 10 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; eauto ].
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
                                  
              (* no recursion *)
              -> nextAction cmd2 cmd2

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' (* lbl3 lbl4 *) adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                    step_user lbl2 suid2 bd3 bd3'
                    /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                    /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                    /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                    /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                    /\ step_user lbl1 suid1 bd4 bd4'
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
          (do 10 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; try congruence; eauto; stuff ] .
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
                                  
              (* no recursion *)
              -> nextAction cmd2 cmd2

              -> summarize cmd1 s
              -> commutes cmd2 s

              -> forall bd3 cmdc2',
                  bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  -> exists bd3' bd4 bd4' (* lbl3 lbl4 *) adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                      step_user lbl2 suid2 bd3 bd3'
                      /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                      /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmdc2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                      /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                      /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                      /\ step_user lbl1 suid1 bd4 bd4'
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

    all : try solve [ eapply commutes_sound_no_recur'; clean_map_lookups; eauto; econstructor; eauto ].

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

      invert H43.
      specialize_simply.
      specialize (IHstep_user _ cmdc2' eq_refl).
      split_ex; subst.
      (do 10 eexists); repeat simple apply conj; eauto.
      econstructor; eauto.

    - cases cmd2;
        repeat 
        match goal with
        | [ H : nextAction ?c1 ?c2 |- _ ] => apply nextAction_couldBe in H; try contradiction
        | [ H : commutes (Send _ _) _ |- _ ] => unfold commutes in H; contradiction
        | [ H : commutes (Recv _) _ |- _ ] => unfold commutes in H; contradiction
        end; step_usr u_id2
        ; (do 10 eexists); (repeat simple apply conj); repeat solver1; eauto; repeat solver1; eauto.

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

              -> forall E (cmd__i2 : user_cmd E),
                  nextAction cmd2 cmd__i2
                  -> summarize cmd1 s
                  -> commutes cmd__i2 s

                  -> forall bd3,
                      bd3 = (usrs1,   adv,  cs,  gks,  ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                      -> exists bd3' bd4 bd4' (* lbl3 lbl4 *) adv2 cs2 gks2 usrs3' usrs4 usrs4' qmsgs3,
                        step_user lbl2 suid2 bd3 bd3'
                        /\ bd3' = (usrs3', adv2, cs2, gks2, ks2', qmsgs3, mycs2', froms2', sents2', cur_n2', cmd2')
                        /\ usrs4 = usrs3' $+ (u_id2, mkUserData ks2' cmd2' qmsgs3 mycs2' froms2' sents2' cur_n2')
                        /\ bd4 = (usrs4,   adv2, cs2, gks2, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                        /\ bd4' = (usrs4', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
                        /\ step_user lbl1 suid1 bd4 bd4'
                        /\ ( usrs4' $+ (u_id1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1') =
                            usrs2' $+ (u_id2, mkUserData ks2' cmd2' qmsgs2' mycs2' froms2' sents2' cur_n2') )
  .
  Proof.
    intros; subst; clean_map_lookups.

    specialize (nextAction_couldBe H20).
    cases cmd__i2; intros; try contradiction; clean_context.

    eapply step_na_return in H20; eauto; split_ands; subst.
    eapply step_no_depend_other_usrs_program in H; eauto; split_ex.
    (do 10 eexists); repeat simple apply conj; eauto.
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
      end.

    all: setup u_id1 cmd1; split_ex; subst;
        (do 10 eexists); repeat simple apply conj; try reflexivity; eauto.
      
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
    forall {A B} (U__r : universe A B) lbl1 u_id1 u_id2 userData1 userData2 bd1 bd1',
      U__r.(users) $? u_id1 = Some userData1
      -> U__r.(users) $? u_id2 = Some userData2
      (* -> honest_cmds_safe U__r *)
      -> syntactically_safe_U U__r
      -> universe_ok U__r
      -> adv_universe_ok U__r
      -> step_user lbl1 (Some u_id1) bd1 bd1'
      -> bd1 = build_data_step U__r userData1
      -> forall U__r' lbl2 bd2 bd2' userData2',
          U__r' = buildUniverse_step bd1' u_id1
          -> u_id1 <> u_id2
          -> U__r'.(users) $? u_id2 = Some userData2'
          -> step_user lbl2 (Some u_id2) bd2 bd2'
          -> bd2 = build_data_step U__r' userData2'
          -> forall C (cmd__n : user_cmd C) s,
              nextAction userData2.(protocol) cmd__n
              -> summarize userData1.(protocol) s
              -> commutes cmd__n s

          -> exists U__r'' (* lbl3 lbl4 *) bd3 bd3' userData1',
                step_user lbl2 (Some u_id2) (build_data_step U__r userData2) bd3
              /\ U__r'' = buildUniverse_step bd3 u_id2
              /\ U__r''.(users) $? u_id1 = Some userData1'
              /\ step_user lbl1 (Some u_id1) (build_data_step U__r'' userData1') bd3'
              /\ buildUniverse_step bd3' u_id1 = buildUniverse_step bd2' u_id2
  .
  Proof.
    intros.
    destruct U__r; destruct U__r'; simpl in *.
    destruct userData1; destruct userData2; destruct userData2'; simpl in *.
    unfold universe_ok, adv_universe_ok in *; split_ands.
    unfold build_data_step, buildUniverse_step, buildUniverse in *; simpl in *.

    dt bd1; dt bd1'; dt bd2; dt bd2'.
    clean_context; subst.
    
    repeat 
      match goal with
      | [ H : {| users := _ |} = _ |- _ ] => invert H; clean_map_lookups
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      | [ H : syntactically_safe_U _ , US1 : _ $? u_id1 = _ , US2 : _ $? u_id2 = _ |- _ ] =>
        generalize (H _ _ US1)
        ; generalize (H _ _ US2)
        ; clear H; intros; simpl in *; split_ex
      end.

    specialize (impact_from_other_user_step H4 eq_refl eq_refl eq_refl H7 H0); intros; split_ex; clean_map_lookups.
    assert (u_id2 <> u_id1) as UNE by congruence.

    eapply commutes_sound_recur' in H8; try reflexivity; try eassumption; split_ex; subst; eauto.
    (do 4 eexists); repeat simple apply conj; simpl; eauto.

    specialize (impact_from_other_user_step_commutes H8 s eq_refl eq_refl eq_refl UNE H11 H13 H); intros; eauto.
    all: simpl; clean_map_lookups; eauto.
    simpl; rewrite H26; eauto.
  Qed.

  (*   Lemma commutes_sound : *)
  (*   forall {A B} (U__r : universe A B) lbl1 u_id1 u_id2 userData1 userData2 bd1, *)
  (*     U__r.(users) $? u_id1 = Some userData1 *)
  (*     -> U__r.(users) $? u_id2 = Some userData2 *)
  (*     (* -> honest_cmds_safe U__r *) *)
  (*     -> syntactically_safe_U U__r *)
  (*     -> universe_ok U__r *)
  (*     -> adv_universe_ok U__r *)
  (*     -> step_user lbl1 (Some u_id1) (build_data_step U__r userData1) bd1 *)
  (*     -> forall U__r' lbl2 bd1' userData2', *)
  (*         U__r' = buildUniverse_step bd1 u_id1 *)
  (*         -> u_id1 <> u_id2 *)
  (*         -> U__r'.(users) $? u_id2 = Some userData2' *)
  (*         -> step_user lbl2 (Some u_id2) (build_data_step U__r' userData2') bd1' *)
  (*         -> forall C (cmd__n : user_cmd C) s, *)
  (*             nextAction userData2.(protocol) cmd__n *)
  (*             -> summarize userData1.(protocol) s *)
  (*             -> commutes cmd__n s *)

  (*         -> exists U__r'' lbl3 lbl4 bd3 bd3' userData1', *)
  (*               step_user lbl3 (Some u_id2) (build_data_step U__r userData2) bd3 *)
  (*             /\ U__r'' = buildUniverse_step bd3 u_id2 *)
  (*             /\ U__r''.(users) $? u_id1 = Some userData1' *)
  (*             /\ step_user lbl4 (Some u_id1) (build_data_step U__r'' userData1') bd3' *)
  (*             /\ buildUniverse_step bd3' u_id1 = buildUniverse_step bd1' u_id2 *)
  (* . *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct U__r; destruct U__r'; simpl in *. *)
  (*   destruct userData1; destruct userData2; destruct userData2'; simpl in *. *)
  (*   unfold universe_ok, adv_universe_ok in *; split_ands. *)
  (*   unfold build_data_step, buildUniverse_step, buildUniverse in *; simpl in *. *)

  (*   dt bd1; dt bd1'. *)
  (*   clean_context; subst. *)
    
  (*   repeat  *)
  (*     match goal with *)
  (*     | [ H : {| users := _ |} = _ |- _ ] => invert H; clean_map_lookups *)
  (*     | [ H : syntactically_safe_U _ , US1 : _ $? u_id1 = _ , US2 : _ $? u_id2 = _ |- _ ] => *)
  (*       generalize (H _ _ US1) *)
  (*       ; generalize (H _ _ US2) *)
  (*       ; clear H; intros; simpl in *; split_ex *)
  (*     end. *)

  (*   specialize (impact_from_other_user_step H4 eq_refl eq_refl eq_refl H6 H0); intros; split_ex; clean_map_lookups. *)
  (*   assert (u_id2 <> u_id1) as UNE by congruence. *)

  (*   eapply commutes_sound_recur' in H8; try reflexivity; try eassumption; split_ex; subst; eauto. *)
  (*   (do 6 eexists); repeat simple apply conj; simpl; eauto. *)
  (*   specialize (impact_from_other_user_step_commutes H8 s eq_refl eq_refl eq_refl UNE H9 H11 H); intros; eauto. *)
  (*   all: simpl; clean_map_lookups; eauto. *)
  (*   simpl; rewrite H26; eauto. *)
  (* Qed. *)

  
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

  Lemma adversary_remains_lame_user_step :
    forall {A B} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd (Base A))
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' b,

      lameAdv b adv
      -> step_user lbl (Some u_id)
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lameAdv b adv'.
  Proof.
    unfold lameAdv; intros; simpl in *.

    - destruct lbl.
      + eapply honest_silent_step_nochange_adversaries in H0; eauto.
        subst; eauto.
      + eapply honest_labeled_step_nochange_adversary_protocol in H0; eauto.
        rewrite <- H0; auto.
  Qed.

  Lemma adversary_remains_lame :
    forall A B (U U' : universe A B) b lbl,
      lameAdv b U.(adversary)
      -> step_universe U lbl U'
      -> lameAdv b U'.(adversary).
  Proof.
    inversion 2; subst; simpl in *; subst; 
      unfold build_data_step, buildUniverse, buildUniverseAdv in *; simpl in *;
        eauto using adversary_remains_lame_user_step.

    dismiss_adv.
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

      -> forall t (cmd__n : user_cmd t), nextAction userData'.(protocol) cmd__n
      -> (forall lbl bd', ~ step_user lbl (Some u_id') (build_data_step U userData') bd')
      \/ (exists u_id2 userData2, u_id' <> u_id2
                          /\ U.(users) $? u_id2 = Some userData2
                          /\ (forall s (* bd' lbl *),
                                (* step_user lbl (Some u_id2) (build_data_step U userData2) bd' *)
                                  summaries $? u_id2 = Some s
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

Hint Resolve adversary_remains_lame_step : core.
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

Lemma summarize_univ_user_step :
  forall A B (U : universe A B)  bd uid ud summaries lbl,

    step_user lbl (Some uid)
              (build_data_step U ud)
              bd
    -> U.(users) $? uid = Some ud
    -> summarize_univ U summaries
    -> summarize_univ (buildUniverse_step bd uid) summaries.
Proof.
  unfold summarize_univ; intros.
  destruct (uid ==n u_id); subst; clean_map_lookups.
  - specialize (H1 _ _ s H0); split_ex; split; eauto.
    dt bd.
    simpl in H2; clean_map_lookups; simpl.
    eapply summarize_user_step; eauto.

  - unfold build_data_step, buildUniverse_step, buildUniverse in *;
      dt bd; destruct U, ud, u_d; simpl in *; clean_map_lookups.

    eapply step_back_into_other_user with (u_id2 := u_id) in H; eauto.
    split_ors; clean_map_lookups.
    specialize (H1 _ _ s H); split_ex; simpl in *; split; eauto.
    specialize (H1 _ _ s H3); split_ex; simpl in *; split; eauto.
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

Lemma commutes_noblock' :
  forall t t__n2 (cmdc2 : user_cmd t) (cmd__n2 : user_cmd t__n2),
    nextAction cmdc2 cmd__n2
  -> forall t__hon t__adv (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) cs cs' gks gks'
      ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' cmd2 cmdc2' uid2 lbl2,

      usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
    -> step_user lbl2 (Some uid2)
              (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmdc2)
              (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmdc2')
    -> forall t1 (cmdc1 : user_cmd t1) s1, summarize cmdc1 s1
    -> forall uid1 summaries, summaries $? uid1 = Some s1
    -> commutes cmd__n2 s1
    -> uid1 <> uid2
    -> forall (usrs1' : honest_users t__hon) (adv1' : user_data t__adv) cs1' gks1'
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' cmd1 cmdc1' lbl1,

        usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
        -> step_user lbl1 (Some uid1)
                  (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1)
                  (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmdc1')
        -> forall ks2'' qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'' cmd1',
          usrs1' $? uid2 = Some (mkUserData ks2'' cmd2 qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'')
        -> exists usrs2' adv2' cs2' gks2' ks2''' qmsgs2''' mycs2''' froms2''' sents2''' cur_n2''' cmdc2'',
          step_user lbl2 (Some uid2)
                    (usrs1' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1'),
                     adv1', cs1', gks1', ks2'', qmsgs2'', mycs2'', froms2'', sents2'', cur_n2'', cmdc2)
                    (usrs2', adv2', cs2', gks2', ks2''', qmsgs2''', mycs2''', froms2''', sents2''', cur_n2''', cmdc2'')
.
Proof.
  induction 1; invert 2.

  Ltac discharge_no_commutes :=
    try match goal with
        | [ H : commutes (Send _ _) _ |- _ ] => invert H
        | [ H : commutes (Recv _) _ |- _ ] => invert H
        end.

  1-4:
    induct 1;
    intros;
    discharge_no_commutes;
    step_usr uid1;
    (do 11 eexists); econstructor; eauto.

  - induct 1;
      intros;
      discharge_no_commutes;
      try solve [ step_usr uid1;
                  clean_map_lookups;
                  (do 11 eexists); econstructor; eauto ].

     step_usr uid1; destruct (uid ==n uid2); clean_map_lookups; (do 11 eexists); econstructor; eauto.
     
     (* both users creating ciphers *)
     step_usr uid1; clean_map_lookups; (do 11 eexists);
       match goal with
       | [ |- context [ cs $+ (?cid,?c) ]] => eapply StepEncrypt with (c_id0 := next_key (cs $+ (cid,c)))
       end; clean_map_lookups; eauto using next_key_not_in.
     step_usr uid1; clean_map_lookups; (do 11 eexists);
       match goal with
       | [ |- context [ cs $+ (?cid,?c) ]] => eapply StepEncrypt with (c_id0 := next_key (cs $+ (cid,c)))
       end; clean_map_lookups; eauto using next_key_not_in.

    step_usr uid1; clean_map_lookups.
    eapply IHsummarize in H7; eauto.
    (do 11 eexists); econstructor; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      clean_map_lookups;
      try solve [ (do 11 eexists); econstructor; eauto ].

    destruct (uid ==n uid2); subst; clean_map_lookups; (do 11 eexists); econstructor; eauto.

    eapply IHsummarize in H7; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      try solve [ (do 11 eexists); econstructor; eauto ].

    destruct (uid ==n uid2); subst; clean_map_lookups; (do 11 eexists); econstructor; eauto.

    (do 11 eexists).
      match goal with
      | [ |- context [ cs $+ (?cid,?c) ]] => eapply StepSign with (c_id0 := next_key (cs $+ (cid,c)))
      end; clean_map_lookups; eauto using next_key_not_in.
    (do 11 eexists).
      match goal with
      | [ |- context [ cs $+ (?cid,?c) ]] => eapply StepSign with (c_id0 := next_key (cs $+ (cid,c)))
      end; clean_map_lookups; eauto using next_key_not_in.

    eapply IHsummarize in H7; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      clean_map_lookups;
      try solve [ (do 11 eexists); econstructor; eauto ].

    destruct (uid ==n uid2); subst; clean_map_lookups; (do 11 eexists); econstructor; eauto.

    eapply IHsummarize in H7; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      try solve [ (do 11 eexists); econstructor; eauto ].

    (do 11 eexists).
      match goal with
      | [ |- context [ gks $+ (?kid,?k) ]] => eapply StepGenerateSymKey with (k_id0 := next_key (gks $+ (kid,k)))
      end; clean_map_lookups; eauto using next_key_not_in.
    (do 11 eexists).
      match goal with
      | [ |- context [ gks $+ (?kid,?k) ]] => eapply StepGenerateSymKey with (k_id0 := next_key (gks $+ (kid,k)))
      end; clean_map_lookups; eauto using next_key_not_in.

    eapply IHsummarize in H7; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      clean_map_lookups;
      try solve [ (do 11 eexists); econstructor; eauto ].

    (do 11 eexists).
      match goal with
      | [ |- context [ gks $+ (?kid,?k) ]] => eapply StepGenerateAsymKey with (k_id0 := next_key (gks $+ (kid,k)))
      end; clean_map_lookups; eauto using next_key_not_in.
    (do 11 eexists).
      match goal with
      | [ |- context [ gks $+ (?kid,?k) ]] => eapply StepGenerateAsymKey with (k_id0 := next_key (gks $+ (kid,k)))
      end; clean_map_lookups; eauto using next_key_not_in.

    eapply IHsummarize in H7; eauto.

  - intros.
    eapply IHnextAction with (uid1 := uid1) in H8; eauto.
    split_ex.
    (do 11 eexists); econstructor; eauto.

  - induct 1;
      intros;
      step_usr uid1;
      discharge_no_commutes;
      try solve [ (do 11 eexists); econstructor; eauto ].

    Unshelve.
    all: auto.
Qed.

Lemma commutes_noblock :
  forall t__hon t__n2 (cmd2 : user_cmd (Base t__hon)) (cmd__n2 : user_cmd t__n2),
    nextAction cmd2 cmd__n2
  -> forall t__adv (usrs usrs' : honest_users t__hon) (adv adv' : user_data t__adv) cs cs' gks gks'
      ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' cmd2' uid2 lbl2,

      usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
    -> step_user lbl2 (Some uid2)
              (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
              (usrs', adv', cs', gks', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
    -> forall (cmd1 : user_cmd (Base t__hon)) s1, summarize cmd1 s1
    -> forall uid1 summaries, summaries $? uid1 = Some s1
    -> commutes cmd__n2 s1
    -> uid1 <> uid2
    -> forall (usrs1' : honest_users t__hon) (adv1' : user_data t__adv) cs1' gks1'
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' cmd1' lbl1,

        usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
        -> step_user lbl1 (Some uid1)
                  (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
                  (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')
        -> forall ks2'' qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'',
          usrs1' $? uid2 = Some (mkUserData ks2'' cmd2 qmsgs2'' mycs2'' froms2'' sents2'' cur_n2'')
        -> exists usrs2' adv2' cs2' gks2' (* lbl2' *) ks2''' qmsgs2''' mycs2''' froms2''' sents2''' cur_n2''' cmd2'',
          step_user lbl2 (Some uid2)
                    (usrs1' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1'),
                     adv1', cs1', gks1', ks2'', qmsgs2'', mycs2'', froms2'', sents2'', cur_n2'', cmd2)
                    (usrs2', adv2', cs2', gks2', ks2''', qmsgs2''', mycs2''', froms2''', sents2''', cur_n2''', cmd2'')
.
Proof.
  intros.
  eapply commutes_noblock' with (cmdc2 := cmd2) (cmdc2' := cmd2') in H7; eauto.
Qed.


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

Lemma user_step_implies_universe_step :
  forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
    (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs'
    froms froms' sents sents' cur_n cur_n' uid lbl,

    step_user lbl (Some uid)
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
              (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
    -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> step_universe
        (mkUniverse usrs adv cs gks)
        lbl
        (buildUniverse usrs' adv' cs' gks' uid (mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n')).
Proof.
  intros; destruct lbl;
    econstructor 1; eauto.
Qed.

Hint Resolve user_step_implies_universe_step : core.

Lemma max_elt_upd_map_elements' :
  forall V (m : NatMap.t V) k v,
    O.max_elt m = Some (k,v)
    -> forall m' v',
      SetoidList.InA (@eq_key_elt V) (k,v') (elements m')
    -> (forall k' v', SetoidList.InA (@eq_key_elt V) (k', v') (elements m')
                -> exists v'', SetoidList.InA (@eq_key_elt V) (k', v'') (elements m))
    -> O.max_elt m' = Some (k,v').
Proof.
  unfold O.max_elt.
  intros *. intro. intro.
  generalize (elements_3 m').
  induction (elements m'); intros.
  invert H1.

  destruct a.
  invert H0.
  invert H6.

  invert H1; invert H3; simpl in *; subst; trivial.

  simpl.
  change (O.max_elt_aux (b :: l0) = Some (k, v')).
  eapply IHl; eauto.
  invert H1; try assumption.

  invert H4; simpl in *; subst.
  exfalso.
  destruct b.
  assert (INA : SetoidList.InA (@eq_key_elt V) (k, v1) ((k0, v0) :: (k, v1) :: l0)).
  apply SetoidList.InA_cons_tl. apply SetoidList.InA_cons_hd.
  econstructor; eauto.
  eapply H2 in INA; split_ex.
  change (O.max_elt m = Some (k0,v)) in H.
  eapply O.max_elt_Above in H.
  unfold O.Above in H.
  unfold lt_key, Raw.PX.ltk in H0; simpl in H0.

  assert (IN: exists x, SetoidList.InA (eq_key_elt (elt:=V)) (k, x) (elements (elt:=V) m)) by eauto.
  rewrite <- elements_in_iff in IN.
  assert (k <> k0) by Omega.omega.
  assert (INM : In k (m $- k0)).
  rewrite in_find_iff, remove_neq_o by auto.
  unfold not; intros; clean_map_lookups.
  eapply H in INM.
  Omega.omega.
Qed.

Lemma max_elt_upd_map_elements :
  forall V (m m': NatMap.t V) k v v',
    O.max_elt m = Some (k,v)
    -> m' $? k = Some v'
    -> (forall k' v', m' $? k' = Some v' -> m $? k' <> None)
    -> O.max_elt m' = Some (k,v').
Proof.
  intros.
  eapply max_elt_upd_map_elements'; eauto.
  rewrite <- elements_mapsto_iff; rewrite <- find_mapsto_iff in H0; assumption.

  intros.
  rewrite <- elements_mapsto_iff, find_mapsto_iff in H2.
  rewrite <- elements_in_iff, in_find_iff.
  eapply H1; eauto.
Qed.

Lemma max_elt_non_stepped_user :
  forall A B cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
    (cmd cmd' : user_cmd (Base A)) ks ks' qmsgs qmsgs' mycs mycs'
    froms froms' sents sents' cur_n cur_n' uid uid' lbl
    ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1,

    NatMap.O.max_elt usrs = Some (uid,mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
    -> uid <> uid'
    -> usrs $? uid' = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> step_user lbl (Some uid')
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
              (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
    -> exists qmsgs1',
        NatMap.O.max_elt (usrs' $+ (uid', mkUserData ks' cmd' qmsgs' mycs' froms' sents' cur_n'))
        = Some (uid,mkUserData ks1 cmd1 qmsgs1' mycs1 froms1 sents1 cur_n1)
        /\ (qmsgs1' = qmsgs1 \/ exists m, qmsgs1' = qmsgs1 ++ [m])
.
Proof.
  intros.
  specialize (user_step_adds_no_users H2 eq_refl eq_refl); intros.
  generalize H2; intros STEP.
  specialize (NatMap.O.max_elt_MapsTo H); intros LK; rewrite find_mapsto_iff in LK.
  eapply step_limited_change_other_user with (u_id2 := uid) in STEP; eauto; split_ands.
  
  split_ors.
  eapply max_elt_upd_map_elements in H5; eauto; intros.
  destruct (k' ==n uid'); subst; clean_map_lookups; eapply H3; eauto.

  eapply max_elt_upd_map_elements in H5; eauto; intros.
  destruct (k' ==n uid'); subst; clean_map_lookups; eapply H3; eauto.

Qed.

Lemma map_add_rw :
  forall V (m : NatMap.t V) k v,
    Raw.add k v m = m $+ (k,v).
Proof.
  intros.
  reflexivity.
Qed.

Lemma step_univ_inv' :
  forall t__hon t__adv lbl ru ru' b,
    @step_universe t__hon t__adv ru lbl ru'
    -> lameAdv b ru.(adversary)
    -> exists uid ud lbl bd,
      ru.(users) $? uid = Some ud
    /\ step_user lbl (Some uid)
                (build_data_step ru ud)
                bd
    /\ ru' = buildUniverse_step bd uid.
Proof.
  induction 1; intros; dismiss_adv; subst; eauto 8.
Qed.

Lemma invert_step_label :
  forall A B C suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' (cmd cmd' : user_cmd C)
        ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' a,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> lbl = Action a
      -> (exists t (msg : crypto t) pat, a = Input msg pat froms)
      \/ (exists t (msg : crypto t) from_usr to_usr, a = Output msg from_usr to_usr sents).
Proof.
  induction 1; inversion 1; inversion 1; intros; try discriminate; subst; eauto.
  invert H20; eauto.
  invert H20; eauto 8.
Qed.

Lemma add_key_perm_as_merge :
  forall ks kid,
    add_key_perm kid true ks = ks $k++ ($0 $+ (kid,true)).
Proof.
  intros.
  assert (RW : add_key_perm kid true ks = ks $+ (kid,true))
    by (unfold add_key_perm; cases (ks $? kid); eauto);
      rewrite RW in *.

  apply map_eq_Equal; unfold Equal; intros.
  destruct (y ==n kid); subst; clean_map_lookups; symmetry.

  - assert (ZERO : $0 $+ (kid,true) $? kid = Some true) by (clean_map_lookups; eauto).
    cases (ks $? kid).
    assert (TR: true = greatest_permission b true)
      by (unfold greatest_permission; rewrite orb_true_r; eauto).
    rewrite TR at 2.
    eapply merge_perms_chooses_greatest; eauto.

    eapply merge_perms_adds_ks2; eauto.

  - cases (ks $? y).
    eapply merge_perms_adds_ks1; eauto.
    clean_map_lookups; eauto.

    eapply merge_perms_adds_no_new_perms; eauto.
Qed.

Lemma message_eq_user_add :
  forall A B (usrs : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
    ks ks' cmd qmsgs mycs froms sents cur_n cmd' qmsgs' mycs' froms' sents' cur_n'
    t (m__rw : crypto t) m__iw iu chid uid,

    usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> (cs' = cs \/ (exists cid c, ~ In cid cs /\ cs' = cs $+ (cid,c)))
    -> (ks' = ks \/ (exists kid k, ~ In kid gks /\ ks' = ks $k++ ($0 $+ (kid,k))))
    -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
    (* -> (forall cid c, cs $? cid = Some c -> cs' $? cid = Some c) *)
    -> MessageEq.message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid
    -> MessageEq.message_eq
        m__rw
        {| users :=
             usrs $+ (uid,
                      {| key_heap := ks';
                         protocol := cmd';
                         msg_heap := qmsgs';
                         c_heap := mycs';
                         from_nons := froms';
                         sent_nons := sents';
                         cur_nonce := cur_n' |});
           adversary := adv';
           all_ciphers := cs';
           all_keys := gks' |} m__iw iu chid.
Proof.
  intros.
  split_ors; split_ex; subst.

  - invert H3; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *;
      destruct (u ==n uid); subst; clean_map_lookups; eauto;
        simpl.

    specialize (H12 _ _ _ H H1 H3); simpl in *; eauto.
    specialize (H12 _ _ _ b__rwenc H H1 H3 H4); simpl in *; eauto.
    
  - invert H3; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *;
      destruct (u ==n uid); subst; clean_map_lookups; eauto;
        simpl.

    specialize (H13 _ _ _ H H3 H4); simpl in *; eauto.
    specialize (H13 _ _ _ b__rwenc H H3 H4 H5); simpl in *; eauto.

  - invert H3; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *.

    + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2.
      specialize (H2 _ _ H10).
      assert (x <> k__sign) by (invert H2; destruct (k__sign ==n x); clean_map_lookups; eauto).
    
      invert H4; solve_perm_merges; eauto; simpl.

      assert (RW: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign).
      cases (ks $? k__sign).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW.

      specialize (H13 _ _ _ H H3); eauto.

    + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2.
      specialize (H2 _ _ H10).
      assert (x <> k__sign) by (invert H2; destruct (k__sign ==n x); clean_map_lookups; eauto).
      assert (x <> k__enc) by (invert H2; destruct (k__enc ==n x); clean_map_lookups; eauto).
    
      invert H4; invert H5; solve_perm_merges; eauto; simpl.

      assert (RW1: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign).
      cases (ks $? k__sign).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW1.

      assert (RW2: ks $k++ ($0 $+ (x, x0)) $? k__enc = ks $? k__enc).
      cases (ks $? k__enc).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW2.

      specialize (H13 _ _ _ b__rwenc H H3); eauto.

  - invert H3; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
      intros;
      autorewrite with find_user_keys in *.

    + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2.
      specialize (H2 _ _ H11).
      assert (x <> k__sign) by (invert H2; destruct (k__sign ==n x); clean_map_lookups; eauto).
    
      invert H5; solve_perm_merges; eauto; simpl.

      assert (RW: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign).
      cases (ks $? k__sign).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW.

      specialize (H14 _ _ _ H H4); eauto.

    + unfold encrypted_ciphers_ok in H2; rewrite Forall_natmap_forall in H2.
      specialize (H2 _ _ H11).
      assert (x <> k__sign) by (invert H2; destruct (k__sign ==n x); clean_map_lookups; eauto).
      assert (x <> k__enc) by (invert H2; destruct (k__enc ==n x); clean_map_lookups; eauto).
    
      invert H5; invert H6; solve_perm_merges; eauto; simpl.

      assert (RW1: ks $k++ ($0 $+ (x, x0)) $? k__sign = ks $? k__sign).
      cases (ks $? k__sign).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW1.

      assert (RW2: ks $k++ ($0 $+ (x, x0)) $? k__enc = ks $? k__enc).
      cases (ks $? k__enc).
      eapply merge_perms_adds_ks1; eauto; clean_map_lookups; eauto.
      eapply merge_perms_adds_no_new_perms; eauto.
      rewrite RW2.

      specialize (H14 _ _ _ b__rwenc H H4); eauto.
Qed.

Lemma message_eq_user_add_inv :
  forall A B (usrs : honest_users A) (adv adv' : user_data B) cs gks gks'
    ks cmd qmsgs mycs froms sents cur_n cmd' qmsgs' mycs' froms' sents' cur_n'
    t (m__rw : crypto t) m__iw iu chid uid,

    usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> MessageEq.message_eq
        m__rw
        {| users :=
             usrs $+ (uid,
                      {| key_heap := ks;
                         protocol := cmd';
                         msg_heap := qmsgs';
                         c_heap := mycs';
                         from_nons := froms';
                         sent_nons := sents';
                         cur_nonce := cur_n' |});
           adversary := adv';
           all_ciphers := cs;
           all_keys := gks' |} m__iw iu chid
    -> MessageEq.message_eq m__rw {| users := usrs; adversary := adv; all_ciphers := cs; all_keys := gks |} m__iw iu chid.
Proof.
  intros.
  
  invert H0; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
    intros;
    autorewrite with find_user_keys in *;
    destruct (u ==n uid); subst; clean_map_lookups; eauto;
      simpl.

  specialize (H11 uid (mkUserData ks cmd' qmsgs' mycs' froms' sents' cur_n') data__iw).
  rewrite add_eq_o in H11 by trivial.
  specialize (H11 eq_refl H1 H2); simpl in H11; eauto.

  specialize (H11 u data__rw data__iw).
  rewrite add_neq_o in H11 by congruence; eauto.

  specialize (H11 uid (mkUserData ks cmd' qmsgs' mycs' froms' sents' cur_n') data__iw b__rwenc).
  rewrite add_eq_o in H11 by trivial.
  specialize (H11 eq_refl H1 H2); simpl in H11; eauto.

  specialize (H11 u data__rw data__iw).
  rewrite add_neq_o in H11 by congruence; eauto.
Qed.

Hint Resolve message_eq_user_add message_eq_user_add_inv : core.

Lemma action_matches_other_user_step' :
  forall A B C suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' (cmd cmd' : user_cmd C)
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' uid1,

      bd = (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd)
      -> bd' = (usrs', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd')
      -> suid = Some uid1
      -> message_queue_ok (findUserKeys usrs) cs qmsgs1 gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queue_ok cs (findUserKeys usrs) mycs1
      -> forall ctx sty, syntactically_safe uid1 ctx cmd sty
      -> typingcontext_sound ctx (findUserKeys usrs) cs uid1
      -> forall cmd1 cmd1' cmd2 cmd2' uid2 ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' a
          usrs'' adv'' cs'' gks'',
          uid1 <> uid2
          -> usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
          -> usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
          -> step_user (Action a) (Some uid2)
                      (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                      (usrs'', adv'', cs'', gks'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
          -> forall ia iu,
              action_matches a (mkUniverse usrs adv cs gks) ia iu
              -> action_matches a (mkUniverse (usrs' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')) adv' cs' gks') ia iu.
Proof.

  Ltac action_matches_solver :=
    repeat 
      match goal with
      | [ H : step_user (Action _) _ _ _ |- _ ] =>
        eapply invert_step_label in H; eauto; split_ors; split_ex; subst; simpl
      | [ H : action_matches _ _ _ _ |- _ ] => invert H
      | [ H : Input _ _ _ = _ |- _ ] => invert H
      | [ H : Output _ _ _ _ = _ |- _ ] => invert H
      | [ |- action_matches (Input _ _ _) _ _ _ ] => econstructor 1; eauto
      | [ |- action_matches (Output _ _ _ _) _ _ _ ] => econstructor 2; eauto
      end.

  Ltac message_eq_solver :=
    match goal with
    | [ H : MessageEq.message_eq _ {| all_ciphers := ?cs |} _ _ _
        |-  MessageEq.message_eq _ {| all_ciphers := ?cs ; users := ?usrs |} _ _ _ ] =>
      match usrs with
      | _ $+ (_ , {| key_heap := add_key_perm ?kid ?k ?ks1 |}) =>
        rewrite add_key_perm_as_merge;
          eapply message_eq_user_add with (cs' := cs) (ks' := ks1 $k++ ($0 $+ (kid,k)))
      | _ $+ (_ , {| key_heap := ?ks1 |}) =>
        eapply message_eq_user_add with (cs' := cs) (ks' := ks1)
      end
    | [ H : MessageEq.message_eq _ {| all_ciphers := ?cs |} _ _ _
        |-  MessageEq.message_eq _ {| all_ciphers := ?cs $+ (?cid,?c) ; users := ?usrs |} _ _ _ ] =>
      match usrs with
      | _ $+ (_ , {| key_heap := ?ks1 |}) =>
        eapply message_eq_user_add with (cs' := cs $+ (cid,c)) (ks' := ks1)
      end
    end.
  
  induction 1; inversion 1; inversion 1; intros; subst;
    try solve [ action_matches_solver; message_eq_solver; eauto ].

  - invert H28.
    eapply IHstep_user in H33; eauto.
  - admit. (* labeled *)

  (* - invert H32; split_ex. *)

  (*   unfold typingcontext_sound in *; split_ex. *)
  (*   assert (msg_pattern_safe (findUserKeys usrs') pat). *)
  (*   invert H34; *)
  (*     match goal with *)
  (*     | [ HK : HonestKey ?ctx _, HON : (forall _, HonestKey ?ctx _ -> findUserKeys usrs' $? _ = Some true) |- _ ] => *)
  (*       specialize (HON _ HK) *)
  (*     end; econstructor; eauto. *)

  (*   assert ( MHS: msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto. *)
  (*   apply Automation.message_honestly_signed_msg_signing_key_honest in MHS; split_ex. *)

  (*   eapply H1 in H9; eauto; split_ex. *)
  (*   eapply H11 in H10; split_ex. *)

  (*   action_matches_solver. *)

  (*   + invert H22; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto; *)
  (*       intros; *)
  (*       autorewrite with find_user_keys in *; *)
  (*       rewrite honestk_merge_new_msgs_keys_same in * by eauto; *)
  (*       destruct (u ==n uid1); subst; clean_map_lookups; eauto; simpl. *)

  (*     * unfold message_no_adv_private in H10. *)
  (*       specialize (H25 _ _ _ H37 H14 H15); simpl in *; eauto. *)
  (*       destruct H25; split; intros. *)
  (*       ** eapply merge_perms_split in H16; split_ors; eauto. *)
  (*          apply H10 in H16; split_ex; discriminate. *)
  (*       ** eapply H13 in H16; solve_perm_merges. *)
  (*     * unfold message_no_adv_private in H10. *)
  (*       specialize (H25 _ _ _ b__rwenc H37 H14 H15 H16); simpl in *; eauto. *)
  (*       destruct H25; split; intros; split_ex. *)
  (*       ** eapply merge_perms_split in H17; split_ors; eauto. *)
  (*          2: apply H10 in H17; split_ex; discriminate. *)
  (*          apply merge_perms_split in H18; split_ors; eauto. *)
  (*          specialize (H10 _ _ H18); split_ex; subst. *)
  (*          unfold MessageEq.resolve_perm. *)

  (*       ** eapply H13 in H16; solve_perm_merges. *)
    
  - admit. (* labeled *)
  - 
    unfold user_cipher_queue_ok in H35; rewrite Forall_forall in H35.
    apply H35 in H7; clear H35; split_ex.

    clean_context.
    unfold cipher_honestly_signed in H5; clean_map_lookups.
    rewrite <- honest_key_honest_keyb in H5; invert H5.
    unfold encrypted_ciphers_ok in H34; rewrite Forall_natmap_forall in H34;
      eapply H34 in H; clear H34.
    invert H; try contradiction.

    action_matches_solver.

    + invert H18; [ econstructor 1 | econstructor 2 | econstructor 3 ]; simpl in *; eauto;
        intros;
        autorewrite with find_user_keys in *;
        rewrite  honestk_merge_new_msgs_keys_dec_same in * by eauto;
        destruct (u ==n uid1); subst; clean_map_lookups; eauto; simpl.

      specialize (H21 _ _ _ H39 H5 H6); simpl in H21.
      destruct kp__sign; eauto. admit.

Admitted.


Lemma action_matches_other_user_step_inv' :
  forall A B C suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' (cmd cmd' : user_cmd C)
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' uid1,

      bd = (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd)
      -> bd' = (usrs', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd')
      -> suid = Some uid1
      -> forall cmd1 cmd1' cmd2 cmd2' uid2 ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' a
          usrs'' adv'' cs'' gks'',
          uid1 <> uid2
          -> usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
          -> usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
          -> step_user (Action a) (Some uid2)
                      (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                      (usrs'', adv'', cs'', gks'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
          -> forall ia iu,
              action_matches a (mkUniverse (usrs' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')) adv' cs' gks') ia iu
              -> action_matches a (mkUniverse usrs adv cs gks) ia iu.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto;
    repeat 
      match goal with
      | [ H : step_user (Action _) _ _ _ |- _ ] =>
        eapply invert_step_label in H; eauto; split_ors; split_ex; subst; simpl
      | [ H : action_matches _ _ _ _ |- _ ] => invert H
      | [ H : Input _ _ _ = _ |- _ ] => invert H
      | [ H : Output _ _ _ _ = _ |- _ ] => invert H
      | [ |- action_matches (Input _ _ _) _ _ _ ] => econstructor 1; eauto
      | [ |- action_matches (Output _ _ _ _) _ _ _ ] => econstructor 2; eauto
      end.

Admitted.

Lemma action_matches_other_user_step_inv :
  forall A B lbl
    cs cs' cs'' (usrs usrs' usrs'': honest_users A) (adv adv' adv'' : user_data B) gks gks' gks'' cmd1 cmd1'
    ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' uid1,

    step_user lbl (Some uid1)
              (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              (usrs', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')

    -> forall cmd2 cmd2' uid2 ks2 ks2' qmsgs2 qmsgs2' mycs2 mycs2' froms2 froms2' sents2 sents2' cur_n2 cur_n2' a,
      uid1 <> uid2
      -> usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
      -> usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
      -> step_user (Action a) (Some uid2)
                  (usrs, adv, cs, gks, ks2, qmsgs2, mycs2, froms2, sents2, cur_n2, cmd2)
                  (usrs'', adv'', cs'', gks'', ks2', qmsgs2', mycs2', froms2', sents2', cur_n2', cmd2')
      -> forall ia iu,
          action_matches a (mkUniverse (usrs' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')) adv' cs' gks') ia iu
          -> action_matches a (mkUniverse usrs adv cs gks) ia iu.
Proof.
  intros.
  eapply action_matches_other_user_step_inv' with (uid1 := uid1) (uid2 := uid2) in H; eauto.
Qed.

Lemma user_step_summaries_still_good' :
  forall A B C suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' (cmdc1 cmdc1' : user_cmd C)
        ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' uid1,

      bd = (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmdc1)
      -> bd' = (usrs', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmdc1')
      -> suid = Some uid1
      -> forall cmd1, usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
      -> forall summaries t__n (cmd__n : user_cmd t__n) uid ud,
          usrs $? uid = Some ud
          -> uid <> uid1
          -> nextAction ud.(protocol) cmd__n
          -> summarize_univ (mkUniverse usrs adv cs gks) summaries
      -> (forall uid2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
            uid <> uid2
            -> usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists s, summaries $? uid2 = Some s /\ commutes cmd__n s)
      -> (forall uid2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2 usrs'' cmd1',
            uid <> uid2
            -> usrs'' = usrs' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')
            -> usrs'' $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists s, summaries $? uid2 = Some s /\ commutes cmd__n s).
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto;
    destruct (uid1 ==n uid2); subst; clean_map_lookups; eauto.

  destruct rec_u; destruct (rec_u_id ==n uid2); subst; clean_map_lookups; eauto.
Qed.

Lemma user_step_summaries_still_good :
  forall A B lbl cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks' cmd1 cmd1'
    ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' froms1 froms1' sents1 sents1' cur_n1 cur_n1' uid1,

    step_user lbl (Some uid1)
              (usrs, adv, cs, gks, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd1)
              (usrs', adv', cs', gks', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd1')

      -> usrs $? uid1 = Some (mkUserData ks1 cmd1 qmsgs1 mycs1 froms1 sents1 cur_n1)
      -> forall summaries t__n (cmd__n : user_cmd t__n) uid ud,
          usrs $? uid = Some ud
          -> uid <> uid1
          -> nextAction ud.(protocol) cmd__n
          -> summarize_univ (mkUniverse usrs adv cs gks) summaries
      -> (forall uid2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
            uid <> uid2
            -> usrs $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists s, summaries $? uid2 = Some s /\ commutes cmd__n s)
      -> (forall uid2 ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2 usrs'',
            uid <> uid2
            -> usrs'' = usrs' $+ (uid1, mkUserData ks1' cmd1' qmsgs1' mycs1' froms1' sents1' cur_n1')
            -> usrs'' $? uid2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists s, summaries $? uid2 = Some s /\ commutes cmd__n s).
Proof.
  eauto using user_step_summaries_still_good'.
Qed.

Hint Resolve user_step_summaries_still_good : core.


(* COMMUTING COMMAND RUNS FIRST!! *)
      
Lemma translate_trace_commute :
  forall t__hon t__adv i st st' b,
    @stepsi t__hon t__adv (1 + i) st st'
    -> lameAdv b (fst st).(adversary)
    (* -> (forall st'', ~ step st' st'') *)
    -> (forall lbl ru, ~ step_universe (fst st') lbl ru)
    -> forall summaries, summarize_univ (fst st) summaries
    -> forall uid ud, NatMap.O.max_elt (fst st).(users) = Some (uid,ud)
    -> forall t (cmd__n : user_cmd t), nextAction ud.(protocol) cmd__n
    -> (forall u_id2 userData2,
          uid <> u_id2
          -> users (fst st) $? u_id2 = Some userData2
          -> exists s,
                summaries $? u_id2 = Some s
              /\ commutes cmd__n s)
    -> forall lbl bd, step_user lbl (Some uid) (build_data_step (fst st) ud) bd
    -> exists lbl' bd' ru,
            step_user lbl' (Some uid) (build_data_step (fst st) ud) bd'
          /\ ru = buildUniverse_step bd' uid
          /\ (match lbl' with
             | Silent    => stepsi i (ru, snd st) st'
             | Action ra => exists iu' iu'' ia,
                               istepSilent^* (snd st) iu'
                               /\ IdealWorld.lstep_universe iu' (Action ia) iu''
                               /\ action_matches ra (fst st) ia iu'
                               /\ stepsi i (ru, iu'') st'
             end).
Proof.
  induct 1; intros; eauto.

  invert H0.

  - clear IHstepsi.
    invert H; simpl in *;
      repeat
        match goal with
        | [ H : step_universe _ _ _ |- _ ] => invert H; dismiss_adv
        | [ H : O.max_elt _ = Some _ |- _ ] =>
          apply NatMap.O.max_elt_MapsTo in H; rewrite find_mapsto_iff in H
        end.

    + destruct (uid ==n u_id); subst; clean_map_lookups.

      (* equal *)
      (do 3 eexists); repeat simple apply conj; simpl; eauto 8.
      simpl; eauto.
      econstructor 1.
      econstructor 1; eauto.
      econstructor.

      (* not equal *) 
      assert (LK : users ru $? u_id = Some userData) by assumption.
      eapply H6 in LK; eauto; split_ex.

      destruct userData, ud; unfold build_data_step in *; simpl in *.

      specialize (H3 _ _ x H); split_ex.
      dt bd.
      unfold buildUniverse in H2.

      generalize H4; intros STEP.
      eapply step_limited_change_other_user in STEP; eauto; split_ex.
      split_ors; clean_map_lookups; eauto.

      * eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs) in H5; eauto; split_ex;
          exfalso; eapply H2; eauto.

      * eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs) in H5; eauto; split_ex;
          exfalso; eapply H2; eauto.

    + destruct (uid ==n u_id); subst; clean_map_lookups.

      (* equal *)
      (do 3 eexists); repeat simple apply conj; eauto 10.
      simpl.
      (do 3 eexists); repeat simple apply conj; eauto.
      econstructor.

      (* not equal *) 
      assert (LK : users ru $? u_id = Some userData) by assumption.
      eapply H6 in LK; eauto; split_ex.

      destruct userData, ud; unfold build_data_step in *; simpl in *.

      specialize (H3 _ _ x H); split_ex.
      dt bd.
      unfold buildUniverse in H2.

      generalize H4; intros STEP.
      eapply step_limited_change_other_user in STEP; eauto; split_ex.
      split_ors; clean_map_lookups; eauto.

      * eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs) in H5; eauto; split_ex;
          exfalso; eapply H2; eauto.
      * eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs) in H5; eauto; split_ex;
          exfalso; eapply H2; eauto.

  - assert (LAME: lameAdv b (adversary (fst st))) by assumption.
    eapply adversary_remains_lame_step in LAME; eauto.

    assert (SUMMARIES : summarize_univ (fst st) summaries) by assumption.
    eapply summarize_univ_step in SUMMARIES; eauto.

    specialize (IHstepsi _ _ eq_refl LAME H2 _ SUMMARIES).

    assert (next : nextAction (protocol ud) cmd__n) by assumption.

    dt bd; destruct ud; simpl in *.

    invert H; simpl in *;
      match goal with
      | [ H : step_universe _ _ _ |- _ ] => invert H; dismiss_adv
      end;
      match goal with
      | [ H : O.max_elt _ = Some _ |- _ ] =>
        let MAX := fresh "H"
        in generalize H; intros MAX;
             apply NatMap.O.max_elt_MapsTo in MAX; rewrite find_mapsto_iff in MAX
      end.

    + destruct (uid ==n u_id); subst; clean_map_lookups.

      (* equal *)
      (do 3 eexists); repeat simple apply conj; eauto.
      simpl; eauto.
      econstructor; eauto.

      (* not equal *)
      assert (LK : users ru $? u_id = Some userData) by assumption.
      eapply H6 in LK; eauto; split_ex.

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.
      specialize (H3 _ _ x H); split_ex.

      generalize H4; intros MAX;
        eapply max_elt_non_stepped_user with (uid := uid) (uid' := u_id) in MAX; eauto; split_ex.
      rename x0 into msg_heap'.

      specialize (IHstepsi _ _ H14 _ _ next); simpl in *.

      apply NatMap.O.max_elt_MapsTo in H14; rewrite find_mapsto_iff in H14; clean_map_lookups.
      eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in next; eauto; split_ex.
      eapply IHstepsi in H11; clear IHstepsi; eauto.

      2 : {
        intros.
        destruct (u_id ==n u_id2); subst; clean_map_lookups; eauto.
        destruct userData2; eapply step_back_into_other_user with (u_id3 := u_id2) in H10; eauto.
        split_ors; split_ex; eauto.
      }
      split_ex; subst.
      eapply commutes_sound with (u_id1 := u_id) (u_id2 := uid) in H11; eauto.
      split_ex; subst.
      2-4: admit. (* silly universe preconditions that need to be added *)
      2-3: unfold build_data_step, buildUniverse_step; simpl; eauto.

      unfold build_data_step in H11; destruct ru; simpl in *.
      (do 3 eexists); repeat simple apply conj; eauto.
      destruct x11; split_ex; eauto.
      econstructor; eauto.
      dt x14; dt x15; destruct x16; simpl in *.
      econstructor 1; eauto.
      econstructor 1; eauto.
      rewrite <- H20; trivial.
      
      (do 3 eexists); repeat simple apply conj; eauto.
      dt x14; eapply action_matches_other_user_step_inv with (uid1 := u_id) (uid2 := uid) in H21; eauto.
      econstructor; eauto.
      dt x14; dt x15; destruct x16; simpl in *.
      econstructor 1; eauto.
      econstructor 1; eauto.
      rewrite <- H20; trivial.

    + destruct (uid ==n u_id); subst; clean_map_lookups.

      (* equal *)
      (do 3 eexists); repeat simple apply conj; eauto 10.
      simpl.
      (do 3 eexists); repeat simple apply conj; eauto.
      econstructor; eauto.

      (* not equal *)
      assert (LK : users ru $? u_id = Some userData) by assumption.
      eapply H6 in LK; eauto; split_ex.

      destruct userData; unfold buildUniverse, build_data_step in *; simpl in *.
      specialize (H3 _ _ x H); split_ex.

      generalize H4; intros MAX;
        eapply max_elt_non_stepped_user with (uid := uid) (uid' := u_id) in MAX; eauto; split_ex.
      rename x0 into msg_heap'.

      specialize (IHstepsi _ _ H17 _ _ next); simpl in *.

      apply NatMap.O.max_elt_MapsTo in H17; rewrite find_mapsto_iff in H17; clean_map_lookups.

      eapply commutes_noblock with (usrs := users ru) (usrs1' := usrs0) in next; eauto; split_ex.
      eapply IHstepsi in H14; clear IHstepsi; eauto.

      2 : {
        intros.
        destruct (u_id ==n u_id2); subst; clean_map_lookups; eauto.
        destruct userData2; eapply step_back_into_other_user with (u_id3 := u_id2) in H13; eauto.
        split_ors; split_ex; eauto.
      }
      split_ex; subst.

      eapply commutes_sound with (u_id1 := u_id) (u_id2 := uid) in H14; eauto.
      split_ex; subst.

      2-4: admit. (* silly universe preconditions that need to be added *)
      2-3: unfold build_data_step, buildUniverse_step; simpl; eauto.
      
      unfold build_data_step in H11; destruct ru; simpl in *.
      (do 3 eexists); repeat simple apply conj; eauto.
      destruct x11; split_ex; eauto.
      econstructor; eauto.
      dt x14; dt x15; destruct x16; simpl in *.
      econstructor 2; eauto.
      econstructor 1; eauto.
      rewrite <- H23; trivial.

      admit. (* action matches other sense *)
      
      (do 3 eexists); repeat simple apply conj; eauto.
      dt x14; eapply action_matches_other_user_step_inv with (uid1 := u_id) (uid2 := uid) in H24; eauto.

      admit. (* action matches other sense LOOK HERE  *)
      
      econstructor; eauto.
      dt x14; dt x15; destruct x16; simpl in *.
      econstructor 2; eauto.
      econstructor 1; eauto.
      rewrite <- H23; trivial.

      admit. (* action matches other sense LOOK HERE  *)

Admitted.

Lemma step_na :
  forall A B uid lbl bd
    cs (usrs: honest_users A) (adv : user_data B) gks
    (cmd : user_cmd (Base A)) ks qmsgs mycs froms sents cur_n,

    step_user lbl (Some uid)
              (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
              bd
    -> usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents cur_n)
    -> exists t (cmd__n : user_cmd t),
        nextAction cmd cmd__n.
Proof.
  intros.
  dt bd.
  eapply step_implies_na in H; eauto.
  split_ors; eauto 8.
Qed.

Lemma na_always_exists :
  forall t (cmd : user_cmd t),
  exists t (cmd__n : user_cmd t),
    nextAction cmd cmd__n.
Proof.
  induction cmd;
    try solve [ (do 2 eexists); econstructor; eauto ].

  split_ex.
  (do 2 eexists); econstructor; eauto.
Qed.

Require Import JMeq.

Lemma na_deterministic :
  forall t (cmd : user_cmd t),
      forall t1 (cmd1 : user_cmd t1), nextAction cmd cmd1
    -> forall t2 (cmd2 : user_cmd t2), nextAction cmd cmd2
    -> t1 = t2 /\ (JMeq cmd1 cmd2).
Proof.
  induct 1;
    try solve [ invert 1; intros; subst; eauto ].
  intros.
  induct H; eauto.
Qed.

Lemma resend_violation_translate' :
  forall t__hon t__adv n st st' b summaries,
    stepsi n st st'
    -> lameAdv b (fst st).(adversary)
    -> summarize_univ (fst st) summaries
    (* -> (forall st'', step st' st'' -> False) *)
    -> (forall lbl ru, step_universe (fst st') lbl ru -> False)
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
          /\ (forall u_id2 userData2 t (cmd__n : user_cmd t),
                uid <> u_id2
              -> (fst st).(users) $? u_id2 = Some userData2
              -> nextAction ud.(protocol) cmd__n
              (* -> forall bd lbl, step_user lbl (Some u_id2) (build_data_step (fst st) userData2) bd *)
              -> exists s,
                  summaries $? u_id2 = Some s
                /\ commutes cmd__n s))).

  - firstorder idtac.

    generalize (O.max_elt_MapsTo H4); intros MT; 
      rewrite find_mapsto_iff in MT.
    destruct x0.
    generalize H5; intros NA; eapply step_na in NA; eauto.
    split_ex; simpl in *.
    eapply translate_trace_commute in H; eauto.
    firstorder idtac; subst.

    unfold build_data_step in *; dt x5; simpl in *.
    assert (LAME: lameAdv b (adversary (fst st))) by assumption.
    eapply adversary_remains_lame_user_step with (lbl := x4) in LAME; eauto.

    assert (SUMMARIES : summarize_univ (fst st) summaries) by assumption.
    eapply summarize_univ_user_step in SUMMARIES; eauto.
    2: unfold build_data_step; simpl; eauto.

    destruct x4; split_ex;
      match goal with
      | [ H : stepsi _ _ _ |- _ ] => eapply IHn in H; eauto; split_ex
      end.

    exists x4; split; eauto.
    eapply TrcFront; eauto.
    destruct st; econstructor; eauto.
    econstructor 1; eauto.
    econstructor 1; eauto.

    exists x7; split; eauto.
    eapply TrcFront; eauto.
    destruct st; econstructor; eauto.
    econstructor 2; eauto.
    econstructor 1; eauto.
    
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
      specialize (H4 x1); simpl in H4; split_ex.
      eapply not_and_or in H4; split_ors; try contradiction.
      eapply not_and_or in H4.

      destruct (x0 ==n u_id); subst; clean_map_lookups.
      * generalize (O.max_elt_MapsTo H8); intros MT.
        rewrite find_mapsto_iff in MT.
        clean_map_lookups.
        econstructor; eauto.

      * econstructor; eauto.
        generalize (na_always_exists (protocol x1)); intros; split_ex.
        econstructor 2; eauto.
        
        split_ors.
        left; unfold not; intros; eauto.
        right; intros.

        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.

        apply imply_to_and in H4; split_ands.
        apply imply_to_and in H10; split_ands.
        apply imply_to_and in H11; split_ands.
        (* apply not_all_ex_not in H12; split_ex. *)
        (* apply not_all_ex_not in H12; split_ex. *)
        (* apply imply_to_and in H12; split_ands. *)
        firstorder idtac; simpl in *.

        eapply na_deterministic in H11; eauto; split_ands; subst.
        invert H13.
        exists x4; exists x5; repeat simple apply conj; eauto; intros; simpl in *.

    + destruct u; unfold build_data_step, lameAdv in *; simpl in *.
      rewrite H0 in H6; invert H6.

    + pose proof (max_element_some _ _ H6); firstorder idtac.
      specialize (H4 x0); firstorder idtac.
      specialize (H4 x1); simpl in H4; split_ex.
      eapply not_and_or in H4; split_ors; try contradiction.
      eapply not_and_or in H4.

      destruct (x0 ==n u_id); subst; clean_map_lookups.
      * generalize (O.max_elt_MapsTo H8); intros MT.
        rewrite find_mapsto_iff in MT.
        clean_map_lookups.
        econstructor; eauto.

      * econstructor; eauto.
        generalize (na_always_exists (protocol x1)); intros; split_ex.
        econstructor 2; eauto.
        
        split_ors.
        left; unfold not; intros; eauto.
        right; intros.

        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.
        apply not_all_ex_not in H4; split_ex.

        apply imply_to_and in H4; split_ands.
        apply imply_to_and in H10; split_ands.
        apply imply_to_and in H11; split_ands.
        (* apply not_all_ex_not in H15; split_ex. *)
        (* apply not_all_ex_not in H15; split_ex. *)
        (* apply imply_to_and in H15; split_ands. *)
        firstorder idtac; simpl in *.

        eapply na_deterministic in H11; eauto; split_ands; subst.
        invert H16.
        exists x4; exists x5; repeat simple apply conj; eauto; intros; simpl in *.
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
