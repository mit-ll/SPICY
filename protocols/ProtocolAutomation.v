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
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     List
     (* Morphisms *)
     Eqdep
.

Require Import
        MyPrelude
        Maps
        Messages
        MessageEq
        Common
        Keys
        KeysTheory
        Automation
        Tactics
        RealWorld
        Simulation
        AdversaryUniverse
        UniverseEqAutomation.

Require IdealWorld RealWorld.

Set Implicit Arguments.

Definition quiet (lbl : rlabel) :=
  match lbl with
  | Silent => True
  | _ => False
  end.

Notation "~^*" := (trc3 step_universe quiet) (at level 0).

Section RealWorldLemmas.
  Import RealWorld.

  Lemma multiStepSilentInv :
    forall {A B} (U__r U__r': universe A B) b,
        ~^* U__r U__r'
      -> U__r.(adversary).(protocol) = Return b
      -> U__r = U__r'
      \/ exists usrs adv cs u_id userData gks ks cmd qmsgs mycs froms tos cur_n,
          ~^* (buildUniverse usrs adv cs gks u_id
                                        {| key_heap := ks
                                         ; protocol := cmd
                                         ; msg_heap := qmsgs
                                         ; c_heap := mycs
                                         ; from_nons := froms
                                         ; sent_nons := tos
                                         ; cur_nonce := cur_n |}) U__r'
          /\ users U__r $? u_id = Some userData
          /\ step_user Silent
                      (Some u_id)
                      (RealWorld.build_data_step U__r userData)
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, cmd).
  Proof.
    intros * H ADV.
    invert H; intuition idtac.
    right.
    invert H1; unfold quiet in H0.
    - unfold quiet in H0; destruct b0; try contradiction.
      repeat eexists; intuition; eauto.
    - exfalso.
      destruct U__r; destruct adversary; simpl in *; subst.
      unfold build_data_step in H; simpl in *.
      invert H.
  Qed.
  
End RealWorldLemmas.

Ltac equality1 :=
  match goal with
  | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition idtac

  | [ H : _ $+ (_,_) $? _ = _ |- _ ] => progress clean_map_lookups
  | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
  | [ H : _ $? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : add _ _ _ $? _ = Some ?UD |- _ ] =>
    match type of UD with
    | RealWorld.user_data bool => apply lookup_some_implies_in in H; simpl in H
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
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
  (* | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => apply inj_pair2 in H *)

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
      inversion H; repeat equality1; subst; intuition idtac; eauto.
    Qed.

    Lemma step_user_inv_bind :
      forall {A B C C'} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n'
        (cmd1 : user_cmd C) (cmd : C -> user_cmd C') (cmd' : user_cmd C'),
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
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd (crypto t)) pat,
        step_user lbl u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Recv pat)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', tos', cur_n', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ tos = tos'
        /\ cur_n = cur_n'
        /\ gks = gks'
        /\ exists msg msgs,
            qmsgs = (existT crypto t msg) :: msgs
          /\ qmsgs' = msgs
          /\ ( ( msg_accepted_by_pattern cs u_id froms pat msg
              /\ ks' = ks $k++ findKeysCrypto cs msg
              /\ mycs' = findCiphers msg ++ mycs
              /\ froms' = updateTrackedNonce u_id froms cs msg
              /\ lbl = Action (Input msg pat froms)
              /\ cmd = Return msg)
            \/ ( ~ msg_accepted_by_pattern cs u_id froms pat msg
              /\ ks = ks'
              /\ mycs = mycs'
              /\froms' = (if msg_signed_addressed (findUserKeys usrs) cs u_id msg
                         then updateTrackedNonce u_id froms cs msg
                         else froms)
              /\ lbl = Silent
              /\ cmd = Recv pat
              )).
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
        /\ tos' = updateTrackedNonce (Some rec_u_id) tos cs msg
        /\ mycs = mycs'
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
        /\ cmd = Return tt
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
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' msg_to cmd,
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
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (u_id, cur_n) msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (SignedCiphertext c_id)).
    Proof.
      intros * H.
      invert H; intuition eauto 12.
    Qed.

    Lemma step_user_inv_dec :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) c_id
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd (message t)),
        step_user lbl
                  u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Decrypt (SignedCiphertext c_id))
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
        /\ List.In c_id mycs
        /\ exists (msg : message t) k__sign k__enc kt__enc kt__sign kp__sign msg_to nonce,
            cs $? c_id     = Some (SigEncCipher k__sign k__enc msg_to nonce msg)
          /\ gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__enc  = Some true
          /\ ks  $? k__sign = Some kp__sign
          /\ ks' = ks $k++ findKeysMessage msg
          /\ mycs' = (* findCiphers msg ++ *) mycs
          /\ cmd = Return msg.
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
        /\ lbl = Silent
        /\ (exists kt__sign,
                gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigCipher k__sign msg_to (u_id, cur_n) msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (SignedCiphertext c_id)).
    Proof.
      intros * H.
      invert H; intuition eauto 12.
    Qed.

    Lemma step_user_inv_verify :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign c_id
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
        step_user lbl
                  u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, Verify k__sign (SignedCiphertext c_id))
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
        /\ List.In c_id mycs
        /\ exists (msg : message t) kt__sign kp__sign msg_to nonce,
            cs $? c_id     = Some (SigCipher k__sign msg_to nonce msg)
          /\ cmd = Return (true,msg)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__sign = Some kp__sign.
    Proof.
      intros * H.
      invert H; intuition eauto 12.
    Qed.

    Lemma step_user_inv_gensym :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) usage
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
        step_user lbl
                  u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, GenerateSymKey usage)
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
          /\ k = MkCryptoKey k_id usage SymKey
          /\ gks' = gks $+ (k_id, k)
          /\ ks' = add_key_perm k_id true ks
          /\ cmd = Return (k_id,true).
    Proof.
      intros * H.
      invert H; intuition eauto 12.
    Qed.

    Lemma step_user_inv_genasym :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) usage
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' cmd,
        step_user lbl
                  u_id
                  (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, GenerateAsymKey usage)
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
          /\ k = MkCryptoKey k_id usage AsymKey
          /\ gks' = gks $+ (k_id, k)
          /\ ks' = add_key_perm k_id true ks
          /\ cmd = Return (k_id,true).
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

  Module T.
    Import RealWorld.

    Ltac churn1 :=
      match goal with

      | [ H : ~ RealWorld.msg_accepted_by_pattern ?cs ?suid ?froms ?pat ?msg |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern cs suid froms pat msg ) by (econstructor; eauto); contradiction

      | [ H : RealWorld.msg_accepted_by_pattern ?cs ?suid ?froms ?pat ?msg -> False |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern cs suid froms pat msg ) by (econstructor; eauto); contradiction

      (* Only take a user step if we have chosen a user *)
      | [ H : RealWorld.step_user _ (Some ?u) _ _ |- _ ] => progress simpl in H
      | [ H : RealWorld.step_user _ (Some ?u) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u;
        match cmd with
        | Return _ => invert H
        | Bind _ _ => apply step_user_inv_bind in H; split_ands; split_ors; split_ands; subst; try discriminate
        | Gen => apply step_user_inv_gen in H
        | Send _ _ => apply step_user_inv_send in H
        | Recv _ => apply step_user_inv_recv in H
        | SignEncrypt _ _ _ => apply step_user_inv_enc in H
        | Decrypt _ => apply step_user_inv_dec in H
        | Sign _ _ _ => apply step_user_inv_sign in H
        | Verify _ _ => apply step_user_inv_verify in H
        | GenerateSymKey _ => apply step_user_inv_gensym in H
        | GenerateAsymKey _ => apply step_user_inv_genasym in H
        | _ => idtac "***Missing inversion: " cmd; intuition idtac; subst; (progress (simpl in H) || invert H)
        end

      | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,_,_,_,RealWorld.protocol ?adv) _
        , LAME : lameAdv _ ?adv |- _ ] => pose proof (adv_no_step LAME STEP); contradiction

      | [ H : RealWorld.step_user _ _ (build_data_step _ _) _ |- _ ] => unfold build_data_step in H; simpl in H

      | [ H : ~^* (RealWorld.buildUniverse _ _ _ _ _ _ ) _ |- _] =>
        unfold RealWorld.buildUniverse in H; autorewrite with simpl_univ in H
      | [ |- context [RealWorld.buildUniverse _ _ _ _ _ _] ] =>
        unfold RealWorld.buildUniverse

      | [ S: ~^* ?U _ |- _ ] => 
        (* Don't actually multiStep unless we know the state of the starting universe
         * meaning it is not some unknown hypothesis in the context...
         *)
        is_not_var U; eapply multiStepSilentInv in S; split_ors; split_ex; intuition idtac; subst

      | [ H: step_universe ?U Silent _ |- _ ] => is_not_var U; invert H
      | [ H: step_universe _ _ _ |- _ ] => invert H

      end.

  End T.

  Import T.
  Export T.

  Local Ltac fill_unification_var_ineq uni v :=
    match goal with
    | [ H : ?uni' = v -> False |- _ ] => unify uni uni'
    | [ H : v = ?uni' -> False |- _ ] => unify uni uni'
    end.

  Local Ltac solve_simple_ineq :=
    match goal with
    | [ |- ?kid1 <> ?kid2 ] =>
      (is_evar kid1; fill_unification_var_ineq kid1 kid2)
      || (is_evar kid2; fill_unification_var_ineq kid2 kid1)
    end; unfold not; intro; congruence.

  Ltac solve_concrete_maps :=
    repeat
      match goal with
      | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
      | [ H : Some _ = Some _ |- _ ] => invert H
      | [ H : Some _ = None |- _ ] => discriminate
      | [ H : None = Some _ |- _ ] => discriminate
                                      
      | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by eauto 2
                                                                               
      | [ H : In ?k ?m -> False |- _ ] =>
        is_not_var k; assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; solve_concrete_maps); contradiction
      | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
      | [ |- ~ In _ _ ] => unfold not; intros

      | [ |- ?m $+ (?kid1,_) $? ?kid1 = _ ] => rewrite add_eq_o
      | [ |- ?m $+ (?kid2,_) $? ?kid1 = _ ] =>
          rewrite add_neq_o by solve_concrete_maps
        || rewrite add_eq_o by (unify kid1 kid2; solve_concrete_maps)

      | [ |- ?m $? ?kid1 = _ ] => progress (unfold m)

      | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H

      | [ |- _ = _ ] => reflexivity
      | [ |- ?kid1 <> ?kid2 ] =>
          ( (is_evar kid1; fill_unification_var_ineq kid1 kid2)
          || (is_evar kid2; fill_unification_var_ineq kid2 kid1));
          unfold not; intro; congruence
      | [ |- _ $? _ = _ ] => eassumption
      end.

  Ltac churn2 :=
    (* (repeat equality1); subst; churn1; intuition idtac; split_ex; intuition idtac; subst; try discriminate; clean_map_lookups. *)
    (repeat equality1); subst; churn1; intuition idtac; split_ex; intuition idtac; subst; try discriminate; solve_concrete_maps.

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
    || eapply RealWorld.StepGenerateSymKey
    || eapply RealWorld.StepGenerateAsymKey
  .

  Ltac pick_user uid :=
    match goal with
    | [ |- _ $? ?euid = Some _ ] => unify euid uid
    end; reflexivity.

  (* Ltac pick_user uid := *)
  (*   match goal with *)
  (*   | [ |- _ $? ?euid = Some _ ] => unify euid uid *)
  (*   end; clean_map_lookups; trivial. *)

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
  Ltac single_silent_multistep3 usr_step := eapply Trc3Front; swap 1 2; [usr_step |..]; simpl; trivial.
  
  Ltac real_single_silent_multistep uid := single_silent_multistep3 ltac:(rsilent_step_univ uid).
  Ltac ideal_single_silent_multistep uid := single_silent_multistep ltac:(isilent_step_univ uid).

  Ltac figure_out_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        does_not_unify usr1 usr2; step_tac u
      end
    end.

  Remove Hints TrcRefl TrcFront Trc3Refl Trc3Front.
  Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl.
  Hint Extern 1 (~^* ?U ?U) => apply Trc3Refl.

  Remove Hints eq_sym (* includes_lookup *).
  Remove Hints trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat.

  Hint Constructors action_matches.
  Hint Resolve IdealWorld.LStepSend' IdealWorld.LStepRecv'.

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
  
  Ltac solve_refl :=
    solve [
        eapply TrcRefl
      | eapply TrcRefl'; simpl; eauto ].

  Ltac solve_refl3 :=
    solve [
        eapply Trc3Refl
      | eapply Trc3Refl'; simpl; smash_universe ].

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

  Ltac rss_clean uid := real_single_silent_multistep uid; [ solve [eauto 3] .. |].

  Ltac real_silent_multistep :=
    simpl_real_users_context;
    match goal with
    | [ |- ~^* ?U1 ?U2 ] =>
      first [
          solve_refl3
        | figure_out_user_step rss_clean U1 U2 ]
    end.

  Ltac ideal_silent_multistep :=
    simpl_ideal_users_context;
    match goal with
    | [ |- istepSilent ^* ?U1 ?U2 ] =>
      is_not_evar U1; is_not_evar U2;
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

  Hint Extern 1 (~^* _ _) => real_silent_multistep.
  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_multistep.
  (* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe. *)
  Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor.
  
  Hint Extern 1 (List.In _ _) => progress simpl.
  Hint Extern 1 (~ In _ _) => solve_concrete_maps.

  Hint Extern 1 (action_adversary_safe _ _ _ = _) => unfold action_adversary_safe; simpl.
  Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.

  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl.
  (* Hint Extern 1 (add _ _ _ = _) => (progress m_equal) || (progress clean_map_lookups). *)
  (* Hint Extern 1 (find _ _ = _) => (progress m_equal) || (progress clean_map_lookups). *)

  Hint Extern 1 (add _ _ _ = _) => reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups).
  Hint Extern 1 (find _ _ = _) => reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups).

  Ltac solve_action_matches1 :=
    match goal with
    | [ |- content_eq _ _ ] => progress simpl
    | [ |- action_matches _ _ _ _ ] => progress simpl_real_users_context
    | [ |- action_matches _ _ _ _ ] => progress simpl_ideal_users_context
    | [ |- action_matches (RealWorld.Output _ _ _ _) _ _ _ ] => eapply Out
    | [ |- action_matches (RealWorld.Input _ _ _) _ _ _ ] => eapply Inp
    | [ |- message_eq (RealWorld.Content _) _ _ _ _ ] => eapply ContentCase
    | [ |- message_eq (RealWorld.SignedCiphertext ?cid)
                     {| RealWorld.users := _;
                        RealWorld.adversary := _;
                        RealWorld.all_ciphers := _ $+ (?cid, RealWorld.SigCipher _ _ _ _);
                        RealWorld.all_keys := _ |}
                     _ _ _ ] => eapply CryptoSigCase
    | [ |- message_eq (RealWorld.SignedCiphertext ?cid)
                     {| RealWorld.users := _;
                        RealWorld.adversary := _;
                        RealWorld.all_ciphers := _ $+ (?cid, RealWorld.SigEncCipher _ _ _ _ _);
                        RealWorld.all_keys := _ |}
                     _ _ _ ] => eapply CryptoSigEncCase
    | [ |- _ <-> _ ] => split
    | [ |- _ -> _ ] => intros
    | [ H : _ $+ (_,_) $? ?uid = Some ?data |- (_ ?data) $? _ = Some _] =>
      apply lookup_some_implies_in in H; simpl in H; split_ors; repeat equality1; subst; try contradiction; simpl in *
    end.

  Hint Extern 1 (action_matches _ _ _ _) => repeat (solve_action_matches1; simpl; eauto 3).

  Hint Resolve
       findUserKeys_foldfn_proper
       findUserKeys_foldfn_transpose.
  
  Lemma findUserKeys_add_reduce :
    forall {A} (usrs : RealWorld.honest_users A) u_id ks p qmsgs mycs froms sents cur_n,
      ~ In u_id usrs
      -> RealWorld.findUserKeys (usrs $+ (u_id, {| RealWorld.key_heap := ks;
                                      RealWorld.protocol := p;
                                      RealWorld.msg_heap := qmsgs;
                                      RealWorld.c_heap := mycs;
                                      RealWorld.from_nons := froms;
                                      RealWorld.sent_nons := sents;
                                      RealWorld.cur_nonce := cur_n |})) = RealWorld.findUserKeys usrs $k++ ks.
  Proof.
    intros.
    unfold RealWorld.findUserKeys.
    rewrite fold_add; eauto.
  Qed.

  Lemma findUserKeys_empty_is_empty :
    forall A, @RealWorld.findUserKeys A $0 = $0.
  Proof. trivial. Qed.
  
  Hint Constructors RealWorld.honest_key RealWorld.msg_pattern_safe.

  Lemma reduce_merge_perms :
    forall perms1 perms2 kid perm1 perm2,
        perm1 = match perms1 $? kid with
                | Some p => p
                | None => false
                end
      -> perm2 = match perms2 $? kid with
                | Some p => p
                | None => false
                end
      -> (perms1 $? kid = None -> perms2 $? kid = None -> False)
      -> perms1 $k++ perms2 $? kid = Some (perm1 || perm2).
  Proof.
    intros; solve_perm_merges; subst; eauto.
    - rewrite orb_false_r; auto.
    - exfalso; eauto.
  Qed.
  
  Ltac solve_concrete_perm_merges :=
    repeat 
      match goal with
      | [ |- context [true || _]  ] => rewrite orb_true_l
      | [ |- context [_ || true]  ] => rewrite orb_true_r
      | [ |- context [$0 $k++ _] ] => rewrite merge_perms_left_identity
      | [ |- context [_ $k++ $0] ] => rewrite merge_perms_right_identity
      | [ |- context [_ $k++ _]  ] => erewrite reduce_merge_perms; clean_map_lookups; eauto
      end; trivial.

  Ltac solve_honest_actions_safe :=
    repeat
      ( match goal with
        | [ H : _ = {| RealWorld.users := _;
                       RealWorld.adversary := _;
                       RealWorld.all_ciphers := _;
                       RealWorld.all_keys := _ |} |- _ ] => invert H
                                                                 
        | [ |- honest_cmds_safe _ ] => unfold honest_cmds_safe; intros; simpl in *
        | [ |- context [ RealWorld.findUserKeys ?usrs ] ] => canonicalize_map usrs
        | [ |- context [ RealWorld.findUserKeys _ ] ] => rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty by eauto
        | [ H : RealWorld.findKeysMessage _ $? _ = _ |- _ ] => progress (simpl in H)
        | [ H : _ $+ (?id1,_) $? ?id2 = _ |- _ ] => is_var id2; destruct (id1 ==n id2); subst; clean_map_lookups
        | [ |- (_ -> _) ] => intros
        | [ |- context [ _ $+ (_,_) $? _ ] ] => progress clean_map_lookups
        | [ |- context [ RealWorld.msg_honestly_signed _ _ _ ]] => unfold RealWorld.msg_honestly_signed
        | [ |- context [ RealWorld.honest_keyb _ _ ]] => unfold RealWorld.honest_keyb
        | [ |- context [ RealWorld.msg_to_this_user _ _ _ ]] => unfold RealWorld.msg_to_this_user
        | [ |- context [ RealWorld.msgCiphersSignedOk _ _ _ ]] => unfold RealWorld.msgCiphersSignedOk
        | [ |- context [ add_key_perm _ _ _ ] ] => unfold add_key_perm
        | [ |- RealWorld.msg_pattern_safe _ _ ] => econstructor
        | [ |- RealWorld.honest_key _ _ ] => econstructor
        | [ |- context [_ $k++ _ $? _ ] ] => progress solve_concrete_perm_merges
        | [ |- context [ ?m $? _ ] ] => unfold m
                                             
        | [ |- next_cmd_safe _ _ _ _ _ _ ] => econstructor
        | [ |- Forall _ _ ] => econstructor
        | [ |- _ /\ _ ] => split
        end; simpl).

End SimulationAutomation.

Import SimulationAutomation.

Section UniverseStep.
  Import RealWorld.

  Definition rewrite_messages {A} (usr : user_data A) (qmsgs : queued_messages) :=
    {| key_heap  := usr.(key_heap)
     ; protocol  := usr.(protocol)
     ; msg_heap  := qmsgs
     ; c_heap    := usr.(c_heap)
     ; from_nons := usr.(from_nons)
     ; sent_nons := usr.(sent_nons)
     ; cur_nonce := usr.(cur_nonce)
    |}.

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


(* Hint Resolve encrypted_ciphers_ok_addnl_cipher. *)

Hint Constructors
     RealWorld.msg_accepted_by_pattern.
