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
     Eqdep
.

Require Import
        MyPrelude
        AdversaryUniverse
        Automation
        Common
        Keys
        KeysTheory
        Maps
        Messages
        MessageEq
        ModelCheck
        RealWorld
        SafeProtocol
        Simulation
        Tactics
        UniverseEqAutomation.

Require
  IdealWorld
  RealWorld
  Sets.

Require
  ChMaps.

Import ChMaps.ChMapNotation ChMaps.ChNotation.

(* Import ChMaps.ChMap. *)

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

  Lemma invert_return :
    forall (t : user_cmd_type) (r1 r2 : denote t),
      Return r1 = Return r2 -> r1 = r2.
  Proof. intros * H; invert H; trivial. Qed.
  
End RealWorldLemmas.

Ltac equality1 :=
  match goal with
  | [ H : ?x = ?x |- _ ] => clear H
  | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition idtac

  | [ H : _ $+ (_,_) $? _ = _ |- _ ] => progress clean_map_lookups
  | [ H : _ #+ (_,_) #? _ = _ |- _ ] => progress clean_map_lookups
  | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
  | [ H : #0 #? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
  | [ H : _ $? _ = Some _ |- _ ] => progress (simpl in H)
  | [ H : _ #? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : _ $+ (_,_) $? _ = Some ?UD |- _ ] =>
    match type of UD with
    | RealWorld.user_data _ => apply lookup_some_implies_in in H; simpl in H
    | _ => apply lookup_split in H; intuition idtac
    end
  | [ H : _ #+ (_,_) #? _ = Some ?UD |- _ ] =>
    apply ChMaps.ChMap.lookup_split in H; intuition idtac

  | [ H : _ = {| RealWorld.users := _ ; RealWorld.adversary := _ ; RealWorld.all_ciphers := _ ; RealWorld.all_keys := _ |} |- _ ]
    => inversion H; clear H; subst
  | [ |- RealWorld.protocol (RealWorld.adversary _) = RealWorld.Return _ ] => simpl
  | [ H : lameAdv _ ?adv |- RealWorld.protocol ?adv = _ ] => unfold lameAdv in H; eassumption

  | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => inversion H; clear H
  | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
  | [ H : (_ :: _) = (_ :: _) |- _ ] => inversion H; clear H
  | [ H : (_ :: _) = ?x |- _ ] => is_var x; inversion H; clear H
  | [ H : ?x = (_ :: _) |- _ ] => is_var x; inversion H; clear H
  | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H
  | [ H : Action _ = Action _ |- _ ] => inversion H; clear H
  | [ H : RealWorld.Return _ = RealWorld.Return _ |- _ ] => apply invert_return in H
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H

  | [ H: RealWorld.SignedCiphertext _ = RealWorld.SignedCiphertext _ |- _ ] => invert H
  | [ H: RealWorld.SigCipher _ _ _ _ = RealWorld.SigCipher _ _ _ _ |- _ ] => invert H
  | [ H: RealWorld.SigEncCipher _ _ _ _ _ = RealWorld.SigEncCipher _ _ _ _ _ |- _ ] => invert H
  | [ H: MkCryptoKey _ _ _ = _ |- _ ] => invert H

  | [ H: _ = {| IdealWorld.read := _ |} |- _ ] => invert H
  | [ H: {| IdealWorld.read := _ |} = _ |- _ ] => invert H

  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H

  | [ H : keyId _ = _ |- _] => inversion H; clear H
  end.

Module SimulationAutomation.

  Hint Constructors RealWorld.msg_accepted_by_pattern : core.

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
      inversion H; repeat equality1; subst; intuition idtac; eauto.
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
        /\ exists msg msgs,
            qmsgs = (existT crypto t msg) :: msgs
          /\ qmsgs' = msgs
          /\ ( ( msg_accepted_by_pattern cs u_id froms pat msg
              /\ ks' = ks $k++ findKeysCrypto cs msg
              /\ mycs' = findCiphers msg ++ mycs
              /\ froms' = updateTrackedNonce u_id froms cs msg
              /\ lbl = Action (Input msg pat froms)
              /\ cmd = @Return (Crypto t) msg)
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
        /\ (exists c_id : nat, 
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigEncCipher k__sign k__enc msg_to (u_id, cur_n) msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = @Return (Crypto t) (SignedCiphertext c_id)).
    Proof.
      intros * H.
      invert H; intuition eauto 12.
    Qed.

    Lemma step_user_inv_dec :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) c_id
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' froms froms' tos tos' cur_n cur_n' (cmd : user_cmd (Message t)),
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
        /\ lbl = Silent
        /\ (exists kt__sign,
                gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigCipher k__sign msg_to (u_id, cur_n) msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = @Return (Crypto t) (SignedCiphertext c_id)).
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
          /\ cmd = @Return (UPair (Base Bool) (Message t)) (true,msg)
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
          /\ cmd = @Return (Base Access) (k_id,true).
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

    (* A nice, boring adversary that can be used for protocol proofs. *)
    Definition startAdv := {| key_heap := $0;
                              protocol := @Return (Base Unit) tt;
                              msg_heap := [];
                              c_heap   := [];
                              from_nons := [];
                              sent_nons := [];
                              cur_nonce := 0 |}.

  End InversionPrinciples.

  Module T.
    Import RealWorld.

    Ltac churn1 :=
      match goal with

      | [ H : ~ RealWorld.msg_accepted_by_pattern ?cs ?suid ?froms ?pat ?msg |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern cs suid froms pat msg )
          by (econstructor; eauto); contradiction

      | [ H : RealWorld.msg_accepted_by_pattern ?cs ?suid ?froms ?pat ?msg -> False |- _ ] =>
        assert ( RealWorld.msg_accepted_by_pattern cs suid froms pat msg )
          by (econstructor; eauto); contradiction

      (* Only take a user step if we have chosen a user *)
      | [ H : RealWorld.step_user _ (Some ?u) _ _ |- _ ] => progress simpl in H
      | [ H : RealWorld.step_user _ (Some ?u) (_,_,_,_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
        is_not_var u;
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
        | _ => idtac "***Missing inversion: " cmd; intuition idtac; subst; (progress (simpl in H) || invert H)
        end

      | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,_,_,_,RealWorld.protocol ?adv) _
        , LAME : lameAdv _ ?adv |- _ ] => pose proof (adv_no_step LAME STEP); contradiction

      | [ H : RealWorld.step_user _ _ (build_data_step _ _) _ |- _ ] =>
        unfold build_data_step in H; autounfold with user_build in H; simpl in H

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

  Ltac fill_unification_var_ineq uni v :=
    match goal with
    | [ H : ?uni' = v -> False |- _ ] => unify uni uni'
    | [ H : v = ?uni' -> False |- _ ] => unify uni uni'
    end.

  Ltac solve_simple_ineq :=
    repeat
      match goal with
      | [ |- ?kid1 <> ?kid2 ] =>
          congruence
        || (is_evar kid1; fill_unification_var_ineq kid1 kid2)
        || (is_evar kid2; fill_unification_var_ineq kid2 kid1)
        || (is_not_var kid1; progress unfold kid1)
        || (is_not_var kid2; progress unfold kid2)
      end.

  Ltac solve_concrete_maps1 :=
    match goal with
    | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
    | [ |- context [ $0 $? _ ]] => rewrite lookup_empty_none
    | [ H : context [ #0 #? _ ] |- _ ] => rewrite ChMaps.ChMap.lookup_empty_none in H
    | [ |- context [ #0 #? _ ]] => rewrite ChMaps.ChMap.lookup_empty_none

    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : Some _ = None |- _ ] => discriminate
    | [ H : None = Some _ |- _ ] => discriminate

    | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
    | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
    | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by solve_simple_ineq (* auto 2 *)
    | [ H : ?m #? ?k = _ |- _ ] => progress (unfold m in H)
    | [ H : ?m #+ (?k1,_) #? ?k1 = _ |- _ ] => rewrite ChMaps.ChMap.F.add_eq_o in H by trivial
    | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- _ ] => rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq (* auto 2 *)

    | [ H : In ?k ?m -> False |- _ ] =>
      is_not_var k;
      assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; repeat solve_concrete_maps1);
      contradiction
    | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
    | [ H : ~ In _ _ |- _ ] => rewrite not_find_in_iff in H
    | [ |- ~ In _ _ ] => rewrite not_find_in_iff; try eassumption
    | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H
    | [ H : ChMaps.ChMap.Map.In ?k ?m -> False |- _ ] =>
      is_not_var k;
      assert (ChMaps.ChMap.Map.In k m) by (clear H; rewrite ChMaps.ChMap.F.in_find_iff; unfold not; intros; repeat solve_concrete_maps1);
      contradiction
    | [ H : ChMaps.ChMap.Map.In _ _ |- _ ] => rewrite ChMaps.ChMap.F.in_find_iff in H
    | [ H : ~ ChMaps.ChMap.Map.In _ _ |- _ ] => rewrite ChMaps.ChMap.F.not_find_in_iff in H
    | [ |- ~ ChMaps.ChMap.Map.In _ _ ] => rewrite ChMaps.ChMap.F.not_find_in_iff; try eassumption
    | [ H : ChMaps.ChMap.Map.In ?x ?xs -> False |- _ ] => change (ChMaps.ChMap.Map.In x xs -> False) with (~ ChMaps.ChMap.Map.In x xs) in H

    | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)

    | [ |- ?m $+ (?kid1,_) $? ?kid1 = _ ] => rewrite add_eq_o by trivial
    | [ |- ?m $+ (?kid2,_) $? ?kid1 = _ ] => rewrite add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_eq_o by trivial
    | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) $? _ = _ ] => rewrite add_eq_o by trivial
    | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) $? _ = _ ] => rewrite add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- _ = (match _ $+ (_,_) $? _ with _ => _ end) ] => symmetry
    | [ |- _ = (match _ $+ (_,_) $? _ with _ => _ end) $? _ ] => symmetry
    | [ |- context [ match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end ] ] => rewrite add_eq_o by trivial
    | [ |- _ $+ (?k1,_) $? ?k2 = _ ] =>
      is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2);
      destruct (k1 ==n k2); subst; try contradiction
    | [ |- _ = ?m $+ (?kid2,_) $? ?kid1 ] => symmetry
    | [ |- ?m #+ (?kid1,_) #? ?kid1 = _ ] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- ?m #+ (?kid2,_) #? ?kid1 = _ ] => rewrite ChMaps.ChMap.F.add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- (match ?m #+ (?kid1,_) #? ?kid1 with _ => _ end) = _ ] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- (match ?m #+ (?kid2,_) #? ?kid1 with _ => _ end) = _ ] => rewrite ChMaps.ChMap.F.add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- (match ?m #+ (?kid1,_) #? ?kid1 with _ => _ end) #? _ = _ ] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- (match ?m #+ (?kid2,_) #? ?kid1 with _ => _ end) #? _ = _ ] => rewrite ChMaps.ChMap.F.add_neq_o by solve_simple_ineq (* auto 2 *)
    | [ |- _ = (match _ #+ (_,_) #? _ with _ => _ end) ] => symmetry
    | [ |- _ = (match _ #+ (_,_) #? _ with _ => _ end) #? _ ] => symmetry
    | [ |- context [ match ?m #+ (?kid1,_) #? ?kid1 with _ => _ end ] ] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- _ #+ (?k1,_) #? ?k2 = _ ] =>
      is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2);
      destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst; try contradiction
    | [ |- _ = ?m #+ (?kid2,_) #? ?kid1 ] => symmetry
                                           
    | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)
    | [ |- context [ ?m $? ?kid1 ] ] => progress (unfold m)
    | [ |- context [ ?m #? ?kid1 ] ] => progress (unfold m)

    | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H
    | [ H : ?m #? ?k <> _ |- _ ] => cases (m #? k); try contradiction; clear H

    | [ |- _ = _ ] => reflexivity
    | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros
    | [ |- _ #+ (_,_) = _ ] => apply ChMaps.ChMap.map_eq_Equal; unfold ChMaps.ChMap.Map.Equal; intros

    | [ |- Some _ = Some _ ] => f_equal
    | [ |- {| RealWorld.key_heap := _ |} = _ ] => f_equal
    | [ |- _ $? _ = _ ] => eassumption
    | [ |- _ #? _ = _ ] => eassumption

                             
    | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ $+ (_,_) $? _ = _ ] =>
      (is_var k1 || is_var k2); idtac "destructing1 " k1 k2; destruct (k1 ==n k2); subst
    | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- (match _ $+ (_,_) $? _ with _ => _ end) $? _ = _ ] =>
      (is_var k1 || is_var k2); idtac "destructing2 " k1 k2; destruct (k1 ==n k2); subst
    | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- _ #+ (_,_) #? _ = _ ] =>
      (is_var k1 || is_var k2); idtac "#destructing1 " k1 k2; destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst
    | [ H : ?m #+ (?k1,_) #? ?k2 = _ |- (match _ #+ (_,_) #? _ with _ => _ end) #? _ = _ ] =>
      (is_var k1 || is_var k2); idtac "#destructing2 " k1 k2; destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst

    end.

  Ltac solve_concrete_maps := repeat solve_concrete_maps1.

  Ltac churn2 :=
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

  Ltac solve_ideal_step_stuff :=
    repeat (
        match goal with
        | [ H : # ?x = # ?y -> False |- _ ] => assert (x <> y) by congruence; clear H
        | [ |- Forall _ _ ] => econstructor
        | [ |- {| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _] => smash_universe; solve_concrete_maps
        | [ |- _ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}] => smash_universe; solve_concrete_maps
        | [ |- IdealWorld.screen_msg _ _ ] => econstructor
        | [ |- IdealWorld.permission_subset _ _ ] => econstructor
        | [ |- IdealWorld.check_perm _ _ _ ] => unfold IdealWorld.check_perm
        | [ |- ?m #? (# ?k) = None ] =>
          solve [ is_evar k; unify (# k) (ChMaps.next_key m); apply ChMaps.next_key_not_in; trivial ] 
        | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) ] => rewrite add_eq_o by trivial
        | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) ] => rewrite add_neq_o by solve_simple_ineq (* auto 2 *)
        | [ |- context [ #0 #? _ ]] => rewrite ChMaps.ChMap.lookup_empty_none
        | [ |- _ = _ ] => reflexivity
        | [ |- context [ _ $? _ ] ] => solve_concrete_maps
        | [ |- context [ _ #? _ ] ] => solve_concrete_maps
        end; simpl).

  (* match goal with *)
  (* | [ |- Forall _ _ ] => econstructor *)
  (* | [ |- {| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _] => smash_universe; solve_concrete_maps *)
  (* | [ |- _ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}] => smash_universe; solve_concrete_maps *)
  (* | [ |- IdealWorld.screen_msg _ _ ] => econstructor *)
  (* | [ |- IdealWorld.permission_subset _ _ ] => econstructor *)
  (* | [ |- IdealWorld.check_perm _ _ _ ] => unfold IdealWorld.check_perm *)
  (* | [ |- context [ _ #? _ ] ] => solve_concrete_maps *)
  (* | [ |- ?m #? (# ?k) = None ] => *)
  (*   solve [ is_evar k; unify (# k) (ChMaps.next_key m); apply ChMaps.next_key_not_in; trivial ]  *)
  (* | [ |- _ = _ ] => reflexivity *)
  (* end; simpl). *)

  Ltac isilent_step_univ uid :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
    ((eapply IdealWorld.LStepBindRecur; i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2  ])
     || (i_single_silent_step; solve [ solve_ideal_step_stuff; eauto 2 ])).
  Ltac rsilent_step_univ uid :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
      ((eapply RealWorld.StepBindRecur; r_single_silent_step) || r_single_silent_step).

  Ltac single_silent_multistep usr_step := eapply TrcFront; [usr_step |]; simpl.
  Ltac single_silent_multistep3 usr_step := eapply Trc3Front; swap 1 2; [usr_step |..]; simpl; trivial.
  
  Ltac real_single_silent_multistep uid := single_silent_multistep3 ltac:(rsilent_step_univ uid).
  Ltac ideal_single_silent_multistep uid := single_silent_multistep ltac:(isilent_step_univ uid).

  Ltac figure_out_ideal_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        let p1 := constr:(IdealWorld.protocol usr1) in
        let p2 := constr:(IdealWorld.protocol usr2) in
        does_not_unify p1 p2; step_tac u
      end
    end.

  Ltac figure_out_real_user_step step_tac U1 U2 :=
    match U1 with
    | context [ add ?u ?usr1 _ ] =>
      match U2 with
      | context [ add u ?usr2 _ ] =>
        let p1 := constr:(RealWorld.protocol usr1) in
        let p2 := constr:(RealWorld.protocol usr2) in
        does_not_unify p1 p2; step_tac u
      end
    end.

  Remove Hints TrcRefl TrcFront Trc3Refl Trc3Front : core.
  Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl : core.

  Remove Hints
         eq_sym (* includes_lookup *)
         trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat : core.

  Hint Constructors action_matches : core.
  Hint Resolve IdealWorld.LStepSend IdealWorld.LStepRecv' : core.

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
      | eapply Trc3Refl'; simpl; smash_universe; solve_concrete_maps ].

  Ltac simpl_real_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ RealWorld.buildUniverse ] ] => progress (unfold RealWorld.buildUniverse; simpl)
      | [ |- context [ {| RealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      (* | [ |- context [ RealWorld.mkUniverse ?usrs _ _ _] ] => canonicalize_map usrs *)
      end.

  Ltac simpl_ideal_users_context :=
    simpl;
    repeat
      match goal with
      | [ |- context [ {| IdealWorld.users := ?usrs |}] ] => progress canonicalize_map usrs
      end.

  Ltac rss_clean uid := real_single_silent_multistep uid; [ solve [eauto 3] .. |].

  Ltac real_silent_multistep :=
    simpl_real_users_context;
    match goal with
    | [ |- ~^* ?U1 ?U2 ] =>
      first [
          solve_refl3
        | figure_out_real_user_step rss_clean U1 U2 ]
    end.

  Ltac ideal_silent_multistep :=
    simpl_ideal_users_context;
    match goal with
    | [ |- istepSilent ^* ?U1 ?U2 ] =>
      is_not_evar U1; is_not_evar U2;
      first [
          solve_refl
        | figure_out_ideal_user_step ideal_single_silent_multistep U1 U2 ]
    end.

  Ltac single_step_ideal_universe :=
    simpl_ideal_users_context;
    match goal with
    | [ |- IdealWorld.lstep_universe ?U1 _ ?U2] =>
      match U1 with
      | IdealWorld.construct_universe _ ?usrs1 =>
        match U2 with
        | IdealWorld.construct_universe _ ?usrs2 =>
          figure_out_ideal_user_step istep_univ usrs1 usrs2
        end
      end
    end.

  Ltac single_labeled_ideal_step uid :=
    eapply IdealWorld.LStepUser' with (u_id := uid);
    [ solve [ solve_concrete_maps ] | simpl | reflexivity ];
    eapply IdealWorld.LStepBindRecur;
    ( (eapply IdealWorld.LStepRecv'; solve [ solve_ideal_step_stuff ])
      || (eapply IdealWorld.LStepSend; solve [ solve_ideal_step_stuff ])).

  Ltac step_each_ideal_user U :=
    match U with
    | ?usrs $+ (?AB,_) =>
      idtac "stepping " AB; (single_labeled_ideal_step AB || step_each_ideal_user usrs)
    end.

  (* TODO: during canonicalization, cleanup the channels map *)
  Local Ltac blah1 :=
    match goal with
    | [ |- context [ IdealWorld.addMsg ]] => unfold IdealWorld.addMsg; simpl
    | [ |- context [ ?m #? _ ]] => progress unfold m
    | [ |- context [ _ #+ (?k1,_) #? ?k1 ]] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- context [ _ #+ (?k1,_) #? ?k2 ]] => rewrite ChMaps.ChMap.F.add_neq_o by congruence
    end.

  Ltac step_ideal_user :=
    match goal with
    | [ |- IdealWorld.lstep_universe _ (Action _) ?U' ] =>
      is_evar U'; simpl_ideal_users_context; (repeat blah1);
      match goal with
      | [ |- IdealWorld.lstep_universe
            {| IdealWorld.users := ?usrs; IdealWorld.channel_vector := _ |} _ _ ] =>
        step_each_ideal_user usrs
      end
    end.

  Hint Extern 1 (~^* _ _) => solve [ repeat real_silent_multistep ] : core.
  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_multistep : core.

  Hint Extern 1 ({| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _) => smash_universe; solve_concrete_maps : core.
  Hint Extern 1 (_ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}) => smash_universe; solve_concrete_maps : core.

  (* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor. *)
  Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => step_ideal_user : core.
  
  Hint Extern 1 (List.In _ _) => progress simpl : core.
  Hint Extern 1 (~ In ?k ?m) =>
      (* (is_evar k; unify k (next_key m); rewrite not_find_in_iff; apply next_key_not_in; trivial) *)
     solve_concrete_maps : core.

  Hint Extern 1 (action_adversary_safe _ _ _ = _) => unfold action_adversary_safe; simpl : core.
  Hint Extern 1 (IdealWorld.screen_msg _ _) => econstructor; progress simpl : core.

  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl : core.

  Hint Extern 1 (_ $+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  Hint Extern 1 (_ $? _ = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress m_equal) || (progress clean_map_lookups) : core.
  Hint Extern 1 (_ #+ (_,_) = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress ChMaps.m_equal) || (progress ChMaps.ChMap.clean_map_lookups) : core.
  Hint Extern 1 (_ #? _ = _) =>
    reflexivity || (solve [ solve_concrete_maps ] ) || (progress ChMaps.m_equal) || (progress ChMaps.ChMap.clean_map_lookups) : core.

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
                     _ _ _ ] => eapply CryptoSigEncCase; [ solve [ simpl; eauto ] .. | ]
    | [ H : _ $+ (?k1,_) $? ?k2 = Some ?d__rw |- context [ RealWorld.key_heap ?d__rw $? _ = Some _ ] ] =>
      is_var d__rw; is_var k2; is_not_var k1;
      destruct (k1 ==n k2); subst; clean_map_lookups; simpl
    | [ H : ?P $? _ = Some {| IdealWorld.read := _; IdealWorld.write := _ |} |- _ ] => simpl in *; unfold P in H; solve_concrete_maps
    | [ |- _ $? _ = Some _ ] => progress solve_concrete_maps
    | [ |- context [ IdealWorld.addMsg ]] => unfold IdealWorld.addMsg; simpl
    | [ |- context [ ?m #? _ ]] => progress unfold m
    | [ |- context [ _ #+ (?k1,_) #? ?k1 ]] => rewrite ChMaps.ChMap.F.add_eq_o by trivial
    | [ |- context [ _ #+ (?k1,_) #? ?k2 ]] => rewrite ChMaps.ChMap.F.add_neq_o by congruence
    | [ |- _ <-> _ ] => split
    | [ |- _ -> _ ] => intros
    | [ |- _ = _ ] => reflexivity
    | [ |- _ /\ _ ] => split
    end; split_ex; simpl in *.

  Hint Extern 1 (action_matches _ _ _ _) =>
    repeat (solve_action_matches1); NatMap.clean_map_lookups ; ChMaps.ChMap.clean_map_lookups : core.

  Hint Resolve
       findUserKeys_foldfn_proper
       findUserKeys_foldfn_transpose : core.
  
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
  
  Hint Constructors RealWorld.honest_key RealWorld.msg_pattern_safe : core.

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

Import SimulationAutomation Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).
Tactic Notation "sets" := MyPrelude.sets.

Module SetLemmas.
  Lemma setminus_empty_subtr : forall {A} (s : set A),
      s \setminus {} = s.
  Proof. sets. Qed.

  Lemma setminus_empty_minu : forall {A} (s : set A),
      {} \setminus s = {}.
  Proof. sets. Qed.

  Lemma setminus_self : forall {A} (s : set A),
      s \setminus s = {}.
  Proof. sets. Qed.

  Lemma setminus_other : forall {A} (s1 s2 : set A),
      s1 \cap s2 = {} -> s1 \setminus s2 = s1.
  Proof. sets. Qed.

  Lemma setminus_distr_subtr : forall {A} (s1 s2 s3 : set A),
      (s1 \cup s2) \setminus s3 = (s1 \setminus s3) \cup (s2 \setminus s3).
  Proof. sets. Qed.

  Lemma setminus_distr_minu : forall {A} (s1 s2 s3 : set A),
      s1 \setminus (s2 \cup s3) = (s1 \setminus s2) \cap (s1 \setminus s3).
  Proof. sets. Qed.

  Lemma union_self : forall {A} (s : set A),
      s \cup s = s.
  Proof. sets. Qed.

  Lemma  union_self_thru : forall {A} (s1 s2 : set A), s1 \cup (s1 \cup s2) = s1 \cup s2.
  Proof. sets. Qed.

  Lemma union_empty_r : forall {A} (s : set A),
      s \cup {} = s.
  Proof. sets. Qed.

  Lemma union_empty_l : forall {A} (s : set A),
      {} \cup s = s.
  Proof. sets. Qed.

  Lemma intersect_self : forall {A} (s : set A),
      s \cap s = s.
  Proof. sets. Qed.

  Lemma intersect_empty_r : forall {A} (s : set A),
      s \cap {} = {}.
  Proof. sets. Qed.

  Lemma intersect_empty_l : forall {A} (s : set A),
      {} \cap s = {}.
  Proof. sets. Qed.
End SetLemmas.

Module Tacs.
  Import SetLemmas.

  Ltac simpl_sets1 disj_tac :=
    match goal with
    | [|- context[?s' \cup ?s']] =>
      rewrite union_self
        with (s := s')
    | [|- context[?s1' \cup (?s1' \cup ?s2')]] =>
      rewrite union_self_thru
        with (s1 := s1') (s2 := s2')
    | [|- context[?s' \cup {}]] =>
      rewrite union_empty_r
        with (s := s')
    | [|- context[{} \cup ?s']] =>
      rewrite union_empty_l
        with (s := s')
    | [|- context[?s' \cap ?s']] =>
      rewrite intersect_self
        with (s := s')
    | [|- context[?s' \cap {}]] =>
      rewrite intersect_empty_r
        with (s := s')
    | [|- context[{} \cap ?s']] =>
      rewrite intersect_empty_l
        with (s := s')
    | [|- context[?s' \setminus ?s']] =>
      rewrite setminus_self
        with (s := s')
    | [|- context[?s' \setminus {}]] =>
      rewrite setminus_empty_subtr
        with (s := s')
    | [|- context[{} \setminus ?s']] =>
      rewrite setminus_empty_minu
        with (s := s')
    | [|- context[(?s1' \cup ?s2') \setminus ?s3']] =>
      rewrite setminus_distr_subtr
        with (s1 := s1') (s2 := s2') (s3 := s3')
    | [|- context[?s1' \setminus (?s2' \cup ?s3')]] =>
      rewrite setminus_distr_minu
        with (s1 := s1') (s2 := s2') (s3 := s3')
    | [|- context[?s1' \setminus ?s2']] =>
      rewrite setminus_other
        with (s1 := s1') (s2 := s2') by disj_tac
    end.

  Ltac sets_invert :=
    repeat match goal with
           | [H : (_ \cup _) _ |- _] => invert H
           | [H : (_ \cap _) _ |- _] => invert H
           | [H : [_ | _] _ |- _] => invert H
           | [H : (_ \setminus _) _ |- _] => invert H
           | [H : _ \in _ |- _] => invert H
           | [H : (complement _) _ |- _] => invert H
           | [H : { } _ |- _] => invert H
           | [H : { _ } _ |- _] => invert H
           end.

  Ltac case_lookup H :=
    match type of H with
    | ?m $? ?k = Some ?v =>
      let t := type of v in
      repeat match m with
             | context[add ?k' ?v' _ ] =>
               let t' := type of v'
               in unify t t'
                  ; match goal with
                    | [e : k = k' |- _] => fail 2
                    | [n : k <> k' |- _] => fail 2
                    | _ => destruct (k ==n k')
                    end
             end
      ; subst
      ; simpl in *
      ; clean_map_lookups
      ; simpl in *
    end.

  Lemma map_sym : forall {v} (m : NatMap.t v) k1 k2 v1 v2,
      k1 <> k2
      -> m $+ (k1, v1) $+ (k2, v2) = m $+ (k2, v2) $+ (k1, v1).
  Proof. intros; maps_equal. Qed.

  Ltac reorder_usrs n :=
    repeat match n with
           | context[add ?a ?va (add ?b ?vb ?rest)] =>
             match eval cbv in (Nat.leb a b) with
               | true =>
                 rewrite map_sym
                   with (m := rest) (k1 := b) (k2 := a) (v1 := vb) (v2 := va)
                   by auto
             end
           end.

  Tactic Notation "simpl_sets" := repeat (simpl_sets1 ltac:(shelve)).
  Tactic Notation "simpl_sets" tactic(disj_tac) := repeat (simpl_sets1 ltac:(disj_tac)).

  Tactic Notation "ifnot" tactic(t) "at" int_or_var(lvl) := tryif t then fail lvl else idtac.
  Tactic Notation "ifnot" tactic(t) := ifnot t at 0.
  Tactic Notation "concrete" constr(x) "at" int_or_var(lvl) :=
    (ifnot (is_var x) at lvl); (ifnot (is_evar x) at lvl).
  Tactic Notation "concrete" constr(x) := concrete x at 0.
  Tactic Notation "concrete" "iuniv" constr(u) :=
    match u with
    | {| IdealWorld.channel_vector := ?cv
         ; IdealWorld.users := ?usrs |} =>
      concrete cv; concrete usrs
    end.
  Tactic Notation "concrete" "iproc" constr(p) :=
    match p with
    | (IdealWorld.protocol ?p) => concrete p at 1
    | _ => concrete p at 1
    end.

  Tactic Notation "canonicalize" "rusers" :=
    repeat match goal with
           | [|- context[{| RealWorld.users := ?usrs
                           ; RealWorld.adversary := _
                           ; RealWorld.all_ciphers := _
                           ; RealWorld.all_keys := _ |}]] =>
             progress canonicalize_concrete_map usrs
           end.

  Tactic Notation "canonicalize" "iusers" :=
    repeat match goal with
           | [|- context[{| IdealWorld.channel_vector := _
                           ; IdealWorld.users := ?usrs |}]] =>
             progress canonicalize_concrete_map usrs
           end.

  Tactic Notation "canonicalize" "users" :=
    canonicalize rusers; canonicalize iusers.
End Tacs.

Import Tacs.

(* Definition S {t__hon t__adv : type} (U__r0 : RealWorld.universe t__hon t__adv) (U__i0 : IdealWorld.universe t__hon) *)
(*   : trsys (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) := *)
(*   {| Initial := {(U__r0, U__i0)} *)
(*      ; Step := step (U__r0, U__i0)  |}. *)


Module Gen.
  Import
    SetLemmas.

  Hint Unfold oneStepClosure oneStepClosure_current oneStepClosure_new : osc.

  Lemma oneStepClosure_grow : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
      (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
      -> oneStepClosure sys inv1 (inv1 \cup inv2).
  Proof. sets; repeat autounfold with osc in *; propositional; eauto. Qed.

  Lemma msc_step_alt : forall {state} (sys : trsys state) wl wl' inv inv',
      oneStepClosure_new sys wl wl'
      -> wl' \cap (wl \cup inv) = { }
      -> multiStepClosure sys ((inv \cup wl) \cup wl') wl' inv'
      -> multiStepClosure sys (inv \cup wl) wl inv'.
  Proof.
    Ltac uf := repeat autounfold with osc in *.
    intros.
    apply MscStep with (inv'0 := (wl \cup wl')).
    - uf; sets; firstorder.
    - replace ((inv \cup wl) \cup (wl \cup wl'))
        with (inv \cup wl \cup wl') by sets.
      replace (((wl \cup wl') \setminus (inv \cup wl)))
        with wl' by sets.
      assumption.
  Qed.

  (* Lemma in_empty_map_contra : (forall {t} x, In (elt := t) x $0 -> False). *)
  (* Proof. propositional. invert H. invert H0. Qed. *)

  Lemma incl_empty_empty : (forall {t}, @incl t [] []).
  Proof. cbv; auto. Qed.

  Hint Resolve
       (* in_empty_map_contra *)
       incl_empty_empty : core.

  (* Definition universe_oks : (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) -> Prop := *)
  (*   lift_fst universe_ok. *)
  (* Definition adv_universe_oks : (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) -> Prop := *)
  (*   lift_fst adv_universe_ok. *)
  (* Definition protos_ok : (RealWorld.universe t__hon t__adv * IdealWorld.universe t__hon) -> Prop := *)
  (*   lift_fst honest_cmds_safe. *)

  Ltac concrete_isteps :=
    match goal with
    | [H : istepSilent^* ?u _ |- _] =>
      concrete iuniv u; invert H
    | [H : istepSilent ?u _ |- _] =>
      concrete iuniv u; invert H
    | [H : IdealWorld.lstep_universe ?u _ _ |- _] =>
      concrete iuniv u; invert H
    | [H : IdealWorld.lstep_user _ (_, ?p, _) _ |- _] =>
      concrete iproc p; invert H
    end.

  Ltac simplify :=
    repeat (unifyTails);
    repeat match goal with
           | [ H : True |- _ ] => clear H
           end;
    repeat progress (simpl in *; intros; try autorewrite with core in *);
                     repeat (normalize_set || doSubtract).

  Ltac infer_istep :=
    match goal with
    | [H : IdealWorld.lstep_user _ (_, ?u.(IdealWorld.protocol), _) _,
           L : ?m $? ?u_id = Some ?u |- _] =>
      case_lookup L
    end.

  Ltac istep := repeat ((repeat concrete_isteps); try infer_istep).

  Ltac incorp :=
    let rec preconditions acc :=
        (match goal with
         | [H : ?P |- _] =>
           match type of P with
           | Prop =>
             match eval hnf in acc with
             | context[P] => fail 1
             | _ =>
               let acc' := eval hnf in (P /\ acc)
                 in preconditions acc'
             end
           end
         | _ => acc
         end)
    in let rec existentialize p :=
           (match goal with
            | [x : ?A |- _] =>
              match type of A with
              | Prop => fail 1
              | _ =>
                match A with
                | ((RealWorld.universe _ _) * (IdealWorld.universe _))%type =>
                  fail 2
                | _  =>
                  match p with
                  | context[x] =>
                    match eval pattern x in p with
                    | ?g _ =>
                      let p' := (eval hnf in (exists y : A, g y))
                      in existentialize p'
                    end
                  end
                end
              end
            | _ => p
            end)
       in let conds := (preconditions True) in
          match goal with
          | [|- ?i ?v] =>
            is_evar i
            ; let lp := constr:(exists x , conds /\ x = v) in
              let p := fresh "p" in
              let p' := fresh "p'" in
              let x := fresh "x" in
              assert (p : lp) by (eexists; intuition eauto)
              ; destruct p as [x p']
              ; let lp' := type of p'
                in clear p'
                   ; let lp'' := existentialize lp'
                     in match eval pattern x in lp'' with
                        | ?f _ =>
                          clear x
                          ; let scomp := (eval simpl in [e | (f e)])
                            in instantiate (1 := (scomp \cup _))
                        end
          end.

  Ltac tidy :=
    autounfold
    ; intros
    ; sets_invert
    ; propositional
    ; subst
    ; clean_map_lookups
    ; subst
    ; repeat match goal with
             | [H : (?x1, ?y1) = ?p |- _] =>
               match p with
               | (?x2, ?y2) =>
                 tryif (concrete x2; concrete y2)
                 then let H' := fresh H
                      in assert (H' : (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2)
                        by equality
                         ; propositional
                         ; discriminate
                 else invert H
               | _ => invert H
               end
             | [H : Step _ _ _ |- _] =>
               simpl in H
             | [H : exists _, _ |- _] =>
               invert H; propositional; subst
             | [H : step ?st _ |- _] =>
               concrete st; invert H
             | [H : In _ $0 |- _] =>
               invert H
             | [H : Raw.PX.MapsTo _ _ $0 |- _] =>
               invert H
             | [H : (existT _ _ _) = (existT _ _ _) |- _] =>
               invert H
             end.

  Ltac s := simpl in *.

  Ltac rstep :=
    repeat (autounfold
            ; equality1
              || (progress s)
              || discriminate
              || match goal with
                | [H : RealWorld.Output _ _ _ _ = RealWorld.Output _ _ _ _ |- _] =>
                  invert H
                | [H : RealWorld.Input _ _ _ = RealWorld.Input _ _ _ |- _] =>
                  invert H
                | [H : action_matches _ _ _ _ |- _] =>
                  invert H
                | [ H : MessageEq.message_eq _ _ _ _ _ |- _ ] =>
                  invert H

                (* clear out resulting assumption that seems to cause a problem for [close] *)
                | [ H : forall _ _ _, _ -> _ -> _ -> _ <-> _ |- _ ] => clear H
                | [ H : forall _ _ _ _, _ -> _ -> _ -> _ -> _ <-> _ |- _ ] => clear H

                | [H : RealWorld.step_universe ?u _ _ |- _] =>
                  concrete u; churn
                | [H : RealWorld.step_user _ None _ _ |- _] =>
                  (* churn *)
                invert H
                | [H : RealWorld.step_user _ _ ?u _ |- _] =>
                  concrete u; churn
                end).

  Ltac cleanup :=
    repeat (
        equality1
        || match goal with
          | [ H : True |- _ ] => clear H
          | [ H : ?X = ?X |- _ ] => clear H
          | [ H : ?x = ?y |- _] => assert (x = y) as EQ by (clear H; trivial); clear H; clear EQ
          | [ H: RealWorld.keys_mine _ $0 |- _ ] => clear H
          | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
              (rewrite add_neq_o in H by solve_simple_ineq)
            || (rewrite add_eq_o in H by trivial)
            || (destruct (k1 ==n k2); subst)
          | [ H : context [ ChMaps.ChannelType.eq _ _ ] |- _ ] => unfold ChMaps.ChannelType.eq in H
          | [ H : _ #+ (?k1,_) #? ?k2 = None |- _ ] =>
              (rewrite ChMaps.ChMap.F.add_neq_o in H by solve_simple_ineq)
            || (rewrite ChMaps.ChMap.F.add_eq_o in H by trivial)
            || (destruct (ChMaps.ChMap.F.eq_dec k1 k2); subst)

          | [ H : ?m $? _ = _ |- _ ] => progress (unfold m in H)
          | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => invert H
          (* | [ H : IdealWorld.msg_permissions_valid _ _ |- _ ] => *)
          (*   generalize (Forall_inv H); generalize (Forall_inv_tail H); clear H; intros *)
          | [ H : IdealWorld.screen_msg _ _ |- _ ] => invert H
          | [ H : IdealWorld.permission_subset _ _ |- _ ] => invert H
          | [ H : context [ IdealWorld.addMsg _ _ _ ] |- _ ] => unfold IdealWorld.addMsg in H; simpl in H
          | [ H : Forall _ [] |- _ ] => clear H
          | [ H : context [true || _]  |- _] => rewrite orb_true_l in H
          | [ H : context [_ || true]  |- _] => rewrite orb_true_r in H
          | [ H : context [false || _]  |- _] => rewrite orb_false_l in H
          | [ H : context [_ || false]  |- _] => rewrite orb_false_r in H
          | [ H : context [$0 $k++ _] |- _] => rewrite merge_perms_left_identity in H
          | [ H : context [_ $k++ $0] |- _] => rewrite merge_perms_right_identity in H
          | [ H : context [_ $k++ _]  |- _] => erewrite reduce_merge_perms in H; clean_map_lookups; eauto
          | [ H : context [match ?m $? _ with _ => _ end] |- _] => progress (unfold m in H)
          | [ H : match _ $+ (?k1,_) $? ?k2 with _ => _ end = _ |- _ ] =>
            (rewrite add_neq_o in H by solve_simple_ineq)
            || (rewrite add_eq_o in H by trivial)
          end
      ).

  Ltac close :=
    match goal with
    | [|- [_ | _] (?ru, ?iu)] =>
      concrete ru
      ; concrete iuniv iu
      ; tidy
      ; repeat eexists
      ; propositional
      ; solve[ eauto
             | canonicalize users
               ; equality ]
    | [|- (?inv1 \cup ?inv2) (?ru, ?iu)] =>
      concrete inv1
      ; concrete ru
      ; concrete iuniv iu
      ; solve[ idtac "trying left"; left; close
             | idtac "left fails; trying right"; right; close
             | idtac "something is horribly wrong" (* prevent an infinite loop *)
             ]
    | [|- ?inv (?ru, ?iu)] =>
      is_evar inv
      ; concrete ru
      ; concrete iuniv iu
      ; repeat equality1
      ; solve_concrete_maps
      ; canonicalize users
      ; clean_context
      ; cleanup
      ; NatMap.clean_map_lookups
      ; ChMaps.ChMap.clean_map_lookups
      ; incorp
      ; solve[ close ]
    end.

  Ltac gen1' :=
    simplify
    ; tidy
    ; idtac "rstep start"
    ; rstep
    ; idtac "rstep done"
    ; idtac "istep start"
    ; istep
    ; idtac "istep done"
    ; subst
    ; canonicalize users
    ; idtac "close start"
    ; repeat close
    ; idtac "close done".

  Ltac gen1 :=
    match goal with
    | [|- multiStepClosure _ _ { } _] =>
      eapply MscDone
      (* eapply MscDone; apply prove_oneStepClosure *)
      (* ; [ solve[ sets ] *)
      (*   | solve[ rewrite ?union_assoc; gen1' ]] *)
    | [|- multiStepClosure _ {(_, _)} {(_, _)} _] =>
      eapply MscStep
      ; [ solve[ apply oneStepClosure_grow; gen1' ]
        | simplify; simpl_sets (sets; tidy)]
    | [|- multiStepClosure _ (_ \cup ?wl) ?wl _] =>
      eapply msc_step_alt
      ; [ solve[ unfold oneStepClosure_new; repeat gen1' ]
        | solve[ simplify
                 ; sets
                 ; split_ex
                 ; propositional
                 ; repeat match goal with
                          | [H : (?x1, ?y1) = ?p |- _] =>
                            match p with
                            | (?x2, ?y2) =>
                              tryif (concrete x2; concrete y2)
                              then let H' := fresh H
                                   in assert (H' : (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2)
                                     by equality
                                      ; propositional
                                      ; discriminate
                              else invert H
                            | _ => invert H
                            end
                          end
               | eapply intersect_empty_l]
        | rewrite ?union_empty_r ]
    end.

  (* Use this to generate the invariant *)
  Ltac gen := repeat gen1.

End Gen.
