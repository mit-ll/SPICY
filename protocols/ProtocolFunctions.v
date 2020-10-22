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
     Classical
     List.

Require Import
        MyPrelude
        Maps
        ChMaps
        Messages
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        SafeProtocol.

From KeyManagement Require
     IdealWorld RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* Permissions *)
Notation owner  := {| IdealWorld.read := true; IdealWorld.write := true |}.
Notation reader := {| IdealWorld.read := true; IdealWorld.write := false |}.
Notation writer := {| IdealWorld.read := false; IdealWorld.write := true |}.

Definition quiet (lbl : RealWorld.rlabel) :=
  match lbl with
  | Silent => True
  | _ => False
  end.

(* Notation "~^*" := (trc3 RealWorld.step_universe quiet) (at level 0). *)

Section RealWorldLemmas.
  Import RealWorld.

  (* Lemma multiStepSilentInv : *)
  (*   forall {A B} (U__r U__r': universe A B) b, *)
  (*       ~^* U__r U__r' *)
  (*     -> U__r.(adversary).(protocol) = Return b *)
  (*     -> U__r = U__r' *)
  (*     \/ exists usrs adv cs u_id userData gks ks cmd qmsgs mycs froms tos cur_n, *)
  (*         ~^* (buildUniverse usrs adv cs gks u_id *)
  (*                                       {| key_heap := ks *)
  (*                                        ; protocol := cmd *)
  (*                                        ; msg_heap := qmsgs *)
  (*                                        ; c_heap := mycs *)
  (*                                        ; from_nons := froms *)
  (*                                        ; sent_nons := tos *)
  (*                                        ; cur_nonce := cur_n |}) U__r' *)
  (*         /\ users U__r $? u_id = Some userData *)
  (*         /\ step_user Silent *)
  (*                     (Some u_id) *)
  (*                     (RealWorld.build_data_step U__r userData) *)
  (*                     (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, tos, cur_n, cmd). *)
  (* Proof. *)
  (*   intros * H ADV. *)
  (*   invert H; intuition idtac. *)
  (*   right. *)
  (*   invert H1; unfold quiet in H0. *)
  (*   - unfold quiet in H0; destruct b0; try contradiction. *)
  (*     repeat eexists; intuition; eauto. *)
  (*   - exfalso. *)
  (*     destruct U__r; destruct adversary; simpl in *; subst. *)
  (*     unfold build_data_step in H; simpl in *. *)
  (*     invert H. *)
  (* Qed. *)

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

  Lemma some_eq_inv :
    forall A (a a' : A), Some a = Some a' -> a = a'.
  Proof. intros * H; invert H; auto.  Qed.
    
  Lemma tuple_eq_inv :
    forall A B (a a' : A) (b b' : B), (a,b) = (a',b') -> a = a' /\ b = b'.
  Proof. intros * H; invert H; eauto. Qed.

  Lemma list_eq_inv :
    forall A (x x' : A) xs xs', x :: xs = x' :: xs' -> x = x' /\ xs = xs'.
  Proof. intros * H; invert H; eauto. Qed.
      

End OtherInvLemmas.

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
    => apply split_real_univ_fields in H; split_ex; subst
  | [ |- RealWorld.protocol (RealWorld.adversary _) = RealWorld.Return _ ] => simpl
  | [ H : lameAdv _ ?adv |- RealWorld.protocol ?adv = _ ] => unfold lameAdv in H; eassumption

  | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => progress (simpl in H)

  | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => inversion H; clear H
  | [ H : Some _ = Some _ |- _ ] => apply some_eq_inv in H; subst
  | [ H : (_ :: _) = (_ :: _) |- _ ] => apply list_eq_inv in H; split_ex; subst
  | [ H : (_ :: _) = ?x |- _ ] => is_var x; invert H
  | [ H : ?x = (_ :: _) |- _ ] => is_var x; invert H
  | [ H : (_,_) = (_,_) |- _ ] => apply tuple_eq_inv in H; split_ex; subst
  | [ H : [] = _ ++ _ :: _ |- _ ] => apply nil_not_app_cons in H; contradiction
  (* | [ H : (_,_,_) = (_,_,_) |- _ ] => inversion H; clear H *)
  | [ H : Action _ = Action _ |- _ ] => apply action_eq_inv in H; subst
  | [ H : Silent = Action _ |- _ ] => discriminate H
  | [ H : Action _ = Silent |- _ ] => discriminate H
  | [ H : RealWorld.Return _ = RealWorld.Return _ |- _ ] => apply invert_return in H
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H

  | [ H: RealWorld.SignedCiphertext _ = RealWorld.SignedCiphertext _ |- _ ] =>
    apply ct_eq_inv in H; split_ex; subst
  | [ H: RealWorld.SigCipher _ _ _ _ = RealWorld.SigCipher _ _ _ _ |- _ ] =>
    apply sigcphr_eq_inv in H; split_ex; subst
  | [ H: RealWorld.SigEncCipher _ _ _ _ _ = RealWorld.SigEncCipher _ _ _ _ _ |- _ ] =>
    apply enccphr_eq_inv in H; split_ex; subst
  | [ H : _ = RealWorld.Output _ _ _ _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
  | [ H : RealWorld.Output _ _ _ _ = _ |- _ ] => apply output_act_eq_inv in H; split_ex; subst
  | [ H : _ = RealWorld.Input _ _ _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
  | [ H : RealWorld.Input _ _ _ = _ |- _ ] => apply input_act_eq_inv in H; split_ex; subst
  | [ H : MkCryptoKey _ _ _ = _ |- _ ] => apply key_eq_inv in H; split_ex; subst

  | [ H: _ = {| IdealWorld.read := _ |} |- _ ] => invert H
  | [ H: {| IdealWorld.read := _ |} = _ |- _ ] => invert H

  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H

  | [ H : keyId _ = _ |- _] => inversion H; clear H
  end.

Section IdealWorldDefs.
  Import IdealWorld.

  Definition mkiUsr {t} (uid : user_id) (p : permissions) (proto : cmd (Base t)) :=
    (uid, {| perms := p ; protocol := proto |}).

  Definition mkiU {t} (cv : channels) (usrs : list (user_id * user t)) :=
    {| channel_vector := cv;
       users := fold_left (fun us u => us $+ (fst u, snd u)) usrs $0
    |}.

  Definition sharePerm (pid : perm_id) (p : permission) :=
    Permission (construct_access p pid).

  Definition getPerm (m : message Access) : perm_id :=
    ch_id (extractPermission m).
    
End IdealWorldDefs.

Section RealWorldDefs.
  Import RealWorld.

  Definition mkrUsr {t} (ks : key_perms) (p : user_cmd (Base t)) :=
    {| key_heap  := ks ;
       protocol  := p ;
       msg_heap  := [] ;
       c_heap    := [] ;
       from_nons := [] ;
       sent_nons := [] ;
       cur_nonce := 0
    |}.

  (* A nice, boring adversary that can be used for protocol proofs. *)
  Definition noAdv := {| key_heap  := $0;
                         protocol  := @Return (Base Unit) tt;
                         msg_heap  := [];
                         c_heap    := [];
                         from_nons := [];
                         sent_nons := [];
                         cur_nonce := 0 |}.

  Record RUserSpec {t} :=
    MkRUserSpec {
        userId    : user_id ;
        userKeys  : key_perms ;
        userProto : user_cmd (Base t)
      }.

  Definition mkrU {t} (gks : keys) (usrs : list (@RUserSpec t)) :=
    let us := fold_left (fun acc u => acc $+ (u.(userId), mkrUsr u.(userKeys) u.(userProto))) usrs $0
    in  {| users       := us ;
           adversary   := noAdv ;
           all_ciphers := $0 ;
           all_keys    := gks
        |}.

  Definition sharePrivKey (kp : key_permission) :=
    Permission (fst kp, true).

  Definition sharePubKey (kp : key_permission) :=
    Permission (fst kp, false).

  Definition getKey (m : message Access) : key_identifier :=
    fst (extractPermission m).

End RealWorldDefs.

Definition mkKeys (ks : list key) :=
  fold_left (fun ks k => ks $+ (k.(keyId),k)) ks $0.

Hint Unfold
     mkiU mkiUsr
     sharePerm getPerm
     mkrU mkrUsr
     sharePrivKey sharePubKey getKey
     mkKeys
     noAdv : user_build.

Hint Unfold
     mkiU mkiUsr
     sharePerm getPerm
     mkrU mkrUsr
     sharePrivKey sharePubKey getKey
     mkKeys
     noAdv : core.

Declare Scope protocol_scope.
(* Notation "uid 'keys' ks >> p" := (MkRUserSpec uid ks p) (at level 80) : protocol_scope. *)

Notation "'skey' kid"     := (MkCryptoKey kid Signing AsymKey) (at level 80) : protocol_scope.
Notation "'ekey' kid"     := (MkCryptoKey kid Encryption AsymKey) (at level 80) : protocol_scope.
Notation "'skey_sym' kid" := (MkCryptoKey kid Signing SymKey) (at level 80) : protocol_scope.
Notation "'ekey_sym' kid" := (MkCryptoKey kid Encryption SymKey) (at level 80) : protocol_scope.

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
                (* \/ ( ~ msg_accepted_by_pattern cs u_id froms pat msg *)
                (*     /\ ks = ks' *)
                (*     /\ mycs = mycs' *)
                (*     /\froms' = (if msg_signed_addressed (findUserKeys usrs) cs u_id msg *)
                (*                then updateTrackedNonce u_id froms cs msg *)
                (*                else froms) *)
                (*     /\ lbl = Silent *)
                (*     /\ cmd = Recv pat) *)
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

Import RealWorld.

Ltac step_usr_id uid :=
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
