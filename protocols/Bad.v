From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Keys Simulation MapLtac Tactics AdversaryUniverse.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__B2A : channel_id := 0.

  Definition idealU1 :=
    {| channel_vector := $0 $+ (CH__B2A, {Exm (Content 2)})
       ; users := $0 $+ (A,  {| perms := $0  ; protocol :=
                                                 m <- @Recv Nat CH__B2A ; Return true |})
    |}.

  Definition idealU2 :=
    {| channel_vector := $0 $+ (CH__B2A, { Exm (Content 2) })
       ; users := $0 $+ (A,  {| perms := $0  ; protocol := Return true |})
    |}.

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID1 : key_identifier := 0.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1).
  Definition A__keys := $0 $+ (KID1, true).

End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs : my_ciphers) (msgs : queued_messages)
             (cs : ciphers) (adv : user_data unit) (p__a : user_cmd bool) : universe bool unit :=
    {| users            := $0 $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs ; c_heap := mycs |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
     |}.

  Definition ru1 adv :=
    mkrU [] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2))) adv
         ( c1 <- Sign KID1 (Plaintext 0)
         ; c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 c1
         ).

  Definition ru2 cid1 adv :=
    mkrU [cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         ( c1 <- Return (Signature (Plaintext 0) KID1 cid1)
         ; c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 c1
         ).

  Definition ru3 cid1 adv :=
    mkrU [cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         ( c2 <- Sign KID1 (Plaintext 1)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru4 cid1 cid2 adv :=
    mkrU [cid2;cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)]
         ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( c2 <- Return (Signature (Plaintext 1) KID1 cid2)
         ; m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru5 cid1 cid2 adv :=
    mkrU [cid2;cid1] [existT _ _ (Signature (Plaintext 2) KID1 5)]
         ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( m <- @Recv Nat (Signed KID1)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru6 cid1 cid2 adv :=
    mkrU [5;cid2;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0)) $+ (cid2, SigCipher KID1 (Plaintext 1))) adv
         ( m <- Return (Signature (Plaintext 2) KID1 5)
         ; Verify KID1 (Signature (Plaintext 0) KID1 cid1)
         ).

  Definition ru7 cid1 adv :=
    mkrU [5;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         (Verify KID1 (Signature (Plaintext 0) KID1 cid1)).

  Definition ru8 cid1 adv :=
    mkrU [5;cid1] [] ($0 $+ (5, SigCipher KID1 (Plaintext 2)) $+ (cid1, SigCipher KID1 (Plaintext 0))) adv
         (Return true).

  Inductive R : RealWorld.simpl_universe bool -> IdealWorld.universe bool -> Prop :=
  | R1 : forall adv,
      lameAdv tt adv
      -> R (peel_adv (ru1 adv)) idealU1
  | R2 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru2 cid1 adv)) idealU1
  | R3 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru3 cid1 adv)) idealU1
  | R4 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru4 cid1 cid2 adv)) idealU1
  | R5 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru5 cid1 cid2 adv)) idealU1
  | R6 : forall cid1 cid2 adv,
      lameAdv tt adv
      -> R (peel_adv (ru6 cid1 cid2 adv)) idealU2
  | R7 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru7 cid1 adv)) idealU2
  | R8 : forall cid1 adv,
      lameAdv tt adv
      -> R (peel_adv (ru8 cid1 adv)) idealU2
  .

End RealProtocol.


Section RealWorldLemmas.
  Import RealWorld.

  Lemma multiStepSilentInv :
    forall {A B} (U__r U__r': universe A B) b,
        rstepSilent ^* U__r U__r'
      -> U__r.(adversary).(protocol) = Return b
      -> U__r = U__r'
      \/ exists usrs adv cs u_id userData gks ks cmd qmsgs mycs,
            rstepSilent ^* (buildUniverse usrs adv cs gks u_id {| key_heap := ks; protocol := cmd; msg_heap := qmsgs; c_heap := mycs |}) U__r'
          /\ users U__r $? u_id = Some userData
          /\ step_user Silent (Some u_id) (RealWorld.build_data_step U__r userData) (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd).
  Proof.
    intros.
    invert H; intuition idtac.
    right. invert H1.
    - repeat eexists; intuition; eauto.
    - exfalso.
      destruct U__r; destruct adversary; simpl in *; subst.
      unfold build_data_step in H; simpl in *.
      invert H.
  Qed.


  Lemma add_univ_simpl1 :
    forall {v} (m : NatMap.t v) k1 v1 k2 v2,
      k1 = k2
      -> m $+ (k1,v1) $+ (k2,v2) = m $+ (k2,v2).
  Proof.
    intros. simpl.
    apply map_eq_Equal; unfold Equal; intros; subst.
    case (k2 ==n y); intros; subst.
    rewrite !add_eq_o; trivial.
    rewrite !add_neq_o; trivial.
  Qed.

  Lemma add_univ_simpl2 :
    forall {v} (m : NatMap.t v) k1 v1 k2 v2 k3 v3,
      k1 = k3
      -> k2 <> k3
      -> m $+ (k1,v1) $+ (k2,v2) $+ (k3,v3) = m $+ (k3,v3) $+ (k2,v2).
  Proof.
    intros. simpl.
    apply map_eq_Equal; unfold Equal; intros; subst.
    case (y ==n k2); intros; subst.
    rewrite add_neq_o by auto; rewrite !add_eq_o; trivial.
    case (y ==n k3); intros; subst.
    rewrite add_eq_o by trivial. rewrite add_neq_o by auto. rewrite add_eq_o; trivial.
    rewrite !add_neq_o by auto; trivial.
  Qed.

  Lemma add_univ_simpl3 :
    forall {v} (m : NatMap.t v) k1 v1 k2 v2 k3 v3,
      k1 = k2
      -> k2 <> k3
      -> m $+ (k1,v1) $+ (k2,v2) $+ (k3,v3) = m $+ (k2,v2) $+ (k3,v3).
  Proof.
    intros. simpl.
    apply map_eq_Equal; unfold Equal; intros; subst.
    case (y ==n k3); intros; subst.
    rewrite !add_eq_o; trivial.
    case (y ==n k2); intros; subst.
    do 2 (rewrite add_neq_o by auto; rewrite add_eq_o by auto); trivial.
    rewrite !add_neq_o by auto; trivial.
  Qed.

  Lemma simplify_build_univ1 :
    forall {A B} (U__r : universe A B) (usrs : honest_users A) uid__a uid__b ud__a ud__b uid ud (adv : user_data B) gks cs,
        uid__a <> uid__b
      -> uid = uid__a
      -> buildUniverse (usrs $+ (uid__a,ud__a) $+ (uid__b,ud__b)) adv cs gks uid ud
        = {| users       := usrs $+ (uid,ud) $+ (uid__b,ud__b)
           ; adversary   := adv
           ; all_ciphers := cs
           ; all_keys    := gks
          |}.
  Proof.
    intros. unfold buildUniverse; simpl.
    f_equal; subst.
    rewrite add_univ_simpl2 by auto; trivial.
  Qed.

  Lemma simplify_build_univ2 :
    forall {A B} (U__r : universe A B) (usrs : honest_users A) uid__a uid__b ud__a ud__b uid ud (adv : user_data B) gks cs,
        uid__a <> uid__b
      -> uid = uid__b
      -> buildUniverse (usrs $+ (uid__a,ud__a) $+ (uid__b,ud__b)) adv cs gks uid ud
        = {| users       := usrs $+ (uid__a,ud__a) $+ (uid,ud)
           ; adversary   := adv
           ; all_ciphers := cs
           ; all_keys    := gks
          |}.
  Proof.
    intros. unfold buildUniverse; simpl.
    f_equal.
    rewrite add_univ_simpl1 by auto; trivial.
  Qed.

End RealWorldLemmas.

Module SimulationAutomation.

  Hint Constructors RealWorld.msg_accepted_by_pattern.

  Ltac equality1 :=
    match goal with
    | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition idtac

    | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
    | [ H : _  $? _ = Some _ |- _ ] => progress (simpl in H)

    | [ H : add _ _ _ $? _ = Some ?UD |- _ ] =>
      match type of UD with
      | RealWorld.user_data bool => apply lookup_some_implies_in in H
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
    | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => apply inj_pair2 in H

    | [ H: RealWorld.SigCipher _ _ = RealWorld.SigCipher _ _ |- _ ] => invert H
    | [ H: RealWorld.SigEncCipher _ _ _ = RealWorld.SigEncCipher _ _ _ |- _ ] => invert H
    | [ H: MkCryptoKey _ _ _ = _ |- _ ] => invert H

    | [ H: exists _, _ |- _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H

    | [ H : keyId _ = _ |- _] => inversion H; clear H
    end.

  Section InversionPrinciples.
    Import RealWorld.

    (* :flag Keep Proof Equalities. *)

    Derive Inversion_clear some_inv with (forall (s1 s2 : Type), Some s1 = Some s2) Sort Prop.

    Derive Inversion_clear step_user_inv_gen with
        (forall (A B : Type) (lbl : rlabel) (u_id : option user_id) (usrs usrs' : honest_users A)
           (adv adv' : user_data B) (cs cs' : ciphers) (gks gks' : keys) (ks ks': key_perms)
           (qmsgs qmsgs' : queued_messages) (mycs mycs' : my_ciphers) (cmd' : user_cmd nat),
            step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Gen) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd'))
        Sort Prop.
    Check step_user_inv_gen.
    Check some_inv.

    Derive Inversion_clear step_user_inv_bind with
        (forall (A B C C': Type) (lbl : rlabel) (u_id : option user_id) (usrs usrs' : honest_users A)
           (adv adv' : user_data B) (cs cs' : ciphers) (gks gks' : keys) (ks ks': key_perms)
           (qmsgs qmsgs' : queued_messages) (mycs mycs' : my_ciphers) (cmd1 cmd1' : user_cmd C) (cmd : C -> user_cmd C'),
            step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind cmd1 cmd) (usrs', adv', cs', gks', ks', qmsgs', mycs', Bind cmd1' cmd))
        Sort Prop.

    Lemma step_user_inv_gen' :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
          step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Gen) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ lbl = Silent
        /\ exists n, cmd = Return n.
    Proof.
      intros.
      inversion H; repeat equality1; subst; intuition idtac; eauto.
    Qed.

    Lemma step_user_inv_bind' :
      forall {A B C C'} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd1 : user_cmd C) (cmd : C -> user_cmd C') (cmd' : user_cmd C'),
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Bind cmd1 cmd) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd')
        -> (exists cmd1',
              step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, cmd1) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd1')
            /\ cmd' = Bind cmd1' cmd
          )
        \/ ( usrs = usrs'
          /\ adv = adv'
          /\ cs = cs'
          /\ gks = gks'
          /\ ks = ks'
          /\ qmsgs = qmsgs'
          /\ mycs = mycs'
          /\ lbl = Silent
          /\ exists c, cmd1 = Return c
               /\ cmd' = cmd c).
    Proof.
      intros.
      invert H; intuition eauto.
    Qed.

    Lemma step_user_inv_recv :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd : user_cmd (message t)) pat,
          step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Recv pat) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ exists msg msgs,
            qmsgs = (existT message t msg) :: msgs
          /\ qmsgs' = msgs
          /\ ( ( msg_accepted_by_pattern pat msg
              /\ ks' = ks $k++ findKeys msg
              /\ mycs' = findCiphers msg ++ mycs
              /\ lbl = Action (Input msg pat ks)
              /\ cmd = Return msg)
            \/ ( ~ msg_accepted_by_pattern pat msg
              /\ ks = ks'
              /\ mycs = mycs'
              /\ lbl = Silent
              /\ cmd = Recv pat
              )).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; intuition eauto.
    Qed.

    Lemma step_user_inv_send :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) (msg : message t)
        lbl u_id rec_u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl (Some u_id) (usrs, adv, cs, gks, ks, qmsgs, mycs, Send rec_u_id msg) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ adv' = addUserKeys (findKeys msg) adv
        /\ rec_u_id <> u_id
        /\ lbl = Action (Output msg)
        /\ cmd = Return tt
        /\ exists rec_u,
            usrs $? rec_u_id = Some rec_u
          /\ usrs' = usrs $+ (rec_u_id, {| key_heap := rec_u.(key_heap)
                                        ; protocol := rec_u.(protocol)
                                        ; msg_heap := rec_u.(msg_heap) ++ [existT _ _ msg]
                                        ; c_heap   := rec_u.(c_heap) |}).
    Proof.
      intros.
      invert H; intuition idtac.
      eexists; eauto.
    Qed.

    Lemma step_user_inv_enc :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign k__enc (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, SignEncrypt k__sign k__enc msg) (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ keys_mine ks (findKeys msg)
        /\ incl (findCiphers msg) mycs
        /\ (exists kt__enc kt__sign kp__enc,
                gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
              /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__enc   = Some kp__enc
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigEncCipher k__sign k__enc msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (SignedCiphertext k__sign k__enc c_id)).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_dec :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign k__enc c_id
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' (cmd : user_cmd (message t)),
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Decrypt (SignedCiphertext k__sign k__enc c_id))
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ List.In c_id mycs
        /\ exists (msg : message t) kt__enc kt__sign kp__sign,
            cs $? c_id     = Some (SigEncCipher k__sign k__enc msg)
          /\ gks $? k__enc  = Some (MkCryptoKey k__enc Encryption kt__enc)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__enc  = Some true
          /\ ks  $? k__sign = Some kp__sign
          /\ ks' = ks $k++ findKeys msg
          /\ mycs' = findCiphers msg ++ mycs
          /\ cmd = Return msg.
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_sign :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Sign k__sign msg)
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ lbl = Silent
        /\ (exists kt__sign,
                gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
              /\ ks $? k__sign  = Some true)
        /\ (exists c_id,
              ~ In c_id cs
              /\ cs' = cs $+ (c_id, SigCipher k__sign msg)
              /\ mycs' = c_id :: mycs
              /\ cmd = Return (Signature msg k__sign c_id)).
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma step_user_inv_verify :
      forall {A B t} (usrs usrs' : honest_users A) (adv adv' : user_data B) k__sign c_id (msg : message t)
        lbl u_id cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        step_user lbl u_id (usrs, adv, cs, gks, ks, qmsgs, mycs, Verify k__sign (Signature msg k__sign c_id))
                  (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
        -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ lbl = Silent
        /\ cmd = Return true
        /\ List.In c_id mycs
        /\ exists (msg : message t) kt__sign kp__sign,
            cs $? c_id     = Some (SigCipher k__sign msg)
          /\ gks $? k__sign = Some (MkCryptoKey k__sign Signing kt__sign)
          /\ ks  $? k__sign = Some kp__sign.
    Proof.
      intros.
      invert H; intuition idtac; repeat eexists; eauto.
    Qed.

    Lemma adv_no_step :
      forall {A B} (usrs usrs' : honest_users A) (adv adv' : user_data B) b
        lbl cs cs' qmsgs qmsgs' gks gks' ks ks' mycs mycs' cmd,
        lameAdv b adv
        -> step_user lbl None (usrs, adv, cs, gks, ks, qmsgs, mycs, protocol adv)
                    (usrs', adv', cs', gks', ks', qmsgs', mycs', cmd)
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

    Ltac is_not_var V :=
      first [ is_var V; fail 1
            | idtac ].

  Ltac churn1 :=
    match goal with

    | [ H : ~ RealWorld.msg_accepted_by_pattern ?pat ?msg |- _ ] =>
      assert ( RealWorld.msg_accepted_by_pattern pat msg ) by eauto; contradiction

    (* Only take a user step if we have chosen a user *)

    | [ H : RealWorld.step_user _ (Some ?u) (_,_,_,_,_,_,_,?cmd) _ |- _ ] =>
      is_not_var u;
        match cmd with
        | Return _ => invert H
        | Bind _ _ => apply step_user_inv_bind' in H; split_ands; split_ors; split_ands; subst; try discriminate
        | Gen => apply step_user_inv_gen' in H
        | Send _ _ => apply step_user_inv_send in H
        | Recv _ => apply step_user_inv_recv in H
        | SignEncrypt _ _ _ => apply step_user_inv_enc in H
        | Decrypt _ => apply step_user_inv_dec in H
        | Sign _ _ => apply step_user_inv_sign in H
        | Verify _ _ => apply step_user_inv_verify in H
        | _ => idtac cmd; intuition idtac; subst; (progress (simpl in H) || invert H)
        end

    (* | GenerateSymKey  (usage : key_usage) : user_cmd key_permission *)
    (* | GenerateAsymKey (usage : key_usage) : user_cmd key_permission *)

    (* | [ H : RealWorld.step_user _ None _ _ |- _ ] => progress (simpl in H) *)
    (* | [ H : RealWorld.step_user _ None (RealWorld.build_data_step _ adv) _ |- _ ] => unfold adv in H; invert H *)
    | [ STEP : RealWorld.step_user _ None (_,_,_,_,_,_,_,RealWorld.protocol ?adv) _
      , LAME : lameAdv _ ?adv |- _ ] => pose proof (adv_no_step LAME STEP); contradiction


    | [ H : RealWorld.step_user _ _ (build_data_step _ _) _ |- _ ] => unfold build_data_step in H; simpl in H

    | [ H :rstepSilent ^* (RealWorld.buildUniverse _ _ _ _ _ _) _ |- _] =>
      unfold RealWorld.buildUniverse in H; autorewrite with simpl_univ in H
    | [ |- context [RealWorld.buildUniverse _ _ _ _ _ _] ] =>
      unfold RealWorld.buildUniverse
      (* (rewrite simplify_build_univ1 in H by auto) || (rewrite simplify_build_univ2 in H by auto) *)
    | [ S: rstepSilent ^* ?U _ |- _ ] => 
      (* Don't actually multiStep unless we know the state of the starting universe
       * meaning it is not some unknown hypothesis in the context...
       *)
      match goal with
      | [U1 : U |- _] => fail 1
      (* | [U1 : RealWorld.step_user _ _ _ _ |- _ ] => idtac "nope1"; fail 1 *)
      (* | [U1 : RealWorld.step_universe _ _ _ |- _ ] => idtac "nope2"; fail 1 *)
      (* | [U1 : rstepSilent _ _ |- _ ] => idtac "nope3"; fail 1 *)
      | [ |- _ ] =>
        (* invert S *)
        eapply multiStepSilentInv in S; split_ors; split_ex; intuition idtac; subst
      end

    | [ H: rstepSilent ?U _ |- _ ] => is_not_var U; invert H
      (* match goal with *)
      (* | [ U1 : U |- _ ] => fail 1 *)
      (* | [ |- _ ] => invert H *)
      (* end *)
    | [ H: RealWorld.step_universe _ _ _ |- _ ] => invert H

    end.

  End T.

  Import T.

  (* Ltac notHyp P := *)
  (*   match goal with *)
  (*   | [ _ : P |- _ ] => fail 1 *)
  (*   | _ => idtac "notHyp" *)
  (*   end. *)

  Ltac churn2 :=
    (repeat equality1); subst; churn1; intuition idtac; split_ex; intuition idtac; subst; try discriminate.

  Ltac churn :=
    repeat churn2.

  Ltac usr_first :=
    eapply find_mapsto_iff;
      eapply elements_mapsto_iff;
      eapply SetoidList.InA_alt;
      eexists;
      unfold eq_key_elt, Raw.PX.eqke; constructor; [intuition idtac | ..].

  Ltac user0 := usr_first; left.
  Ltac user1 := usr_first; right; left.

  Ltac istep_univ pick :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..];
      (try eapply @eq_refl); (try f_equal); simpl.
  Ltac rstep_univ pick :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick | ..]; (try eapply @eq_refl); simpl.

  Ltac istep_univ0 := istep_univ user0.
  Ltac istep_univ1 := istep_univ user1.
  Ltac rstep_univ0 := rstep_univ user0.
  Ltac rstep_univ1 := rstep_univ user1.

  Ltac i_single_silent_step :=
      eapply IdealWorld.LStepBindProceed
    || eapply IdealWorld.LStepGen
    || eapply IdealWorld.LStepCreateChannel
  .

  Ltac r_single_silent_step :=
      eapply RealWorld.StepBindProceed
    || eapply RealWorld.StepGen
    || eapply RealWorld.StepRecvDrop
    || eapply RealWorld.StepEncrypt
    || eapply RealWorld.StepDecrypt
    || eapply RealWorld.StepSign
    || eapply RealWorld.StepVerify
  .

  Ltac isilent_step_univ pick :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..]; (try simple eapply @eq_refl);
      ((eapply IdealWorld.LStepBindRecur; i_single_silent_step) || i_single_silent_step).
  Ltac rsilent_step_univ pick :=
    eapply  RealWorld.StepUser; simpl; swap 2 3; [ pick | ..]; (try simple eapply @eq_refl);
      ((eapply RealWorld.StepBindRecur; r_single_silent_step) || r_single_silent_step).

  Ltac silent_step usr_step := eapply TrcFront; [usr_step |]; simpl.

  Ltac real_silent_step0 := silent_step ltac:(rsilent_step_univ user0).
  Ltac real_silent_step1 := silent_step ltac:(rsilent_step_univ user1).

  Ltac ideal_silent_step0 := silent_step ltac:(isilent_step_univ user0).
  Ltac ideal_silent_step1 := silent_step ltac:(isilent_step_univ user1).

  Ltac ideal_silent_steps :=
    (ideal_silent_step0 || ideal_silent_step1);
      repeat ideal_silent_step0;
      repeat ideal_silent_step1;
      eapply TrcRefl.

  Remove Hints TrcRefl TrcFront.
  Hint Extern 1 (_ ^* ?U ?U) => apply TrcRefl.

  Remove Hints eq_sym (* includes_lookup *).
  Remove Hints trans_eq_bool mult_n_O plus_n_O eq_add_S f_equal_nat.

  Hint Constructors R action_matches msg_eq.
  Hint Resolve IdealWorld.LStepSend' IdealWorld.LStepRecv'.

  Lemma TrcRefl' :
    forall {A} (R : A -> A -> Prop) x1 x2,
      x1 = x2 ->
      trc R x1 x2.
  Proof.
    intros. subst. apply TrcRefl.
  Qed.

  Hint Extern 0 (rstepSilent ^* _ _) => solve [eapply TrcRefl || eapply TrcRefl'; simpl; smash_universe].
  Hint Extern 1 (rstepSilent ^* _ _) => real_silent_step0.
  Hint Extern 1 (rstepSilent ^* _ _) => real_silent_step1.
  Hint Extern 1 (R (RealWorld.buildUniverse _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.

  Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ0.
  Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ1.
  Hint Extern 1 (IdealWorld.lstep_user _ (_, IdealWorld.Bind _ _, _) _) => eapply IdealWorld.LStepBindRecur.
  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_steps || apply TrcRefl.

  Hint Extern 1 (List.In _ _) => progress simpl.

  (* Hint Extern 1 (RealWorld.encryptMessage _ _ _ = _) => unfold RealWorld.encryptMessage; simpl. *)
  (* Hint Extern 1 (RealWorld.signMessage _ _ _ = _) => unfold RealWorld.signMessage; simpl. *)
  Hint Extern 1 (RealWorld.action_adversary_safe _ _ _ = _) => unfold RealWorld.action_adversary_safe; simplify.
  Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.

  Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, KEY1, KID1.
  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl.
  Hint Extern 1 (add _ _ _ = _) => m_equal.
  Hint Extern 1 (find _ _ = _) => m_equal.
  Hint Extern 1 (_ \in _) => sets.

End SimulationAutomation.

Import SimulationAutomation.

Section FeebleSimulates.

  Hint Rewrite @add_univ_simpl1 using (trivial || discriminate) : simpl_univ.
  Hint Rewrite @add_univ_simpl2 using (trivial || discriminate) : simpl_univ.
  Hint Rewrite @add_univ_simpl3 using (trivial || discriminate) : simpl_univ.

  Ltac simplUniv :=
    repeat match goal with
           | [ |- context[ _ $+ (?A,_) $+ (?A,_) ] ] => rewrite add_univ_simpl1 by trivial
           | [ |- context[ _ $+ (?A,_) $+ (?B,_) $+ (?A,_) ] ] => rewrite add_univ_simpl2 by auto
           | [ |- context[ _ $+ (?A,_) $+ (?A,_) $+ (?B,_) ] ] => rewrite add_univ_simpl3 by auto
           end.

  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Ltac solve_universe_ok :=
    repeat
      match goal with
      | [ H : universe_ok _ |- universe_ok _ ] =>
        unfold universe_ok, RealWorld.buildUniverse in H;
        unfold universe_ok, RealWorld.buildUniverse;
        simpl in H; simpl
      | [ |- encrypted_ciphers_ok _ _ ] => econstructor
      | [ |- encrypted_cipher_ok _ _ _ ] => econstructor
      | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
      | [ |- forall k, RealWorld.findKeys _ $? _ = Some true -> False ] => intros
      | [ H : RealWorld.findKeys _ $? _ = Some true |- False ] => progress simpl in H; invert H
      end.


  Lemma rpingbase_silent_simulates :
    simulates_silent_step (lameAdv tt) R.
  Proof.
    unfold simulates_silent_step; intros.

    intros; invert H;
      try destruct U__r0; try destruct U__r; simpl in *; subst.

    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R2; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R3; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        simpl.
        eapply R4; eauto.

    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R5; eauto.
    - churn. admit.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R7; eauto.
    - churn.
      * eexists; split; swap 1 2; eauto 9.
        rewrite map_add_eq; auto.
        eapply R8; eauto.




End FeebleSimulates.
