From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Keys Simulation MapLtac Tactics Automation AdversaryUniverse.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.
Definition B : user_id   := 1.

Transparent A B.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := 0.
  Definition CH__B2A : channel_id := 1.

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := false; write := true |}) $+ (CH__B2A, {| read := true; write := false |}).
  Definition PERMS__b := $0 $+ (CH__B2A, {| read := false; write := true |}) $+ (CH__A2B, {| read := true; write := false |}).

  Definition mkiU (cv : channels) (p__a p__b : cmd bool): universe bool :=
    {| channel_vector := cv
     ; users := $0
         $+ (A,   {| perms    := PERMS__a ; protocol := p__a |})
         $+ (B,   {| perms    := PERMS__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU ($0 $+ (CH__A2B, { }) $+ (CH__B2A, { }))
         ( n <- Gen
         ; _ <- Send (Content n) CH__A2B
         ; m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- @Recv Nat CH__A2B
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_sent1 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, { }))
         ( _ <- Return tt
         ; m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- @Recv Nat CH__A2B
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_recd1 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, { }))
         ( m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( m <- Return (Content n)
         ; _ <- Send m CH__B2A
         ; Return true).

  Definition ideal_univ_sent2 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         ( m <- @Recv Nat CH__B2A
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         ( _ <- Return tt
         ; Return true).

  Definition ideal_univ_recd2 n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         ( m <- Return (Content n)
         ; Return match extractContent m with
                  | None =>    false
                  | Some n' => if n ==n n' then true else false
                  end)
         (Return true).

  Definition ideal_univ_done n :=
    mkiU ($0 $+ (CH__A2B, {Exm (Content n)}) $+ (CH__B2A, {Exm (Content n)}))
         (Return true)
         (Return true).

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID1 : key_identifier := 0.
  Definition KID2 : key_identifier := 1.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEY2  := MkCryptoKey KID2 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1) $+ (KID2, KEY2).

  Definition A__keys := $0 $+ (KID1, true) $+ (KID2, false).
  Definition B__keys := $0 $+ (KID1, false) $+ (KID2, true).
End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs1 mycs2 : my_ciphers) (msgs1 msgs2 : queued_messages)
                  (cs : ciphers) (p__a p__b : user_cmd bool) (adv : user_data unit) : universe bool unit :=
    {| users            := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs1 ; c_heap := mycs1 |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b ; msg_heap := msgs2 ; c_heap := mycs2 |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
     |}.

  Definition real_univ_start cs mycs1 mycs2 :=
    mkrU  mycs1 mycs2 [] [] cs
         ( n  <- Gen
         ; m  <- Sign KID1 (Plaintext n)
         ; _  <- Send B m
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent1 n cs mycs1 mycs2 cid1 :=
    mkrU  mycs1 mycs2 [] [existT _ _ (Signature (Plaintext n) KID1 cid1)]
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)
         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_recd1 n cs mycs1 mycs2 cid1 :=
    mkrU mycs1 mycs2 [] []
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- Return (Signature (Plaintext n) KID1 cid1)
         ; v  <- Verify KID1 m
         ; m' <- match unSig m with
                | Some p => Sign KID2 p
                | _      => Sign KID2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent2 n cs mycs1 mycs2 cid1 cid2 :=
    mkrU mycs1 mycs2 [existT _ _ (Signature (Plaintext n) KID2 cid2)] []
         (cs $+ (cid1, SigCipher KID1 (Plaintext n)) $+ (cid2, SigCipher KID2 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_recd2 n cs mycs1 mycs2 cid1 cid2 :=
    mkrU mycs1 mycs2 [] [] (cs $+ (cid1, SigCipher KID1 (Plaintext n)) $+ (cid2, SigCipher KID2 (Plaintext n)))
         ( m' <- Return (Signature (Plaintext n) KID2 cid2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_done mycs1 mycs2 cs :=
    mkrU mycs1 mycs2 [] [] cs (Return true) (Return true).

  Inductive RPingPongBase: RealWorld.simpl_universe bool -> IdealWorld.universe bool -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 adv,
        rstepSilent^* (real_univ_start mycs1 mycs2 cs adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) ideal_univ_start

  | Sent1 : forall U__r cs mycs1 mycs2 cid1 n adv,
        rstepSilent^* (real_univ_sent1 n cs mycs1 mycs2 cid1 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_sent1 n)

  | Recd1 : forall U__r cs mycs1 mycs2 cid1 n adv,
        rstepSilent^* (real_univ_recd1 n cs mycs1 mycs2 cid1 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_recd1 n)

  | Sent2 : forall U__r cs mycs1 mycs2 cid1 cid2 n adv,
        rstepSilent^* (real_univ_sent2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_sent2 n)

  | Recd2 : forall U__r cs mycs1 mycs2 cid1 cid2 n adv,
        rstepSilent^* (real_univ_recd2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> lameAdv tt adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_recd2 n)

  | Done : forall U__r cs mycs1 mycs2 n adv,
      lameAdv tt adv
      -> U__r = real_univ_done cs mycs1 mycs2 adv
      -> RPingPongBase (peel_adv U__r) (ideal_univ_done n)
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

    | [ H : RealWorld.step_user _ (Some ?u) _ _ |- _ ] => progress simpl in H
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

    (* | [ S: rstepSilent ^* ?U _ |- _ ] =>  *)
    (*   match goal with *)
    (*   | [U1 : U |- _] => fail 1 *)
    (*   | [ |- _ ] => *)
    (*     eapply multiStepSilentInv in S; split_ors; split_ex; intuition idtac; subst *)
    (*   end *)

    | [ S: rstepSilent ^* ?U _ |- _ ] => 
      (* Don't actually multiStep unless we know the state of the starting universe
       * meaning it is not some unknown hypothesis in the context...
       *)
      is_not_var U; eapply multiStepSilentInv in S; split_ors; split_ex; intuition idtac; subst

    | [ H: rstepSilent ?U _ |- _ ] => is_not_var U; invert H
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

  Hint Constructors RPingPongBase action_matches msg_eq.
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
  Hint Extern 1 (rstepSilent ^* _ _) =>
        progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1,
                        real_univ_sent2, real_univ_recd2, real_univ_done, mkrU; simpl).
  Hint Extern 1 (RPingPongBase (RealWorld.buildUniverse _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.

  Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ0.
  Hint Extern 2 (IdealWorld.lstep_universe _ _ _) => istep_univ1.
  Hint Extern 1 (IdealWorld.lstep_universe _ _ _) =>
      progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1,
                      ideal_univ_sent2, ideal_univ_recd2, ideal_univ_done, mkiU; simpl).
  Hint Extern 1 (IdealWorld.lstep_user _ (_, IdealWorld.Bind _ _, _) _) => eapply IdealWorld.LStepBindRecur.
  Hint Extern 1 (istepSilent ^* _ _) => ideal_silent_steps || apply TrcRefl.

  Hint Extern 1 (List.In _ _) => progress simpl.

  (* Hint Extern 1 (RealWorld.encryptMessage _ _ _ = _) => unfold RealWorld.encryptMessage; simpl. *)
  (* Hint Extern 1 (RealWorld.signMessage _ _ _ = _) => unfold RealWorld.signMessage; simpl. *)
  Hint Extern 1 (RealWorld.action_adversary_safe _ _ _ = _) => unfold RealWorld.action_adversary_safe; simplify.
  Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.

  Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2.
  Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2.
  Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
  Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.
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

  Hint Resolve encrypted_ciphers_ok_addnl_cipher.

  Lemma rpingbase_silent_simulates :
    simulates_silent_step (lameAdv tt) RPingPongBase.
  Proof.

    unfold simulates_silent_step.

    Import T.

    time (
        intros;
        invert H;
        try destruct U__r0; try destruct U__r; simpl in *; subst;
        churn; autorewrite with simpl_univ;
        [> eexists; split; swap 1 2; eauto 9 ..]
      ).

  Qed.

  Lemma rpingbase_loud_simulates :
    simulates_labeled_step (lameAdv tt) RPingPongBase.
  Proof.
    unfold simulates_labeled_step.

    Import T.

    time
      (intros;
       invert H;
       try destruct U__r0; try destruct U__r; simpl in *; subst;
       churn;
       autorewrite with simpl_univ;
       simpl;
       (do 3 eexists;
        repeat
          match goal with
          | [ |- _ /\ _ ] => split
          end; swap 3 4; swap 1 3; [ .. | admit (* action matches predicate *)];
        eauto; eauto 12)).

  Admitted.

  Section UniverseStep.
    Import RealWorld.

    Definition rewrite_messages {A} (usr : user_data A) (qmsgs : queued_messages) :=
      {| key_heap := usr.(key_heap)
       ; protocol := usr.(protocol)
       ; msg_heap := qmsgs
       ; c_heap   := usr.(c_heap)
      |}.

    Lemma invert_users :
      forall {A} (usrs__ra usrs__r : honest_users A) u_id u,
          usrs__r = clean_users (findUserKeys usrs__ra) usrs__ra
        -> usrs__ra $? u_id = Some u
        -> exists msgs u', usrs__r $? u_id = Some u'
                   /\ u = rewrite_messages u' msgs
                   /\ Forall (fun m => msg_filter (findUserKeys usrs__ra) m = false \/ List.In m u'.(msg_heap)) msgs.
    Proof.
      intros.
      subst; destruct u; simpl in *.
      repeat eexists.
      eapply clean_users_cleans_user; eauto.
      unfold rewrite_messages; simpl; reflexivity.
      rewrite Forall_forall; intros.
      cases (msg_filter (findUserKeys usrs__ra) x); auto.
      right; simpl.
      unfold clean_messages; rewrite filter_In; auto.
    Qed.

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

  Hint Resolve
       RealWorld.findUserKeys_foldfn_proper
       RealWorld.findUserKeys_foldfn_transpose
       RealWorld.findUserKeys_foldfn_proper_Equal
       RealWorld.findUserKeys_foldfn_transpose_Equal.

  Ltac solve_adv_safe :=
    repeat
      match goal with
      | [ |- RealWorld.action_adversary_safe _ _ _] => unfold RealWorld.action_adversary_safe
      | [ |- RealWorld.msg_pattern_safe _ _ ] => econstructor
      | [ |- RealWorld.honest_key _ _ ] => econstructor
      | [ |- RealWorld.honest_keyb _ _ = true ] => rewrite <- RealWorld.honest_key_honest_keyb
      | [ H : RealWorld.findUserKeys ?usrs = _ |- RealWorld.findUserKeys ?usrs $? _ = Some _ ] => rewrite H
      | [ H : _ = clean_users ?honestk ?usrs |- context [ clean_users ?honestk ?usrs ] ] => rewrite <- H
      | [ |- RealWorld.msg_contains_only_honest_public_keys _ _ ] => econstructor
      | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
      | [ |- RealWorld.msgCipherOk _ _ _ ] => unfold RealWorld.msgCipherOk
      | [ |- RealWorld.msg_honestly_signed _ _ = true] => unfold RealWorld.msg_honestly_signed
      | [ |- _ /\ _ ] => split
      | [ H : _ = clean_ciphers ?honk ?cs |- ?cs $? ?cid = Some ?c ] =>
        assert (clean_ciphers honk cs $? cid = Some c) by (rewrite <- H; clean_map_lookups; trivial); clear H
      | [ H : clean_ciphers _ ?cs $? ?cid = Some ?c |- ?cs $? ?cid = Some ?c ] =>
        rewrite <- find_mapsto_iff in H; rewrite clean_ciphers_mapsto_iff in H; split_ands;
        rewrite <- find_mapsto_iff; assumption
      end.

  Ltac users_inversion :=
    match goal with
    | [ H : ?usrs $? _ = Some ?u
      , E : _ = clean_users _ _
        |- _ ] =>
      generalize (invert_users _ E H); intros
    end; split_ex; split_ands; subst; simpl in *.

  Ltac solve_uok :=
    try match goal with
        | [ |- universe_ok (RealWorld.buildUniverseAdv _ _ _ _ ) ] => solve [ eapply universe_ok_adv_step; eauto ]
        end;
    users_inversion; churn; repeat equality1;
    unfold universe_ok in *;
    simpl;
    autorewrite with find_user_keys;
    try assumption; simpl in *;
    repeat
      match goal with
      | [ H : Forall _ (existT _ _ _ :: _) |- encrypted_ciphers_ok _ _ ] =>
        invert H; split_ors; try contradiction
      | [ H : RealWorld.msg_accepted_by_pattern (RealWorld.Signed _) _ |- _ ] => invert H; simpl in *
      | [ H : RealWorld.honest_keyb ?findUsers _ = false |- _ ] => unfold RealWorld.honest_keyb in H
      | [ H : ?cusrs = clean_users (RealWorld.findUserKeys ?usrs) ?usrs |- _ ] =>
        assert (RealWorld.findUserKeys usrs = RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys usrs) usrs))
          as UKS by (symmetry; eapply clean_users_no_change_findUserKeys);
        rewrite <- H in UKS;
        clear H
      | [ M : match RealWorld.findUserKeys ?usrs $? _ with _ => _ end = _
        , H : RealWorld.findUserKeys ?usrs = _ |- _ ] => rewrite H in M; clear H; simpl in M; try discriminate
      | [ H : RealWorld.Signature _ _ _ = RealWorld.Signature _ _ _ |- _ ] => invert H
      | [ |- encrypted_ciphers_ok _ _ ] => econstructor
      | [ |- encrypted_cipher_ok _ _ _ ] => econstructor
      | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
      | [ |- forall k, RealWorld.findKeys _ $? _ = Some true -> False ] => intros
      | [ H : RealWorld.findKeys _ $? _ = Some true |- False ] => progress simpl in H; invert H
      | [ |- RealWorld.findUserKeys _ $? _ = Some true ] => eapply RealWorld.findUserKeys_has_private_key_of_user
      end.

  Lemma rpingbase_univere_ok :
    simulates_universe_ok RPingPongBase.
  Proof.
    unfold simulates_universe_ok; intros.

    Import T.

    time (
        inversion H; clear H; churn; solve_uok; eauto
      ).

  Qed.

  Lemma rpingbase_labeled_simulates_safe :
    simulates_labeled_step_safe RPingPongBase.
  Proof.
    unfold simulates_labeled_step_safe.
    intros.

    Import T.

    assert (RealWorld.findUserKeys U__r.(RealWorld.users) =
            RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.users)))
      by (symmetry; eapply clean_users_no_change_findUserKeys).
    remember (RealWorld.findUserKeys U__r.(RealWorld.users)) as honestk.

    time(
        inversion H; clear H;
        churn;
        [> users_inversion; churn; repeat equality1; solve_adv_safe; eauto .. ]
      ).

  Qed.


  (* Timings:
   *
   * 20190715 (laptop run: update to simulation statement)
   * Tactic call ran for 1003.739 secs (1003.249u,0.435s) (success)
   * Tactic call ran for 67.14 secs (67.13u,0.008s) (success)
   * Tactic call ran for 51.881 secs (51.877u,0.004s) (success)
   * Tactic call ran for 38.373 secs (38.364u,0.008s) (success)
   *
   * 20190628 (laptop run: inversion lemmas)
   * Tactic call ran for 870.78 secs (870.427u,0.272s) (success)
   * Tactic call ran for 64.791 secs (64.786u,0.004s) (success)
   * Tactic call ran for 38.868 secs (38.868u,0.s) (success)
   *
   * 20190624 (laptop run: block inversion of rstepSilent if don't know start univ -- saving restepping through protocol for adversary)
   * Tactic call ran for 1272.565 secs (1271.919u,0.596s) (success)
   * Tactic call ran for 314.031 secs (314.027u,0.004s) (success)
   * Tactic call ran for 283.061 secs (282.885u,0.148s) (success)
   * --------------------------------------------------------------
   * (no date, desktop run (laptop more like 1700): starting point after refactor)
   * Tactic call ran for 1468.475 secs (1467.238u,1.061s) (success)
   * Tactic call ran for 257.673 secs (257.516u,0.091s) (success)
   * --------------------------------------------------------------
   *)

  Hint Resolve
       rpingbase_silent_simulates
       rpingbase_loud_simulates
       rpingbase_univere_ok
       rpingbase_labeled_simulates_safe.

  Lemma univ_ok_start :
    forall adv,
      lameAdv tt adv
      -> universe_ok (real_univ_start $0 [] [] adv).
  Proof.
    unfold real_univ_start; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start :
    forall adv U__r honestk,
        U__r = real_univ_start $0 [] [] adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv_message_queue_ok honestk adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      -> adv_universe_ok (real_univ_start $0 [] [] adv).
  Proof.
    unfold real_univ_start, adv_universe_ok, adv_no_honest_keys;
      simpl; intuition (subst; eauto).

    - unfold keys_good, KEYS, KID1, KID2, KEY1, KEY2; intros.
      cases (0 ==n k_id); cases (1 ==n k_id); subst; clean_map_lookups; eauto.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

  Qed.

  Hint Resolve
       univ_ok_start
       adv_univ_ok_start.

  Theorem base_pingpong_refines_ideal_pingpong :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv_message_queue_ok honestk adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      (* real_univ_start $0 [] [] adv <| ideal_univ_start / lameAdv tt. *)
      -> refines (lameAdv tt) U__r ideal_univ_start.
  Proof.
    exists RPingPongBase; unfold simulates.
    intuition (subst; eauto).
  Qed.

End FeebleSimulates.
