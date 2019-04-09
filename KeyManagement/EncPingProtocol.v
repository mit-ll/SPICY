From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Simulation MapLtac.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.
Definition B : user_id   := 1.
Definition ADV : user_id := 2.

Transparent A B ADV.

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

  Definition KEY1  := MkCryptoKey KID1 Signing (AsymKey true).
  Definition KEY2  := MkCryptoKey KID2 Signing (AsymKey true).
  Definition KEY__pub1 := MkCryptoKey KID1 Signing (AsymKey false).
  Definition KEY__pub2 := MkCryptoKey KID2 Signing (AsymKey false).
  Definition KEYS  := $0 $+ (KID1, KEY1) $+ (KID2, KEY2).

  Definition A__keys := $0 $+ (KID1, KEY1) $+ (KID2, KEY__pub2).
  Definition B__keys := $0 $+ (KID1, KEY__pub1) $+ (KID2, KEY2).
End RealProtocolParams.

Module Type enemy.
  Import RealWorld.
  Parameter code : user_cmd bool.
End enemy.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (msgs1 msgs2 : queued_messages) (cs : ciphers) (p__a p__b : user_cmd bool) (adversaries : adversaries unit) : universe bool unit :=
    {| users            := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs1 |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b ; msg_heap := msgs2 |})
     ; adversary        := adversaries
     ; all_ciphers      := cs
     |}.

  Definition real_univ_start cs :=
    mkrU [] [] cs
         ( n  <- Gen
         ; m  <- Sign KEY1 (Plaintext n)
         ; _  <- Send B m
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KEY__pub1 m
         ; m' <- match unSig m with
                | Some p => Sign KEY2 p
                | _      => Sign KEY2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent1 n cs cid1 :=
    mkrU [] [Exm (Signature (Plaintext n) cid1)]
         (cs $+ (cid1, SigCipher cid1 KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)
         ( m  <- @Recv Nat (Signed KID1)
         ; v  <- Verify KEY__pub1 m
         ; m' <- match unSig m with
                | Some p => Sign KEY2 p
                | _      => Sign KEY2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_recd1 n cs cid1 :=
    mkrU [] []
         (cs $+ (cid1, SigCipher cid1 KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( m  <- Return (Signature (Plaintext n) cid1)
         ; v  <- Verify KEY__pub1 m
         ; m' <- match unSig m with
                | Some p => Sign KEY2 p
                | _      => Sign KEY2 (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent2 n cs cid1 cid2 :=
    mkrU [Exm (Signature (Plaintext n) cid2)] []
         (cs $+ (cid1, SigCipher cid1 KID1 (Plaintext n)) $+ (cid2, SigCipher cid2 KID2 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv Nat (Signed KID2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_recd2 n cs cid1 cid2 :=
    mkrU [] [] (cs $+ (cid1, SigCipher cid1 KID1 (Plaintext n)) $+ (cid2, SigCipher cid2 KID2 (Plaintext n)))
         ( m' <- Return (Signature (Plaintext n) cid2)
         ; Return match unSig m' with
                  | Some (Plaintext n') => if n ==n n' then true else false (* also do verify? *)
                  | _       => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_done cs :=
    mkrU [] [] cs (Return true) (Return true).

  Inductive RPingPongBase: RealWorld.universe bool unit -> IdealWorld.universe bool -> Prop :=
  | Start : forall U__r cs,
        rstepSilent^* (real_univ_start cs $0) U__r
      -> RPingPongBase U__r ideal_univ_start

  | Sent1 : forall U__r cs cid1 n,
        rstepSilent^* (real_univ_sent1 n cs cid1 $0) U__r
      -> RPingPongBase U__r (ideal_univ_sent1 n)

  | Recd1 : forall U__r cs cid1 n,
        rstepSilent^* (real_univ_recd1 n cs cid1 $0) U__r
      -> RPingPongBase U__r (ideal_univ_recd1 n)

  | Sent2 : forall U__r cs cid1 cid2 n,
        rstepSilent^* (real_univ_sent2 n cs cid1 cid2 $0) U__r
      -> RPingPongBase U__r (ideal_univ_sent2 n)

  | Recd2 : forall U__r cs cid1 cid2 n,
        rstepSilent^* (real_univ_recd2 n cs cid1 cid2 $0) U__r
      -> RPingPongBase U__r (ideal_univ_recd2 n)

  | Done : forall cs n,
      RPingPongBase (real_univ_done cs $0) (ideal_univ_done n)
  .

End RealProtocol.

Section RealWorldLemmas.
  Import RealWorld.


  Lemma multiStepSilentInv :
    forall {A B} (U__r U__r': universe A B),
        rstepSilent ^* U__r U__r'
      -> U__r.(adversary) = $0
      -> U__r = U__r'
      \/ exists usrs adv cs u_id userData ks cmd qmsgs,
            rstepSilent ^* (buildUniverse usrs adv cs u_id {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |}) U__r'
          /\ users U__r $? u_id = Some userData
          /\ step_user u_id Silent (RealWorld.build_data_step U__r userData) (usrs, adv, cs, ks, qmsgs, cmd).
  Proof.
    intros.
    invert H.
    - left; trivial.
    - right. invert H1.
      + do 9 eexists; intuition; eauto.
      + rewrite H0 in H; invert H.
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
    forall {A B} (U__r : universe A B) (usrs : honest_users A) uid__a uid__b ud__a ud__b uid ud (adv : adversaries B) cs,
        uid__a <> uid__b
      -> uid = uid__a
      -> buildUniverse (usrs $+ (uid__a,ud__a) $+ (uid__b,ud__b)) adv cs uid ud
        = {| users       := usrs $+ (uid,ud) $+ (uid__b,ud__b)
           ; adversary   := adv
           ; all_ciphers := cs
          |}.
  Proof.
    intros. unfold buildUniverse; simpl.
    f_equal; subst.
    rewrite add_univ_simpl2 by auto; trivial.
  Qed.

  Lemma simplify_build_univ2 :
    forall {A B} (U__r : universe A B) (usrs : honest_users A) uid__a uid__b ud__a ud__b uid ud (adv : adversaries B) cs,
        uid__a <> uid__b
      -> uid = uid__b
      -> buildUniverse (usrs $+ (uid__a,ud__a) $+ (uid__b,ud__b)) adv cs uid ud
        = {| users       := usrs $+ (uid__a,ud__a) $+ (uid,ud)
           ; adversary   := adv
           ; all_ciphers := cs
          |}.
  Proof.
    intros. unfold buildUniverse; simpl.
    f_equal.
    rewrite add_univ_simpl1 by auto; trivial.
  Qed.

End RealWorldLemmas.

Module SimulationAutomation.

  Hint Constructors RealWorld.msg_accepted_by_pattern.

  Ltac churn1 :=
    match goal with
    | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition idtac

    | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction
    | [ H : _  $? _ = Some _ |- _ ] => progress (simpl in H)

    | [ H : add _ _ _ $? _ = Some ?UD |- _ ] =>
      match type of UD with
      | RealWorld.user_data bool => apply lookup_some_implies_in in H
      | _ => apply lookup_split in H; intuition idtac
      end

    | [ H : RealWorld.users _ $? _ = Some _ |- _ ] => progress (simpl in H)

    | [ H : _ = RealWorld.mkUserData _ _ _ |- _ ] => invert H
    | [ H : Some _ = Some _ |- _ ] => invert H
    | [ H : (_ :: _) = _ |- _ ] => invert H
    | [ H : _ = (_ :: _) |- _ ] => invert H
    | [ H : (_,_) = (_,_) |- _ ] => invert H

    | [ H: RealWorld.SigCipher _ _ _ = RealWorld.SigCipher _ _ _ |- _ ] => invert H
    | [ H: RealWorld.SigEncCipher _ _ _ _ = RealWorld.SigEncCipher _ _ _ _ |- _ ] => invert H
    | [ H: RealWorld.MkCryptoKey _ _ _ = _ |- _ ] => invert H
    | [ H: RealWorld.AsymKey _ = _ |- _ ] => invert H
    (* | [ H: RealWorld.AsymKey _ _ = _ |- _ ] => invert H *)

    | [ H: exists _, _ |- _ ] => invert H
    | [ H: _ /\ _ |- _ ] => invert H

    | [ H : RealWorld.keyId _ = _ |- _] => invert H

    (* NEW | [H : RealWorld.users_msg_buffer _ $? _ = _ |- _ ] => progress (simpl in H) *)

    (* | [ H: RealWorld.msg_accepted_by_pattern_compute _ _ _ = false |- _ ] => *)
    (*   simpl in H; *)
    (*   rewrite add_eq_o in H by auto; *)
    (*   try discriminate *)

    | [ H : ~ RealWorld.msg_accepted_by_pattern ?cs ?pat ?msg |- _ ] =>
      assert ( RealWorld.msg_accepted_by_pattern cs pat msg ) by eauto; contradiction

    | [ H: RealWorld.signMessage _ _ _ = _ |- _ ] => unfold RealWorld.signMessage; simpl in H
    | [ H: RealWorld.encryptMessage _ _ _ _ = _ |- _ ] => unfold RealWorld.encryptMessage; simpl in H

    (* Only take a user step if we have chosen a user *)
    | [ H: RealWorld.step_user A _ _ _ |- _ ] => invert H
    | [ H: RealWorld.step_user B _ _ _ |- _ ] => invert H

    | [ H: rstepSilent _ _ |- _ ] => invert H
    | [ H: RealWorld.step_universe _ _ _ |- _ ] => invert H

    | [ H :rstepSilent ^* (RealWorld.buildUniverse _ _ _ _ _) _ |- _] =>
      (rewrite simplify_build_univ1 in H by auto) || (rewrite simplify_build_univ2 in H by auto)
    | [ S: rstepSilent ^* ?U _ |- _ ] => 
      (* Don't actually multiStep unless we know the state of the starting universe
       * meaning it is not some unknown hypothesis in the context...
       *)
      match goal with
      | [U1 : U |- _] => fail 1
      | [ |- _ ] =>
        (* invert S *)
        (* eapply multiStepSilentInv in S; intuition; repeat match goal with [ H : exists _, _ |- _] => destruct H end; intuition; subst *)
        eapply multiStepSilentInv in S; intuition idtac; repeat match goal with [ H : exists _, _ |- _] => destruct H end; intuition idtac; subst
      end

    end.

  (* Ltac notHyp P := *)
  (*   match goal with *)
  (*   | [ _ : P |- _ ] => fail 1 *)
  (*   | _ => idtac "notHyp" *)
  (*   end. *)

  Ltac churn := repeat churn1.

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

  Hint Extern 1 (RealWorld.encryptMessage _ _ _ = _) => unfold RealWorld.encryptMessage; simpl.
  Hint Extern 1 (RealWorld.signMessage _ _ _ = _) => unfold RealWorld.signMessage; simpl.
  Hint Extern 1 (RealWorld.action_adversary_safe _ _ = _) => unfold RealWorld.action_adversary_safe; simplify.
  Hint Extern 1 (IdealWorld.msg_permissions_valid _ _) => progress simpl.

  Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KEY__pub1, KEY__pub2, KID1, KID2.
  Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KEY__pub1, KEY__pub2, KID1, KID2.
  Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
  Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.
  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl.
  Hint Extern 1 (add _ _ _ = _) => m_equal.
  Hint Extern 1 (find _ _ = _) => m_equal.
  Hint Extern 1 (_ \in _) => sets.

End SimulationAutomation.

Import SimulationAutomation.

Section FeebleSimulates.

  Ltac simplUniv :=
    repeat match goal with
           | [ |- context[ _ $+ (?A,_) $+ (?A,_) ] ] => rewrite add_univ_simpl1 by trivial
           | [ |- context[ _ $+ (?A,_) $+ (?B,_) $+ (?A,_) ] ] => rewrite add_univ_simpl2 by auto
           | [ |- context[ _ $+ (?A,_) $+ (?A,_) $+ (?B,_) ] ] => rewrite add_univ_simpl3 by auto
           end.

  Lemma rpingbase_silent_simulates :
    forall U__r U__i,
      RPingPongBase U__r U__i
      -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
          /\ RPingPongBase U__r' U__i'.
  Proof.

    time (
        intros;
        invert H;
        churn; simplUniv;
        [> eexists; constructor; swap 1 2 ; eauto 9 .. ]
      ).

    (* Tactic call ran for 2481.944 secs (2480.162u,1.672s) (success) *)
    (* No more subgoals. *)
 
    (* Tactic call ran for 494.024 secs (493.416u,0.596s) (success) *)

    (* time ( *)
    (*     intros; *)
    (*     invert H; *)
    (*     churn; simplUniv; *)
    (*     [> eexists; constructor; swap 1 2 .. ]; *)
    (*     eauto 9). *)

    (* Tactic call ran for 2579.235 secs (2577.438u,1.502s) (success) *)
    (* No more subgoals. *)

  Qed.



  Lemma rpingbase_loud_simulates : 
    forall U__r U__i,
      RPingPongBase U__r U__i
      -> forall a1 U__r',
        RealWorld.step_universe U__r (Action a1) U__r'
        -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ RPingPongBase U__r' U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.adversary)) a1 = true.
  Proof.


    time
      (intros;
       invert H;
       churn;
       unfold RealWorld.buildUniverse;
       simpl; simplUniv;
       (do 3 eexists;
        propositional; swap 3 4; swap 1 3;
        [ .. | admit (* action matches predicate *) ]; eauto; eauto 12)).

  Admitted.

  Theorem base_pingpong_refines_ideal_pingpong :
    real_univ_start $0 $0 <| ideal_univ_start.
  Proof.
    exists RPingPongBase.
    firstorder; eauto using rpingbase_silent_simulates, rpingbase_loud_simulates.
  Qed.

End FeebleSimulates. 
