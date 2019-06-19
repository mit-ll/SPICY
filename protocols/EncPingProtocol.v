From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Module Foo <: EMPTY. End Foo.
Module Import SN := SetNotations(Foo).

Require Import Common Maps Keys Simulation MapLtac.

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

  Definition adv :=
    {| key_heap := $0
     ; protocol := Return tt
     ; msg_heap := []
     ; c_heap   := []
 |}.

  Inductive RPingPongBase: RealWorld.universe bool unit -> IdealWorld.universe bool -> Prop :=
  | Start : forall U__r cs mycs1 mycs2,
        rstepSilent^* (real_univ_start mycs1 mycs2 cs adv) U__r
      -> RPingPongBase U__r ideal_univ_start

  | Sent1 : forall U__r cs mycs1 mycs2 cid1 n,
        rstepSilent^* (real_univ_sent1 n cs mycs1 mycs2 cid1 adv) U__r
      -> RPingPongBase U__r (ideal_univ_sent1 n)

  | Recd1 : forall U__r cs mycs1 mycs2 cid1 n,
        rstepSilent^* (real_univ_recd1 n cs mycs1 mycs2 cid1 adv) U__r
      -> RPingPongBase U__r (ideal_univ_recd1 n)

  | Sent2 : forall U__r cs mycs1 mycs2 cid1 cid2 n,
        rstepSilent^* (real_univ_sent2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> RPingPongBase U__r (ideal_univ_sent2 n)

  | Recd2 : forall U__r cs mycs1 mycs2 cid1 cid2 n,
        rstepSilent^* (real_univ_recd2 n cs mycs1 mycs2 cid1 cid2 adv) U__r
      -> RPingPongBase U__r (ideal_univ_recd2 n)

  | Done : forall cs mycs1 mycs2 n,
      RPingPongBase (real_univ_done cs mycs1 mycs2 adv) (ideal_univ_done n)
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
    | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => apply inj_pair2 in H; subst

    | [ H: RealWorld.SigCipher _ _ = RealWorld.SigCipher _ _ |- _ ] => invert H
    | [ H: RealWorld.SigEncCipher _ _ _ = RealWorld.SigEncCipher _ _ _ |- _ ] => invert H
    | [ H: MkCryptoKey _ _ _ = _ |- _ ] => invert H
    (* | [ H: AsymKey _ = _ |- _ ] => invert H *)

    | [ H: exists _, _ |- _ ] => invert H
    | [ H: _ /\ _ |- _ ] => invert H

    | [ H : keyId _ = _ |- _] => invert H

    | [ H : ~ RealWorld.msg_accepted_by_pattern ?pat ?msg |- _ ] =>
      assert ( RealWorld.msg_accepted_by_pattern pat msg ) by eauto; contradiction

    (* Only take a user step if we have chosen a user *)
    | [ H: RealWorld.step_user _ (Some A) _ _ |- _ ] => invert H
    | [ H: RealWorld.step_user _ (Some B) _ _ |- _ ] => invert H
    | [ H : RealWorld.step_user _ None _ _ |- _ ] => progress simpl in H
    | [ H : RealWorld.step_user _ None (RealWorld.build_data_step _ adv) _ |- _ ] => unfold adv in H; invert H

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
        simpl in H; simpl;
        rewrite !RealWorld.findUserKeys_readd_user_same_keys_idempotent' in H by auto;
        rewrite !RealWorld.findUserKeys_readd_user_same_keys_idempotent' by auto
      | [ |- encrypted_ciphers_ok _ _ ] => econstructor
      | [ |- encrypted_cipher_ok _ _ _ ] => econstructor
      | [ |- RealWorld.msgCiphersSigned _ _ _ ] => econstructor
      | [ |- forall k, RealWorld.findKeys _ $? _ = Some true -> False ] => intros
      | [ H : RealWorld.findKeys _ $? _ = Some true |- False ] => progress simpl in H; invert H
      end.

  Lemma rpingbase_silent_simulates :
    simulates_silent_step RPingPongBase.
  Proof.

    unfold simulates_silent_step.
    (* intros; invert H. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)
    (* - churn; *)
    (*     [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto ..]. *)

    time (
        intros;
        invert H;
        churn;
        [> eexists; split; [|split]; swap 1 3; simplUniv; eauto 9; solve_universe_ok; eauto .. ]
    ).

  Qed.


  Lemma rpingbase_loud_simulates :
    simulates_labeled_step RPingPongBase.
  Proof.
    unfold simulates_labeled_step.

    time
      (intros;
       invert H;
       churn;
       unfold RealWorld.buildUniverse;
       simpl; simplUniv;
       (do 3 eexists;
        repeat
          match goal with
          | [ |- _ /\ _ ] => split
          end; swap 3 4; swap 4 5; swap 1 3; [ .. | admit (* action matches predicate *)];
        eauto; eauto 12)).

  Admitted.

  Lemma rpingbase_labeled_simulates_safe :
    simulates_labeled_step_safe RPingPongBase.
  Proof.
    unfold simulates_labeled_step_safe.
    intros; invert H; churn.
    unfold RealWorld.action_adversary_safe; simplify.
    churn.
    destruct U; simpl in *.
    unfold strip_adversary, real_univ_start, mkrU in *; simpl in *.
     invert H0. inve


  Theorem base_pingpong_refines_ideal_pingpong :
    real_univ_start $0 $0 <| ideal_univ_start.
  Proof.
    exists RPingPongBase.
    firstorder; eauto using rpingbase_silent_simulates, rpingbase_loud_simulates.
  Qed.

End FeebleSimulates. 
