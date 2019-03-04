From Coq Require Import
     List
     Logic.ProofIrrelevance.

Require Import MyPrelude.

Require Import Users Common Simulation MapLtac.

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

  Definition KEY1  := MkCryptoKey KID1 Signing.
  Definition KEY2  := MkCryptoKey KID2 Signing.
  Definition KEY__A  := AsymKey KEY1 true.
  Definition KEY__B  := AsymKey KEY2 true.
  Definition KEYS  := $0 $+ (KID1, AsymKey KEY1 true) $+ (KID2, AsymKey KEY2 true).

  Definition A__keys := $0 $+ (KID1, AsymKey KEY1 true)  $+ (KID2, AsymKey KEY2 false).
  Definition B__keys := $0 $+ (KID1, AsymKey KEY1 false) $+ (KID2, AsymKey KEY2 true).
End RealProtocolParams.

Module Type enemy.
  Import RealWorld.
  Parameter code : user_cmd bool.
End enemy.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (usr_msgs : queued_messages) (cs : ciphers) (p__a p__b : user_cmd bool) (adversaries : user_list (user_data unit)) : universe bool :=
    {| users            := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b |})
     ; adversary        := adversaries
     ; univ_data        := {| users_msg_buffer := usr_msgs
                            ; all_keys         := KEYS
                            ; all_ciphers      := cs
                            |}
     |}.

  Definition real_univ_start cs :=
    mkrU $0 cs
         ( n  <- Gen
         ; m  <- Sign KEY__A (Plaintext n)
         ; _  <- Send B m
         ; m' <- @Recv (Pair Nat CipherId) (Signed KID2 Accept)
         ; Return match unPair m' with
                  | Some (Plaintext n', _) => if n ==n n' then true else false (* also do verify? *)
                  | _ => false
                  end)

         ( m  <- @Recv (Pair Nat CipherId) (Signed KID1 Accept)
         ; v  <- Verify (AsymKey KEY1 false) m
         ; m' <- match unPair m with
                | Some (p,_) => Sign KEY__B p
                | Nothing    => Sign KEY__B (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent1 n cs cid1 :=
    mkrU ($0 $+ (B, [Exm (Signature (Plaintext n) cid1)]))
         (cs $+ (cid1, Cipher cid1 KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv (Pair Nat CipherId) (Signed KID2 Accept)
         ; Return match unPair m' with
                  | Some (Plaintext n', _) => if n ==n n' then true else false (* also do verify? *)
                  | _ => false
                  end)

         ( m  <- @Recv (Pair Nat CipherId) (Signed KID1 Accept)
         ; v  <- Verify (AsymKey KEY1 false) m
         ; m' <- match unPair m with
                | Some (p,_) => Sign KEY__B p
                | Nothing    => Sign KEY__B (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_recd1 n cs cid1 :=
    mkrU $0
         (cs $+ (cid1, Cipher cid1 KID1 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv (Pair Nat CipherId) (Signed KID2 Accept)
         ; Return match unPair m' with
                  | Some (Plaintext n', _) => if n ==n n' then true else false (* also do verify? *)
                  | _ => false
                  end)

         ( m  <- Return (Signature (Plaintext n) cid1)
         ; v  <- Verify (AsymKey KEY1 false) m
         ; m' <- match unPair m with
                | Some (p,_) => Sign KEY__B p
                | Nothing    => Sign KEY__B (Plaintext 1)
                end
         ; _  <- Send A m'
         ; Return v).

  Definition real_univ_sent2 n cid1 cid2 :=
    mkrU ($0 $+ (A, [Exm (Signature (Plaintext n) cid2)]))
         ($0 $+ (cid1, Cipher cid1 KID1 (Plaintext n)) $+ (cid2, Cipher cid2 KID2 (Plaintext n)))
         ( _  <- Return tt
         ; m' <- @Recv (Pair Nat CipherId) (Signed KID2 Accept)
         ; Return match unPair m' with
                  | Some (Plaintext n', _) => if n ==n n' then true else false (* also do verify? *)
                  | _ => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_recd2 n cid1 cid2 :=
    mkrU $0 ($0 $+ (cid1, Cipher cid1 KID1 (Plaintext n)) $+ (cid2, Cipher cid2 KID2 (Plaintext n)))
         ( m' <- Return (Signature (Plaintext n) cid2)
         ; Return match unPair m' with
                  | Some (Plaintext n', _) => if n ==n n' then true else false (* also do verify? *)
                  | _ => false
                  end)

         ( _  <- Return tt ; Return true).

  Definition real_univ_done cs :=
    mkrU $0 cs (Return true) (Return true).

  Inductive RPingPongBase: RealWorld.universe bool -> IdealWorld.universe bool -> Prop :=
  | Start : forall U__r cs,
        rstepSilent^* (real_univ_start cs $0) U__r
      -> RPingPongBase U__r ideal_univ_start

  | Sent1 : forall U__r cs cid1 n,
        rstepSilent^* (real_univ_sent1 n cs cid1 $0) U__r
      -> RPingPongBase U__r (ideal_univ_sent1 n)

  | Recd1 : forall U__r cs cid1 n,
        rstepSilent^* (real_univ_recd1 n cs cid1 $0) U__r
      -> RPingPongBase U__r (ideal_univ_recd1 n)

  | Sent2 : forall U__r cid1 cid2 n,
        rstepSilent^* (real_univ_sent2 n cid1 cid2 $0) U__r
      -> RPingPongBase U__r (ideal_univ_sent2 n)

  | Recd2 : forall U__r cid1 cid2 n,
        rstepSilent^* (real_univ_recd2 n cid1 cid2 $0) U__r
      -> RPingPongBase U__r (ideal_univ_recd2 n)

  | Done : forall cs n,
      RPingPongBase (real_univ_done cs $0) (ideal_univ_done n)
  .

End RealProtocol.

Module SimulationAutomation.

  Ltac churn1 :=
    match goal with
    | [ H : List.In _ _ |- _ ] => progress (simpl in H); intuition

    | [ H : _ $? _ = Some _ |- _ ] => progress (simpl in H)

    (* | [ H : $0 $? _ = Some _ |- _ ] => apply lookup_empty_not_Some in H; contradiction *)
    | [ H : $0 $? _ = Some _ |- _ ] => apply find_mapsto_iff in H; apply empty_mapsto_iff in H; contradiction

    (* | [ H : _ $? _ = Some _ |- _ ] => apply lookup_split in H; intuition (* propositional *); subst *)
    | [ H : _ $? _ = Some _ |- _ ] => apply lookup_some_implies_in in H
    (* | [ H : (_ $- _) $? _ = Some _ |- _ ] => rewrite addRemoveKey in H by auto *)
    | [ H : Some _ = Some _ |- _ ] => invert H

    | [ H : (_ :: _) = _ |- _ ] => invert H
    | [ H : (_,_) = (_,_) |- _ ] => invert H

    (* | [ H : updF _ _ _ = _ |- _ ] => unfold updF; simpl in H *)

    | [ H: RealWorld.Cipher _ _ _ = RealWorld.Cipher _ _ _ |- _ ] => invert H
    | [ H: RealWorld.SymKey _ = _ |- _ ] => invert H
    | [ H: RealWorld.AsymKey _ _ = _ |- _ ] => invert H

    | [ H: exists _, _ |- _ ] => invert H
    | [ H: _ /\ _ |- _ ] => invert H

    | [ H : RealWorld.keyId _ = _ |- _] => invert H

    | [H : RealWorld.users_msg_buffer _ $? _ = _ |- _ ] => progress (simpl in H)

    (* | [ H: RealWorld.msg_accepted_by_pattern _ _ _ = _ |- _ ] => *)
    (*   simpl in H; *)
    (*   rewrite lookup_add_eq in H by eauto; *)
    (*   try discriminate *)

    | [ H: RealWorld.msg_accepted_by_pattern _ _ _ = _ |- _ ] =>
      simpl in H;
      rewrite add_eq_o in H by auto;
      try discriminate

    (* | [ H : RealWorld.msg_spoofable _ _ _ = _ |- _] => *)
    (*   unfold RealWorld.msg_spoofable in H; *)
    (*   rewrite lookup_add_eq in H by eauto; *)
    (*   simplify; *)
    (*   discriminate *)

    | [ H: RealWorld.signMessage _ _ _ = _ |- _ ] => unfold RealWorld.encryptMessage; simpl in H
    | [ H: RealWorld.encryptMessage _ _ _ = _ |- _ ] => unfold RealWorld.encryptMessage; simpl in H

    (* Only take a user step if we have chosen a user *)
    | [ H: RealWorld.lstep_user A _ _ _ |- _ ] => invert H
    | [ H: RealWorld.lstep_user B _ _ _ |- _ ] => invert H

    | [ H: rstepSilent _ _ |- _ ] => invert H
    | [ H: RealWorld.lstep_universe _ _ _ |- _ ] => invert H

    | [ S: rstepSilent ^* ?U _ |- _ ] => 
      (* Don't actually multiStep unless we know the state of the starting universe
       * meaning it is not some unknown hypothesis in the context...
       *)
      match goal with
      | [U1 : U |- _] => fail 1
      | [ |- _ ] => invert S
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
      unfold eq_key_elt, Raw.PX.eqke; constructor; [intuition | ..].

  Ltac user0 := usr_first; left.
  Ltac user1 := usr_first; right; left.

  Ltac istep_univ pick :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..];
    unfold updateUserList; (try eapply @eq_refl); (try f_equal); simpl.
  Ltac rstep_univ pick :=
    eapply  RealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..]; (try eapply @eq_refl); simpl.

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
      eapply RealWorld.LStepBindProceed
    || eapply RealWorld.LGen
    || eapply RealWorld.LStepRecvDrop
    || eapply RealWorld.LStepEncrypt
    || eapply RealWorld.LStepDecrypt
    || eapply RealWorld.LStepSign
    || eapply RealWorld.LStepVerify
  .

  Ltac isilent_step_univ pick :=
    eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..]; (try simple eapply @eq_refl);
      ((eapply IdealWorld.LStepBindRecur; i_single_silent_step) || i_single_silent_step).
  Ltac rsilent_step_univ pick :=
    eapply  RealWorld.LStepUser'; simpl; swap 2 3; [ pick | ..]; (try simple eapply @eq_refl);
      ((eapply RealWorld.LStepBindRecur; r_single_silent_step) || r_single_silent_step).

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

  Hint Extern 0 (rstepSilent ^* _ _) => solve [eapply TrcRefl || eapply TrcRefl'; smash_universe].
  Hint Extern 1 (rstepSilent ^* _ _) => real_silent_step0.
  Hint Extern 1 (rstepSilent ^* _ _) => real_silent_step1.
  Hint Extern 1 (rstepSilent ^* _ _) =>
        progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1,
                        real_univ_sent2, real_univ_recd2, real_univ_done, mkrU; simpl).
  Hint Extern 1 (RPingPongBase (RealWorld.updateUniverse _ _ _ _ _ _) _) => unfold RealWorld.updateUniverse; simpl.

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

  Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KEY__A, KEY__B, KID1, KID2.
  Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KEY__A, KEY__B, KID1, KID2.
  Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
  Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.
  Hint Extern 1 (_ = RealWorld.addUserKeys _ _) => unfold RealWorld.addUserKeys, map; simpl.
  Hint Extern 1 (add _ _ _ = _) => m_equal.
  Hint Extern 1 (find _ _ = _) => m_equal.
  Hint Extern 1 (_ \in _) => sets.

End SimulationAutomation.

Import SimulationAutomation.

Section FeebleSimulates.

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
        churn;
        [> eexists; constructor; swap 1 2 .. ];
        eauto 9).
  Qed.


  Lemma rpingbase_loud_simulates : 
    forall U__r U__i,
      RPingPongBase U__r U__i
      -> forall a1 U__r',
        RealWorld.lstep_universe U__r (Action a1) U__r'
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
       unfold RealWorld.updateUniverse, RealWorld.setGlobalUserMsgs, RealWorld.addGlobalUserMsg,
              RealWorld.multiMapAdd, updateUserList;
       simpl;
       (do 3 eexists;
        autorewrite with core;
        propositional; swap 3 4; swap 1 3;
        [ .. | admit (* action matches predicate *) ]; eauto; eauto 12)).

  Admitted.

  Theorem base_pingpong_refines_ideal_pingpong :
    real_univ_start $0 [] <| ideal_univ_start.
  Proof.
    exists RPingPongBase.
    firstorder; eauto using rpingbase_silent_simulates, rpingbase_loud_simulates.
  Qed.

End FeebleSimulates. 

Section SingleAdversarySimulates.

  (* If we have a simulation proof, we know that:
   *   1) No receives could have accepted spoofable messages
   *   2) Sends we either of un-spoofable, or were 'public' and are safely ignored
   *
   * This should mean we can write some lemmas that say we can:
   *   safely ignore all adversary messages (wipe them from the universe) -- Adam's suggestion, I am not exactly sure how...
   *   or, prove an appended simulation relation, but I am not sure how to generically express this
   *)

  Definition add_adversary {A} (U__r : RealWorld.universe A) (advcode : RealWorld.user_cmd A) :=
    RealWorld.addUniverseUsers U__r [(ADV, {| RealWorld.key_heap := $0 ; RealWorld.protocol := advcode |})].

  Definition strip_adversary {A} (U__r : RealWorld.universe A) : RealWorld.universe A :=
    {|
      RealWorld.users            := removelast U__r.(RealWorld.users)
    ; RealWorld.users_msg_buffer := U__r.(RealWorld.users_msg_buffer)
    ; RealWorld.all_keys         := U__r.(RealWorld.all_keys)
    ; RealWorld.all_ciphers      := U__r.(RealWorld.all_ciphers)
    ; RealWorld.adversary        := U__r.(RealWorld.adversary)
    |}.


  Lemma step_clean_or_adversary :
    forall {A} (U__r U__ra U__ra' : RealWorld.universe A) advcode lbl u_id u,
      In (u_id,u) U__r.(RealWorld.users)
      -> u_id <> ADV
      -> U__ra = add_adversary U__r advcode
      -> RealWorld.lstep_universe U__ra lbl U__ra'
      -> forall stepUdata uks advk cs ks qmsgs (cmd' : RealWorld.user_cmd A),
          (* Legit step *)
          ( forall stepUid,
              In (stepUid,stepUdata) U__r.(RealWorld.users)
            /\ RealWorld.lstep_user
                stepUid lbl
                (RealWorld.universe_data_step U__r stepUdata)
                (advk, cs, ks, qmsgs, uks, cmd')

          ) \/
          (* Adversary step *)
          ( In (ADV,stepUdata) U__ra.(RealWorld.users)
          /\ RealWorld.lstep_user
              ADV lbl
              (RealWorld.universe_data_step U__ra stepUdata)
              (advk, cs, ks, qmsgs, uks, cmd')

          )
  .
  Proof.
  Admitted.

  Lemma simulates_implies_noninterference:
    forall {A} (U__r U__ra : RealWorld.universe A) (U__i : IdealWorld.universe A),
      U__r <| U__i
      -> forall U__ra' u_id advcode a udata,
        U__ra = add_adversary U__r advcode
        -> RealWorld.lstep_universe U__ra (Action a) U__ra'
        -> RealWorld.lstep_user u_id (Action a) (RealWorld.universe_data_step U__ra udata) (RealWorld.universe_data_step U__ra' udata) 
        -> In (u_id,udata) U__ra.(RealWorld.users)
        -> u_id <> ADV.
  Proof.
  Admitted.


  (* Maybe this isn't provable.  One big question I have is whether we can actually
   * make the connection for some arbitrary relation.  The biggest problem (maybe)
   * being that adversaries will certainly affect the book keeping fields of the
   * simulation relation like: all_keys, all_ciphers, users_message_buffer.
   * There is no guarantee that the R in the original simulation relation doesn't say
   * something relevant about those fields.
   *)
  Theorem simulates_implies_sim_with_adv :
    forall {A} (U__r U__ra : RealWorld.universe A) (U__i : IdealWorld.universe A),
      U__r <| U__i
      -> forall advcode,
        U__ra = add_adversary U__r advcode
        -> U__ra <| U__i.
  Proof.

  Admitted.



  (* Can't really write this as is.  Perhaps derive some
   * kind of traces predicate like in MessagesAndRefinement?  Does that
   * get to the final theorem we want to prove?
   *)
  (* Definition final_answers_agree {A} (U__r : RealWorld.universe A) (U__i : IdealWorld.universe A) : *)
  (*   forall U__r' U__i', *)
  (*     RealWorld.lstep_universe^* U__r lbl U__r' *)
  (*     -> IdealWorld.lstep_universe^* U__i lbl' U__i' *)
  (*     ->  *)









  Definition still_simulates_with_adversary (U__i : IdealWorld.universe bool)  (U__r : RealWorld.universe bool) :=
    U__r <| U__i
    -> forall U__r' advcode,
      U__r' = RealWorld.addUniverseUsers U__r [(ADV, {| RealWorld.key_heap := $0 ; RealWorld.protocol := advcode |})]
      -> U__r' <| U__i.



    (* Idea:  We have a relation: R : Ureal -> Uideal and need R' : U'real -> Uideal  where U'real is augmented
     *        with the adversary.  One approach may be to find R'' : U'real -> Ureal and then compose the relations.
     *        Hrm.  Relations don't really compose...
     *  What components could go into this R''?
     *    1. rstepSilent^* -- could provide some support for dropping messages sent by the adversary
     *    2. some U'real -> Ureal which just peels off the adversary
     * 
     * I think the biggest remaining challenge is handling Sends from the adversary.  Should these be 'loud?'
     *
     *)

(* How do we augment the simulation relation from above to include an arbitrary adversary? *)

End SingleAdversarySimulates.