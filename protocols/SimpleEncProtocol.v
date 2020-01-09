From Coq Require Import
     List.
     (* Logic.ProofIrrelevance. *)

(* Require Import MyPrelude. *)

(* Module Foo <: EMPTY. End Foo. *)
(* Module Import SN := SetNotations(Foo). *)

Require Import
        MyPrelude
        Maps
        Messages
        MessageEq
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ProtocolAutomation.

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

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := false; write := true |}). (* writer *)
  Definition PERMS__b := $0 $+ (CH__A2B, {| read := true; write := false |}). (* reader *)

  Definition mkiU (cv : channels) (p__a p__b : cmd nat): universe nat :=
    {| channel_vector := cv
     ; users := $0
         $+ (A,   {| perms    := PERMS__a ; protocol := p__a |})
         $+ (B,   {| perms    := PERMS__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU ($0 $+ (CH__A2B, []))
         (* user A *)
         ( n <- Gen
         ; _ <- Send (Content n) CH__A2B
         ; Return n)
         (* user B *)
         ( m <- @Recv Nat CH__A2B
         ; Return match extractContent m with
                  | None =>    0
                  | Some n' => n'
                  end).

  Definition ideal_univ_sent1 n :=
    mkiU ($0 $+ (CH__A2B, [existT _ _ (Content n)]))
         (* user A *)
         ( _ <- Return tt
         ; Return n)
         (* user B *)
         ( m <- @Recv Nat CH__A2B
         ; Return match extractContent m with
                  | None =>    0
                  | Some n' => n'
                  end).

  Definition ideal_univ_recd1 n :=
    mkiU ($0 $+ (CH__A2B, []))
         (* user A *)
         (Return n)
         (* user B *)
         ( m <- Return (Content n)
         ; Return match extractContent m with
                  | None =>    0
                  | Some n' => n'
                  end).

  Definition ideal_univ_done n :=
    mkiU ($0 $+ (CH__A2B, []))
         (* user A *)
         (Return n)
         (* user B *)
         (Return n).

End IdealProtocol.

Section RealProtocolParams.
  Import RealWorld.

  Definition KID__A : key_identifier := 0.
  Definition KID__B : key_identifier := 1.

  Definition KEY__A  := MkCryptoKey KID__A Signing AsymKey.
  Definition KEY__B := MkCryptoKey KID__B Encryption AsymKey.
  Definition KEYS  := $0 $+ (KID__A, KEY__A) $+ (KID__B, KEY__B).

  Definition A__keys := $0 $+ (KID__A, true) $+ (KID__B, false).
  Definition B__keys := $0 $+ (KID__A, false) $+ (KID__B, true).
End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs1 mycs2 : my_ciphers) (froms1 froms2 : recv_nonces)
                  (sents1 sents2 : sent_nonces) (cur_n1 cur_n2 : nat)
                  (msgs1 msgs2 : queued_messages) (cs : ciphers)
                  (p__a p__b : user_cmd nat) (adv : user_data unit) : universe nat unit :=
    {| users := $0
         $+ (A, {| key_heap := A__keys ; protocol := p__a ; msg_heap := msgs1 ; c_heap := mycs1
                 ; from_nons := froms1 ; sent_nons := sents1 ; cur_nonce := cur_n1 |})
         $+ (B, {| key_heap := B__keys ; protocol := p__b ; msg_heap := msgs2 ; c_heap := mycs2
                 ; from_nons := froms2 ; sent_nons := sents2 ; cur_nonce := cur_n2 |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := KEYS
    |}.

  Definition real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 :=
    mkrU mycs1 mycs2 [] [] [] [] cur_n1 cur_n2 [] [] cs
         (* user A *)
         ( n  <- Gen
         ; c  <- SignEncrypt KID__A KID__B B (message.Content n)
         ; _  <- Send B c
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (SignedEncrypted KID__A KID__B)
         ; v  <- Decrypt c
         ; Return match v with
                        | message.Content p => p
                        | _                 => 0
                        end).
  
  Definition real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [] [non1] [] cur_n1 cur_n2 [] [existT _ Nat (SignedCiphertext cid1)]
         (cs $+ (cid1, SigEncCipher KID__A KID__B B non1 (message.Content n)))
         (* user A *)
         ( _  <- Return tt
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (SignedEncrypted KID__A KID__B)
         ; v  <- Decrypt c
         ; Return match v with
                        | message.Content p => p
                        | _                 => 0
                        end).

  Definition real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [non1] [non1] [] cur_n1 cur_n2 [] []
         (cs $+ (cid1, SigEncCipher KID__A KID__B B non1 (message.Content n)))
         (* user A *)
         ( _  <- Return tt
         ; Return n)

         (* user B *)
         ( c  <- (Return (SignedCiphertext cid1))
         ; v  <- @Decrypt Nat  c
         ; Return match v with
                        | message.Content p => p
                        | _                 => 0
                        end).

  Inductive RSimplePing : RealWorld.simpl_universe nat -> IdealWorld.universe nat -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 adv,
      rstepSilent^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) ideal_univ_start
  | Sent1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      rstepSilent^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_sent1 n)
  | Recd1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      rstepSilent^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_recd1 n)
  (* | Done : forall U__r cs mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2 n cid1 seq1 adv, *)
  (*     rstepSilent^* (real_univ_done n cs mycs1 mycs2 froms1 froms2 sents1 sents2 cur_n1 cur_n2 cid1 seq1 adv) U__r *)
  (*     -> lameAdv tt adv *)
  (*     -> RSimplePing (peel_adv U__r) (ideal_univ_done n) *)
  .

End RealProtocol.

Hint Constructors RealWorld.msg_accepted_by_pattern.
Hint Constructors RSimplePing.

Import SimulationAutomation.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start real_univ_sent1 real_univ_recd1  mkrU
     ideal_univ_start ideal_univ_sent1 ideal_univ_recd1 ideal_univ_done mkiU : constants.

Hint Extern 0 (rstepSilent ^* _ _) =>
 progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
Hint Extern 1 (RSimplePing (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.
Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) => unfold RealWorld.peel_adv; simpl.

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl).

Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor.

(* Hint Extern 1 (KEYS $? _ = _) => unfold KEYS, A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
(* Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
(* Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Section FeebleSimulates.

  Hint Extern 0 (istepSilent ^* _ _) =>
    progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl).
  Hint Extern 1 (istepSilent ^* _ _) =>
    repeat (ideal_single_silent_multistep A);
    repeat (ideal_single_silent_multistep B); solve_refl.

  Lemma rsimpleping_silent_simulates :
    simulates_silent_step (lameAdv tt) RSimplePing.
  Proof.
    unfold simulates_silent_step.

    Time (
        intros * R UOK AOK LAME * STEP;
        clear UOK AOK;
        invert R;
        destruct U__r0; destruct U__r; simpl in *; subst;
        churn; simpl_real_users_context;
        [> eexists; split; swap 1 2; eauto 12 ..]
      ).
  Qed.

  Lemma rsimpleping_loud_simulates :
    simulates_labeled_step (lameAdv tt) RSimplePing.
  Proof.
    unfold simulates_labeled_step.

    intros * R UOK AOK LAME * STEP;
      clear UOK AOK;
      invert R;
      destruct U__r0; destruct U__r; simpl in *; subst.

    - churn.
      
      do 3 eexists;
        repeat (apply conj);
        swap 3 4; swap 2 3; swap 1 2;
       simpl; clean_map_lookups;
         eauto; eauto 12.

      simpl_real_users_context.
      simpl_ideal_users_context.
      eapply Out; simpl; auto.
      eapply CryptoSigEncCase; simpl; eauto. reflexivity.
      econstructor.  (* pull in master*)
      intros. unfold PERMS__b in H1. unfold PERMS__a in H1. churn.
      split_ands. in H7; intros; eauto.

      apply lookup_some_implies_in in H1; simpl in H1; split_ors; try contradiction;
        invert H1; clean_map_lookups; eauto.
      simpl. unfold PERMS__a; clean_map_lookups; eauto.

      
      shelve. split.

      apply lookup_some_implies_in in H1; simpl in H1; split_ors; try contradiction;
        invert H1; clean_map_lookups; simpl; eauto.
      
      apply lookup_some_implies_in in H1; simpl in H1; split_ors; try contradiction;
        invert H1; clean_map_lookups; simpl; eauto.

      simpl in *. shelve. 

    - churn.
      + do 3 eexists;
         repeat (apply conj);
         swap 3 4; swap 2 3; swap 1 2;
           simpl; clean_map_lookups; simpl.

        eapply Recd1; eauto.
        unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl.
        eapply TrcFront; simpl.
        eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user A | ..]; (try simple eapply @eq_refl).
        unfold A , B; clean_map_lookups; eauto.
        ((eapply IdealWorld.LStepBindRecur; i_single_silent_step) || i_single_silent_step); simpl.
        solve_refl.

        unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl; eauto 9.
        
      simpl_real_users_context.
      simpl_ideal_users_context.
      eapply Inp; simpl; auto.
      eapply CryptoSigCase; simpl; eauto
      econstructor.
      intros.
      split; intros; eauto.

      apply lookup_some_implies_in in H0; simpl in H0; split_ors; try contradiction;
        invert H0; clean_map_lookups; eauto.
      simpl. unfold PERMS__a; clean_map_lookups; eauto.

      apply lookup_some_implies_in in H0; simpl in H0; split_ors; try contradiction;
        invert H0; clean_map_lookups; simpl; eauto.

      unfold A , B in *; clean_map_lookups; simpl.
      unfold A__keys; eauto.

      + do 3 eexists;
          repeat (apply conj);
          swap 3 4; swap 2 3; swap 1 2;
            simpl; clean_map_lookups;
              eauto 9.
        
      simpl_real_users_context.
      simpl_ideal_users_context.
      eapply Inp; simpl; auto.
      eapply CryptoSigCase; simpl; eauto.
      econstructor.
      intros.
      split; intros; eauto.

      apply lookup_some_implies_in in H1; simpl in H1; split_ors; try contradiction;
        invert H1; clean_map_lookups; eauto.
      simpl. unfold PERMS__a; clean_map_lookups; eauto.

      apply lookup_some_implies_in in H2; simpl in H2; split_ors; try contradiction;
        invert H2; clean_map_lookups; simpl; eauto.

    - churn.

    (* time *)
    (*   (intros; *)
    (*    invert H; *)
    (*    try destruct U__r0; try destruct U__r; simpl in *; subst; *)
    (*    churn; *)
    (*    simpl_real_users_context; *)
    (*    (* autorewrite with simpl_univ; *) *)
    (*    (* simpl; *) *)
    (*    (do 3 eexists; *)
    (*     repeat (apply conj); *)
    (*     swap 3 4; swap 2 3; swap 1 2; [ .. | admit (* action matches predicate *)]; *)
    (*     simpl; clean_map_lookups; *)
    (*     eauto; eauto 12)). *)

  Qed.

  Lemma rsimpleping_univere_ok :
    simulates_universe_ok RSimplePing.
  Proof.
    unfold simulates_universe_ok; intros.

    (* time ( *)
    (*     inversion H; clear H; churn; solve_uok; eauto *)
    (*   ). *)

  Admitted.

  Lemma rsimpleping_labeled_simulates_safe :
    simulates_labeled_step_safe RSimplePing.
  Proof.
    unfold simulates_labeled_step_safe.
    intros.

    (* assert (RealWorld.findUserKeys U__r.(RealWorld.users) = *)
    (*         RealWorld.findUserKeys (clean_users (RealWorld.findUserKeys U__r.(RealWorld.users)) U__r.(RealWorld.users))) *)
    (*   by (symmetry; eapply clean_users_no_change_findUserKeys). *)
    (* remember (RealWorld.findUserKeys U__r.(RealWorld.users)) as honestk. *)

    (* time( *)
    (*     inversion H; clear H; *)
    (*     churn; *)
    (*     [> users_inversion; churn; repeat equality1; solve_adv_safe; eauto .. ] *)
    (*   ). *)

  Admitted.

  (* Timings:
   *
   * --------------------------------------------------------------
   * --------------------------------------------------------------
   *)

  Hint Resolve
       rsimpleping_silent_simulates
       rsimpleping_loud_simulates
       rsimpleping_univere_ok
       rsimpleping_labeled_simulates_safe.

  Lemma univ_ok_start :
    forall adv,
      lameAdv tt adv
      -> universe_ok (real_univ_start $0 [] [] [] [] [] [] 0 0 adv).
  Proof.
    unfold real_univ_start; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] [] [] [] [] 0 0 adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv.(RealWorld.msg_heap) = []
      -> adv.(RealWorld.key_heap) = $0
      -> adv_universe_ok (real_univ_start $0 [] [] [] [] [] [] 0 0 adv).
  Proof.
    intros; unfold lameAdv in *;
    unfold real_univ_start
         , adv_universe_ok
         , keys_and_permissions_good
         , permission_heap_good.
         
    simpl; intuition (subst; eauto).

    - unfold KEYS in *; solve_simple_maps; eauto.
    - rewrite Forall_natmap_forall; intros;
        unfold A__keys, B__keys, KEYS in *;
        simpl in *; solve_simple_maps;
          simpl in *; solve_simple_maps;
            eauto.
    - subst.


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
