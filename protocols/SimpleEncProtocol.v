From Coq Require Import
     List.
     (* Logic.ProofIrrelevance. *)

(* Require Import MyPrelude. *)

(* Module Foo <: EMPTY. End Foo. *)
(* Module Import SN := SetNotations(Foo). *)

Require Import
        MyPrelude
        Maps
        ChMaps
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

  Definition p__A2B : nat := 0.
  Definition CH__A2B : channel_id := #p__A2B.

  Definition PERMS__a := $0 $+ (p__A2B, {| read := false; write := true |}). (* writer *)
  Definition PERMS__b := $0 $+ (p__A2B, {| read := true; write := false |}). (* reader *)

  Definition mkiU (cv : channels) (p__a p__b : cmd (Base Nat) ): universe Nat :=
    {| channel_vector := cv
     ; users := $0
         $+ (A,   {| perms    := PERMS__a ; protocol := p__a |})
         $+ (B,   {| perms    := PERMS__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU (#0 #+ (CH__A2B, []))
         (* user A *)
         ( n <- Gen
         ; _ <- Send (Content n) CH__A2B
         ; Return n)
         (* user B *)
         ( m <- @Recv Nat CH__A2B
           ; ret (extractContent m)).

  Definition ideal_univ_sent1 n :=
    mkiU (#0 #+ (CH__A2B, [existT _ _ (Content n)]))
         (* user A *)
         ( _ <- ret tt
         ; ret n)
         (* user B *)
         ( m <- @Recv Nat CH__A2B
             ; ret (extractContent m)).

  Definition ideal_univ_recd1 n :=
    mkiU (#0 #+ (CH__A2B, []))
         (* user A *)
         (Return n)
         (* user B *)
         ( m <- @Return (Message Nat) (Content n)
         ; ret (extractContent m)).

  Definition ideal_univ_done n :=
    mkiU (#0 #+ (CH__A2B, []))
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
                  (p__a p__b : user_cmd (Base Nat)) (adv : user_data Unit) : universe Nat Unit :=
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
         ( c  <- @Recv Nat (SignedEncrypted KID__A KID__B true)
         ; v  <- Decrypt c
         ; ret (extractContent v)).
  
  Definition real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [] [non1] [] cur_n1 cur_n2 [] [existT _ Nat (SignedCiphertext cid1)]
         (cs $+ (cid1, SigEncCipher KID__A KID__B B non1 (message.Content n)))
         (* user A *)
         ( _  <- ret tt
         ; ret n )

         (* user B *)
         ( c  <- @Recv Nat (SignedEncrypted KID__A KID__B true)
         ; v  <- Decrypt c
         ; ret (extractContent v)).

  Definition real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [non1] [non1] [] cur_n1 cur_n2 [] []
         (cs $+ (cid1, SigEncCipher KID__A KID__B B non1 (message.Content n)))
         (* user A *)
         ( _  <- ret tt
         ; ret n)

         (* user B *)
         ( c  <- (@Return (Crypto Nat) (SignedCiphertext cid1))
         ; v  <- @Decrypt Nat  c
         ; ret (extractContent v)).

  Inductive RSimpleEnc : RealWorld.simpl_universe Nat -> IdealWorld.universe Nat -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 adv,
      ~^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimpleEnc (peel_adv U__r) ideal_univ_start
  | Sent1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimpleEnc (peel_adv U__r) (ideal_univ_sent1 n)
  | Recd1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimpleEnc (peel_adv U__r) (ideal_univ_recd1 n)
  .

  Lemma Sent1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> U__i = ideal_univ_sent1 n
      -> RSimpleEnc (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Sent1; eauto. Qed.
  
  Lemma Recd1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> U__i = ideal_univ_recd1 n
      -> RSimpleEnc (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Recd1; eauto. Qed.

End RealProtocol.

Import SimulationAutomation.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start real_univ_sent1 real_univ_recd1  mkrU
     ideal_univ_start ideal_univ_sent1 ideal_univ_recd1 ideal_univ_done mkiU : constants.

Hint Unfold mkrU : user_build.

Hint Constructors RealWorld.msg_accepted_by_pattern : core.
Hint Extern 1 (RSimpleEnc (RealWorld.peel_adv _) _) =>
  simpl; simpl_real_users_context; simpl_ideal_users_context; simpl;
   ( (eapply Start  ; solve [ eauto ])
   || (eapply Recd1' ; solve [ eauto ])
   || (eapply Sent1' ; solve [ eauto ]) ).
(* Hint Constructors RSimpleEnc : core. *)

Hint Extern 0 (~^* _ _) =>
 progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl) : core.
Hint Extern 1 (RSimpleEnc (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl : core.
(* Hint Extern 1 (RSimpleEnc (RealWorld.peel_adv _) _) => unfold RealWorld.peel_adv; simpl : core. *)

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl) : core.
(* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor : core. *)

Hint Extern 1 (istepSilent ^* _ _) =>
progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl);
  repeat (ideal_single_silent_multistep A);
  repeat (ideal_single_silent_multistep B); solve_refl : core.

Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a : core.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b : core.

Section FeebleSimulates.


  Lemma rsimpleenc_silent_simulates :
    simulates_silent_step (@lameAdv Unit tt) RSimpleEnc.
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

  Lemma rsimpleenc_loud_simulates :
    simulates_labeled_step (@lameAdv Unit tt) RSimpleEnc.
  Proof.
    unfold simulates_labeled_step.
    time (
        intros * R UOK AOK LAME * STEP;
        clear UOK AOK;
        invert R;
        destruct U__r0; destruct U__r; simpl in *; subst;
        churn; simpl_real_users_context;
        [> do 3 eexists;
         repeat (apply conj); eauto 12 ..]
         (* swap 3 4; swap 2 3; swap 1 2; *)
         (* simpl; clean_map_lookups; eauto 12 ..] *)
      ).
  Qed.
  
  Lemma rsimpleenc_honest_actions_safe :
    honest_actions_safe Unit RSimpleEnc.
  Proof.
    unfold honest_actions_safe; intros. (* R UOK AOK LAME ** .*)
    clear H1 H0.
    inversion H; clear H;
      destruct U__r0; destruct U__r; simpl in *; subst.

    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].

    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].

    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].

      Unshelve. all: eauto.
  Qed.
  
  Hint Resolve
       rsimpleenc_silent_simulates
       rsimpleenc_loud_simulates
       rsimpleenc_honest_actions_safe : core.

  Lemma univ_ok_start :
    forall adv,
      @lameAdv Unit tt adv
      -> universe_ok (real_univ_start $0 [] [] 0 0 adv).
  Proof.
    unfold real_univ_start; econstructor; eauto.
  Qed.

  Lemma merge_perms_true_either_true :
    forall ks1 ks2 k_id,
      ks1 $? k_id = Some true \/ ks2 $? k_id = Some true
      -> ks1 $k++ ks2 $? k_id = Some true.
  Proof.
    intros; split_ors; solve_perm_merges.
  Qed.

  Hint Resolve merge_perms_true_either_true : core.

  Lemma adv_univ_ok_start :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] 0 0 adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> @lameAdv Unit tt adv
      -> adv.(RealWorld.key_heap) = $0
      -> adv.(RealWorld.msg_heap) = []
      -> adv.(RealWorld.c_heap) = []
      -> adv_universe_ok (real_univ_start $0 [] [] 0 0 adv).
  Proof.
    intros; unfold lameAdv in *;
      unfold real_univ_start, adv_universe_ok, keys_and_permissions_good, permission_heap_good.
    simpl; intuition (subst; eauto).
    - unfold KEYS in *; solve_simple_maps; eauto.
    - rewrite Forall_natmap_forall; intros;
        unfold A__keys, B__keys, KEYS in *;
        simpl in *; solve_simple_maps;
          simpl in *; solve_simple_maps;
            eauto.
    - rewrite H2 in H5; clean_map_lookups.
      
    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold adv_cipher_queue_ok.
      rewrite Forall_forall; intros.
      rewrite H4 in H; contradiction.

    - unfold adv_message_queue_ok.
      rewrite Forall_forall; intros.
      rewrite H3 in H; contradiction.

    - unfold adv_no_honest_keys; intros.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto.
      unfold A__keys, B__keys; destruct (k_id ==n KID__A); destruct (k_id ==n KID__B); subst; solve_perm_merges.
      + right. right. rewrite H2. split. eauto. clean_map_lookups.
      + right; right. rewrite H2. split. eauto. clean_map_lookups.
      + left. apply merge_perms_adds_no_new_perms; clean_map_lookups; eauto.

    - unfold honest_nonces_ok; intros.
      unfold honest_nonce_tracking_ok.

      destruct (u_id ==n A); destruct (u_id ==n B);
        destruct (rec_u_id ==n A); destruct (rec_u_id ==n B);
          unfold A in *; unfold B in *;
            subst; try contradiction; try discriminate;
              clean_map_lookups; eauto; simpl; repeat (apply conj); intros;
                clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      destruct (u_id ==n A); destruct (u_id ==n B);
        subst; simpl in *; clean_map_lookups;
          rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto; simpl in *.
      + unfold A__keys in H0; destruct (KID__A ==n k_id); destruct (KID__B ==n k_id);
          subst; clean_map_lookups; eauto.
      + unfold B__keys in H0; destruct (KID__A ==n k_id); destruct (KID__B ==n k_id);
          subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve univ_ok_start adv_univ_ok_start : core.

  Theorem base_pingpong_refines_ideal_pingpong :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] 0 0 adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> @lameAdv Unit tt adv
      -> RealWorld.key_heap adv = $0
      -> RealWorld.msg_heap adv = []
      -> RealWorld.c_heap adv = []
      -> adv_message_queue_ok U__r.(RealWorld.users) U__r.(RealWorld.all_ciphers) U__r.(RealWorld.all_keys) adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      (* real_univ_start $0 [] [] adv <| ideal_univ_start / lameAdv tt. *)
      -> refines (@lameAdv Unit tt) U__r ideal_univ_start.
  Proof.
    exists RSimpleEnc; unfold simulates.
    intuition (subst; eauto).
  Qed.

End FeebleSimulates.
