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
     List.

Require Import
        MyPrelude
        Maps
        Messages
        (* MessageEq *)
        Common
        Keys
        (* KeysTheory *)
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

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := 0.

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := true; write := true |}). (* writer *)
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

  Definition KID1 : key_identifier := 0.

  Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
  Definition KEYS  := $0 $+ (KID1, KEY1).

  Definition A__keys := $0 $+ (KID1, true).
  Definition B__keys := $0 $+ (KID1, false).
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
         ; c  <- Sign KID1 B (message.Content n)
         ; _  <- Send B c
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; Return (if fst v
                   then match snd v with
                        | message.Content p => p
                        | _                 => 0
                        end
                   else 1)).
  
  Definition real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [] [non1] [] cur_n1 cur_n2 [] [existT _ Nat (SignedCiphertext cid1)]
         (cs $+ (cid1, SigCipher KID1 B non1 (message.Content n)))
         (* user A *)
         ( _  <- Return tt
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; Return (if fst v
                   then match snd v with
                        | message.Content p => p
                        | _                 => 0
                        end
                   else 1)).

  Definition real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [non1] [non1] [] cur_n1 cur_n2 [] []
         (cs $+ (cid1, SigCipher KID1 B non1 (message.Content n)))
         (* user A *)
         ( _  <- Return tt
         ; Return n)

         (* user B *)
         ( c  <- (Return (SignedCiphertext cid1))
         ; v  <- @Verify Nat KID1 c
         ; Return (if fst v
                   then match snd v with
                        | message.Content p => p
                        | _                 => 0
                        end
                   else 1)).

  Inductive RSimplePing : RealWorld.simpl_universe nat -> IdealWorld.universe nat -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 adv,
      ~^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) ideal_univ_start
  | Sent1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_sent1 n)
  | Recd1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> lameAdv tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_recd1 n)
  .

End RealProtocol.

Hint Constructors
     RSimplePing.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start real_univ_sent1 real_univ_recd1 mkrU
     ideal_univ_start ideal_univ_sent1 ideal_univ_recd1 ideal_univ_done mkiU : constants.

Import SimulationAutomation.

Hint Extern 0 (~^* _ _) =>
 progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
Hint Extern 1 (RSimplePing (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.
Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) => unfold RealWorld.peel_adv; simpl.

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl).

(* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor. *)
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Section FeebleSimulates.

  Hint Extern 0 (istepSilent ^* _ _) =>
    progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl).
  Hint Extern 1 (istepSilent ^* _ _) =>
    unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl;
    repeat (ideal_single_silent_multistep A);
    repeat (ideal_single_silent_multistep B); solve_refl.

  Lemma rsimpleping_silent_simulates :
    simulates_silent_step (lameAdv tt) RSimplePing.
  Proof.
    unfold simulates_silent_step.

    time (
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

    time (
        intros * R UOK AOK LAME * STEP;
        clear UOK AOK;
        invert R;
        destruct U__r0; destruct U__r; simpl in *; subst;
        churn;
        [> do 3 eexists;
         repeat (apply conj);
         swap 3 4; swap 2 3; swap 1 2;
         simpl; clean_map_lookups;
         eauto; eauto 12 ..]
      ).

  Qed.

  Lemma rsimpleping_honest_actions_safe :
    honest_actions_safe unit RSimplePing.
  Proof.
    unfold honest_actions_safe; intros.
    clear H0 H1.
    inversion H; clear H;
      destruct U__r0; destruct U__r; simpl in *; subst.

    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].

    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].
      
    - churn;
        [> solve_honest_actions_safe; clean_map_lookups; eauto 8 .. ].
  Qed.

  (* Timings:
   *
   * --------------------------------------------------------------
   * --------------------------------------------------------------
   *)

  Hint Resolve
       rsimpleping_silent_simulates
       rsimpleping_loud_simulates
       rsimpleping_honest_actions_safe.

  Lemma univ_ok_start :
    forall adv,
      lameAdv tt adv
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

    Hint Resolve merge_perms_true_either_true.


  Lemma adv_univ_ok_start :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] 0 0 adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> adv.(RealWorld.key_heap) = $0
      -> adv.(RealWorld.msg_heap) = []
      -> adv.(RealWorld.c_heap) = []
      -> adv_universe_ok (real_univ_start $0 [] [] 0 0 adv).
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
    - rewrite H2 in H5; clean_map_lookups.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold message_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k); subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold adv_cipher_queue_ok.
      rewrite Forall_forall; intros.
      rewrite H4 in H; simpl in H; contradiction.

    - unfold adv_message_queue_ok.
      rewrite Forall_forall; intros.
      rewrite H3 in H; simpl in H; contradiction.

    - unfold adv_no_honest_keys; intros.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto.
      unfold A__keys , B__keys; destruct (k_id ==n KID1); subst; solve_perm_merges.
      + right; right.
        rewrite H2; split; clean_map_lookups; eauto.
      + left; apply merge_perms_adds_no_new_perms; eauto.

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
        subst;
        simpl in *;
        clean_map_lookups;
        rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty;
        eauto;
        simpl in *.

      + unfold A__keys in H0; destruct (KID1 ==n k_id); subst; clean_map_lookups; eauto.
      + unfold B__keys in H0; destruct (KID1 ==n k_id); subst; clean_map_lookups; eauto.
  Qed.

  Hint Resolve
       univ_ok_start
       adv_univ_ok_start.

  Theorem base_pingpong_refines_ideal_pingpong :
    forall adv U__r honestk,
      U__r = real_univ_start $0 [] [] 0 0 adv
      -> honestk = RealWorld.findUserKeys U__r.(RealWorld.users)
      -> lameAdv tt adv
      -> RealWorld.key_heap adv = $0
      -> RealWorld.msg_heap adv = []
      -> RealWorld.c_heap adv = []
      -> adv_message_queue_ok U__r.(RealWorld.users) U__r.(RealWorld.all_ciphers) U__r.(RealWorld.all_keys) adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      -> refines (lameAdv tt) U__r ideal_univ_start.
  Proof.
    exists RSimplePing; unfold simulates.
    intuition (subst; eauto).
  Qed.

End FeebleSimulates.
