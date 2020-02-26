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
        ChMaps
        Messages
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ProtocolAutomation
        SafeProtocol.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Set Implicit Arguments.

(* User ids *)
Definition A : user_id   := 0.
Definition B : user_id   := 1.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := (Single 0).
  Definition P__A2B : perm_id := 0.

  Definition PERMS__a := $0 $+ (P__A2B, {| read := true; write := true |}). (* writer *)
  Definition PERMS__b := $0 $+ (P__A2B, {| read := true; write := false |}). (* reader *)

  Definition mkiU (cv : channels) (p__a p__b : cmd (Base Nat)): universe Nat :=
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
         ; c  <- Sign KID1 B (message.Content n)
         ; _  <- Send B c
         ; Return n)

         (* user B *)
         ( c  <- @Recv Nat (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; ret (if fst v
                then match snd v with
                     | message.Content p => p
                     | _                 => 0
                     end
                else 1)).
  
  Definition real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [] [non1] [] cur_n1 cur_n2 [] [existT _ Nat (SignedCiphertext cid1)]
         (cs $+ (cid1, SigCipher KID1 B non1 (message.Content n)))
         (* user A *)
         ( _  <- ret tt
         ; ret n)

         (* user B *)
         ( c  <- @Recv Nat (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; ret (if fst v
                then match snd v with
                     | message.Content p => p
                     | _                 => 0
                     end
                else 1)).

  Definition real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [non1] [non1] [] cur_n1 cur_n2 [] []
         (cs $+ (cid1, SigCipher KID1 B non1 (message.Content n)))
         (* user A *)
         ( _  <- ret tt
         ; ret n)

         (* user B *)
         ( c  <- (@Return (Crypto Nat) (SignedCiphertext cid1))
         ; v  <- @Verify Nat KID1 c
         ; ret (if fst v
                then match snd v with
                     | message.Content p => p
                     | _                 => 0
                     end
                else 1)).

  Inductive RSimplePing : RealWorld.simpl_universe Nat -> IdealWorld.universe Nat -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 adv,
      ~^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimplePing (peel_adv U__r) ideal_univ_start
  | Sent1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_sent1 n)
  | Recd1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimplePing (peel_adv U__r) (ideal_univ_recd1 n)
  .

  Lemma Sent1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_sent1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> U__i = ideal_univ_sent1 n
      -> RSimplePing (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Sent1; eauto. Qed.
  
  Lemma Recd1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 n cid1 non1 adv,
      ~^* (real_univ_recd1 n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> U__i = ideal_univ_recd1 n
      -> RSimplePing (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Recd1; eauto. Qed.

End RealProtocol.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start real_univ_sent1 real_univ_recd1 mkrU
     ideal_univ_start ideal_univ_sent1 ideal_univ_recd1 mkiU : constants.

Import SimulationAutomation.

(* Hint Constructors *)
(*      RSimplePing. *)
Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) =>
  simpl; simpl_real_users_context; simpl_ideal_users_context; simpl;
   ( (eapply Start  ; solve [ eauto ])
   || (eapply Recd1' ; solve [ eauto ])
   || (eapply Sent1' ; solve [ eauto ]) ).

Hint Extern 0 (~^* _ _) =>
 progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
Hint Extern 1 (RSimplePing (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, mkiU; simpl).

(* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor. *)
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Hint Extern 1 (istepSilent ^* _ _) =>
unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, mkiU; simpl;
  repeat (ideal_single_silent_multistep A);
  repeat (ideal_single_silent_multistep B); solve_refl.

Hint Unfold mkrU : user_build.

Module SimplePingProtocolSecure <: SafeProtocol.
  Definition A := Nat.
  Definition B := Unit.

  Definition U__i := ideal_univ_start.
  Definition U__r := real_univ_start $0 [] [] 0 0 startAdv.

  Definition b := tt.
  Definition R := RSimplePing.

  Lemma U_good : @universe_starts_sane _ Unit b U__r.
  Proof.
    unfold b, U__r, real_univ_start, mkrU, startAdv.
    unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - solve_perm_merges; eauto.
    - econstructor.
    - unfold AdversarySafety.keys_honest, KEYS; rewrite Forall_natmap_forall; intros.
      econstructor; simpl.
      rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty; eauto.
      solve_perm_merges.
    - unfold lameAdv; simpl; eauto.
  Qed.

  Lemma R_silent_simulates : simulates_silent_step (@lameAdv Unit b) R.
  Proof.
    unfold b, R, simulates_silent_step.

    intros * R UOK AOK LAME * STEP;
      clear UOK AOK;
      invert R;
      destruct U__r0; destruct U__r; simpl in *; subst.

    - churn; simpl_real_users_context.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.

    - churn; simpl_real_users_context.
      + eexists; split; [ solve_refl | ]; eauto 12.
        
    - churn; simpl_real_users_context.
 
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.

    (* Time ( *)
    (*     intros * R UOK AOK LAME * STEP; *)
    (*     clear UOK AOK; *)
    (*     invert R; *)
    (*     destruct U__r0; destruct U__r; simpl in *; subst; *)
    (*     churn; simpl_real_users_context; *)
    (*     [> eexists; split; swap 1 2; eauto 12 ..] *)
    (*   ). *)
  Qed.

  Lemma R_loud_simulates : simulates_labeled_step (@lameAdv Unit b) R.
  Proof.
    unfold b, R, simulates_labeled_step.

    intros * R UOK AOK LAME * STEP;
      clear UOK AOK;
      invert R;
      destruct U__r0; destruct U__r; simpl in *; subst.

    - churn; simpl_real_users_context; simpl.

      + do 3 eexists;
          repeat (apply conj); eauto 12. admit. admit.

    - churn; simpl_real_users_context.
      
      + do 3 eexists;
          repeat (apply conj); eauto.
        eapply IdealWorld.LStepUser' with (u_id := SimplePingProtocol.B); eauto. simpl.
        eapply IdealWorld.LStepBindRecur.
        eapply IdealWorld.LStepRecv.
        unfold CH__A2B. clean_chmap_lookups. reflexivity. unfold PERMS__b. clean_map_lookups. reflexivity. reflexivity. reflexivity.
        simpl. unfold ideal_univ_recd1, mkiU. clean_chmap_lookups. unfold CH__A2B. clean_chmap_lookups. f_equal. clean_chmap_lookups.
        rewrite map_add_eq. reflexivity.
        maps_equal. eauto.  repeat solve_action_matches1. 

        invert H.

      + do 3 eexists;
          repeat (apply conj); eauto 12.

    - churn; simpl_real_users_context.

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
  
  Lemma R_honest_actions_safe : honest_actions_safe B R.
  Proof.
    unfold B, R, honest_actions_safe; intros.
    clear H0 H1.
    
    inversion H; clear H;
      destruct U__r0; destruct U__r; simpl in *; subst;
        try match goal with
            | [ H : ~ In ?k KEYS |- _ ] => 
              rewrite not_find_in_iff in H;
              solve_concrete_maps; solve_perm_merges
            end.

    - churn;
        [> solve_honest_actions_safe; eauto 8 ..].
      
    - churn;
        [> solve_honest_actions_safe; eauto 8 ..].

    - churn;
        [> solve_honest_actions_safe; eauto 8 ..].

      Unshelve.
      all: auto.
  Qed.

  Lemma univ_ok_start : universe_ok U__r.
  Proof.
    unfold real_univ_start, U__r; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start : adv_universe_ok U__r.
  Proof.
    unfold adv_universe_ok, U__r; eauto.
    unfold keys_and_permissions_good.
    pose proof (adversary_is_lame_adv_univ_ok_clauses U_good).

    intuition eauto;
      unfold real_univ_start, mkrU in *; simpl in *.

    - unfold KEYS in *; solve_simple_maps; eauto.
    - rewrite Forall_natmap_forall; intros.
      solve_simple_maps; simpl;
        unfold permission_heap_good, KEYS, A__keys, B__keys; intros;
          solve_simple_maps; eauto.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (SimplePingProtocol.A ==n k); cases (SimplePingProtocol.B ==n k);
        subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold honest_nonces_ok; intros.
      unfold honest_nonce_tracking_ok.

      destruct (u_id ==n SimplePingProtocol.A); destruct (u_id ==n SimplePingProtocol.B);
        destruct (rec_u_id ==n SimplePingProtocol.A); destruct (rec_u_id ==n SimplePingProtocol.B);
          subst; try contradiction; try discriminate; clean_map_lookups; simpl;
            repeat (apply conj); intros; clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      destruct (u_id ==n SimplePingProtocol.A);
        destruct (u_id ==n SimplePingProtocol.B);
        subst;
        simpl in *;
        clean_map_lookups;
        rewrite !findUserKeys_add_reduce, findUserKeys_empty_is_empty;
        eauto;
        simpl in *;
        solve_perm_merges;
        solve_concrete_maps;
        solve_simple_maps;
        eauto.
  Qed.
  
  
  Lemma universe_starts_safe : R (RealWorld.peel_adv U__r) U__i /\ universe_ok U__r /\ adv_universe_ok U__r.
  Proof.
    repeat (simple apply conj);
      eauto using univ_ok_start, adv_univ_ok_start.

    pose proof U_good;
      unfold universe_starts_sane, adversary_is_lame in *;
      split_ands;
      unfold R;
      unfold U__r in *;
      eapply Start;
      eauto.
  Qed.

End SimplePingProtocolSecure.

(* Timings:
 *
 * --------------------------------------------------------------
 * --------------------------------------------------------------
 *)
