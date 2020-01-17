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
 * as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq Require Import
     List.

Require Import
        MyPrelude
        Maps
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

Transparent A B.

Section IdealProtocol.
  Import IdealWorld.

  Definition CH__A2B : channel_id := 0.
  Definition CH__B2A : channel_id := 1.
  Definition empty_chs : channels := ($0 $+ (CH__A2B, []) $+ (CH__B2A, [])).

  Definition owner  := {| read := true; write := true |}.
  Definition reader := {| read := true; write := false |}.
  Definition writer := {| read := false; write := true |}.

  Definition PERMS__a := $0 $+ (CH__A2B, owner) $+ (CH__B2A, reader).
  Definition PERMS__b := $0 $+ (CH__A2B, reader) $+ (CH__B2A, owner).

  Definition mkiU (cv : channels) (perm__a perm__b : permissions) (p__a p__b : cmd (Base Nat)): universe Nat :=
    {| channel_vector := cv
     ; users := $0
         $+ (A, {| perms := perm__a ; protocol := p__a |})
         $+ (B, {| perms := perm__b ; protocol := p__b |})
    |}.

  Definition ideal_univ_start :=
    mkiU empty_chs PERMS__a PERMS__b
         (* user A *)
         ( n <- Gen
         ; chid <- CreateChannel
         ; _ <- Send (MsgPair (Content n) (Permission {| ch_perm := writer ; ch_id := chid |})) CH__A2B
         ; Return n)
         (* user B *)
         ( m <- @Recv (TPair Nat Access) CH__A2B
         ; ret (extractContent (msgFst m))).

  Definition ideal_univ_sent1 chid n :=
    mkiU ($0
           $+ (CH__A2B,
                 [existT _ _ (MsgPair (Content n) (Permission {| ch_perm := writer ; ch_id := chid |})) ])
           $+ (CH__B2A, [])
           $+ (chid, []))
         (PERMS__a $+ (chid, creator_permission)) PERMS__b
         (* user A *)
         ( _ <- ret tt
         ; ret n)
         (* user B *)
         ( m <- @Recv (TPair Nat Access) CH__A2B
         ; ret (extractContent (msgFst m))).

  Definition ideal_univ_recd1 chid n :=
    mkiU (empty_chs $+ (chid, []))
         (PERMS__a $+ (chid, owner))
         (PERMS__b $+ (chid, writer))
         (* user A *)
         (Return n)
         (* user B *)
         ( m <- @Return (Message (TPair Nat Access))
                       (MsgPair (Content n) (Permission {| ch_perm := writer ; ch_id := chid |}))
         ; ret (extractContent (msgFst m))).

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

  Definition startAdv := {| key_heap := $0;
                            protocol := ret tt;
                            msg_heap := [];
                            c_heap   := [];
                            from_nons := [];
                            sent_nons := [];
                            cur_nonce := 0 |}.
End RealProtocolParams.

Section RealProtocol.
  Import RealWorld.

  Definition mkrU (mycs1 mycs2 : my_ciphers) (froms1 froms2 : recv_nonces)
             (sents1 sents2 : sent_nonces) (cur_n1 cur_n2 : nat)
             (ks1 ks2 : key_perms)
             (gks : keys)
             (msgs1 msgs2 : queued_messages) (cs : ciphers)
             (p__a p__b : user_cmd (Base Nat)) (adv : user_data Unit) : universe Nat Unit :=
    {| users := $0
         $+ (A, {| key_heap := ks1 ; protocol := p__a ; msg_heap := msgs1 ; c_heap := mycs1
                 ; from_nons := froms1 ; sent_nons := sents1 ; cur_nonce := cur_n1 |})
         $+ (B, {| key_heap := ks2 ; protocol := p__b ; msg_heap := msgs2 ; c_heap := mycs2
                 ; from_nons := froms2 ; sent_nons := sents2 ; cur_nonce := cur_n2 |})
     ; adversary        := adv
     ; all_ciphers      := cs
     ; all_keys         := gks
    |}.

  Definition real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 :=
    mkrU mycs1 mycs2 [] [] [] [] cur_n1 cur_n2 A__keys B__keys KEYS [] [] cs
         (* user A *)
         ( n <- Gen
         ; kp <- GenerateAsymKey Encryption
         ; c  <- Sign KID1 B (MsgPair (message.Content n) (Permission (fst kp, false)))
         ; _  <- Send B c
         ; Return n)

         (* user B *)
         ( c  <- @Recv (TPair Nat Access) (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; ret (if fst v
                then (extractContent (msgFst (snd v)))
                else 1)).
  
  Definition real_univ_sent1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [] [non1] [] cur_n1 cur_n2
         (add_key_perm k_id true A__keys) B__keys (KEYS $+ (k_id, k))
         [] [existT _ (TPair Nat Access) (SignedCiphertext cid1)]
         (cs $+ (cid1, SigCipher KID1 B non1 (MsgPair (message.Content n) (Permission (k_id, false)))))
         (* user A *)
         ( _  <- ret tt
         ; ret n)

         (* user B *)
         ( c  <- @Recv (TPair Nat Access) (Signed KID1 true)
         ; v  <- Verify KID1 c
         ; ret (if fst v
                then (extractContent (msgFst (snd v)))
                else 1)).

  Definition real_univ_recd1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 :=
    mkrU mycs1 mycs2 [] [non1] [non1] [] cur_n1 cur_n2
         (add_key_perm k_id true A__keys) (B__keys $k++ ($0 $+ (k_id,false))) (KEYS $+ (k_id,k)) [] []
         (cs $+ (cid1, SigCipher KID1 B non1 (MsgPair (message.Content n) (Permission (k_id, false)))))
         (* user A *)
         ( _  <- ret tt
         ; ret n)

         (* user B *)
         ( c  <- (@Return (Crypto (TPair Nat Access)) (SignedCiphertext cid1))
         ; v  <- @Verify (TPair Nat Access) KID1 c
         ; ret (if fst v
                then (extractContent (msgFst (snd v)))
                else 1)).

  Inductive RSimplePing : RealWorld.simpl_universe Nat -> IdealWorld.universe Nat -> Prop :=
  | Start : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 adv,
      ~^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> @lameAdv Unit tt adv
      -> RSimplePing (peel_adv U__r) ideal_univ_start
  | Sent1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 k k_id n chid cid1 non1 adv,
      ~^* (real_univ_sent1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> ~ In k_id KEYS
      -> ~ In chid empty_chs
      -> RSimplePing (peel_adv U__r) (ideal_univ_sent1 chid n)
  | Recd1 : forall U__r cs mycs1 mycs2 cur_n1 cur_n2 k k_id n chid cid1 non1 adv,
      ~^* (real_univ_recd1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> ~ In k_id KEYS
      -> ~ In chid empty_chs
      -> RSimplePing (peel_adv U__r) (ideal_univ_recd1 chid n)
  .

  Lemma Start' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 adv,
      ~^* (real_univ_start cs mycs1 mycs2 cur_n1 cur_n2 adv) U__r
      -> @lameAdv Unit tt adv
      -> U__i = ideal_univ_start
      -> RSimplePing (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Start; eauto. Qed.

  Lemma Sent1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 k k_id n chid cid1 non1 adv,
      ~^* (real_univ_sent1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> ~ In k_id KEYS
      -> ~ In chid empty_chs
      -> U__i = ideal_univ_sent1 chid n
      -> RSimplePing (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Sent1; eauto. Qed.

  Lemma Recd1' : forall U__r U__i cs mycs1 mycs2 cur_n1 cur_n2 k k_id n chid cid1 non1 adv,
      ~^* (real_univ_recd1 k_id k n cs mycs1 mycs2 cur_n1 cur_n2 cid1 non1 adv) U__r
      -> @lameAdv Unit tt adv
      -> ~ In k_id KEYS
      -> ~ In chid empty_chs
      -> U__i = ideal_univ_recd1 chid n
      -> RSimplePing (peel_adv U__r) U__i.
  Proof. intros; subst; eapply Recd1; eauto. Qed.

End RealProtocol.

Hint Constructors RealWorld.msg_accepted_by_pattern.

(* Hint Constructors RSimplePing. *)

Import SimulationAutomation.

Hint Unfold
     A B PERMS__a PERMS__b
     real_univ_start real_univ_sent1 real_univ_recd1 mkrU
     ideal_univ_start ideal_univ_sent1 ideal_univ_recd1 mkiU : constants.

Hint Extern 0 (~^* _ _) =>
 progress(unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
Hint Extern 1 (RSimplePing (RealWorld.buildUniverse _ _ _ _ _ _) _) => unfold RealWorld.buildUniverse; simpl.
(* Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) => unfold RealWorld.peel_adv; simpl. *)

Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
 progress(unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, mkiU; simpl).

Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => single_step_ideal_universe; eauto 2; econstructor.

Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

Hint Extern 1 (istepSilent ^* _ _) =>
unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, mkiU; simpl;
  repeat (ideal_single_silent_multistep A);
  repeat (ideal_single_silent_multistep B); solve_refl.


Ltac clear_extra_adversary :=
  match goal with
  | [ |- context [ RSimplePing
                    (RealWorld.peel_adv {| RealWorld.users := _;
                                           RealWorld.adversary := ?a;
                                           RealWorld.all_ciphers := _;
                                           RealWorld.all_keys := _ |}) _ ]] =>
    repeat match goal with
           | [ H : lameAdv _ ?bada |- _ ] =>
             does_not_unify bada a; clear H bada
           end
  end.

Hint Extern 1 ({| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _) => smash_universe; solve_concrete_maps : core.
Hint Extern 1 (_ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}) => smash_universe; solve_concrete_maps : core.

Ltac solve_ideal_step_stuff :=
  repeat (
      match goal with
      | [ |- Forall _ _ ] => econstructor
      | [ |- {| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _] => smash_universe; solve_concrete_maps
      | [ |- _ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}] => smash_universe; solve_concrete_maps
      | [ |- IdealWorld.msg_permissions_valid _ _ ] => unfold IdealWorld.msg_permissions_valid
      | [ |- IdealWorld.permission_subset _ _ ] => econstructor
      | [ |- context [ _ $? _ ] ] => solve_concrete_maps
      | [ |- ~ In ?k ?m ] => is_evar k; unify k (next_key m); rewrite not_find_in_iff; apply next_key_not_in; trivial
      | [ |- _ = _ ] => reflexivity
      end; simpl).

Ltac single_labeled_ideal_step uid :=
  eapply IdealWorld.LStepUser' with (u_id := uid);
  [ solve [ solve_concrete_maps ] | simpl | reflexivity ];
  eapply IdealWorld.LStepBindRecur;
  ( (eapply IdealWorld.LStepRecv; solve [ solve_ideal_step_stuff ])
    || (eapply IdealWorld.LStepSend; solve [ solve_ideal_step_stuff ])).

Ltac step_each_ideal_user U :=
  match U with
  | ?usrs $+ (?AB,_) =>
    idtac "stepping " AB; (single_labeled_ideal_step AB || step_each_ideal_user usrs)
  end.

Ltac step_ideal_user :=
  match goal with
  | [ |- IdealWorld.lstep_universe _ (Action _) ?U' ] =>
    is_evar U'; simpl_ideal_users_context;
    match goal with
    | |- IdealWorld.lstep_universe
          {| IdealWorld.users := ?usrs; IdealWorld.channel_vector := _ |} _ _ =>
      step_each_ideal_user usrs
    end
  end.

Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => step_ideal_user : core.
Hint Extern 1 (RSimplePing (RealWorld.peel_adv _) _) =>
  simpl; simpl_real_users_context; simpl_ideal_users_context; simpl;
   ( (eapply Start  ; solve [ eauto ])
   || (eapply Recd1' ; swap 1 4; solve [ eauto ])
   || (eapply Sent1' ; swap 1 3; swap 2 4; solve [ eauto ]) ).

Module ShareSecretNewKeyProtocolSecure <: SafeProtocol.
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

    - churn; simpl_real_users_context; clear_extra_adversary.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.
      + eexists; split; [ solve_refl | ]; eauto 12.

    - churn; simpl_real_users_context; clear_extra_adversary.
      + eexists; split; [ solve_refl | ]; eauto 12.
        
    - churn; simpl_real_users_context; clear_extra_adversary.
 
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

    - churn; simpl_real_users_context; simpl; clear_extra_adversary.

      + do 3 eexists;
          repeat (apply conj); eauto 12.

    - churn; simpl_real_users_context; clear_extra_adversary.
      
      + do 3 eexists;
          repeat (apply conj); eauto.

      + do 3 eexists;
          repeat (apply conj); eauto 12.

    - churn; simpl_real_users_context; clear_extra_adversary.

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

    - churn.
      
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
        solve_perm_merges.
        solve_perm_merges; eauto.
        solve_perm_merges.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.

    - churn.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.

    - churn.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.
      + solve_honest_actions_safe; eauto 8.

  Qed.

  Lemma univ_ok_start : universe_ok U__r.
  Proof.
    unfold real_univ_start, U__r; econstructor; eauto.
  Qed.

  Section Foo.
    Import RealWorld.

    Lemma adversary_is_lame_adv_univ_ok_clauses :
      forall A B (U : universe A B) b,
        universe_starts_sane b U
        -> permission_heap_good U.(all_keys) U.(adversary).(key_heap)
        /\ message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
        /\ adv_cipher_queue_ok U.(all_ciphers) U.(users) U.(adversary).(c_heap)
        /\ adv_message_queue_ok U.(users) U.(all_ciphers) U.(all_keys) U.(adversary).(msg_heap)
        /\ adv_no_honest_keys (findUserKeys U.(users)) U.(adversary).(key_heap).
    Proof.
      unfold universe_starts_sane, adversary_is_lame; intros; split_ands.
      repeat match goal with
             | [ H : _ (adversary _) = _ |- _ ] => rewrite H; clear H
             end.
      repeat (simple apply conj); try solve [ econstructor; eauto ].

      - unfold message_queues_ok.
        rewrite Forall_natmap_forall; intros.
        specialize (H _ _ H2); rewrite H; econstructor.
      - unfold adv_no_honest_keys; intros.
        cases (findUserKeys (users U) $? k_id); eauto.
        destruct b1; eauto.
        right; right; apply conj; eauto.
        clean_map_lookups.

        Unshelve.
        exact (MkCryptoKey 1 Encryption SymKey).
    Qed.
  End Foo.
                                                                                      
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
      cases (ShareSecretNewKeyProtocol.A ==n k); cases (ShareSecretNewKeyProtocol.B ==n k);
        subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold honest_nonces_ok; intros.
      unfold honest_nonce_tracking_ok.

      destruct (u_id ==n ShareSecretNewKeyProtocol.A); destruct (u_id ==n ShareSecretNewKeyProtocol.B);
        destruct (rec_u_id ==n ShareSecretNewKeyProtocol.A); destruct (rec_u_id ==n ShareSecretNewKeyProtocol.B);
          subst; try contradiction; try discriminate; clean_map_lookups; simpl;
            repeat (apply conj); intros; clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      destruct (u_id ==n ShareSecretNewKeyProtocol.A);
        destruct (u_id ==n ShareSecretNewKeyProtocol.B);
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

End ShareSecretNewKeyProtocolSecure.

(* Timings:
 *
 * --------------------------------------------------------------
 * --------------------------------------------------------------
 *)
