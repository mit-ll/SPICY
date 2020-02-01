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

  Definition CH__A2B : channel_id := 0.

  Definition PERMS__a := $0 $+ (CH__A2B, {| read := true; write := true |}). (* writer *)
  Definition PERMS__b := $0 $+ (CH__A2B, {| read := true; write := false |}). (* reader *)

  Definition mkiU (cv : channels) (p__a p__b : cmd (Base Nat)): universe Nat :=
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
  
End RealProtocol.

Import SimulationAutomation.

Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Module SimplePingProtocolSecure <: AutomatedSafeProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start $0 [] [] 0 0 startAdv.

  Import Gen ModelCheck Invariant Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start mkiU real_univ_start mkrU : core.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0)}; Step := @step t__hon t__adv  |}
      (lift_fst honest_cmds_safe).
  Proof.
    eapply Invariant.invariant_weaken.

    - apply multiStepClosure_ok; simpl.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.

    - intros.
      simpl in *.
      sets_invert; unfold lift_fst;
        split_ex; simpl in *; subst; solve_honest_actions_safe;
          clean_map_lookups; eauto 8.

      Unshelve.
      all:eauto.
  Qed.

  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
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

  Lemma univ_ok_start : universe_ok ru0.
  Proof.
    autounfold; econstructor; eauto.
  Qed.

  Lemma adv_univ_ok_start : adv_universe_ok ru0.
  Proof.
    autounfold; unfold adv_universe_ok; eauto.
    unfold keys_and_permissions_good.
    pose proof (adversary_is_lame_adv_univ_ok_clauses U_good).

    intuition eauto;
      simpl in *.

    - unfold KEYS in *; solve_simple_maps; eauto.
    - rewrite Forall_natmap_forall; intros.
      solve_simple_maps; simpl;
        unfold permission_heap_good, KEYS, A__keys, B__keys; intros;
          solve_simple_maps; eauto.

    - unfold user_cipher_queues_ok.
      rewrite Forall_natmap_forall; intros.
      cases (A ==n k); cases (B ==n k);
        subst; clean_map_lookups; simpl in *; econstructor; eauto.

    - unfold honest_nonces_ok; intros.
      unfold honest_nonce_tracking_ok.

      destruct (u_id ==n A); destruct (u_id ==n B);
        destruct (rec_u_id ==n A); destruct (rec_u_id ==n B);
          subst; try contradiction; try discriminate; clean_map_lookups; simpl;
            repeat (apply conj); intros; clean_map_lookups; eauto.

    - unfold honest_users_only_honest_keys; intros.
      destruct (u_id ==n A);
        destruct (u_id ==n B);
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
  
  Lemma universe_starts_safe : universe_ok ru0 /\ adv_universe_ok ru0.
  Proof.
    repeat (simple apply conj);
      eauto using univ_ok_start, adv_univ_ok_start.
  Qed.


End SimplePingProtocolSecure.
