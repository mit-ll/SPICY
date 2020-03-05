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
        ChMaps
        Messages
        ModelCheck
        Common
        Keys
        Automation
        Tactics
        Simulation
        AdversaryUniverse
        UniverseEqAutomation
        ExampleProtocols
        ProtocolAutomation
        SafeProtocol.

Require IdealWorld RealWorld.

Import IdealWorld.IdealNotations.
Import RealWorld.RealWorldNotations.

Import SimulationAutomation.

Import Sets.
Module Foo <: EMPTY.
End Foo.
Module Import SN := SetNotations(Foo).

Set Implicit Arguments.

Module ShareSecretProtocol.

  Section IW.
    Import IdealWorld.

    Notation CH__A2B := (Single 0).
    Notation CH__B2A := (Single 1).
    Notation pCH__A2B := 0.
    Notation pCH__B2A := 1.

    Definition empty_chs : channels := (#0 #+ (CH__A2B, []) #+ (CH__B2A, [])).

    Definition PERMS__a := $0 $+ (pCH__A2B, owner) $+ (pCH__B2A, reader).
    Definition PERMS__b := $0 $+ (pCH__A2B, reader) $+ (pCH__B2A, owner).

    Definition ideal_univ_start :=
      mkiU empty_chs PERMS__a PERMS__b
           (* user A *)
           ( chid <- CreateChannel
           ; _ <- Send (Permission {| ch_perm := writer ; ch_id := chid |}) CH__A2B
           ; m <- @Recv Nat (chid #& pCH__B2A)
           ; @Return (Base Nat) (extractContent m)
           )

           (* user B *)
           ( m <- @Recv Access CH__A2B
           ; n <- Gen
           ; _ <- let chid := ch_id (extractPermission m)
                 in  Send (Content n) (chid #& pCH__B2A)
           ; @Return (Base Nat) n
           ).

  End IW.

  Section RW.
    Import RealWorld.

    Definition KID1 : key_identifier := 0.
    Definition KID2 : key_identifier := 1.

    Definition KEY1  := MkCryptoKey KID1 Signing AsymKey.
    Definition KEY2  := MkCryptoKey KID2 Signing AsymKey.
    Definition KEYS  := $0 $+ (KID1, KEY1) $+ (KID2, KEY2).

    Definition A__keys := $0 $+ (KID1, true) $+ (KID2, false).
    Definition B__keys := $0 $+ (KID1, false) $+ (KID2, true).

    Definition real_univ_start :=
      mkrU KEYS A__keys B__keys
           (* user A *)
           ( kp <- GenerateAsymKey Encryption
           ; c1 <- Sign KID1 B (Permission (fst kp, false))
           ; _  <- Send B c1
           ; c2 <- @Recv Nat (SignedEncrypted KID2 (fst kp) true)
           ; m  <- Decrypt c2
           ; @Return (Base Nat) (extractContent m) )

           (* user B *)
           ( c1 <- @Recv Access (Signed KID1 true)
           ; v  <- Verify KID1 c1
           ; n  <- Gen
           ; c2 <- SignEncrypt KID2 (fst (extractPermission (snd v))) A (message.Content n)
           ; _  <- Send A c2
           ; @Return (Base Nat) n).
  
  End RW.

  Hint Unfold
       A B KID1 KID2 KEY1 KEY2 A__keys B__keys
       PERMS__a PERMS__b
       real_univ_start mkrU mkrUsr
       ideal_univ_start mkiU : constants.
  
  Import SimulationAutomation.

  Hint Extern 0 (~^* _ _) =>
    progress(autounfold with constants; simpl).

  Hint Extern 0 (IdealWorld.lstep_universe _ _ _) =>
    progress(autounfold with constants; simpl).

  Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
  Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.

  Hint Extern 1 (istepSilent ^* _ _) =>
  autounfold with constants; simpl;
    repeat (ideal_single_silent_multistep A);
    repeat (ideal_single_silent_multistep B); solve_refl.
  
End ShareSecretProtocol.

Module ShareSecretProtocolSecure <: AutomatedSafeProtocol.

  Import ShareSecretProtocol.

  Definition t__hon := Nat.
  Definition t__adv := Unit.
  Definition b := tt.
  Definition iu0  := ideal_univ_start.
  Definition ru0  := real_univ_start startAdv.

  Import Gen Tacs SetLemmas.

  Hint Unfold t__hon t__adv b ru0 iu0 ideal_univ_start mkiU real_univ_start mkrU mkrUsr startAdv : core.

  Ltac step1 := eapply msc_step_alt; [ unfold oneStepClosure_new; simplify; tidy; rstep; istep | ..].
  Ltac step2 := 
    solve[ simplify
           ; sets
           ; split_ex
           ; propositional
           ; repeat match goal with
                    | [H : (?x1, ?y1) = ?p |- _] =>
                      match p with
                      | (?x2, ?y2) =>
                        tryif (concrete x2; concrete y2)
                        then let H' := fresh H
                             in assert (H' : (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2)
                               by equality
                                ; propositional
                                ; discriminate
                        else invert H
                      | _ => invert H
                      end
                    end
         | eapply intersect_empty_l ].

  Ltac step3 := rewrite ?union_empty_r.

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ labels_align st ).
  Proof.
    eapply invariant_weaken.

    - apply multiStepClosure_ok; simpl.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      gen1.
      
    - intros.
      simpl in *; split.
      
      + sets_invert; unfold safety;
          split_ex; simpl in *; subst; solve_honest_actions_safe;
            clean_map_lookups; eauto 8.

        Unshelve.
        all:clean_map_lookups.
        
      + sets_invert; unfold labels_align;
          split_ex; subst; intros; rstep; subst.

Ltac g :=
  match goal with
  | [ H : # ?x = # ?y -> False |- _ ] => assert (x <> y) by congruence; clear H
  | [ |- Forall _ _ ] => econstructor
  | [ |- {| IdealWorld.channel_vector := _; IdealWorld.users := _ |} = _] => smash_universe; solve_concrete_maps
  | [ |- _ = {| IdealWorld.channel_vector := _; IdealWorld.users := _ |}] => smash_universe; solve_concrete_maps
  | [ |- IdealWorld.screen_msg _ _ ] => econstructor
  | [ |- IdealWorld.permission_subset _ _ ] => econstructor
  | [ |- IdealWorld.check_perm _ _ _ ] => unfold IdealWorld.check_perm
  | [ |- ?m #? (# ?k) = None ] =>
    solve [ is_evar k; unify (# k) (ChMaps.next_key m); apply ChMaps.next_key_not_in; trivial ] 
  | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) ] => rewrite add_eq_o by trivial
  | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) ] => rewrite add_neq_o by solve_simple_ineq (* auto 2 *)
  | [ |- context [ #0 #? _ ]] => rewrite ChMap.lookup_empty_none
  | [ |- _ = _ ] => reflexivity
  | [ |- context [ _ $? _ ] ] => solve_concrete_maps
  | [ |- context [ _ #? _ ] ] => solve_concrete_maps
  end; simpl.
Ltac single_silent_multistep' usr_step := eapply TrcFront; [usr_step |]; simpl.
Ltac isilent_step_univ' uid :=
  eapply IdealWorld.LStepUser'; simpl; swap 2 3; [ pick_user uid | ..]; (try simple eapply @eq_refl);
  ((eapply IdealWorld.LStepBindRecur; i_single_silent_step; solve [ repeat g; eauto 2  ])
   || (i_single_silent_step; solve [ repeat g; eauto 2 ])).
Ltac ideal_single_silent_multistep' uid := single_silent_multistep' ltac:(isilent_step_univ' uid).
Hint Extern 1 (istepSilent ^* _ _) =>
  autounfold with constants; simpl;
    repeat (ideal_single_silent_multistep' A);
    repeat (ideal_single_silent_multistep' B); solve_refl.
Ltac single_labeled_ideal_step' uid :=
  eapply IdealWorld.LStepUser' with (u_id := uid);
  [ solve [ solve_concrete_maps ] | simpl | reflexivity ];
  eapply IdealWorld.LStepBindRecur;
  ( (eapply IdealWorld.LStepRecv; solve [ repeat g ])
    || (eapply IdealWorld.LStepSend; solve [ repeat g ])).
Ltac blah1 :=
  match goal with
  | [ |- context [ IdealWorld.addMsg ]] => unfold IdealWorld.addMsg, empty_chs; simpl
  | [ |- context [ _ #+ (?k1,_) #? ?k1 ]] => rewrite ChMap.F.add_eq_o by trivial
  | [ |- context [ _ #+ (?k1,_) #? ?k2 ]] => rewrite ChMap.F.add_neq_o by congruence
  end.
Hint Extern 1 (IdealWorld.lstep_universe _ (Action _) _) => 
  canonicalize users; repeat blah1; (single_labeled_ideal_step' A || single_labeled_ideal_step' B).

    * (do 3 eexists); repeat (simple apply conj); eauto.
    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1); clean_map_lookups; ChMap.clean_map_lookups; eauto.
    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1); clean_map_lookups; ChMap.clean_map_lookups; eauto.
    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.
      
    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.
      
    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.

    * (do 3 eexists); repeat (simple apply conj); eauto.
      repeat (solve_action_matches1 || blah1 || g); clean_map_lookups; ChMap.clean_map_lookups; eauto.
      unfold IdealWorld.perm_intersection; simpl; eauto.
      solve_perm_merges; solve_concrete_maps; eauto.
      erewrite merge_perms_adds_ks1; eauto; solve_concrete_maps.
      erewrite merge_perms_adds_ks2; eauto; solve_concrete_maps.
  Qed.

  Lemma U_good : @universe_starts_sane _ Unit b ru0.
  Proof.
    autounfold;
      unfold universe_starts_sane; simpl.
    repeat (apply conj); intros; eauto.
    - solve_perm_merges; eauto.
    - econstructor.
    - unfold AdversarySafety.keys_honest, KEYS; rewrite Forall_natmap_forall; intros.
      econstructor; unfold mkrUsr; simpl.
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
        unfold mkrUsr; simpl; 
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

End ShareSecretProtocolSecure.
