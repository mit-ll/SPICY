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

    Definition CH__A2B : channel_id := 0.
    Definition CH__B2A : channel_id := 1.
    Definition empty_chs : channels := ($0 $+ (CH__A2B, []) $+ (CH__B2A, [])).

    Definition PERMS__a := $0 $+ (CH__A2B, owner) $+ (CH__B2A, reader).
    Definition PERMS__b := $0 $+ (CH__A2B, reader) $+ (CH__B2A, owner).

    Definition ideal_univ_start :=
      mkiU ($0 $+ (CH__A2B, [])) PERMS__a PERMS__b
           (* user A *)
           ( n <- Gen
           ; chid <- CreateChannel
           ; _ <- Send (MsgPair (Content n) (Permission {| ch_perm := writer ; ch_id := chid |})) CH__A2B
           ; Return n)

           (* user B *)
           ( m <- @Recv (TPair Nat Access) CH__A2B
           ; ret (extractContent (msgFst m))).

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

  Lemma safe_invariant :
    invariantFor
      {| Initial := {(ru0, iu0)}; Step := @step t__hon t__adv  |}
      (fun st => safety st /\ liveness st ).
  Proof.
    eapply invariant_weaken.

    - apply multiStepClosure_ok; simpl.
      gen1.

      Ltac cleanup :=
        repeat (
            equality1
            || match goal with
              | [ H : True |- _ ] => clear H
              | [ H : ?X = ?X |- _ ] => clear H
              | [ H : ?x = ?y |- _] => assert (x = y) as EQ by (clear H; trivial); clear H; clear EQ
              | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
                (rewrite add_neq_o in H by solve_simple_ineq)
                || (rewrite add_eq_o in H by trivial)
                || (destruct (k1 ==n k2); subst)
              | [ H : ?m $? _ = _ |- _ ] => progress (unfold m in H)
              | [ H : RealWorld.msg_accepted_by_pattern _ _ _ _ _ |- _ ] => invert H
              | [ H : IdealWorld.msg_permissions_valid _ _ |- _ ] =>
                generalize (Forall_inv H); generalize (Forall_inv_tail H); clear H; intros
              | [ H : IdealWorld.permission_subset _ _ |- _ ] => invert H
              | [ H : Forall _ [] |- _ ] => clear H
              | [ H : context [true || _]  |- _] => rewrite orb_true_l in H
              | [ H : context [_ || true]  |- _] => rewrite orb_true_r in H
              | [ H : context [false || _]  |- _] => rewrite orb_false_l in H
              | [ H : context [_ || false]  |- _] => rewrite orb_false_r in H
              | [ H : context [$0 $k++ _] |- _] => rewrite merge_perms_left_identity in H
              | [ H : context [_ $k++ $0] |- _] => rewrite merge_perms_right_identity in H
              | [ H : context [_ $k++ _]  |- _] => erewrite reduce_merge_perms in H; clean_map_lookups; eauto
              | [ H : context [match ?m $? _ with _ => _ end] |- _] => progress (unfold m in H)
              | [ H : match _ $+ (?k1,_) $? ?k2 with _ => _ end = _ |- _ ] =>
                (rewrite add_neq_o in H by solve_simple_ineq)
                || (rewrite add_eq_o in H by trivial)
              end
          ).

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

      step1; [cleanup; progress canonicalize users; close | step2 | step3].
      step1; [cleanup; progress canonicalize users; close | step2 | step3].
      step1; [cleanup; progress canonicalize users; close | step2 | step3].
      step1; [cleanup; progress canonicalize users; close | step2 | step3].
      step1; [cleanup; progress canonicalize users; close | step2 | step3].
      step1; [cleanup; progress canonicalize users; close | step2 | step3].

      step1; [cleanup; close .. | step2 | step3].
      step1; [cleanup; close .. | step2 | step3].
      step1; [cleanup; close .. | step2 | step3].
      step1; [cleanup; close .. | step2 | step3].
      step1; [cleanup; close .. | step2 | step3].
      step1; [cleanup; close .. | step2 | step3].
      eapply MscDone.
      

      
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.
      cleanup; subst. close.

      step2.
      step3.


      

      match goal with
      | [ |- context[ {| RealWorld.users := ?usrs |} ]] =>
        let s := eval compute in (canon_map usrs) in replace usrs with s
      end.

      2: maps_equal.

      eapply msc_step_alt
      ; [ solve[ unfold oneStepClosure_new; simplify; tidy; rstep; istep ]
        | solve[ simplify
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
               | eapply intersect_empty_l]
        | rewrite ?union_empty_r ]

    simplify
    ; tidy
    ; idtac "rstep start"
    ; rstep
    ; idtac "rstep done"
    ; idtac "istep start"
    ; istep
    ; idtac "istep done"
    ; subst
    ; canonicalize users
    ; idtac "close start"
    ; repeat close
    ; idtac "close done".

          
      

      ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1
          ; gen1 ).
      gen1.
      
    - intros.
      simpl in *; split.
      
      + sets_invert; unfold safety;
          split_ex; simpl in *; subst; solve_honest_actions_safe;
            clean_map_lookups; eauto 8.
      + sets_invert; unfold liveness; intros;
          split_ex; subst; intros; rstep.
        * do 3 eexists;
            repeat (apply conj); eauto.
        * do 3 eexists;
            repeat (apply conj); eauto.
          subst; repeat (solve_action_matches1); clean_map_lookups.
        * do 3 eexists;
            repeat (apply conj); eauto.
          subst; repeat (solve_action_matches1); clean_map_lookups.

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

End SimplePingProtocolSecure.
