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

(* Hint Extern 1 (KEYS $? _ = _) => unfold KEYS, A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
(* Hint Extern 1 (A__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
(* Hint Extern 1 (B__keys $? _ = _) => unfold A__keys, B__keys, KEY1, KEY2, KID1, KID2. *)
Hint Extern 1 (PERMS__a $? _ = _) => unfold PERMS__a.
Hint Extern 1 (PERMS__b $? _ = _) => unfold PERMS__b.


Section FeebleSimulates.

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

  (* Lemma rsimpleping_silent_simulates : *)
  (*   simulates_silent_step (@lameAdv Unit tt) RSimplePing. *)
  (* Proof. *)
  (*   unfold simulates_silent_step. *)

  (*   (* time ( *) *)
  (*   (*     intros * R UOK AOK LAME * STEP; *) *)
  (*   (*     clear UOK AOK; *) *)
  (*   (*     invert R; *) *)
  (*   (*     destruct U__r0; destruct U__r; simpl in *; subst; *) *)
  (*   (*     churn; simpl_real_users_context; *) *)
  (*   (*     [> eexists; split; swap 1 2; eauto 12 ..] *) *)
  (*   (*   ). *) *)


  (*   intros * R UOK AOK LAME * STEP; *)
  (*     clear UOK AOK; *)
  (*     invert R; *)
  (*     destruct U__r0; destruct U__r; simpl in *; subst. *)

  (*   - churn; simpl_real_users_context; clear_extra_adversary. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)

  (*   - churn; simpl_real_users_context; clear_extra_adversary. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
        
  (*   - churn; simpl_real_users_context; clear_extra_adversary. *)
 
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)
  (*     + eexists; split; [ solve_refl | ]; eauto 12. *)

  (*       Unshelve. *)
  (*       all:apply tt. *)

  (*   (* Time ( *) *)
  (*   (*     intros * R UOK AOK LAME * STEP; *) *)
  (*   (*     clear UOK AOK; *) *)
  (*   (*     invert R; *) *)
  (*   (*     destruct U__r0; destruct U__r; simpl in *; subst; *) *)
  (*   (*     churn; simpl_real_users_context; *) *)
  (*   (*     [> eexists; split; swap 1 2; eauto 12 ..] *) *)
  (*   (*   ). *) *)
  (* Qed. *)

  Lemma lookup_none_noteq_all_keys :
    forall {V} (m : NatMap.t V) k1 v k2,
      m $? k2 = None /\ k1 <> k2
      -> m $+ (k1,v) $? k2 = None.
  Proof. intros; split_ands; rewrite add_neq_o; assumption. Qed.

  Lemma rsimpleping_loud_simulates :
    simulates_labeled_step (@lameAdv Unit tt) RSimplePing.
  Proof.
    unfold simulates_labeled_step.

    intros * R UOK AOK LAME * STEP;
      clear UOK AOK;
      invert R;
      destruct U__r0; destruct U__r; simpl in *; subst.

    (* Hint Extern 1 (IdealWorld.lstep_universe _ _ _) => eapply IdealWorld.LStepUser'; simpl : core. *)
    (* Hint Extern 1 (IdealWorld.lstep_user (Action _) _ _) => eapply IdealWorld.LStepBindRecur; eapply IdealWorld.LStepSend; simpl : core. *)
    (* Hint Extern 1 (IdealWorld.lstep_user (Action _) _ _) => eapply IdealWorld.LStepBindRecur; eapply IdealWorld.LStepRecv; simpl : core. *)
    (* Hint Extern 1 (Forall _ [ _ ]) => *)
    (*   eapply Forall_cons; *)
    (*     repeat *)
    (*       match goal with *)
    (*       | [ |- match _ $? _ with _ => _ end ] => solve_concrete_maps *)
    (*       end : core. *)
    (* Hint Constructors IdealWorld.permission_subset. *)
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
      (  (eapply Start' ; solve [ eauto ])
         || (eapply Recd1' ; solve [ eauto ])
         || (eapply Sent1' ; solve [ eauto ]) ).

    - churn; simpl_real_users_context; clear_extra_adversary.
      
      do 3 eexists;
        repeat (apply conj); eauto 12.

    - churn; simpl_real_users_context; clear_extra_adversary.
      
      + do 3 eexists;
          repeat (apply conj); eauto 12.

        simpl.
        simpl_ideal_users_context.
        simpl_real_users_context.
        eapply Recd1'.

        3: solve_concrete_maps.
        
        *  progress (unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
           eapply Trc3Refl'; simpl.
           apply real_univ_eq_fields_eq.
           ** solve_concrete_maps.
              clean_map_lookups; simpl.



        repeat (solve_action_matches1; simpl; eauto 3).

            repeat
      match goal with
      | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
      | [ H : Some _ = Some _ |- _ ] => invert H
      | [ H : Some _ = None |- _ ] => discriminate
      | [ H : None = Some _ |- _ ] => discriminate
                                              
      | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by eauto 2
                                                                                       
      | [ H : In ?k ?m -> False |- _ ] =>
        is_not_var k; assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; solve_concrete_maps); contradiction
      | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
      | [ |- ~ In _ _ ] => unfold not; intros
      | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H
      | [ H : ~ In ?x ?xs |- _ ] => rewrite not_find_in_iff in H
                                                               
      | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)
      | [ |- ?m $+ (?kid1,_) $? ?kid1 = _ ] => rewrite add_eq_o by trivial
      | [ |- ?m $+ (?kid2,_) $? ?kid1 = _ ] => rewrite add_neq_o by auto 2
      (*   rewrite add_neq_o by solve_concrete_maps *)
      (* || rewrite add_eq_o by (unify kid1 kid2; solve_concrete_maps) *)
      | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_eq_o by trivial
      | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_neq_o by auto 2
      | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) $? _ = _ ] => rewrite add_eq_o by trivial
      | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) $? _ = _ ] => rewrite add_neq_o by auto 2
      | [ |- context [ $0 $? _ ]] => rewrite lookup_empty_none
      | [ |- _ $+ (?k1,_) $? ?k2 = _ ] =>
        is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2);
          destruct (k1 ==n k2); subst; try contradiction
      | [ |- _ = ?m $+ (?kid2,_) $? ?kid1 ] => symmetry
                                           
      | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)
      | [ |- context [ ?m $? ?kid1 ] ] => progress (unfold m)

      | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H

      | [ |- _ = _ ] => reflexivity
      | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros

      | [ |- Some _ = Some _ ] => f_equal
      | [ |- {| RealWorld.key_heap := _ |} = _ ] => f_equal
      | [ |- ?kid1 <> ?kid2 ] =>
        ( (is_evar kid1; fill_unification_var_ineq kid1 kid2)
          || (is_evar kid2; fill_unification_var_ineq kid2 kid1));
        unfold not; intro; congruence
      | [ |- _ $? _ = _ ] => eassumption

                             
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ $+ (_,_) $? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "destructing1 " k1 k2; destruct (k1 ==n k2); subst
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- (match _ $+ (_,_) $? _ with _ => _ end) $? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "destructing2 " k1 k2; destruct (k1 ==n k2); subst
      (* | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- context [ _ $? _ ] ] => *)
      (*   (is_var k1 || is_var k2); idtac "destructing " k1 k2; destruct (k1 ==n k2); subst *)
      end.


        simpl_ideal_users_context.

        eapply IdealWorld.LStepUser' with (u_id := B);
        [ solve [ solve_concrete_maps ] | simpl | reflexivity ];
        eapply IdealWorld.LStepBindRecur;
        eapply IdealWorld.LStepRecv; solve_ideal_step_stuff; eauto 3.
        


    repeat
      match goal with
      | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
      | [ H : Some _ = Some _ |- _ ] => invert H
      | [ H : Some _ = None |- _ ] => discriminate
      | [ H : None = Some _ |- _ ] => discriminate
                                              
      | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by eauto 2
                                                                                       
      | [ H : In ?k ?m -> False |- _ ] =>
        is_not_var k; assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; solve_concrete_maps); contradiction
      | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
      | [ |- ~ In _ _ ] => unfold not; intros
      | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H
      | [ H : ~ In ?x ?xs |- _ ] => rewrite not_find_in_iff in H
                                                               
      | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)
      | [ |- ?m $+ (?kid1,_) $? ?kid1 = _ ] => rewrite add_eq_o by trivial
      | [ |- ?m $+ (?kid2,_) $? ?kid1 = _ ] => rewrite add_neq_o by auto 2
      (*   rewrite add_neq_o by solve_concrete_maps *)
      (* || rewrite add_eq_o by (unify kid1 kid2; solve_concrete_maps) *)
      | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_eq_o by trivial
      | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_neq_o by auto 2
      | [ |- context [ $0 $? _ ]] => rewrite lookup_empty_none
      | [ |- _ $+ (?k1,_) $? ?k2 = _ ] =>
        is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2);
          destruct (k1 ==n k2); subst; try contradiction
      | [ |- _ = ?m $+ (?kid2,_) $? ?kid1 ] => symmetry
                                           
      | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)
      | [ |- context [ ?m $? ?kid1 ] ] => progress (unfold m)

      | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H

      | [ |- _ = _ ] => reflexivity
      | [ |- _ $+ (_,_) = _ ] => apply map_eq_Equal; unfold Equal; intros

      | [ |- Some _ = Some _ ] => f_equal
      | [ |- {| RealWorld.key_heap := _ |} = _ ] => f_equal
      | [ |- ?kid1 <> ?kid2 ] =>
        ( (is_evar kid1; fill_unification_var_ineq kid1 kid2)
          || (is_evar kid2; fill_unification_var_ineq kid2 kid1));
        unfold not; intro; congruence
      | [ |- _ $? _ = _ ] => eassumption

      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ $+ (_,_) $? _ = _ ] =>
        (is_var k1 || is_var k2); idtac "destructing " k1 k2; destruct (k1 ==n k2); subst
      end.

    eauto. eauto.
        
        solve_concrete_maps.

        ( (eapply IdealWorld.LStepRecv; solve [ solve_ideal_step_stuff ])
          || (eapply IdealWorld.LStepSend; solve [ solve_ideal_step_stuff ])).

        

      simpl.
      simpl_real_users_context.
      simpl_ideal_users_context.
      eapply Sent1'; eauto.
      debug eauto.

      + progress (unfold real_univ_start, real_univ_sent1, real_univ_recd1, mkrU; simpl).
        eapply Trc3Refl'; simpl; solve_concrete_maps.

        simpl_real_users_context.


        match goal with
        | |- ~^* ?U1 ?U2 => first [ solve_refl3 | figure_out_user_step ltac:(rss_clean) U1 U2 ]
        end

        
        debug eauto.

        
        eapply Trc3Refl'.
        eapply real_univ_eq_fields_eq; eauto 2.
        apply map_eq_Equal; unfold Equal; intros y.

        repeat
      match goal with
      | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
      | [ H : Some _ = Some _ |- _ ] => invert H
      | [ H : Some _ = None |- _ ] => discriminate
      | [ H : None = Some _ |- _ ] => discriminate
                                              
      | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
      | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
      | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by eauto 2
                                                                                       
      | [ H : In ?k ?m -> False |- _ ] =>
        is_not_var k; assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; solve_concrete_maps); contradiction
      | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
      | [ |- ~ In _ _ ] => unfold not; intros
      | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H
      | [ H : ~ In ?x ?xs |- _ ] => rewrite not_find_in_iff in H
                                                               
      | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)
      | [ |- ?m $+ (?kid1,_) $? ?kid1 = _ ] => rewrite add_eq_o by trivial
      | [ |- ?m $+ (?kid2,_) $? ?kid1 = _ ] => rewrite add_neq_o by auto 2
      (*   rewrite add_neq_o by solve_concrete_maps *)
      (* || rewrite add_eq_o by (unify kid1 kid2; solve_concrete_maps) *)
      | [ |- (match ?m $+ (?kid1,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_eq_o by trivial
      | [ |- (match ?m $+ (?kid2,_) $? ?kid1 with _ => _ end) = _ ] => rewrite add_neq_o by auto 2
      | [ |- context [ $0 $? _ ]] => rewrite lookup_empty_none
      | [ |- _ $+ (?k1,_) $? ?k2 = _ ] =>
        is_not_evar k2; is_not_evar k2; (is_var k1 || is_var k2);
          destruct (k1 ==n k2); subst; try contradiction
      | [ |- _ = ?m $+ (?kid2,_) $? ?kid1 ] => symmetry
                                           
      | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)
      | [ |- context [ ?m $? ?kid1 ] ] => progress (unfold m)

      | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H

      | [ |- _ = _ ] => reflexivity
      | [ |- Some _ = Some _ ] => f_equal
      | [ |- {| RealWorld.key_heap := _ |} = _ ] => f_equal
      | [ |- ?kid1 <> ?kid2 ] =>
        ( (is_evar kid1; fill_unification_var_ineq kid1 kid2)
          || (is_evar kid2; fill_unification_var_ineq kid2 kid1));
        unfold not; intro; congruence
      | [ |- _ $? _ = _ ] => eassumption

                             
      (* | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- context [ _ $? _ ] ] => *)
      (*   (is_var k1 || is_var k2); idtac "destructing " k1 k2; destruct (k1 ==n k2); subst *)
      end.




      
        destruct (y ==n A); destruct (y ==n B); subst;
          try contradiction; clean_map_lookups; eauto.
      f_equal.
      unfold add_key_perm; f_equal; eauto.
      clean_map_lookups; simpl; trivial.


      
      apply map_eq_Equal; unfold Equal; intros y;
        destruct (y ==n A); destruct (y ==n B); subst;
          try contradiction; clean_map_lookups; eauto.
      f_equal.
      unfold add_key_perm; f_equal; eauto.
      clean_map_lookups; simpl; trivial.
      


      f_equal.
      f_equal.
      f_equal.
      simpl.

      
      real_silent_multistep.
      unfold RealWorld.buildUniverse; simpl; simpl_real_users_context.
      simpl.
      debug eauto.
      
      eauto 12.
      

    - churn; simpl_real_users_context; clear_extra_adversary.

      + do 3 eexists;
          repeat (apply conj).

        * eauto 12.
        * eapply IdealWorld.LStepUser' with (u_id := B);
            [ solve [ solve_concrete_maps ] | simpl | reflexivity ].
          eapply IdealWorld.LStepBindRecur.

          eapply IdealWorld.LStepRecv; solve_ideal_step_stuff.

          reflexivity.
          reflexivity.

        * 

          repeat (solve_action_matches1; simpl; eauto 3).

          Ltac solve_concrete_maps' :=
            repeat
              match goal with
              | [ H : context [ $0 $? _ ] |- _ ] => rewrite lookup_empty_none in H
              | [ H : Some _ = Some _ |- _ ] => invert H
              | [ H : Some _ = None |- _ ] => discriminate
              | [ H : None = Some _ |- _ ] => discriminate
                                              
              | [ H : ?m $? ?k = _ |- _ ] => progress (unfold m in H)
              | [ H : ?m $+ (?k1,_) $? ?k1 = _ |- _ ] => rewrite add_eq_o in H by trivial
              | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- _ ] => rewrite add_neq_o in H by eauto 2
                                                                                       
              | [ H : In ?k ?m -> False |- _ ] =>
                is_not_var k; assert (In k m) by (clear H; rewrite in_find_iff; unfold not; intros; solve_concrete_maps); contradiction
              | [ H : In _ _ |- _ ] => rewrite in_find_iff in H
              | [ |- ~ In _ _ ] => unfold not; intros
              | [ H : In ?x ?xs -> False |- _ ] => change (In x xs -> False) with (~ In x xs) in H
              | [ H : ~ In ?x ?xs |- _ ] => rewrite not_find_in_iff in H
                                                                       
              | [ |- context [ next_key ] ] => progress (unfold next_key; simpl)
              | [ |- context [ ?m $+ (?kid1,_) $? ?kid1 ] ] => rewrite add_eq_o by trivial
              | [ |- context [ ?m $+ (?kid2,_) $? ?kid1 ] ] =>
                rewrite add_neq_o by auto 2
              | [ |- context [ $0 $? _ ]] => rewrite lookup_empty_none
              (*   rewrite add_neq_o by solve_concrete_maps *)
              (* || rewrite add_eq_o by (unify kid1 kid2; solve_concrete_maps) *)
                                          
              | [ |- context [ add_key_perm _ _ _ ]] => progress (unfold add_key_perm)
              | [ |- context [ ?m $? ?kid1 ] ] => progress (unfold m)
                                                 
              | [ H : ?m $? ?k <> _ |- _ ] => cases (m $? k); try contradiction; clear H

              | [ |- _ = _ ] => reflexivity
              (* | [ |- ?kid1 <> ?kid2 ] => *)
              (*   ( (is_evar kid1; fill_unification_var_ineq kid1 kid2) *)
              (*     || (is_evar kid2; fill_unification_var_ineq kid2 kid1)); *)
              (*   unfold not; intro; congruence *)
              | [ |- _ $? _ = _ ] => eassumption
                                                                                    
              | [ H : ?m $+ (?k1,_) $? ?k2 = _ |- context [ _ $? _ ] ] =>
                (is_var k1 || is_var k2); idtac "destructing " k1 k2; destruct (k1 ==n k2); subst
              end.


          solve_concrete_maps.
          
          unfold add_key_perm.
          simpl.
          
          solve_concrete_maps.
          simpl.

          
           simpl.
          change (In chid empty_chs -> False) with (~ In chid empty_chs) in H6.
          rewrite not_find_in_iff in H6.
          solve_concrete_maps.
          repeat match goal with
            | [ H : _ $+ (?k1,_) $? ?k2 = None |- _ ] =>
              destruct (k1 ==n k2); subst; try discriminate; solve_concrete_maps
            end.

          clean_map_lookups.
          solve_concrete_maps.
          

          
          solve_concrete_maps. clean_map_lookups.
          
            ( (eapply IdealWorld.LStepRecv; solve [ solve_ideal_step_stuff ])
              || (eapply IdealWorld.LStepSend; solve [ solve_ideal_step_stuff ])).

      + do 3 eexists;
          repeat (apply conj).

        unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl;
          repeat (ideal_single_silent_multistep A);
          repeat (ideal_single_silent_multistep B).
        solve_refl.

        * eapply IdealWorld.LStepUser' with (u_id := B); simpl; eauto.
          simpl.
          eapply IdealWorld.LStepBindRecur; simpl.
          simpl; econstructor; eauto.

        * simpl. simpl_real_users_context. simpl_ideal_users_context.
          econstructor; eauto.
          simpl.
          clean_map_lookups.
          reflexivity.
          econstructor; simpl; eauto.
          econstructor; econstructor; eauto.
          intros; simpl in *.
          apply lookup_some_implies_in in H; simpl in H.
          split_ors; subst; try contradiction;
            repeat equality1; subst; try congruence; simpl in *; eauto.
          unfold add_key_perm, A__keys; eauto.
          change (In k_id KEYS -> False) with (~ In k_id KEYS) in H5.
          rewrite not_find_in_iff in H5.
          solve_concrete_maps.
          destruct (KID1 ==n k_id); subst; clean_map_lookups; try discriminate.
          rewrite lookup_empty_none; clean_map_lookups; trivial.

        * simpl_real_users_context.
          simpl_ideal_users_context.
          eapply Recd1'; simpl; eauto.

          unfold ideal_univ_recd1, mkiU; simpl.
          eapply ideal_univ_eq_fields_eq; maps_equal.

      + do 3 eexists;
          repeat (apply conj).

        unfold ideal_univ_start, ideal_univ_sent1, ideal_univ_recd1, ideal_univ_done, mkiU; simpl;
          repeat (ideal_single_silent_multistep A);
          repeat (ideal_single_silent_multistep B).
        solve_refl.

        * eapply IdealWorld.LStepUser' with (u_id := B); simpl; eauto.
          simpl.
          eapply IdealWorld.LStepBindRecur; eauto.

        * simpl.
          simpl_real_users_context. simpl_ideal_users_context.
          econstructor; eauto.
          simpl.
          clean_map_lookups.
          reflexivity.
          econstructor; simpl; eauto.
          econstructor; econstructor; eauto.
          intros; simpl in *.
          repeat (solve_action_matches1; simpl; eauto).
          unfold add_key_perm, A__keys; eauto.
          change (In k_id KEYS -> False) with (~ In k_id KEYS) in H5.
          rewrite not_find_in_iff in H5.
          solve_concrete_maps.
          destruct (KID1 ==n k_id); subst; clean_map_lookups; try discriminate.
          rewrite lookup_empty_none; clean_map_lookups; trivial.

        * simpl_real_users_context.
          simpl_ideal_users_context.
          eapply Recd1' with (chid := chid); simpl; eauto.

          ** unfold real_univ_recd1, mkrU; simpl.
             simpl_real_users_context.
             real_single_silent_multistep A.
             simpl_real_users_context.
             eapply Trc3Refl'; smash_universe.

          ** unfold  ideal_univ_recd1, mkiU; simpl.
             eapply ideal_univ_eq_fields_eq; maps_equal.
          
    - churn; simpl_real_users_context; clear_extra_adversary.

      Unshelve.
      all: apply tt.

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

  Lemma rsimpleping_honest_actions_safe :
    honest_actions_safe Unit RSimplePing.
  Proof.
    unfold honest_actions_safe; intros.
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

    Hint Resolve merge_perms_true_either_true.


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
      -> @lameAdv Unit tt adv
      -> RealWorld.key_heap adv = $0
      -> RealWorld.msg_heap adv = []
      -> RealWorld.c_heap adv = []
      -> adv_message_queue_ok U__r.(RealWorld.users) U__r.(RealWorld.all_ciphers) U__r.(RealWorld.all_keys) adv.(RealWorld.msg_heap)
      -> adv_no_honest_keys honestk adv.(RealWorld.key_heap)
      -> refines (@lameAdv Unit tt) U__r ideal_univ_start.
  Proof.
    exists RSimplePing; unfold simulates.
    intuition (subst; eauto).
  Qed.


End FeebleSimulates.
