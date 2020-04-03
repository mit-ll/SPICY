From Coq Require Import
     Classical
     List.

From KeyManagement Require Import
     MyPrelude
     Common
     Automation
     Maps
     Keys
     KeysTheory
     Messages
     MessagesTheory
     Tactics
     Simulation
     RealWorld
     AdversarySafety.

From protocols Require Import
     ExampleProtocols
     ProtocolAutomation
     SafeProtocol.

Set Implicit Arguments.
Import RealWorld RealWorldNotations.
Import SimulationAutomation.
Import AdversarySafety.Automation.

Inductive ty : Set :=
| TyDontCare
| TyMyCphr
| TyHonestKey
| TyMsgVerify (t : type)
| TyCMsg (t : type)
| TySentMsg (t : type)
| TyPair (t1 t2 : ty)
.

Record safe_typ :=
  { cmd_type : user_cmd_type ;
    cmd_val  : << cmd_type >> ;
    safetyTy : ty
  }.

Require Import Coq.Program.Equality Coq.Logic.JMeq.

Lemma safe_typ_eq :
  forall t1 t2 tv1 tv2 styp1 styp2,
    {| cmd_type := t1 ; cmd_val := tv1 ; safetyTy := styp1 |} =
    {| cmd_type := t2 ; cmd_val := tv2 ; safetyTy := styp2 |}
    -> t1 = t2
    /\ styp1 = styp2
    /\ JMeq tv1 tv2
.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Inductive HonestKey (context : list safe_typ) : key_identifier -> Prop :=
| HonestPermission : forall k tf,
    List.In {| cmd_type := Base Access ; cmd_val := (k,tf) ; safetyTy := TyHonestKey |} context
    -> HonestKey context k
| HonestPermissionOpaque : forall kp,
    List.In {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} context
    -> HonestKey context (fst kp)
| HonestKeyFromMsgVerify : forall (v : bool * message Access),
    List.In {| cmd_type := UPair (Base Bool) (Message Access) ;
               cmd_val := v ;
               safetyTy := TyMsgVerify Access |}
            context
    -> HonestKey context (fst (extractPermission (snd v)))
.

Fixpoint init_context (ks : list key_permission) : list safe_typ :=
  match ks with
  | []         => []
  | (kp :: kps) =>
    {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} :: init_context kps
  end.

Inductive syntactically_safe :
  list safe_typ -> forall t, user_cmd t -> ty -> Prop :=

| SafeBind : forall {t t'} context (cmd1 : user_cmd t') (cmd2 : <<t'>> -> user_cmd t) t1 t2,
    syntactically_safe context cmd1 t1
    -> (forall a, syntactically_safe ({| cmd_type := t' ; cmd_val := a ; safetyTy := t1 |} :: context) (cmd2 a) t2)
    -> syntactically_safe context (Bind cmd1 cmd2) t2

| SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to,
    HonestKey context k__enc
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id)
    -> syntactically_safe context (SignEncrypt k__sign k__enc msg_to msg) (TyCMsg t)

| SafeSign : forall context {t} (msg : message t) k msg_to,
    (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id /\ kp = false)
    -> syntactically_safe context (Sign k msg_to msg) (TyCMsg t)

| SafeRecv : forall context t pat,
    (exists k, pat = Signed k true /\ HonestKey context k)
    \/ (exists k__sign k__enc, pat = SignedEncrypted k__sign k__enc true /\ HonestKey context k__sign)
    -> syntactically_safe context (@Recv t pat) (TyCMsg t)

| SafeSend : forall context t (msg : crypto t) msg_to,
    ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySentMsg t |} context
    -> List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyCMsg t |} context
    -> syntactically_safe context (Send msg_to msg) (TySentMsg t)

| SafeReturn : forall {A} context (a : << A >>),
    syntactically_safe context (Return a) TyDontCare
| SafeGen : forall context,
    syntactically_safe context Gen TyDontCare
| SafeDecrypt : forall context t (c : crypto t),
    syntactically_safe context (Decrypt c) TyDontCare (* add to things to care about with keys in msg *)
| SafeVerify : forall context t k c,
    syntactically_safe context (@Verify t k c) (TyMsgVerify t)
| SafeGenerateSymKey : forall context usage,
    syntactically_safe context (GenerateSymKey usage) TyHonestKey
| SafeGenerateAsymKey : forall context usage,
    syntactically_safe context (GenerateAsymKey usage) TyHonestKey
.

Section TestProto.

  Notation KID1 := 0.
  Notation KID2 := 1.

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
  
End TestProto.

Definition U_syntactically_safe {A B} (U : RealWorld.universe A B) :=
  forall u_id u,
    U.(users) $? u_id = Some u
    -> forall ctx,
      ctx =  init_context (elements u.(key_heap))
      -> exists t,
        syntactically_safe ctx u.(protocol) t.

Lemma share_secret_synctactically_safe :
  U_syntactically_safe (real_univ_start startAdv).
Proof.
  unfold U_syntactically_safe, real_univ_start, mkrU, mkrUsr, A__keys, B__keys; simpl; 
    intros; subst.

  destruct (u_id ==n A); destruct (u_id ==n B); subst; clean_map_lookups; simpl.

  - eexists.

    econstructor.
    econstructor.

    intros; econstructor; simpl.
    econstructor; simpl.

    intros; destruct (fst a ==n k_id); subst; clean_map_lookups; eauto.
    econstructor; simpl; eauto.
    eapply HonestPermissionOpaque; eauto.

    econstructor; simpl.
    econstructor; simpl; eauto.
    unfold not; intros H; split_ors; invert H.

    econstructor; simpl.
    econstructor; simpl; eauto.
    right; (do 2 eexists); split; eauto.
    econstructor; eauto.

    intros; econstructor; simpl.
    econstructor; simpl; simpl.

    intros; econstructor.

  - eexists.

    econstructor.
    econstructor.

    left; eauto.

    intros; econstructor; simpl.
    econstructor; simpl.

    intros; econstructor; simpl.
    econstructor; simpl. 

    intros; econstructor; simpl.
    econstructor; simpl; simpl.

    intros; econstructor; simpl.
    econstructor; simpl; simpl.

    intros; econstructor; simpl.
    econstructor; simpl; simpl; eauto.
    
    intros; econstructor; simpl.
    econstructor; simpl; simpl; eauto.

    eapply HonestKeyFromMsgVerify; eauto.

    intros; clean_map_lookups.

    intros; econstructor; simpl.
    econstructor; simpl; simpl; eauto.
    unfold not; intros; split_ors; invert H.

    intros; econstructor; simpl.
Qed.


(* Definition vars_coherent {t}(u_id : user_id) (u : user_data t) (cphrs : ciphers) (s : proto_summary) := *)
(*   s.(me) = u_id *)
(*   /\ s.(hon_keys) = u.(key_heap) *)
(*   /\ s.(sents) = u.(sent_nons) *)
(*   /\ s.(cnon) = u.(cur_nonce) *)
(*   /\ (forall cid c, s.(cs) $? cid = Some c -> cphrs $? cid = Some c). *)

Hint Constructors
     HonestKey
     syntactically_safe
     : core.

Lemma HonestKey_split :
  forall t (tv : <<t>>) styp k context key_rec,
    key_rec = {| cmd_type := t ; cmd_val := tv ; safetyTy := styp |}
    -> HonestKey (key_rec :: context) k
    -> (exists tf, key_rec = {| cmd_type := Base Access ; cmd_val := (k,tf) ; safetyTy := TyHonestKey |})
    \/ (exists kp, key_rec = {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} /\ k = fst kp)
    \/ (exists v, key_rec = {| cmd_type := UPair (Base Bool) (Message Access) ;
                         cmd_val := v ;
                         safetyTy := TyMsgVerify Access |} /\ k = fst (extractPermission (snd v)))
    \/ HonestKey context k
.
Proof.
  intros; subst.
  invert H0; simpl in *; split_ors; eauto 8.
Qed.

Lemma HonestKey_skip :
  forall t (tv : <<t>>) styp k context key_rec,
    HonestKey context k
    -> key_rec = {| cmd_type := t ; cmd_val := tv ; safetyTy := styp |}
    -> HonestKey (key_rec :: context) k
.
Proof.
  intros; subst.
  invert H; eauto.
Qed.

Hint Resolve HonestKey_skip HonestKey_split : core.

Lemma message_no_adv_private_merge :
  forall honestk t (msg : crypto t) cs,
    message_no_adv_private honestk cs msg
    -> honestk $k++ findKeysCrypto cs msg = honestk.
Proof.
  intros.
  unfold message_no_adv_private in *.
  maps_equal.
  cases (findKeysCrypto cs msg $? y); solve_perm_merges; eauto.
  specialize (H _ _ Heq); split_ands; subst; clean_map_lookups; eauto.
  specialize (H _ _ Heq); split_ands; clean_map_lookups; eauto.
Qed.

Lemma message_only_honest_merge :
  forall honestk t (msg : message t),
    (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> honestk $? k_id = Some true)
    -> honestk $k++ findKeysMessage msg = honestk.
Proof.
  intros.
  maps_equal.
  cases (findKeysMessage msg $? y); solve_perm_merges; eauto.
  specialize (H _ _ Heq); split_ands; subst; clean_map_lookups; eauto.
  specialize (H _ _ Heq); split_ands; clean_map_lookups; eauto.
Qed.

Lemma honest_keys_perservation' :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cphrs cphrs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd honestk,
      
      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> honestk = findUserKeys usrs
      -> message_queue_ok honestk cphrs qmsgs gks
      -> encrypted_ciphers_ok honestk cphrs gks
      -> honest_users_only_honest_keys usrs
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmdc cmdc
      -> (forall r, cmdc <> Return r)
      -> forall ctx t honestk' cmd',
          (forall kid, HonestKey ctx kid <-> honestk $? kid = Some true)
          -> syntactically_safe ctx cmdc t
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmd';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |}))
          -> exists ctx' t',
              (forall kid, HonestKey ctx' kid <-> honestk' $? kid = Some true)
              /\ syntactically_safe ctx' cmdc' t'
.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst; clean_context;
      autorewrite with find_user_keys;
      try solve [
            match goal with
            | [ H : nextAction _ _ |- _ ] => apply nextAction_couldBe in H
            end; (contradiction || eauto)
          ].

  - (do 2 eexists).
    invert H33; split_ands.
    
    assert (msg_pattern_safe (findUserKeys usrs') pat) by
        (invert H40; split_ors; split_ex; subst; econstructor; generalize (H39 x); intros IFF; destruct IFF; eauto).
    assert (msg_honestly_signed (findUserKeys usrs') cphrs' msg = true) by
        (eauto using accepted_safe_msg_pattern_honestly_signed).

    pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ H4); split_ex.
    pose proof (msg_honestly_signed_signing_key_honest _ _ _ H4 H5).
    specialize (H1 _ H5); split_ands.
    specialize (H9 H8); split_ands.
    rewrite message_no_adv_private_merge; eauto.
    
  - (do 2 eexists).
    unfold honest_users_only_honest_keys in *.
    specialize (H36 _ _ H37 _ _ H3); simpl in *.
    encrypted_ciphers_prop.
    rewrite message_only_honest_merge; eauto.

  - match goal with | [ H : syntactically_safe _ _ _ |- _ ] => invert H end.
    (do 2 eexists).
    split.
    + intros.
      match goal with
      | [ |- HonestKey ?ectx _ <-> _ ] =>
        unify ectx ({| cmd_type := Base Access ; cmd_val := (k_id,true) ; safetyTy := TyHonestKey |} :: ctx)
      end.
      destruct (kid ==n k_id); subst; split; swap 1 2; intros; clean_map_lookups; eauto.
      * eapply HonestKey_split with (t := Base Access) in H0; auto.
        split_ors; split_ex; eauto.

        apply safe_typ_eq in H0; split_ands.
        invert H2.
        invert H4; contradiction.
        
        apply safe_typ_eq in H0; split_ands.
        invert H3; simpl in *; contradiction.

        specialize (H35 kid); destruct H35; eauto.

      * specialize (H35 kid); destruct H35.
        specialize_simply; eauto.
        eapply HonestKey_skip with (t := Base Access); eauto.
        
    + econstructor.      
      
  - match goal with | [ H : syntactically_safe _ _ _ |- _ ] => invert H end.
    (do 2 eexists).
    split; eauto.

    intros.
    match goal with
    | [ |- HonestKey ?ectx _ <-> _ ] =>
      unify ectx ({| cmd_type := Base Access ; cmd_val := (k_id,true) ; safetyTy := TyHonestKey |} :: ctx)
    end.
    destruct (kid ==n k_id); subst; split; swap 1 2; intros; clean_map_lookups; eauto.
    * eapply HonestKey_split with (t := Base Access) in H0; auto.
      split_ors; split_ex; eauto.

      apply safe_typ_eq in H0; split_ands.
      invert H2.
      invert H4; contradiction.
        
      apply safe_typ_eq in H0; split_ands.
      invert H3; simpl in *; contradiction.

      specialize (H35 kid); destruct H35; eauto.

    * specialize (H35 kid); destruct H35.
      specialize_simply; eauto.
      eapply HonestKey_skip with (t := Base Access); eauto.
Qed.

Lemma honest_keys_perservation :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cphrs cphrs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd honestk,
      
      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> honestk = findUserKeys usrs
      -> message_queue_ok honestk cphrs qmsgs gks
      -> encrypted_ciphers_ok honestk cphrs gks
      -> honest_users_only_honest_keys usrs
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmd cmdc
      -> (forall r, cmdc <> Return r)
      -> forall ctx t honestk' cmd',
          (forall kid, HonestKey ctx kid <-> honestk $? kid = Some true)
          -> syntactically_safe ctx cmd t
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmd';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |}))
          -> exists ctx' t',
              (forall kid, HonestKey ctx' kid <-> honestk' $? kid = Some true)
              /\ syntactically_safe ctx' cmd' t'
.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst;
      autorewrite with find_user_keys;
      clean_context.

  - admit.
  - admit.
  - 
  





Lemma honestKey_implies_honestk :
  forall ctx honestk k_id,
    HonestKey ctx k_id
    -> honestk $? k_id = Some true.
Proof.
Admitted.

Hint Resolve honestKey_implies_honestk.

Lemma syntactically_safe_implies_next_cmd_safe'' :
  forall t (p : user_cmd t) ctx styp honestk u_id cs froms sents,
    syntactically_safe ctx p styp
    -> next_cmd_safe honestk cs u_id froms sents p.
Proof.
  induction 1; unfold next_cmd_safe; intros;
    try solve [ 
          match goal with
          | [ H : nextAction _ _ |- _ ] => invert H
          end; eauto ].

  - invert H2.
    specialize (IHsyntactically_safe _ _ H6); eauto.

  - match goal with
    | [ H : nextAction _ _ |- _ ] => invert H
    end; eauto.

    intros * FKM; specialize (H _ _ FKM); split_ands; split; eauto.

  - match goal with
    | [ H : nextAction _ _ |- _ ] => invert H
    end; split_ors; split_ex; subst; econstructor; eauto.

  - match goal with
    | [ H : nextAction _ _ |- _ ] => invert H
    end.
    admit.

Admitted.



Lemma syntactically_safe_implies_next_cmd_safe'' :
  forall {t} (p : user_cmd t) sum v sum' honestk froms cphrs,
    syntactically_safe sum p v sum'
    -> (forall cid c, sum.(cs) $? cid = Some c -> cphrs $? cid = Some c)
    -> (forall k v, sum.(hon_keys) $? k = Some v -> honestk $? k = Some v \/ honestk $? k = Some true )
    -> next_cmd_safe honestk cphrs sum.(me) froms sum.(sents) p.
Proof.
  induction 1; unfold next_cmd_safe; intros;
    try solve [ 
          match goal with
          | [ H : nextAction _ _ |- _ ] => invert H
          end; eauto ].

  - invert H3.
    eapply IHsyntactically_safe1 in H7; eauto.
  - invert H7.
    apply H6 in H0; split.
    split_ors; trivial.
    intros * FKM; apply H2 in FKM.
    apply H6 in FKM; split_ors; eauto.
  - invert H6; intros.
    specialize (H1 _ _ H2); split_ands; split; eauto.
    specialize (H5 _ _ H1); split_ors; eauto.
  - invert H4; split_ors; subst; econstructor; eauto.
    apply H3 in H0; split_ors; eauto.
    apply H3 in H0; split_ors; eauto.
  - invert H8.
    apply H6 in H0.
    apply H7 in H2.
    unfold msg_honestly_signed, msg_to_this_user, msgCiphersSignedOk; simpl;
      unfold honest_keyb;
      context_map_rewrites.
    split.
    split_ors; context_map_rewrites; trivial.

    destruct (cipher_to_user c ==n cipher_to_user c); subst; try contradiction; repeat simple apply conj; eauto.
    econstructor; eauto.

    unfold msg_honestly_signed, msg_signing_key, honest_keyb.
    context_map_rewrites; split_ors; context_map_rewrites; eauto.
    do 2 eexists; eauto.
Qed.

Lemma syntactically_safe_implies_next_cmd_safe' :
  forall {t} (p : user_cmd t) pv sum sum' uid ks honestk cphrs all_cphrs sumsents froms n,
    syntactically_safe sum p pv sum'
    -> sum = {| me := uid ;
               hon_keys := ks ;
               sents := sumsents ;
               cnon := n ;
               cs := cphrs |}
    -> (forall k v, ks $? k = Some v -> honestk $? k = Some v \/ honestk $? k = Some true )
    -> (forall k v, cphrs $? k = Some v -> all_cphrs $? k = Some v)
    -> next_cmd_safe honestk all_cphrs uid froms sumsents p.
Proof.
  intros.
  destruct sum.
  invert H0.
  eapply syntactically_safe_implies_next_cmd_safe'' in H; eauto.
Qed.

Lemma findUserKeys_has_user_key_or_better :
  forall {A} (usrs : honest_users A) u_id u_d ks k kp,
    usrs $? u_id = Some u_d
    -> ks = key_heap u_d
    -> ks $? k = Some kp
    -> findUserKeys usrs $? k = Some kp
      \/ findUserKeys usrs $? k = Some true.
Proof.
  intros.
  induction usrs using map_induction_bis; intros; Equal_eq;
    subst; clean_map_lookups; eauto;
      unfold findUserKeys.

  rewrite fold_add; auto 2.
  rewrite !findUserKeys_notation.
  destruct (x ==n u_id); subst; clean_map_lookups.
  - cases (findUserKeys usrs $? k).
    destruct b; [right | left]; solve_perm_merges.
    left; solve_perm_merges.
    
  - split_ors; try solve [ right; solve_perm_merges ].
    cases (key_heap e $? k).
    destruct b; [right | left]; solve_perm_merges.
    left; solve_perm_merges.
Qed.

(*
 * If we can prove that some simple syntactic symbolic execution implies
 * the honest_cmds_safe predicate...
 *)
Lemma syntactically_safe_implies_next_cmd_safe :
  forall {A B} (U : universe A B),
    U_syntactically_safe U
    -> honest_cmds_safe U.
Proof.
  unfold U_syntactically_safe, honest_cmds_safe; intros.
  generalize (H _ _ H1 _ eq_refl); intros.
  split_ex; subst.
  eapply syntactically_safe_implies_next_cmd_safe'.
  exact H2.
  unfold sum_init; reflexivity.
  intros * KH; eapply findUserKeys_has_user_key_or_better in KH; eauto.

  intros; eauto.
Qed.

(* Definition rstepSilent {A B} (U U' : universe A B) := *)
(*   step_universe U Silent U'. *)

(* Hint Extern 1 (_ $k++ _ $? _ = Some true) => solve [ solve_perm_merges ]. *)
(* Ltac synctactically_safe_solver := *)
(*   repeat *)
(*     match goal with *)
(*     | [ ARG : findKeysMessage _ $? _ = Some _ , H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _) |- _ ] => *)
(*       specialize (H _ _ ARG) *)
(*     | [ H : ?honk $? ?k = Some true |- ?honk $k++ _ $? ?k = Some true ] => solve_perm_merges *)
(*     | [ |- _ /\ _ ] => split_ands; split *)
(*     | [ |- _ \/ _ ] => subst; split_ors *)
(*     end. *)

(* Lemma next_key_add_ne : *)
(*   forall V (v : V) k m, *)
(*     k <> next_key (m $+ (k,v)). *)
(* Proof. *)
(*   intros; *)
(*     unfold not; intros CONTRA; *)
(*       apply next_key_not_in in CONTRA; clean_map_lookups; discriminate. *)
(* Qed. *)

(* Hint Resolve next_key_add_ne. *)

Lemma synctactically_safe_preservation_non_stepped_user :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cphrs cphrs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd cmd',
      
      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmd cmdc
      -> (forall r, cmdc <> Return r)
      -> (exists f, cmd = f cmdc /\ cmd' = f cmdc')
      -> forall pv sum' sumcphrs,
          syntactically_safe {| me := u_id ;
                                hon_keys := ks ;
                                sents := sents ;
                                cnon := cur_n ;
                                cs := sumcphrs |} cmd pv sum'
          -> (forall uid ud cphrs,
                usrs $? uid = Some ud
                -> forall sum,
                  sum = {| me := uid; hon_keys := ud.(key_heap); sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := cphrs |}
                  -> exists sum' pv,
                    syntactically_safe sum ud.(protocol) pv sum')
          -> forall usrs'' uid ud sum1,
              usrs'' = usrs' $+ (u_id,
                                 {| key_heap := ks';
                                    protocol := cmd';
                                    msg_heap := qmsgs';
                                    c_heap := mycs';
                                    from_nons := froms';
                                    sent_nons := sents';
                                    cur_nonce := cur_n' |})
              -> uid <> u_id
              -> usrs'' $? uid = Some ud
              -> sum1 = {| me := uid; hon_keys := ud.(key_heap); sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := sum'.(cs) |}
              -> exists sum1' pv1,
                  syntactically_safe sum1 ud.(protocol) pv1 sum1'
.
Proof.
  induct 1; inversion 1; inversion 1;
    intros; subst; clean_map_lookups; clean_context;
      simpl in *;
      eauto.

  - apply nextAction_couldBe in H26; contradiction.
  - destruct (rec_u_id ==n uid); subst; clean_map_lookups; simpl; eauto.
Qed.

Lemma synctactically_safe_preservation_non_stepped_user' :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cphrs cphrs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd cmd',
      
      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmd cmdc
      -> (forall r, cmdc <> Return r)
      -> (exists f, cmd = f cmdc /\ cmd' = f cmdc')
      -> forall pv sum' sumcphrs,
          syntactically_safe {| me := u_id ;
                                hon_keys := ks ;
                                sents := sents ;
                                cnon := cur_n ;
                                cs := sumcphrs |} cmd pv sum'
          -> (forall uid ud cphrs,
                usrs $? uid = Some ud
                -> forall sum,
                  sum = {| me := uid; hon_keys := ud.(key_heap); sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := cphrs |}
                  -> exists sum' pv,
                    syntactically_safe sum ud.(protocol) pv sum')
          -> forall usrs'',
              usrs'' = usrs' $+ (u_id,
                                 {| key_heap := ks';
                                    protocol := cmd';
                                    msg_heap := qmsgs';
                                    c_heap := mycs';
                                    from_nons := froms';
                                    sent_nons := sents';
                                    cur_nonce := cur_n' |})
              -> honest_cmds_safe {| users := usrs'' ;
                                    adversary := adv' ;
                                    all_keys := gks' ;
                                    all_ciphers := cphrs' |}
.
Proof.
  induct 1; inversion 1; inversion 1;
    intros; subst; clean_map_lookups; clean_context;
      unfold honest_cmds_safe;
      intros;
      simpl in *;
      subst;
      autorewrite with find_user_keys;
      try solve [ destruct (u_id0 ==n u_id); subst; clean_map_lookups; eauto ].

  - admit.
  - admit.
  - destruct (u_id0 ==n u_id); subst; clean_map_lookups; simpl; eauto.
    + admit.
    + specialize (H29 _ _ _ H0 _ eq_refl).


  - apply nextAction_couldBe in H26; contradiction.
  - destruct (rec_u_id ==n uid); subst; clean_map_lookups; simpl; eauto.
Qed.
Lemma step_na_not_return :
  forall {A B C D} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cphrs cphrs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) (cmd__n : user_cmd D) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' u_id,

      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> nextAction cmd cmd__n
      -> suid = Some u_id
      -> (forall r, cmd__n <> Return r)
      -> forall pv sum' sumcphrs,
          syntactically_safe {| me := u_id ;
                                hon_keys := ks ;
                                sents := sents ;
                                cnon := cur_n ;
                                cs := sumcphrs |} cmd pv sum'


          -> exists f cmd__n',
            step_user lbl suid
                      (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd__n)
                      (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd__n')
            /\ cmd = f cmd__n
            /\ cmd' = f cmd__n'
            /\ forall lbl1 suid1 (usrs1 usrs1' : honest_users A) (adv1 adv1' : user_data B)
                cs1 cs1' gks1 gks1'
                ks1 ks1' qmsgs1 qmsgs1' mycs1 mycs1' (cmd__n'' : user_cmd D)
                froms1 froms1' sents1 sents1' cur_n1 cur_n1',

                step_user lbl1 suid1
                          (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, cmd__n)
                          (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', cmd__n'')
                -> step_user lbl1 suid1
                            (usrs1, adv1, cs1, gks1, ks1, qmsgs1, mycs1, froms1, sents1, cur_n1, f cmd__n)
                            (usrs1', adv1', cs1', gks1', ks1', qmsgs1', mycs1', froms1', sents1', cur_n1', f cmd__n'').
Proof.
  Hint Constructors step_user.

  induction 1; inversion 1; inversion 1; invert 1; intros.

  - eapply IHstep_user in H28; eauto.
    split_ex.
    exists (fun CD => x <- x CD; cmd2 x).
    eexists; subst; split; eauto.
  - invert H27.
    unfold not in *; exfalso; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
  - exists (fun x => x); eexists; repeat simple apply conj; swap 1 3; eauto.
Qed.



Require Import Coq.Program.Equality.

Lemma synctactically_safe_preservation_stepped_user :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cphrs cphrs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd cmd',
      
      bd = (usrs, adv, cphrs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cphrs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap   := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmd cmdc
      -> (forall r, cmdc <> Return r)
      -> (exists f, cmd = f cmdc /\ cmd' = f cmdc')
      -> forall pv sum' sumcphrs,
          syntactically_safe {| me := u_id ;
                                hon_keys := ks ;
                                sents := sents ;
                                cnon := cur_n ;
                                cs := sumcphrs |} cmd pv sum'
          -> (forall uid ud cphrs,
                usrs $? uid = Some ud
                -> forall sum,
                  sum = {| me := uid; hon_keys := ud.(key_heap); sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := cphrs |}
                  -> exists sum' pv,
                    syntactically_safe sum ud.(protocol) pv sum')
          -> forall usrs'' uid ud sum1,
              usrs'' = usrs' $+ (u_id,
                                 {| key_heap := ks';
                                    protocol := cmd';
                                    msg_heap := qmsgs';
                                    c_heap := mycs';
                                    from_nons := froms';
                                    sent_nons := sents';
                                    cur_nonce := cur_n' |})
              -> uid = u_id
              -> usrs'' $? uid = Some ud
              -> sum1 = {| me := uid; hon_keys := ud.(key_heap); sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := sum'.(cs) |}
              -> exists sum1' pv1,
                  syntactically_safe sum1 ud.(protocol) pv1 sum1'
.
Proof.
  intros *; intro STEP.
  dependent induction STEP; inversion 1; inversion 1;
    intros; subst; clean_map_lookups; clean_context;
      simpl in *;
      try solve [ (do 2 eexists); econstructor; eauto ] .

  - admit.
  - admit.
  - 

  - apply nextAction_couldBe in H26; contradiction.
  - destruct (rec_u_id ==n uid); subst; clean_map_lookups; simpl; eauto.
Qed.



Lemma synctactically_safe_preservation :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'

    -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
        u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmdc cmdc' : user_cmd C) cmd cmd',
      
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmdc)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmdc')
      -> suid = Some u_id
      -> usrs $? u_id = Some {| key_heap := ks;
                               protocol := cmd;
                               msg_heap := qmsgs;
                               c_heap := mycs;
                               from_nons := froms;
                               sent_nons := sents;
                               cur_nonce := cur_n |}
      -> nextAction cmd cmdc
      -> (forall r, cmdc <> Return r)
      -> (exists f, cmd = f cmdc /\ cmd' = f cmdc')
      -> (forall uid ud,
            usrs $? uid = Some ud
            -> forall sum,
              sum = {| me := uid; hon_keys := findUserKeys usrs; sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := cs |}
              -> exists sum',
                syntactically_safe sum ud.(protocol) sum')
      -> forall usrs'' uid ud sum,
          usrs'' = usrs' $+ (u_id,
                             {| key_heap := ks';
                                protocol := cmd';
                                msg_heap := qmsgs';
                                c_heap := mycs';
                                from_nons := froms';
                                sent_nons := sents';
                                cur_nonce := cur_n' |})
          -> usrs'' $? uid = Some ud
          -> sum = {| me := uid; hon_keys := findUserKeys usrs''; sents := ud.(sent_nons); cnon := ud.(cur_nonce); cs := cs' |}
          -> exists sum',
              syntactically_safe sum ud.(protocol) sum'
.
Proof.
  induct 1; inversion 1; inversion 1;
    intros; subst; clean_context.
  

  - admit.
  - apply nextAction_couldBe in H25; contradiction.
  - destruct (u_id0 ==n uid); subst;
      autorewrite with find_user_keys; clean_map_lookups; simpl in *; eauto.

    specialize (H28 _ _ H24 _ eq_refl); simpl in H28.

    
    (*
     * And that the syntactic safety predicate is preserved through any
     * real world step
     *)
    Lemma syntactically_safe_preservation :
      forall {A B} (U U': universe A B) b,
        U_syntactically_safe U
        -> lameAdv b U.(adversary)
        -> forall lbl,
            step_universe U lbl U'
            -> U_syntactically_safe U'.
    Proof.
      unfold U_syntactically_safe; intros; subst; simpl in *.
      invert H1; unfold build_data_step, buildUniverse in *; simpl in *.
      -  admit.
      - unfold lameAdv in H0; rewrite H0 in H3; invert H3.

    Admitted.

    Lemma syntactically_safe_preservation :
      forall {A B} (U U': universe A B),
        U_syntactically_safe U
        -> rstepSilent ^* U U'
        -> U_syntactically_safe U'.
    Proof.
    Admitted



         (* Inductive syntactically_safe : *)
         (*   forall {t}, typing_context -> user_cmd t -> ty -> Prop := *)

         (* | SafeBind : forall {t t'} context (cmd1 : user_cmd t') (cmd2 : <<t'>> -> user_cmd t) t1 t2, *)
         (*     syntactically_safe context cmd1 t1 *)
         (*     -> forall a, *)
         (*       (* need to augment context here, but with what? *) *)
         (*       syntactically_safe (addVar context (Pr t' a t1)) (cmd2 a) t2 *)
         (*       -> syntactically_safe context (Bind cmd1 cmd2) t2 *)

         (* | SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to, *)

         (*     context.(vars) $? k__enc = Some HonKey *)
         (*     -> match msg with *)
         (*       | Permission k => context.(vars) $? fst k = Some (BPair HonKey BBool) *)
         (*       | message.Content _ => True *)
         (*       | MsgPair m1 m2 => False *)
         (*       end *)
         (*     -> syntactically_safe context (SignEncrypt k__sign k__enc msg_to msg) MyCphr *)

         (* | SafeSign : forall context {t} (msg : message t) k msg_to, *)
         
         (*     match msg with *)
         (*     | Permission k => context.(vars) $? fst k = Some HonKey /\ snd k = false *)
         (*     | message.Content _ => True *)
         (*     | MsgPair m1 m2 => False *)
         (*     end *)
         (*     -> syntactically_safe context (Sign k msg_to msg) MyCphr *)

         (* (* split into two rules? *) *)
         (* | SafeRecv : forall context t pat, *)
         (*     (exists k, pat = Signed k true /\ context.(vars) $? k = Some HonKey) *)
         (*     \/ (exists k__sign k__enc, pat = SignedEncrypted k__sign k__enc true /\ context.(vars) $? k__sign = Some HonKey) *)
         (*     -> syntactically_safe context (@Recv t pat) CText *)

         (* | SafeSend : forall context t (msg : crypto t) msg_to c_id, *)
         (*       msg = SignedCiphertext c_id *)
         (*       -> context.(vars) $? c_id = Some MyCphr *)
         (*       (* need to add check about only sending once *) *)
         (*       -> syntactically_safe context (Send msg_to msg) BUnit *)

         (* | SafeReturn : forall {A} context (a : << A >>), *)
         (*     syntactically_safe context (Return a) BNat *)
         (* | SafeGen : forall context, *)
         (*     syntactically_safe context Gen BNat *)
         (* | SafeDecrypt : forall context t (c : crypto t), *)
         (*     syntactically_safe context (Decrypt c) Msg *)
         (* | SafeVerify : forall context t k c, *)
         (*     syntactically_safe context (@Verify t k c) (BPair BBool Msg) *)
         (* | SafeGenerateSymKey : forall context usage, *)
         (*     syntactically_safe context (GenerateSymKey usage) (BPair HonKey BBool) *)
         (* | SafeGenerateAsymKey : forall context usage, *)
         (*     syntactically_safe context (GenerateAsymKey usage) (BPair HonKey BBool) *)
         (* . *)

         (* Record proto_summary := *)
         (*   { me : user_id ;  *)
         (*     hon_keys : key_perms ; *)
         (*     sents : sent_nonces ; *)
         (*     cnon : nat ; *)
         (*     cs : ciphers *)
         (*   }. *)

         (* Inductive syntactically_safe : *)
         (*   forall {t}, proto_summary -> user_cmd t -> <<t>> -> proto_summary -> Prop := *)

         (* | SafeBind : forall {r A} (cmd1 : user_cmd r) (cmd2 : <<r>> -> user_cmd A) cmd1_val cmd2_val sum1 sum2, *)
         (*     syntactically_safe sum1 cmd1 cmd1_val sum2 *)
         (*     -> forall sum3, *)
         (*       syntactically_safe sum2 (cmd2 cmd1_val) cmd2_val sum3 *)
         (*       -> syntactically_safe sum1 (Bind cmd1 cmd2) cmd2_val sum3 *)

         (* | SafeEncrypt : forall {t} (msg : message t) k__sign k__enc msg_to c_id c sum sum', *)
         (*     ~ In c_id sum.(cs) *)
         (*     -> In k__enc sum.(hon_keys) *)
         (*     (* -> In k__sign sum.(hon_keys) *) *)
         (*     -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> In k_id sum.(hon_keys)) *)
         (*     -> c = SigEncCipher k__sign k__enc msg_to (Some sum.(me), sum.(cnon)) msg *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys); *)
         (*                 sents := sum.(sents); *)
         (*                 cnon := 1 + sum.(cnon) ; *)
         (*                 cs := sum.(cs) $+ (c_id,c) |} *)
         (*     -> syntactically_safe sum (SignEncrypt k__sign k__enc msg_to msg) (SignedCiphertext c_id) sum' *)

         (* | SafeSign : forall {t} (msg : message t) k msg_to c_id c sum sum', *)
         (*     ~ In c_id sum.(cs) *)
         (*     (* -> In k sum.(hon_keys) *) *)
         (*     -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> In k_id sum.(hon_keys) /\ kp = false) *)
         (*     -> c = SigCipher k msg_to (Some sum.(me), sum.(cnon)) msg *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys); *)
         (*                 sents := sum.(sents); *)
         (*                 cnon := 1 + sum.(cnon) ; *)
         (*                 cs := sum.(cs) $+ (c_id,c) |} *)
         (*     -> syntactically_safe sum (Sign k msg_to msg) (SignedCiphertext c_id) sum' *)

         (* (* split into two rules? *) *)
         (* | SafeRecv : forall t pat sum sum', *)
         (*     (exists k, pat = Signed k true /\ In k sum.(hon_keys)) *)
         (*     \/ (exists k__sign k__enc, pat = SignedEncrypted k__sign k__enc true /\ In k__sign sum.(hon_keys)) *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys); *)
         (*                 sents := sum.(sents) ; *)
         (*                 cnon := sum.(cnon) ; *)
         (*                 cs := sum.(cs) |} *)
         (*      -> forall c, *)
         (*         (* (forall k kp, findKeysCrypto sum.(cs) c $? k = Some kp -> In k sum.(hon_keys)) *) *)
         (*          syntactically_safe sum (@Recv t pat) c sum *)

         (* | SafeSend : forall t (msg : crypto t) msg_to c_id c sum sum', *)
         (*     msg = SignedCiphertext c_id *)
         (*     -> sum.(cs) $? c_id = Some c *)
         (*     -> cipher_to_user c = msg_to *)
         (*     -> In (cipher_signing_key c) sum.(hon_keys) *)
         (*     (* -> msg_to = sum.(me) *) *)
         (*     (* -> (forall k kp, findKeysCrypto sum.(cs) msg $? k = Some kp -> sum.(hon_keys) $? k = Some true) *) *)
         (*     (* replay stuff *) *)
         (*     -> fst (cipher_nonce c) = Some sum.(me) *)
         (*     -> ~ List.In (cipher_nonce c) sum.(sents) *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys); *)
         (*                 sents := (Some sum.(me), sum.(cnon)) :: sum.(sents) ; *)
         (*                 cnon := sum.(cnon) ; *)
         (*                 cs := sum.(cs) |} *)
         (*     -> syntactically_safe sum (Send msg_to msg) tt sum' *)

         (* | SafeReturn : forall {A} (a : << A >>) sum, *)
         (*     syntactically_safe sum (Return a) a sum *)
         (* | SafeGen : forall sum n, *)
         (*     syntactically_safe sum Gen n sum *)
         (* | SafeDecrypt : forall t (c : crypto t) msg sum, *)
         (*     syntactically_safe sum (Decrypt c) msg sum *)
         (* | SafeVerify : forall t k c sum msg, *)
         (*     syntactically_safe sum (@Verify t k c) (true,msg) sum *)
         (* | SafeGenerateSymKey : forall k_id usage sum sum', *)
         (*     ~ In k_id sum.(hon_keys) *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys) $+ (k_id, true) ; *)
         (*                 sents := sum.(sents) ; *)
         (*                 cnon := sum.(cnon) ; *)
         (*                 cs := sum.(cs) |} *)
         (*     -> syntactically_safe sum (GenerateSymKey usage) (k_id,true) sum' *)
         (* | SafeGenerateAsymKey : forall k_id usage sum sum', *)
         (*     ~ In k_id sum.(hon_keys) *)
         (*     -> sum' = {| me := sum.(me); *)
         (*                 hon_keys := sum.(hon_keys) $+ (k_id, true) ; *)
         (*                 sents := sum.(sents) ; *)
         (*                 cnon := sum.(cnon) ; *)
         (*                 cs := sum.(cs) |} *)
         (*     -> syntactically_safe sum (GenerateAsymKey usage) (k_id, true) sum' *)
         (* . *)

         
