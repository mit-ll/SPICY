(* DISTRIBUTION STATEMENT A. Approved for public release. Distribution is unlimited.
 *
 * This material is based upon work supported by the Department of the Air Force under Air Force
 * Contract No. FA8702-15-D-0001. Any opinions, findings, conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily reflect the views of the
 * Department of the Air Force.
 *
 * © 2020 Massachusetts Institute of Technology.
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
     SafeProtocol
     RealWorldStepLemmas
.

Set Implicit Arguments.
Import RealWorld RealWorldNotations.
Import SimulationAutomation.
Import AdversarySafety.Automation.

Inductive ty : Set :=
| TyDontCare
| TyHonestKey
| TyMyCphr (uid : user_id) (k_id : key_identifier)
| TyRecvMsg
| TyRecvCphr
| TySent
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
| HonestKeyFromMsgVerify : forall (v : bool * message Access),
    List.In {| cmd_type := UPair (Base Bool) (Message Access) ;
               cmd_val := v ;
               safetyTy := TyRecvMsg |}
            context
    -> HonestKey context (fst (extractPermission (snd v)))
.

Fixpoint init_context (ks : list key_permission) : list safe_typ :=
  match ks with
  | []         => []
  | (kp :: kps) =>
    {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} :: init_context kps
  end.

Inductive syntactically_safe (u_id : user_id) :
  list safe_typ -> forall t, user_cmd t -> ty -> Prop :=

| SafeBind : forall {t t'} context (cmd1 : user_cmd t') t1,
    syntactically_safe u_id context cmd1 t1
    -> forall (cmd2 : <<t'>> -> user_cmd t) t2,
      (forall a, syntactically_safe u_id ({| cmd_type := t' ; cmd_val := a ; safetyTy := t1 |} :: context) (cmd2 a) t2)
      -> syntactically_safe u_id context (Bind cmd1 cmd2) t2

| SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to,
    HonestKey context k__enc
    -> HonestKey context k__sign
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id)
    -> syntactically_safe u_id context (SignEncrypt k__sign k__enc msg_to msg) (TyMyCphr msg_to k__sign)

| SafeSign : forall context {t} (msg : message t) k msg_to,
    HonestKey context k
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id /\ kp = false)
    -> syntactically_safe u_id context (Sign k msg_to msg) (TyMyCphr msg_to k)

| SafeRecvSigned : forall context t k,
    HonestKey context k
    -> syntactically_safe u_id context (@Recv t (Signed k true)) TyRecvCphr

| SafeRecvEncrypted : forall context t k__sign k__enc,
    HonestKey context k__sign
    -> syntactically_safe u_id context (@Recv t (SignedEncrypted k__sign k__enc true)) TyRecvCphr

| SafeSend : forall context t (msg : crypto t) msg_to k,
    (* ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySent |} context *)
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} context
    -> syntactically_safe u_id context (Send msg_to msg) TyDontCare

| SafeReturn : forall {A} context (a : << A >>) sty,
    List.In {| cmd_type := A ; cmd_val := a ; safetyTy := sty |} context
    -> syntactically_safe u_id context (Return a) sty

| SafeReturnUntyped : forall {A} context (a : << A >>),
    syntactically_safe u_id context (Return a) TyDontCare

| SafeGen : forall context,
    syntactically_safe u_id context Gen TyDontCare

| SafeDecrypt : forall context t (msg : crypto t),
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe u_id context (Decrypt msg) TyRecvMsg
| SafeVerify : forall context t k msg,
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe u_id context (@Verify t k msg) TyRecvMsg

| SafeGenerateSymKey : forall context usage,
    syntactically_safe u_id context (GenerateSymKey usage) TyHonestKey
| SafeGenerateAsymKey : forall context usage,
    syntactically_safe u_id context (GenerateAsymKey usage) TyHonestKey
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
        syntactically_safe u_id ctx u.(protocol) t.

Hint Constructors
     HonestKey
     syntactically_safe
  : core.

Lemma share_secret_synctactically_safe :
  U_syntactically_safe (real_univ_start startAdv).
Proof.
  unfold U_syntactically_safe, real_univ_start, mkrU, mkrUsr, A__keys, B__keys; simpl; 
    intros; subst.

  destruct (u_id ==n A); destruct (u_id ==n B); subst; clean_map_lookups; simpl.

  - eexists.

    econstructor.
    econstructor.

    intros; econstructor; simpl; eauto.
    econstructor; simpl; eauto.

    intros; destruct (fst a ==n k_id); subst; clean_map_lookups; eauto.
    econstructor; simpl; eauto.
    destruct a; simpl; econstructor; eauto.

    econstructor; simpl; eauto.
    econstructor; simpl; eauto.

    intros; econstructor; subst; eauto.
    econstructor; simpl; eauto 8.

  - eexists.

    econstructor.
    econstructor.
    econstructor; eauto.

    intros; econstructor; simpl.
    econstructor; simpl; eauto 8.

    intros; econstructor; simpl.
    econstructor; simpl; eauto.

    intros; econstructor; simpl; eauto.
    econstructor; simpl; simpl.

    eapply HonestKeyFromMsgVerify; eauto.
    intros; econstructor; simpl; eauto 8.
    intros; clean_map_lookups.
Qed.

Lemma HonestKey_split :
  forall t (tv : <<t>>) styp k context key_rec,
    key_rec = {| cmd_type := t ; cmd_val := tv ; safetyTy := styp |}
    -> HonestKey (key_rec :: context) k
    -> (exists tf, key_rec = {| cmd_type := Base Access ; cmd_val := (k,tf) ; safetyTy := TyHonestKey |})
    \/ (exists v, key_rec  = {| cmd_type := UPair (Base Bool) (Message Access) ;
                          cmd_val := v ;
                          safetyTy := TyRecvMsg |}
            /\ k = fst (extractPermission (snd v)))
    \/ HonestKey context k
.
Proof.
  intros; subst.
  invert H0; simpl in *; split_ors; eauto 15.
Qed.

Lemma HonestKey_split_drop :
  forall t (tv : <<t>>) k context sty,
    sty <> TyHonestKey
    -> sty <> TyRecvMsg
    -> HonestKey ({| cmd_type := t ; cmd_val := tv ; safetyTy := sty |} :: context) k
    -> HonestKey context k
.
Proof.
  intros; subst.
  eapply HonestKey_split in H1; split_ors; eauto.
  all: eapply safe_typ_eq in H1; split_ands; subst; contradiction.
Qed.

Hint Resolve HonestKey_split_drop : core.

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

Lemma HonestKey_augment_context :
  forall k ctx ctx',
    HonestKey ctx k
    -> Forall (fun styp => List.In styp ctx') ctx
    -> HonestKey ctx' k.
  intros * H FOR; invert H; rewrite Forall_forall in FOR; intros; eauto.
Qed.

Hint Resolve
     HonestKey_skip HonestKey_split
     HonestKey_augment_context
  : core.

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

Lemma Forall_In_refl :
  forall a (l : list a),
    Forall (fun e => List.In e l) l.
Proof.
  intros; rewrite Forall_forall; intros; eauto.
Qed.

Lemma Forall_In_add :
  forall a (l : list a) elem,
    Forall (fun e => List.In e (elem :: l)) l.
Proof.
  intros; rewrite Forall_forall; intros; eauto.
Qed.

Hint Resolve
     Forall_In_refl
     Forall_In_add
  : core.

Lemma syntactically_safe_add_ctx :
  forall ctx u_id A (cmd : user_cmd A) sty,
    syntactically_safe u_id ctx cmd sty
    -> forall ctx',
      List.Forall (fun styp => List.In styp ctx') ctx
      -> syntactically_safe u_id ctx' cmd sty.
Proof.
  induction 1; intros;
    eauto;
    try solve [ rewrite Forall_forall in *; eauto 8 ].

  - econstructor; eauto.
    intros.
    eapply H1; eauto.
    econstructor; eauto.
    rewrite Forall_forall in *; intros; eauto.
    
  - econstructor; intros; eauto.
  - econstructor; intros; eauto.
    specialize (H0 _ _ H2); split_ands; eauto.
Qed.

Definition typingcontext_sound (ctx : list safe_typ)
           (honestk : key_perms) (cs : ciphers)
           (* (ks : key_perms) *)
           (u_id : user_id) :=
  (forall kid, HonestKey ctx kid -> honestk $? kid = Some true)
(* /\ (forall kid, ks $? kid = Some true -> HonestKey ctx kid) *)
/\ (forall t msg msg_to k,
      List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} ctx
      -> exists c_id c,
        msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ cipher_to_user c = msg_to
        /\ cipher_signing_key c = k
        /\ fst (cipher_nonce c) = Some u_id
        /\ HonestKey ctx k)
(* /\ (forall t msg, *)
(*       List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} ctx *)
(*       -> forall kid kp, *)
(*         findKeysCrypto cs msg $? kid = Some kp -> HonestKey ctx kid) *)
.

Ltac process_ctx1 :=
  match goal with
  | [ H : ?x = ?x |- _ ] => clear H
  | [ H : Crypto _ = Crypto _ |- _ ] => invert H
  | [ H : TyMyCphr _ _  = _ |- _ ] => invert H
  | [ H : UPair _ _ = UPair _ _ |- _ ] => invert H
  | [ H : (_,_) = (_,_) |- _ ] => invert H
  | [ H : {| cmd_type := _ |} = {| cmd_type := _ |} |- _ ] => eapply safe_typ_eq in H; split_ex; subst; try discriminate
  | [ H : _ ~= _ |- _ ] => invert H
  | [ H : syntactically_safe _ _ (Return _) _ |- _ ] => invert H
  | [ H : (forall _ _ _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] =>
    specialize (H _ _ _ _ ARG); split_ex; subst
  | [ H : (forall _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] =>
    specialize (H _ _ ARG)
  | [ H : HonestKey ({| cmd_type := ?cty |} :: _) ?kid |- context [ ?kid ] ] =>
    eapply (@HonestKey_split cty _ _ _ _ _ eq_refl) in H; split_ors
  | [ H : List.In _ (_ :: _) |- _ ] => simpl in H; split_ors
  | [ HK : HonestKey ?ctx _, H : (forall _, HonestKey ?ctx _  -> _) |- _ ] => specialize (H _ HK)
  | [ |- _ $k++ _ $? _ = Some true ] => solve_perm_merges
  | [ |- exists _ _, _ ] => (do 2 eexists); repeat simple apply conj
  end.

Ltac process_ctx := repeat process_ctx1.

Ltac dismiss_adv :=
  repeat
    match goal with
    | [ LAME : lameAdv _ (adversary ?ru), STEP : step_user _ None _ _ |- _ ] =>
      destruct ru; unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
    | [ LAME : lameAdv _ _, STEP : step_user _ None _ _ |- _ ] =>
      unfold build_data_step in *; unfold lameAdv in LAME; simpl in *
    | [ ADVP : protocol ?adv = Return _, STEP : step_user _ None (_,_,_,_,_,_,_,_,_,_,protocol ?adv) _ |- _ ] =>
      rewrite ADVP in STEP; invert STEP
    end.

Lemma syntactically_safe_honest_keys_preservation' :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall honestk honestk' cmdc cmdc' u_id,
          suid = Some u_id
          -> syntactically_safe u_id ctx cmd sty
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> typingcontext_sound ctx honestk cs u_id
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmdc';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |}))

          -> exists ctx',
              List.Forall (fun styp => List.In styp ctx') ctx
              /\ typingcontext_sound ctx' honestk' cs' u_id
              /\ syntactically_safe u_id ctx' cmd' sty
.
Proof.

  induction 1; inversion 1; inversion 1;
    invert 2;
    unfold typingcontext_sound;
    intros; subst;
      autorewrite with find_user_keys;
      try solve [
            split_ands; eexists; repeat simple apply conj; swap 1 4; intros; eauto; process_ctx; eauto 8
          ].

  - clean_context.
    eapply IHstep_user in H32; eauto.
    clear IHstep_user.
    split_ex; eauto.
    unfold typingcontext_sound in H1; split_ands.
    eexists; repeat simple apply conj; eauto.
    econstructor; eauto.
    intros.
    eapply syntactically_safe_add_ctx; eauto.
    econstructor; eauto.
    rewrite Forall_forall in *; eauto.

  - split_ands; eexists; repeat simple apply conj; swap 1 4; intros; eauto; process_ctx; eauto 8.

    simpl; specialize (H10 _ _ H5 _ _ H0); encrypted_ciphers_prop.
    dependent destruction msg; simpl in *.
    specialize (H17 (fst acc) (snd acc)); rewrite add_eq_o in H17 by eauto.
    specialize (H17 eq_refl); split_ands; eauto.
Qed.

Lemma syntactically_safe_honest_keys_preservation :
  forall {A B} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        cmd cmd' ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall honestk honestk' u_id,
          suid = Some u_id
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmd;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> syntactically_safe u_id ctx cmd sty
          -> typingcontext_sound ctx honestk cs u_id
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> honestk' = findUserKeys (usrs' $+ (u_id, {| key_heap := ks';
                                                        protocol := cmd';
                                                        msg_heap := qmsgs';
                                                        c_heap   := mycs';
                                                        from_nons := froms';
                                                        sent_nons := sents';
                                                        cur_nonce := cur_n' |}))

          -> exists ctx',
              List.Forall (fun styp => List.In styp ctx') ctx
              /\ typingcontext_sound ctx' honestk' cs' u_id
              /\ syntactically_safe u_id ctx' cmd' sty
.
Proof.
  intros; subst; eapply syntactically_safe_honest_keys_preservation'; eauto.
Qed.

Definition syntactically_safe_U {A B} (U : universe A B) :=
  forall uid u,
    U.(users) $? uid = Some u
    -> exists sty ctx,
      syntactically_safe uid ctx u.(protocol) sty
      /\ typingcontext_sound ctx (findUserKeys U.(users)) U.(all_ciphers) uid.

Lemma syntactically_safe_na :
  forall A uid ctx (p : user_cmd A) sty,
    syntactically_safe uid ctx p sty
    -> forall B (p__n : user_cmd B),
      nextAction p p__n
      -> exists sty', syntactically_safe uid ctx p__n sty'.
Proof.
  induction 1; try solve [ invert 1; eauto ]; intros.
Qed.

Lemma typingcontext_sound_other_user_step :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> message_queues_ok cs usrs gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
      -> forall cmdc cmdc' u_id1 u_id2 ctx ctx__step sty, 
          suid = Some u_id1
          -> u_id1 <> u_id2
          -> usrs $? u_id1 = Some {| key_heap := ks;
                                    protocol := cmdc;
                                    msg_heap := qmsgs;
                                    c_heap   := mycs;
                                    from_nons := froms;
                                    sent_nons := sents;
                                    cur_nonce := cur_n |}
          -> syntactically_safe u_id1 ctx__step cmd sty
          -> typingcontext_sound ctx__step (findUserKeys usrs) cs u_id1
          -> typingcontext_sound ctx (findUserKeys usrs) cs u_id2
          -> typingcontext_sound ctx (findUserKeys (usrs' $+ (u_id1,
                                                           mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n'))) cs' u_id2.
Proof.
  induction 1; inversion 1; inversion 1; 
    intros; subst; autorewrite with find_user_keys; eauto.

  - invert H30; eauto.

  - msg_queue_prop.
    unfold typingcontext_sound in *; repeat simple apply conj; intros; split_ands; eauto.
    assert (msg_pattern_safe (findUserKeys usrs') pat) by (invert H37; eauto).

    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.
    unfold msg_honestly_signed in H12.
    destruct (msg_signing_key cs' msg); try discriminate.
    rewrite <- honest_key_honest_keyb in H12.
    specialize (H1 _ eq_refl); split_ands.
    specialize (H13 H12); split_ands.
    rewrite message_no_adv_private_merge by eauto; eauto.
    
  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    apply H6 in H11; eauto; split_ex; subst; eauto 8.
  - user_cipher_queues_prop.
    encrypted_ciphers_prop.

    rewrite message_only_honest_merge by eauto; eauto.
    
  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    apply H4 in H9; eauto; split_ex; subst; eauto 8.
  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    destruct (k_id ==n kid); subst; clean_map_lookups; eauto.
  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    destruct (k_id ==n kid); subst; clean_map_lookups; eauto.

Qed.

Lemma syntactically_safe_U_preservation_stepU :
  forall A B (U U' : universe A B) lbl b,
    step_universe U lbl U'
    -> universe_ok U
    -> adv_universe_ok U
    -> lameAdv b U.(adversary)
    -> syntactically_safe_U U
    -> syntactically_safe_U U'.
Proof.
  intros * STEP UOK AUOK LAME SS.
  invert STEP; dismiss_adv.

  unfold syntactically_safe_U, build_data_step in *; destruct U; destruct userData;
    simpl in *; intros.
  unfold universe_ok in UOK;
    unfold adv_universe_ok in AUOK;
    split_ors; simpl in *.
  msg_queue_prop.

  destruct (u_id ==n uid); subst; clean_map_lookups; simpl.
  - specialize (SS _ _ H); split_ex.
    eapply syntactically_safe_honest_keys_preservation in H0; eauto.
    split_ex; eauto.

  - generalize H0; intros STEP.
    eapply step_user_nochange_that_user_in_honest_users in H0; eauto.
    destruct u; generalize STEP; intros STEP'.
    eapply step_back_into_other_user in STEP; simpl; eauto.
    
    split_ors; split_ex; subst.
    + subst.
      generalize (SS _ _ H); intros; split_ex.
      specialize (SS _ _ H11); split_ex; simpl in *.
      (do 2 eexists); split; eauto.
      eapply typingcontext_sound_other_user_step; eauto.
    + subst.
      generalize (SS _ _ H); intros; split_ex.
      specialize (SS _ _ H12); split_ex; simpl in *.
      (do 2 eexists); split; eauto.
      eapply typingcontext_sound_other_user_step; eauto.

Qed.

Lemma syntactically_safe_U_preservation_step :
  forall t__hon t__adv (st st' : universe t__hon t__adv * IdealWorld.universe t__hon) b,
    step st st'
    -> universe_ok (fst st)
    -> adv_universe_ok (fst st)
    -> lameAdv b (fst st).(adversary)
    -> syntactically_safe_U (fst st)
    -> syntactically_safe_U (fst st').
Proof.
  inversion 1; intros; subst; simpl in *; eapply syntactically_safe_U_preservation_stepU; eauto.
Qed.

Definition no_resends (sents : sent_nonces) :=
  NoDup sents.

Definition no_resends_U {A B} (U : universe A B) :=
  Forall_natmap (fun u => no_resends u.(sent_nons)) U.(users).

Lemma no_resends_user_step :
  forall {A B C} suid lbl bd bd',
    step_user lbl suid bd bd'
    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> forall cmdc u_id,
          suid = Some u_id
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> no_resends sents'
          -> no_resends sents.
Proof.
  induction 1; inversion 1; inversion 1; unfold no_resends; intros; subst; eauto.

  - eapply IHstep_user in H25; eauto.
  - unfold updateTrackedNonce in H33.
    destruct msg; eauto.
    cases (cs' $? c_id); eauto.
    destruct (rec_u_id ==n cipher_to_user c); subst; eauto.
    destruct (count_occ msg_seq_eq sents0 (cipher_nonce c)); eauto.
    invert H33; eauto.
Qed.

Lemma resend_violation_step' :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> no_resends_U (fst st')
    -> no_resends_U (fst st).
Proof.
  induction 1; unfold no_resends_U; rewrite !Forall_natmap_forall; destruct ru, v; simpl in *; intros.

  - invert H; unfold build_data_step in *; simpl in *; dismiss_adv.
  
    destruct (u_id ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H1 k); rewrite add_eq_o in H1 by trivial.
      specialize (H1 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H1 k); rewrite add_neq_o in H1 by congruence.
      destruct userData; eapply silent_step_nochange_other_user with (u_id2 := k) in H4; eauto.
      clean_map_lookups; simpl in *.
      specialize (H1 _ H4); eauto.

  - invert H; unfold build_data_step in *; simpl in *.
    destruct (u_id ==n k); subst; clean_map_lookups; simpl in *; eauto.
    + specialize (H4 k); rewrite add_eq_o in H4 by trivial.
      specialize (H4 _ eq_refl); simpl in *.
      eapply no_resends_user_step; eauto.
    + specialize (H4 k); rewrite add_neq_o in H4 by congruence.
      destruct userData; eapply step_limited_change_other_user with (u_id2 := k) in H7; eauto.
      split_ex; split_ors; clean_map_lookups; simpl in *.
      specialize (H4 _ H7); eauto.
      specialize (H4 _ H7); eauto.
Qed.

Lemma resend_violation_step :
  forall t__hon t__adv st st' b,
    @step t__hon t__adv st st'
    -> lameAdv b (fst st).(adversary)
    -> ~ no_resends_U (fst st)
    -> ~ no_resends_U (fst st').
Proof.
  unfold not; intros.
  eauto using resend_violation_step'.
Qed.

Lemma single_step_stays_lame :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) st st'
    -> lameAdv b (adversary (fst st))
    -> lameAdv b (adversary (fst st')).
Proof.
  intros.
  invert H;
    simpl in *;
    eauto using universe_step_preserves_lame_adv.
Qed.

Lemma resend_violation_steps :
  forall t__hon t__adv st st' b,
    (@step t__hon t__adv) ^* st st'
    -> lameAdv b (fst st).(adversary)
    -> ~ no_resends_U (fst st)
    -> ~ no_resends_U (fst st').
Proof.
  induction 1; intros; eauto.

  specialize (single_step_stays_lame H H1); intros.
  destruct x, y, z; simpl in *.

  generalize H; intros VIOL; eapply resend_violation_step in VIOL; eauto.
Qed.
