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
     InvariantsTheory
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

Section PredicatePreservation.
  Import RealWorld.

  Hint Resolve
       encrypted_cipher_ok_addnl_cipher
       encrypted_cipher_ok_addnl_key
       encrypted_cipher_ok_addnl_honest_key
       encrypted_ciphers_ok_new_honest_key_adv_univ
       users_permission_heaps_good_merged_permission_heaps_good
       : core.

  Lemma silent_user_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk ctx styp,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honestk = findUserKeys usrs
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> syntactically_safe u_id ctx cmd styp
          -> typingcontext_sound ctx honestk cs u_id
          -> lbl = Silent
          -> forall cmd' usrs'',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' honestk',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                       ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs'
                                              ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                -> honestk' = findUserKeys usrs''
                -> encrypted_ciphers_ok honestk' cs' gks'.
  Proof.
    induction 1; inversion 2; invert 5; inversion 3; intros; subst;
      try discriminate;
      eauto 2;
      autorewrite with find_user_keys in *;
      keys_and_permissions_prop;
      clean_context;
      eauto.
  
    - unfold typingcontext_sound in *; split_ex.
      econstructor; eauto.
      eapply SigEncCipherHonestSignedEncKeyHonestOk; eauto.
      unfold encrypted_ciphers_ok in *; rewrite Forall_natmap_forall in *; intros; eauto.
      
    - user_cipher_queues_prop; encrypted_ciphers_prop.
      rewrite merge_keys_addnl_honest; eauto.
    - unfold typingcontext_sound in *; split_ex.
      econstructor; eauto.
      econstructor; eauto.
      intros * FKM.
      eapply H32 in FKM; split_ex; eauto.
      unfold encrypted_ciphers_ok in *; rewrite Forall_natmap_forall in *; intros; eauto.

    - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs'));
        simpl; eauto; simpl; eauto.
    - eapply encrypted_ciphers_ok_new_honest_key_adv_univ with (honestk := (findUserKeys usrs'));
        simpl; eauto; simpl; eauto.
  Qed.

  Hint Resolve
       honest_users_only_honest_keys_nochange_keys
       honest_users_only_honest_keys_gen_key
    : core.

  Lemma honest_users_only_honest_keys_honest_steps :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
          honestk = findUserKeys usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honest_users_only_honest_keys usrs
          -> forall ctx styp, syntactically_safe u_id ctx cmd styp
          -> typingcontext_sound ctx honestk cs u_id
          (* -> next_cmd_safe (findUserKeys usrs) cs u_id froms sents cmd *)
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok  cs honestk usrs
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'',
                usrs $? u_id = Some {| key_heap := ks
                                       ; msg_heap := qmsgs
                                       ; protocol := cmdc
                                       ; c_heap := mycs
                                       ; from_nons := froms
                                       ; sent_nons := sents
                                       ; cur_nonce := cur_n |}
                -> usrs'' = usrs' $+ (u_id, {| key_heap := ks'
                                              ; msg_heap := qmsgs'
                                              ; protocol := cmdc'
                                              ; c_heap := mycs'
                                              ; from_nons := froms'
                                              ; sent_nons := sents'
                                              ; cur_nonce := cur_n' |})
                -> honest_users_only_honest_keys usrs''.
  Proof.
    induction 1; inversion 3; inversion 6; intros;
      subst;
      autorewrite with find_user_keys;
      (* process_next_cmd_safe; *)
      eauto;
      clean_context.

    - invert H15.
      eapply IHstep_user in H7; eauto.

    - unfold honest_users_only_honest_keys in *; intros.
      destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto;
        simpl in *;
        rewrite findUserKeys_readd_user_addnl_keys; eauto.

      specialize (H10 _ _ H27); simpl in *.

      assert (msg_pattern_safe (findUserKeys usrs') pat) by
          (unfold typingcontext_sound in *; split_ex; invert H22; eauto).
      
      solve_perm_merges;
        try
          match goal with
          | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
          end; clean_map_lookups; eauto;
          assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by eauto.

      + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
        eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
        unfold msg_cipher_id in H2; destruct msg; try discriminate;
          clean_context; simpl in *.
        cases (cs' $? c_id); try discriminate.
        clean_context; invert MHS.
        destruct c; simpl in *; clean_map_lookups; eauto.
        encrypted_ciphers_prop; eauto.
        specialize (H13 _ _ H1); split_ands; subst; clean_map_lookups; eauto.

      + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
        eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
        unfold msg_cipher_id in H2; destruct msg; try discriminate;
          clean_context; simpl in *.
        cases (cs' $? c_id); try discriminate.
        clean_context; invert MHS.
        destruct c; simpl in *; clean_map_lookups; eauto.
        encrypted_ciphers_prop; eauto.
        specialize (H13 _ _ H1); split_ands; subst; clean_map_lookups; eauto.

      + eapply H10 in H; eauto.
        solve_perm_merges; eauto.

    - unfold honest_users_only_honest_keys in *; intros.
      assert (rec_u_id <> u_id) by (unfold not; intros; subst; contradiction).
      destruct (u_id ==n u_id0); destruct (u_id ==n rec_u_id);
        subst;
        try contradiction;
        clean_map_lookups;
        simpl in *;
        eauto.

      + generalize H27; intros; eapply H10 in H27; eauto.
        autorewrite with find_user_keys; eauto.

      + destruct (u_id0 ==n rec_u_id); subst;
          clean_map_lookups;
          autorewrite with find_user_keys;
          eauto 2.

    - unfold typingcontext_sound in *; split_ex.
      user_cipher_queues_prop.
      encrypted_ciphers_prop; clean_map_lookups.
      unfold honest_users_only_honest_keys in *; intros.
      autorewrite with find_user_keys.
      destruct (u_id ==n u_id0);
        subst;
        try contradiction;
        clean_map_lookups;
        simpl in *;
        eauto.

      specialize (H11 _ _ H28); simpl in *.
      apply merge_perms_split in H9; split_ors;
        match goal with
        | [ ARG : findKeysMessage _ $? _ = Some _, H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _) |- _ ] =>
          specialize (H _ _ ARG)
        | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
        end; solve_perm_merges; eauto.
      
      eapply H11 in H9; eauto; solve_perm_merges; eauto.
  Qed.

  Lemma honest_labeled_step_encrypted_ciphers_ok :
    forall {A B C} cs cs' u_id suid lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> message_queues_ok cs usrs gks
      -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
      -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> forall ctx styp, syntactically_safe u_id ctx cmd styp
          -> typingcontext_sound ctx (findUserKeys usrs) cs u_id
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs' gks'.
  Proof.
    induction 1; inversion 4; inversion 4; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys;
        clean_context; eauto.

    invert H4.
    eapply IHstep_user in H9; eauto.

    unfold typingcontext_sound in *; split_ex.
    assert (msg_pattern_safe (findUserKeys usrs') pat) by
        (unfold typingcontext_sound in *; split_ex; invert H11; eauto).
    msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
    specialize_msg_ok; eauto.
  Qed.

  Lemma honest_labeled_step_user_cipher_queues_ok :
    forall {A B C} u_id cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a suid,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honestk = findUserKeys usrs
          -> message_queues_ok cs usrs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> forall cmd' honestk',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Action a
              -> forall ctx styp, syntactically_safe u_id ctx cmd styp
              -> typingcontext_sound ctx (findUserKeys usrs) cs u_id
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> user_cipher_queues_ok cs' honestk' usrs''.
  Proof.
    induction 1; inversion 2; inversion 4; intros; subst; try discriminate; eauto;
      autorewrite with find_user_keys; clean_context.

    - invert H29.
      eapply IHstep_user in H6; eauto.

    - assert (msg_pattern_safe (findUserKeys usrs') pat) by
          (unfold typingcontext_sound in *; split_ex; invert H36; eauto).

      msg_queue_prop; eauto.
      specialize_msg_ok.
      eapply user_cipher_queues_ok_add_user; autorewrite with find_user_keys; eauto.

    - remember ((usrs $+ (rec_u_id,
                          {| key_heap := key_heap rec_u;
                             protocol := protocol rec_u;
                             msg_heap := msg_heap rec_u ++ [existT crypto t0 msg];
                             c_heap := c_heap rec_u |}))) as usrs'.

      assert (findUserKeys usrs = findUserKeys usrs') as RW
          by (subst; autorewrite with find_user_keys; eauto).

      rewrite RW; clear RW.
      destruct rec_u; simpl in *.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
      autorewrite with find_user_keys.
      eapply user_cipher_queues_ok_readd_user; subst; clean_map_lookups; eauto.
  Qed.

  Lemma honest_labeled_step_message_queues_ok :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honestk = findUserKeys usrs
          -> message_queues_ok cs usrs gks
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> forall cmd' honestk',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Action a
              -> forall ctx styp, syntactically_safe u_id ctx cmd styp
              -> typingcontext_sound ctx (findUserKeys usrs) cs u_id
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc
                                         ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                  -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc'
                                                ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |})
                  -> honestk' = findUserKeys usrs''
                  -> message_queues_ok cs' usrs'' gks'.
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys; eauto;
        clean_context; msg_queue_prop; specialize_msg_ok; eauto.

    - invert H31.
      eapply IHstep_user in H7; eauto.

    - assert (msg_pattern_safe (findUserKeys usrs') pat) by
          (unfold typingcontext_sound in *; split_ex; invert H38; eauto).

      unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros;
        autorewrite with find_user_keys in *.

      assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.
      eapply message_honestly_signed_msg_signing_key_honest in H5; split_ex.
      specialize_simply.
      rewrite honestk_merge_new_msgs_keys_same; eauto.
      destruct (u_id ==n k); subst; clean_map_lookups; eauto.

    - unfold message_queues_ok in *; rewrite Forall_natmap_forall in *; intros;
        autorewrite with find_user_keys in *.
      assert (rec_u_id <> u_id) by (unfold not; intros; subst; contradiction).

      unfold typingcontext_sound in *; split_ex.
      invert H38.

      destruct (rec_u_id ==n k);
        destruct (u_id ==n k);
        subst;
        clean_map_lookups;
        simpl;
        eauto.

      eapply H7 in H13; split_ex; subst.
      eapply H21 in H2; unfold message_queue_ok in H2.
      eapply Forall_app; simpl; econstructor; eauto.

      eapply H6 in H12.
      keys_and_permissions_prop.

      encrypted_ciphers_prop;
        repeat simple apply conj;
        intros;
        simpl in *;
        context_map_rewrites;
        clean_map_lookups;
        eauto.

      + eapply H18 in H15; split_ex; subst.
        eapply H13 in H15; split_ex; clean_map_lookups.
      + simpl in *; context_map_rewrites.
        repeat simple apply conj; intros; eauto.
        discriminate.
        unfold message_no_adv_private, msgCiphersSignedOk; simpl.
        context_map_rewrites.
        split; intros; eauto.
        econstructor; eauto.
        unfold msg_honestly_signed, msg_signing_key; context_map_rewrites;
          simpl;
          rewrite <- honest_key_honest_keyb;
          eauto.
      + simpl in *; context_map_rewrites.
        repeat simple apply conj; intros; eauto.
        discriminate.
        unfold message_no_adv_private, msgCiphersSignedOk; simpl.
        context_map_rewrites.
        split; intros; eauto.
        clean_map_lookups.
        econstructor; eauto.
        unfold msg_honestly_signed, msg_signing_key; context_map_rewrites;
          simpl;
          rewrite <- honest_key_honest_keyb;
          eauto.
  Qed.

  (* Lemma honest_labeled_step_adv_cipher_queue_ok : *)
  (*   forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
  (*     gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a, *)
  (*     step_user lbl suid bd bd' *)
  (*     -> suid = Some u_id *)
  (*     -> forall (cmd : user_cmd C) honestk, *)
  (*         bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
  (*         -> honestk = findUserKeys usrs *)
  (*         -> encrypted_ciphers_ok honestk cs gks *)
  (*         -> adv_message_queue_ok usrs cs gks adv.(msg_heap) *)
  (*         -> message_queues_ok cs usrs gks *)
  (*         -> honest_nonces_ok cs usrs *)
  (*         -> user_cipher_queues_ok cs honestk usrs *)
  (*         -> adv_cipher_queue_ok cs usrs adv.(c_heap) *)
  (*         -> forall cmd', *)
  (*             bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
  (*             -> lbl = Action a *)
  (*             -> forall ctx styp, syntactically_safe u_id ctx cmd styp *)
  (*             -> typingcontext_sound ctx (findUserKeys usrs) cs u_id *)
  (*             (* -> action_adversary_safe honestk cs a *) *)
  (*             -> forall cmdc cmdc' usrs'', *)
  (*                 usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc *)
  (*                                        ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |} *)
  (*                 -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' *)
  (*                                               ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}) *)
  (*                 -> adv_cipher_queue_ok cs' usrs'' adv'.(c_heap). *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 8; intros; subst; try discriminate; *)
  (*     eauto 2; autorewrite with find_user_keys; eauto; *)
  (*       intros; *)
  (*       clean_context. *)

  (*   - invert H33. *)
  (*     eapply IHstep_user in H6; eauto. *)

  (*   - unfold typingcontext_sound in *; split_ex. *)
  (*     assert (msg_pattern_safe (findUserKeys usrs') pat) by *)
  (*         (unfold typingcontext_sound in *; split_ex; invert H40; eauto). *)
      
  (*     unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; intros. *)
  (*     assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto. *)

  (*     specialize (H26 _ H2); split_ex. *)
  (*     eexists; split; eauto. *)
  (*     autorewrite with find_user_keys; split_ors; split_ex; split_ands; subst; eauto. *)
  (*     + left; split; eauto; subst. *)
  (*       msg_queue_prop; context_map_rewrites. *)
  (*       eapply message_honestly_signed_msg_signing_key_honest in H3; split_ex. *)
  (*       specialize_simply. *)
  (*       unfold message_no_adv_private in H13; simpl in H13; context_map_rewrites. *)
  (*       rewrite cipher_honestly_signed_honest_keyb_iff in *; *)
  (*         unfold honest_keyb in *. *)
  (*       cases (findUserKeys usrs' $? cipher_signing_key x0); solve_perm_merges; eauto. *)
  (*       specialize (H13 _ _ H15); split_ex; subst; trivial. *)
  (*       specialize (H13 _ _ H15); split_ex; subst; trivial. *)

  (*     + right. *)

  (* Ltac process_predicate := *)
  (*   repeat ( *)
  (*       contradiction *)
  (*       || discriminate *)
  (*       || match goal with *)
  (*         | [ H : msg_to_this_user _ _ _ = true |- _ ] => *)
  (*           unfold msg_to_this_user, msg_destination_user in H; context_map_rewrites *)
  (*         | [ H : (if ?cond then _ else _) = _ |- _ ] => destruct cond; try discriminate; try contradiction *)
  (*         | [ |- ?c1 /\ _ ] => *)
  (*           match c1 with *)
  (*           (* simplify *) *)
  (*           | List.In _ (sent_nons ?sents) => is_not_var sents; simpl *)
  (*           | List.In _ ?arg => match arg with *)
  (*                              | context [ _ $? _ ] => context_map_rewrites *)
  (*                              | context [ if ?cond then _ else _ ] => destruct cond *)
  (*                              end *)
  (*           (* process *) *)
  (*           | _ =>  *)
  (*             split; [ *)
  (*               match c1 with *)
  (*               | (_ $+ (?k1,_) $? ?k2 = _) => *)
  (*                 solve [ subst; clean_map_lookups; eauto ] *)
  (*               | _ => solve [ eauto 2 ] *)
  (*               end | ] *)
  (*           end *)
  (*         | [ H : List.In ?cn _ \/ Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] => *)
  (*           split_ors; eauto *)
  (*         | [ H : Exists _ _ |- List.In ?cn _ \/ Exists _ _ ] => *)
  (*           rewrite Exists_exists in *; split_ex *)
  (*         | [ H : let (_,_) := ?x in msg_signed_addressed _ _ _ _ = true /\ _ |- _ ] => destruct x; split_ands *)
  (*         | [ H : List.In ?m ?heap |- context [ ?heap ++ _ ] ] => right; simpl; exists m; rewrite in_app_iff; eauto *)
  (*         end). *)

        
  (*       destruct (u_id ==n x1); *)
  (*         [| destruct (u_id ==n cipher_to_user x0)]; *)
  (*         subst; clean_map_lookups; simpl in *; *)
  (*           (do 3 eexists); *)
  (*           process_predicate; *)
  (*           eauto; *)
  (*           simpl. *)

  (*       * right; eexists; split; eauto; simpl. *)
  (*         split; eauto. *)
  (*         (do 2 msg_queue_prop). *)
  (*         generalize (message_honestly_signed_msg_signing_key_honest _ _ _ H3); intros; split_ex; *)
  (*           specialize_simply. *)
  (*         rewrite honestk_merge_new_msgs_keys_same by eauto. *)

  (*         unfold msg_honestly_signed, msg_signing_key in H3; *)
  (*           context_map_rewrites; *)
  (*           simpl in *; *)
  (*           encrypted_ciphers_prop; eauto. *)

  (*       * unfold updateTrackedNonce. *)
  (*         generalize (message_honestly_signed_msg_signing_key_honest _ _ _ H3); intros; split_ex; *)
  (*           specialize_simply. *)
  (*         unfold msg_signing_key in H12; destruct msg; try discriminate. *)
  (*         cases (cs' $? c_id); try discriminate. *)
  (*         invert H12. *)
  (*         destruct (cipher_to_user x0 ==n cipher_to_user c); eauto. *)
  (*         cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto. *)

  (*       * unfold updateTrackedNonce. *)
  (*         generalize (message_honestly_signed_msg_signing_key_honest _ _ _ H3); intros; split_ex; *)
  (*           specialize_simply. *)
  (*         unfold msg_signing_key in H14; destruct msg; try discriminate. *)
  (*         cases (cs' $? c_id); try discriminate. *)
  (*         invert H14. *)

  (*         simpl in H11; split_ors. *)
  (*         ** invert H11. *)
  (*            unfold msg_nonce_same in H13. *)
  (*            unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H12; *)
  (*              context_map_rewrites; *)
  (*              rewrite andb_true_iff in H12; split_ex. *)
  (*            cases (cipher_to_user c0 ==n cipher_to_user x0); try discriminate. *)
  (*            rewrite e; destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction. *)
  (*            generalize Heq; intros; eapply H13 in Heq; eauto. *)

  (*            left. *)
  (*            cases (count_occ msg_seq_eq froms (cipher_nonce c0)). *)
  (*            rewrite Heq; simpl; eauto. *)
  (*            rewrite Heq. *)
  (*            rewrite count_occ_In with (eq_dec := msg_seq_eq). *)
  (*            rewrite Heq1; eauto. *)
  (*            Omega.omega. *)
             
  (*         ** right; eexists; split; eauto. *)
  (*            simpl; context_map_rewrites; eauto. *)
  (*            split; eauto. *)

  (*            destruct c0; eauto. *)
  (*            rewrite msg_signed_addressed_new_msg_keys'; eauto. *)
  (*            simpl in *. *)
  (*            invert H15. *)
  (*            encrypted_ciphers_prop; eauto. *)

  (*       * right; eexists; simpl; split; eauto. *)
  (*         simpl; split; eauto. *)
  (*         (do 2 msg_queue_prop). *)
  (*         specialize_simply. *)
  (*         rewrite honestk_merge_new_msgs_keys_same; eauto. *)

  (*   - unfold typingcontext_sound in H41; split_ex; invert H40. *)
  (*     eapply H4 in H10; split_ex; subst; clear H4. *)

  (*     unfold adv_cipher_queue_ok in *; rewrite Forall_forall in *; simpl in *; intros; *)
  (*       context_map_rewrites. *)

  (*     specialize (H26 _ H4); split_ex; split_ands. *)
  (*     eapply H in H10. *)
  (*     eexists; split; eauto. *)
  (*     autorewrite with find_user_keys; split_ors; split_ex; split_ands; eauto. *)
  (*     right; subst; simpl in *. *)

  (*     process_predicate. *)
  (*     clean_context. *)
  (*     (* symmetry in e; subst. *) *)
  (*     assert (u_id <> cipher_to_user x0) by (unfold not; intros; subst; contradiction); clear H3. *)

  (*     destruct (cipher_to_user x0 ==n cipher_to_user x2); *)
  (*       destruct (cipher_to_user x0 ==n x3); *)
  (*       destruct (u_id ==n x3); *)
  (*       destruct (u_id ==n cipher_to_user x2); *)
  (*       subst; *)
  (*       try contradiction; *)
  (*       clean_map_lookups; *)
  (*       do 3 eexists; *)
  (*       process_predicate; eauto. *)
  (* Qed. *)

  (* Lemma honest_labeled_step_adv_message_queue_ok : *)
  (*   forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
  (*             gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a, *)
  (*     step_user lbl suid bd bd' *)
  (*     -> suid = Some u_id *)
  (*     -> forall (cmd : user_cmd C) honestk, *)
  (*       bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
  (*       -> honestk = findUserKeys usrs *)
  (*       -> message_queues_ok cs usrs gks *)
  (*       -> keys_and_permissions_good gks usrs adv.(key_heap) *)
  (*       -> encrypted_ciphers_ok (findUserKeys usrs) cs gks *)
  (*       -> user_cipher_queues_ok cs honestk usrs *)
  (*       -> adv_message_queue_ok usrs cs gks adv.(msg_heap) *)
  (*       -> forall cmd' honestk', *)
  (*           bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
  (*           -> lbl = Action a *)
  (*           -> forall ctx styp, syntactically_safe u_id ctx cmd styp *)
  (*           -> typingcontext_sound ctx (findUserKeys usrs) cs u_id *)
  (*           (* -> action_adversary_safe honestk cs a *) *)
  (*           -> forall cmdc cmdc' usrs'', *)
  (*               usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |} *)
  (*               -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}) *)
  (*               -> honestk' = findUserKeys usrs'' *)
  (*               -> adv_message_queue_ok usrs'' cs' gks' adv'.(msg_heap). *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 7; intros; subst; try discriminate; *)
  (*     eauto 2; autorewrite with find_user_keys; eauto; *)
  (*       clean_context. *)

  (*   - invert H32. *)
  (*     eapply IHstep_user in H6; eauto. *)

  (*   - assert (msg_pattern_safe (findUserKeys usrs') pat) by *)
  (*         (unfold typingcontext_sound in *; split_ex; invert H39; eauto). *)
      
  (*     unfold adv_message_queue_ok in *; rewrite Forall_forall in *; intros. *)
  (*     assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto. *)

  (*     specialize (H25 _ H0). *)
  (*     destruct x as [t__m msg']; split_ex. *)
  (*     repeat simple apply conj; eauto; intros. *)
  (*     + specialize (H3 _ _ H7); split_ex; split; intros; subst; eauto. *)
  (*       autorewrite with find_user_keys. *)
  (*       msg_queue_prop. *)
  (*       generalize (message_honestly_signed_msg_signing_key_honest _ _ _ H1); intros; split_ex; *)
  (*         specialize_simply. *)
  (*       rewrite honestk_merge_new_msgs_keys_same; eauto. *)
  (*     + specialize (H5 _ H7); split_ex. *)
  (*       msg_queue_prop. *)
  (*       generalize (message_honestly_signed_msg_signing_key_honest _ _ _ H1); intros; split_ex; *)
  (*         specialize_simply. *)
  (*       autorewrite with find_user_keys; eauto. *)
  (*       eexists; split; eauto. *)
  (*       rewrite honestk_merge_new_msgs_keys_same by eauto. *)
  (*       split_ors; split_ex; eauto. *)
  (*       right. *)
  (*       destruct (u_id ==n x1); destruct (u_id ==n cipher_to_user x); *)
  (*         subst; clean_map_lookups; *)
  (*           (do 3 eexists); repeat simple apply conj; eauto. *)
  (*       simpl in *; eauto. *)

  (*       split_ors. *)
  (*       * left. *)
  (*         unfold msg_signing_key in H12. *)
  (*         unfold updateTrackedNonce. *)
  (*         destruct msg; eauto. *)
  (*         cases (cs' $? c_id0); eauto. *)
  (*         destruct (cipher_to_user x ==n cipher_to_user c); eauto. *)
  (*         destruct (count_occ msg_seq_eq froms (cipher_nonce c)); eauto. *)

  (*       * rewrite Exists_exists in *; split_ex; destruct x3; split_ex. *)
  (*         simpl in H11; split_ors. *)
  (*         invert H11. *)
  (*         unfold msg_nonce_same in H26. *)
  (*         left; unfold updateTrackedNonce. *)
  (*         unfold msg_signing_key in H12. *)
  (*         destruct c; try discriminate. *)
  (*         cases (cs' $? c_id0); try discriminate. *)
  (*         invert H12. *)
  (*         specialize (H26 _ _ eq_refl Heq0). *)
  (*         simpl in *; context_map_rewrites. *)
  (*         unfold msg_signed_addressed, msg_to_this_user, msg_destination_user in H25; *)
  (*           context_map_rewrites; *)
  (*           rewrite !andb_true_iff in H25; *)
  (*           split_ex. *)
  (*         destruct (cipher_to_user c ==n cipher_to_user x); try discriminate. *)
  (*         rewrite e; destruct (cipher_to_user x ==n cipher_to_user x); try contradiction. *)
  (*         rewrite H26. *)
  (*         cases (count_occ msg_seq_eq froms (cipher_nonce c)); eauto. *)
  (*         rewrite count_occ_In with (eq_dec := msg_seq_eq). *)
  (*         Omega.omega. *)

  (*         right; eexists; split; simpl; eauto. *)
  (*         cases (existT (fun H27 : type => crypto H27) x3 c). *)
  (*         invert Heq0; eauto. *)

  (*   - unfold typingcontext_sound in *; split_ex. *)
  (*     invert H39. *)
  (*     specialize (H4 _ _ _ _ H10); split_ex; clear H10. *)
  (*     unfold adv_message_queue_ok in *; rewrite Forall_forall in *; intros; simpl in *. *)

  (*     apply in_app_or in H10; simpl in H10; split_ors; subst; try contradiction. *)
  (*     + specialize (H25 _ H10); destruct x1 as [t__m msg']; split_ex. *)

  (*       repeat simple apply conj; eauto; intros. *)
  (*       specialize (H6 _ _ H12); split_ex. *)
  (*       split; eauto; intros; subst. *)
  (*       autorewrite with find_user_keys; eauto. *)
  (*       specialize (H11 _ H12); split_ex. *)
  (*       eexists; split; eauto. *)
  (*       autorewrite with find_user_keys; eauto. *)
  (*       split_ors; eauto. *)
  (*       assert (u_id <> cipher_to_user x0) by (unfold not; intros; subst; contradiction). *)
        
  (*       right; *)
  (*         (* destruct (x ==n cipher_to_user x0); *) *)
  (*         destruct (u_id ==n x2); *)
  (*         destruct (u_id ==n cipher_to_user x1); *)
  (*         destruct (x2 ==n cipher_to_user x0); *)
  (*         destruct (x2 ==n cipher_to_user x1); *)
  (*         destruct (cipher_to_user x0 ==n cipher_to_user x1); *)
  (*         subst; clean_map_lookups; *)
  (*           (do 3 eexists); process_predicate; eauto. *)

  (*     + repeat simple apply conj; eauto; intros; simpl in *; context_map_rewrites. *)
  (*       * unfold not; intros; simpl in *; invert H4; clean_map_lookups. *)
  (*       * user_cipher_queues_prop. *)

  (*         apply H in H9. *)
  (*         autorewrite with find_user_keys. *)
  (*         keys_and_permissions_prop. *)
  (*         destruct x0; clean_map_lookups; simpl in *. *)
  (*         encrypted_ciphers_prop; eauto. *)
  (*         generalize (H27 _ _ H4); intros; split_ex; subst. *)
  (*         apply H12 in H3; eauto; split_ex. *)
  (*         split; intros; clean_map_lookups. *)

  (*       * invert H4. *)
  (*         keys_and_permissions_prop. *)
  (*         eapply H in H9. *)
  (*         eapply H10 in H9; split_ex; clean_map_lookups. *)

  (*       * apply H in H9. *)
  (*         split_ors; subst; try contradiction. *)
  (*         eexists; split; eauto. *)
  (*         autorewrite with find_user_keys. *)

  (*         right; eauto. *)
  (*         (do 3 eexists); split; eauto. *)
  (*         split. *)
  (*         clean_map_lookups. *)
  (*         reflexivity. *)
  (*         split. *)
  (*         unfold not; intros; subst; contradiction. *)
  (*         simpl. *)
  (*         destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction. *)
  (*         split. *)
  (*         cases (count_occ msg_seq_eq sents (cipher_nonce x0)); eauto. *)
  (*         rewrite count_occ_In with (eq_dec := msg_seq_eq); Omega.omega. *)
  (*         split. *)
  (*         clean_map_lookups; reflexivity. *)
  (*         simpl. *)
          
  (*         right; rewrite Exists_exists. *)
  (*         exists (existT crypto t0 (SignedCiphertext c_id)); split. *)
  (*         apply in_or_app; eauto. *)
  (*         unfold *)
  (*           msg_signed_addressed, msg_nonce_same, *)
  (*           msg_honestly_signed, msg_signing_key, *)
  (*           msg_to_this_user, msg_destination_user; context_map_rewrites. *)
  (*         assert ( HK : honest_keyb (findUserKeys usrs) (cipher_signing_key x0) = true) *)
  (*           by (unfold honest_keyb; context_map_rewrites; trivial). *)
  (*         rewrite HK. *)
  (*         destruct (cipher_to_user x0 ==n cipher_to_user x0); try contradiction; split; eauto. *)
  (*         intros. *)
  (*         invert H4; clean_map_lookups; eauto. *)
  (* Qed. *)
  
  (* Lemma honest_labeled_step_adv_no_honest_keys : *)
  (*   forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B) *)
  (*     gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a, *)
  (*     step_user lbl suid bd bd' *)
  (*     -> suid = Some u_id *)
  (*     -> forall (cmd : user_cmd C) honestk, *)
  (*         bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd) *)
  (*         -> honestk = findUserKeys usrs *)
  (*         -> message_queues_ok cs usrs gks *)
  (*         -> encrypted_ciphers_ok honestk cs gks *)
  (*         -> user_cipher_queues_ok cs honestk usrs *)
  (*         -> adv_no_honest_keys honestk adv.(key_heap) *)
  (*         -> forall cmd' honestk', *)
  (*             bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd') *)
  (*             -> lbl = Action a *)
  (*             -> forall ctx styp, syntactically_safe u_id ctx cmd styp *)
  (*             -> typingcontext_sound ctx (findUserKeys usrs) cs u_id *)
  (*             (* -> action_adversary_safe honestk cs a *) *)
  (*             -> forall cmdc cmdc' usrs'', *)
  (*                 usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |} *)
  (*                 -> usrs'' = usrs' $+ (u_id, {| key_heap := ks' ; msg_heap := qmsgs' ; protocol := cmdc' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}) *)
  (*                 -> honestk' = findUserKeys usrs'' *)
  (*                 -> adv_no_honest_keys honestk' adv'.(key_heap). *)
  (* Proof. *)
  (*   induction 1; inversion 2; inversion 6; intros; subst; *)
  (*     try discriminate; eauto 2; *)
  (*       autorewrite with find_user_keys; eauto; *)
  (*         clean_context. *)

  (*   - invert H31. *)
  (*     eapply IHstep_user in H6; eauto. *)

  (*   - msg_queue_prop; specialize_msg_ok; *)
  (*       unfold adv_no_honest_keys, message_no_adv_private in *; *)
  (*       simpl in *; *)
  (*       repeat *)
  (*         match goal with *)
  (*         | [ RW : honest_keyb ?honk ?kid = _ , H : if honest_keyb ?honk ?kid then _ else _ |- _] => rewrite RW in H *)
  (*         | [ H : (forall k_id, findUserKeys _ $? k_id = None \/ _) |- (forall k_id, _) ] => intro KID; specialize (H KID) *)
  (*         | [ |- context [ _ $k++ $0 ] ] => rewrite merge_keys_right_identity *)
  (*         | [ FK : findKeysCrypto _ ?msg $? ?kid = Some _, H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _) *)
  (*             |- context [ _ $k++ findKeysCrypto _ ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try solve_perm_merges *)
  (*         | [ FK : findKeysCrypto _ ?msg $? ?kid = None |- context [ ?uks $k++ findKeysCrypto _ ?msg $? ?kid] ] => *)
  (*           split_ors; split_ands; solve_perm_merges *)
  (*         | [ H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeysCrypto ?cs ?msg $? ?kid] ] => *)
  (*           match goal with *)
  (*           | [ H : findKeysCrypto cs msg $? kid = _ |- _ ] => fail 1 *)
  (*           | _ => cases (findKeysCrypto cs msg $? kid) *)
  (*           end *)
  (*         end; eauto. *)

  (*     assert (msg_pattern_safe (findUserKeys usrs') pat) by *)
  (*         (unfold typingcontext_sound in *; split_ex; invert H38; eauto). *)
            
  (*     assert (MHS: msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto. *)
  (*     generalize (message_honestly_signed_msg_signing_key_honest _ _ _ MHS); intros; split_ex; *)
  (*         specialize_simply. *)

  (*     rewrite honestk_merge_new_msgs_keys_same; eauto. *)

  (*   - unfold adv_no_honest_keys in *; intros. *)
  (*     specialize (H24 k_id). *)
  (*     split_ex; subst; simpl in *. *)
  (*     unfold typingcontext_sound in *; split_ex. *)
  (*     invert H38. *)
  (*     eapply H4 in H10; split_ex; subst; simpl in *. *)
      
  (*     assert (List.In x mycs') by eauto. *)
  (*     user_cipher_queues_prop. *)
      
  (*     rewrite cipher_honestly_signed_honest_keyb_iff in H8. *)
  (*     encrypted_ciphers_prop; eauto. *)
  (*     intuition idtac. *)
  (*     right; right; split; eauto; intros. *)
  (*     solve_perm_merges; *)
  (*       specialize (H13 _ _ H16); split_ands; discriminate. *)
  (* Qed. *)

  Definition goodness_predicates {A B} (U : RealWorld.universe A B) : Prop :=
    let honestk := RealWorld.findUserKeys U.(RealWorld.users)
    in  encrypted_ciphers_ok honestk U.(RealWorld.all_ciphers) U.(RealWorld.all_keys)
      /\ keys_and_permissions_good U.(RealWorld.all_keys) U.(RealWorld.users) U.(RealWorld.adversary).(RealWorld.key_heap)
      /\ user_cipher_queues_ok U.(RealWorld.all_ciphers) honestk U.(RealWorld.users)
      /\ message_queues_ok U.(RealWorld.all_ciphers) U.(RealWorld.users) U.(RealWorld.all_keys)
      /\ honest_users_only_honest_keys U.(RealWorld.users).

  Lemma goodness_preservation :
    forall {A B} (U U' : universe A B) lbl b,
      step_universe U lbl U'
      -> lameAdv b U.(adversary)
      -> syntactically_safe_U U
      -> goodness_predicates U
      -> goodness_predicates U'.
  Proof.
    intros.

    invert H; dismiss_adv.

    unfold goodness_predicates, syntactically_safe_U in *; simpl in *.
    destruct lbl, U, userData;
      unfold build_data_step in *; simpl in *;
        specialize (H1 _ _ H3); split_ex; simpl in *.
    
    - intuition
        eauto using silent_user_step_encrypted_ciphers_ok,
      honest_silent_step_keys_good,
      honest_silent_step_user_cipher_queues_ok,
      honest_silent_step_message_queues_ok,
      honest_users_only_honest_keys_honest_steps
    .

    eapply honest_silent_step_message_queues_ok; eauto; keys_and_permissions_prop; eauto.

    - intuition
        eauto using
         honest_labeled_step_encrypted_ciphers_ok,
      honest_labeled_step_keys_and_permissions_good,
      honest_labeled_step_user_cipher_queues_ok,
      honest_labeled_step_message_queues_ok,
      honest_users_only_honest_keys_honest_steps
      .
  Qed.

  Lemma syntactically_safe_U_preservation_stepU :
    forall A B (U U' : universe A B) lbl b,
      step_universe U lbl U'
      -> lameAdv b U.(adversary)
      -> goodness_predicates U
      -> syntactically_safe_U U
      -> syntactically_safe_U U'.
  Proof.
    intros * STEP LAME GOOD SS.
    invert STEP; dismiss_adv.

    unfold syntactically_safe_U, build_data_step in *; destruct U; destruct userData;
      simpl in *; intros.
    unfold goodness_predicates in *; split_ex; simpl in *.
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
        specialize (SS _ _ H8); split_ex; simpl in *.
        (do 2 eexists); split; eauto.
        eapply typingcontext_sound_other_user_step; eauto.
      + subst.
        generalize (SS _ _ H); intros; split_ex.
        specialize (SS _ _ H9); split_ex; simpl in *.
        (do 2 eexists); split; eauto.
        eapply typingcontext_sound_other_user_step; eauto.

  Qed.

  Lemma syntactically_safe_U_preservation_step :
    forall t__hon t__adv (st st' : universe t__hon t__adv * IdealWorld.universe t__hon) b,
      step st st'
      -> lameAdv b (fst st).(adversary)
      -> goodness_predicates (fst st)
      -> syntactically_safe_U (fst st)
      -> syntactically_safe_U (fst st').
  Proof.
    inversion 1; intros; subst; simpl in *; eapply syntactically_safe_U_preservation_stepU; eauto.
  Qed.

End PredicatePreservation.

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
