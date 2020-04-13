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
| TyHonestKey
| TyMyCphr (uid : user_id) (k_id : key_identifier)
| TyRecvMsg
| TyRecvCphr
(* | TyMsgVerify (t : type) *)
| TySent
(* | TyPair (t1 t2 : ty) *)
.

(* Lemma type_dec_eq : *)
(*   forall type1 type2 : type, { type1 = type2 } + { type1 <> type2 }. *)
(*   decide equality. *)
(* Qed. *)

(* Lemma ty_dec_eq : *)
(*   forall ty1 ty2 : ty, { ty1 = ty2 } + { ty1 <> ty2 }. *)
(*   decide equality; auto using type_dec_eq. *)
(* Qed. *)

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

Definition findKeysRecur {t} (cs : ciphers) (msg : crypto t) : key_perms :=
  match msg with
  | Content  m          => findKeysMessage m
  | SignedCiphertext c_id  =>
    match cs $? c_id with
    | Some (SigEncCipher _ _ _ _ m) => findKeysMessage m
    | Some (SigCipher _ _ _ m)      => findKeysMessage m
    | None                          => $0
    end
  end.

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
(* | HonestKeyFromCrypto : forall t (msg : crypto t) cs kid tf, *)
(*     List.In {| cmd_type := Crypto t ; *)
(*                cmd_val :=  msg ; *)
(*                safetyTy := TyRecvCphr |} *)
(*             context *)
(*     -> findKeysCrypto cs msg $? kid = Some tf *)
(*     -> HonestKey context kid *)
.

(* Lemma HonestKeyFromMsg' : *)
(*   forall context t tv (f : << t >> -> << Message Access >>) ftv, *)
(*     List.In {| cmd_type := t ; *)
(*                cmd_val := tv ; *)
(*                safetyTy := TyRecvMsg |} context *)
(*     -> ftv = f tv *)
(*     -> HonestKey context (fst (extractPermission ftv)). *)
(* Proof. intros; subst; eapply HonestKeyFromMsg; eauto. Qed. *)

(* Hint Resolve HonestKeyFromMsg' : core. *)

Fixpoint init_context (ks : list key_permission) : list safe_typ :=
  match ks with
  | []         => []
  | (kp :: kps) =>
    {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} :: init_context kps
  end.

Inductive syntactically_safe :
  list safe_typ -> forall t, user_cmd t -> ty -> Prop :=

| SafeBind : forall {t t'} context (cmd1 : user_cmd t') t1,
    syntactically_safe context cmd1 t1
    -> forall (cmd2 : <<t'>> -> user_cmd t) t2,
      (forall a, syntactically_safe ({| cmd_type := t' ; cmd_val := a ; safetyTy := t1 |} :: context) (cmd2 a) t2)
      -> syntactically_safe context (Bind cmd1 cmd2) t2

| SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to,
    HonestKey context k__enc
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id)
    -> syntactically_safe context (SignEncrypt k__sign k__enc msg_to msg) (TyMyCphr msg_to k__sign)

| SafeSign : forall context {t} (msg : message t) k msg_to,
    (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id /\ kp = false)
    -> syntactically_safe context (Sign k msg_to msg) (TyMyCphr msg_to k)

| SafeRecvSigned : forall context t k,
    HonestKey context k
    -> syntactically_safe context (@Recv t (Signed k true)) TyRecvCphr

| SafeRecvEncrypted : forall context t k__sign k__enc,
    HonestKey context k__sign
    -> syntactically_safe context (@Recv t (SignedEncrypted k__sign k__enc true)) TyRecvCphr

| SafeSend : forall context t (msg : crypto t) msg_to k,
    (* ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySent |} context *)
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} context

    -> (forall cs cid c,
          msg_cipher_id msg = Some cid
          -> cs $? cid = Some c
          -> k = cipher_signing_key c
          -> msg_to = cipher_to_user c
          -> HonestKey context k
          /\ msg_to_this_user cs (Some msg_to) msg = true)
        (* /\ msgCiphersSignedOk honestk cs msg) *)


    (* msg_honestly_signed honestk cs msg = true /\ *)
    (* msg_to_this_user cs (Some msg_to) msg = true /\ *)
    (* msgCiphersSignedOk honestk cs msg /\ *)
    
    (* -> HonestKey context k *)
    -> syntactically_safe context (Send msg_to msg) TyDontCare

(* | SafeSendSigned : forall context t (msg : crypto t) msg_to, *)
(*     (* ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySent |} context *) *)

(*     (* msg_honestly_signed honestk cs msg = true /\ *) *)
(*     (* msg_to_this_user cs (Some msg_to) msg = true /\ *) *)
(*     (* msgCiphersSignedOk honestk cs msg /\ *) *)
    
(*     List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to) |} context *)
(*     -> syntactically_safe context (Send msg_to msg) TyDontCare *)

(* | SafeSendEncrypted : forall context t (msg : crypto t) msg_to, *)
(*     (* ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySent |} context *) *)

(*     (* msg_honestly_signed honestk cs msg = true /\ *) *)
(*     (* msg_to_this_user cs (Some msg_to) msg = true /\ *) *)
(*     (* msgCiphersSignedOk honestk cs msg /\ *) *)
    
(*     List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to) |} context *)
(*     -> syntactically_safe context (Send msg_to msg) TyDontCare *)

| SafeReturn : forall {A} context (a : << A >>) sty,
    List.In {| cmd_type := A ; cmd_val := a ; safetyTy := sty |} context
    -> syntactically_safe context (Return a) sty

| SafeReturnUntyped : forall {A} context (a : << A >>),
    syntactically_safe context (Return a) TyDontCare

| SafeGen : forall context,
    syntactically_safe context Gen TyDontCare

| SafeDecrypt : forall context t (msg : crypto t),
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe context (Decrypt msg) TyRecvMsg
| SafeVerify : forall context t k msg,
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe context (@Verify t k msg) TyRecvMsg

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
    econstructor; simpl.

    intros; destruct (fst a ==n k_id); subst; clean_map_lookups; eauto.
    econstructor; simpl; eauto.
    destruct a; simpl; econstructor; eauto.

    econstructor; simpl; eauto.
    econstructor; simpl; eauto.

    intros; econstructor; subst; eauto.
    unfold msg_cipher_id in H; dependent destruction a0; try discriminate.
    invert H.
    unfold msg_to_this_user, msg_destination_user; context_map_rewrites; simpl.
    rewrite <- H2; simpl; trivial.

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
    intros; clean_map_lookups.

    econstructor; eauto.
    econstructor; eauto.
    
    intros.
    unfold msg_cipher_id in H.
    dependent destruction a2; try discriminate.
    invert H.
    econstructor; eauto.
    econstructor; simpl; eauto 8.
    unfold msg_to_this_user, msg_destination_user; context_map_rewrites.
    rewrite <- H2; simpl; trivial.
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
    (* \/ (exists t' msg cs tf, *)
    (*       key_rec = {| cmd_type := Crypto t' ; *)
    (*                    cmd_val  := msg ; *)
    (*                    safetyTy := TyRecvCphr |} *)
    (*       /\ findKeysCrypto cs msg $? k = Some tf ) *)
    \/ HonestKey context k
.
Proof.
  intros; subst.
  invert H0; simpl in *; split_ors; eauto 10.
Qed.

(* Lemma HonestKey_split : *)
(*   forall t (tv : <<t>>) styp k context key_rec, *)
(*     key_rec = {| cmd_type := t ; cmd_val := tv ; safetyTy := styp |} *)
(*     -> HonestKey (key_rec :: context) k *)
(*     -> (exists tf, key_rec = {| cmd_type := Base Access ; cmd_val := (k,tf) ; safetyTy := TyHonestKey |}) *)
(*     \/ (exists v, key_rec = {| cmd_type := UPair (Base Bool) (Message Access) ; *)
(*                          cmd_val := v ; *)
(*                          safetyTy := TyRecvMsg |}) *)
(*     \/ HonestKey context k *)
(* . *)
(* Proof. *)
(*   intros; subst. *)
(*   invert H0; simpl in *; split_ors; eauto 8. *)
(* Qed. *)

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
  forall ctx A (cmd : user_cmd A) sty,
    syntactically_safe ctx cmd sty
    -> forall ctx',
      List.Forall (fun styp => List.In styp ctx') ctx
      -> syntactically_safe ctx' cmd sty.
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
    specialize (H _ _ H1); split_ands; split; eauto 8.

  - econstructor.
    rewrite Forall_forall in *; intros; eauto.
    intros.
    specialize (H0 _ _ _ H2 H3 H4 H5); split_ands; eauto.
Qed.

Lemma step_user_steps_syntactically_safe :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> syntactically_safe ctx cmd sty

      -> exists ctx',
          List.Forall (fun styp => List.In styp ctx') ctx
          /\ syntactically_safe ctx' cmd' sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    try solve [ invert 1; intros; subst; eauto ];
    intros; subst; clean_context.

  invert H13.
  eapply IHstep_user in H6; eauto; split_ex.
  eexists; split; swap 1 2; eauto.
  econstructor; eauto; eauto.
  intros.
  specialize (H7 a); eauto.

  eapply syntactically_safe_add_ctx; eauto.
  econstructor; eauto.
  rewrite Forall_forall in *; intros; eauto.
  
  Unshelve.

  exact {| cmd_type := Base Nat ; cmd_val := 0 ; safetyTy := TyDontCare |}.
  econstructor.
  econstructor.
  exact {| cmd_type := Base Nat ; cmd_val := 0 ; safetyTy := TyDontCare |}.
Qed.

Definition typechecker_sound (ctx : list safe_typ) (honestk : key_perms) :=
  (forall kid, HonestKey ctx kid <-> honestk $? kid = Some true)
/\ (forall t msg msg_to k,
      List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} ctx
      -> exists c_id cs c,
        msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ cipher_to_user c = msg_to
        /\ cipher_signing_key c = k).

Lemma syntactically_safe_honest_keys_preservation :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> syntactically_safe ctx cmd sty

      -> forall honestk honestk' cmdc cmdc' u_id,
          suid = Some u_id
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> typechecker_sound ctx honestk
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
              /\ typechecker_sound ctx' honestk'
              /\ syntactically_safe ctx' cmd' sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    invert 1;
    unfold typechecker_sound;
    intros; subst;
      autorewrite with find_user_keys;
      eauto 10.

  - clean_context.
    eapply IHstep_user in H31; eauto.
    clear IHstep_user.
    split_ex; eauto.
    unfold typechecker_sound in H1; split_ands.
    eexists; repeat simple apply conj; eauto.
    econstructor; eauto.
    intros.
    eapply syntactically_safe_add_ctx; eauto.
    econstructor; eauto.
    rewrite Forall_forall in *; eauto.
    
  - eexists; repeat simple apply conj; swap 1 4; swap 2 4; split_ands; eauto 8.

    intros; simpl in H1; split_ors; eauto.
    eapply safe_typ_eq in H1; split_ands; subst.
    invert H4.
    invert H30; eauto.
    
    intros; split; intros;
      specialize (i kid); invert i; eauto.

    invert H30; eauto.
    eapply HonestKey_split in H1; split_ors; eauto.

  - invert H3; split_ands.
    clear H10.
    generalize (H1 k); intros IFF; destruct IFF; eauto.
    assert (msg_pattern_safe (findUserKeys usrs') (Signed k true)) as MPS; eauto.
    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by
        (eauto using accepted_safe_msg_pattern_honestly_signed).

    pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ex.
    pose proof (msg_honestly_signed_signing_key_honest _ _ _ MHS H12).
    specialize (H3 _ H12); split_ands.
    specialize (H15 H14); split_ands.
    rewrite message_no_adv_private_merge; eauto.
    
    eexists; repeat simple apply conj; eauto.
    intros KID; specialize (H1 KID); destruct H1; split; intros; eauto.
    eapply HonestKey_split with (t := Crypto t0) in H18; eauto.
    split_ors; split_ex; eauto.

    intros.
    simpl in H17; split_ors; eauto.
    eapply safe_typ_eq in H17; split_ands; subst; discriminate.

  - invert H3; split_ands.
    clear H10.
    generalize (H1 k__sign); intros IFF; destruct IFF; eauto.
    assert (msg_pattern_safe (findUserKeys usrs') (SignedEncrypted k__sign k__enc true)) as MPS by eauto.
    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by
        (eauto using accepted_safe_msg_pattern_honestly_signed).

    pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ex.
    pose proof (msg_honestly_signed_signing_key_honest _ _ _ MHS H12).
    specialize (H3 _ H12); split_ands.
    specialize (H15 H14); split_ands.
    rewrite message_no_adv_private_merge; eauto.
    
    eexists; repeat simple apply conj; eauto.
    intros KID; specialize (H1 KID); destruct H1; split; intros; eauto.
    eapply HonestKey_split_drop in H18; eauto; unfold not; intros; discriminate.

    intros.
    simpl in H17; split_ors; eauto.
    eapply safe_typ_eq in H17; split_ands; subst; discriminate.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros; specialize (i kid); destruct i; split; intros; eauto.
    eapply HonestKey_split_drop in H8; eauto; unfold not; intros; discriminate.

    intros.
    simpl in H5; split_ors; eauto.
    eapply safe_typ_eq in H5; split_ands; subst.
    invert H5.
    invert H7.
    (do 3 eexists); repeat simple apply conj; eauto.
    assert (cs0 $+ (c_id, SigEncCipher k k__encid msg_to0 (Some u_id0, cur_n0) msg) $? c_id = Some (SigEncCipher k k__encid msg_to0 (Some u_id0, cur_n0) msg)) as CS by (clean_map_lookups; eauto).
    exact CS.
    simpl; eauto.
    simpl; eauto.

  - unfold honest_users_only_honest_keys in *.
    specialize (H13 _ _ H5 _ _ H3); simpl in *.
    encrypted_ciphers_prop.
    rewrite message_only_honest_merge; eauto.

    eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split with (t := Message t0) in H10; eauto.
    split_ors; eauto.
    
    intros.
    simpl in H4; split_ors; eauto.
    eapply safe_typ_eq in H4; split_ands; subst; discriminate.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split_drop in H5; eauto; unfold not; intros; discriminate.

    intros.
    simpl in H2; split_ors; eauto.
    eapply safe_typ_eq in H2; split_ands; subst.
    invert H2; invert H4; eauto.

    intros.
    (* simpl in H5; split_ors; eauto. *)
    (* eapply safe_typ_eq in H5; split_ands; subst. *)
    (* invert H5. *)
    (* invert H7. *)
    (do 3 eexists); repeat simple apply conj; eauto.
    assert (cs0 $+ (c_id, SigCipher k msg_to0 (Some u_id0, cur_n0) msg) $? c_id = Some (SigCipher k msg_to0 (Some u_id0, cur_n0) msg)) as CS by (clean_map_lookups; eauto).
    exact CS.
    simpl; eauto.
    simpl; eauto.
    
  - unfold honest_users_only_honest_keys in *.
    specialize (H11 _ _ H6 _ _ H0); simpl in *.
    encrypted_ciphers_prop.

    eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split with (t := UPair (Base Bool) (Message t0)) in H8; eauto.
    split_ors; eauto.
    simpl in *.
    apply safe_typ_eq in H8; split_ands.
    invert H8.
    invert H15.
    simpl in *.
    dependent destruction msg; simpl in *.
    specialize (H18 (fst acc) (snd acc)).
    rewrite add_eq_o in H18.
    specialize (H18 eq_refl); split_ands; eauto.
    auto.
    
    intros.
    simpl in H5; split_ors; eauto.
    eapply safe_typ_eq in H5; split_ands; subst; discriminate.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros.
    + eapply HonestKey_split with (t := Base Access) in H5; eauto.
      split_ors; eauto.
      * apply safe_typ_eq in H5; split_ands.
        invert H10.
        invert H12; eauto.
      * destruct (k_id ==n KID); subst; eauto.

    + destruct (k_id ==n KID); subst; eauto.

    + intros.
      simpl in H0; split_ors; eauto.
      eapply safe_typ_eq in H0; split_ands; subst; discriminate.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros.
    + eapply HonestKey_split with (t := Base Access) in H5; eauto.
      split_ors; eauto.
      * apply safe_typ_eq in H5; split_ands.
        invert H10.
        invert H12; eauto.
      * destruct (k_id ==n KID); subst; eauto.

    + destruct (k_id ==n KID); subst; eauto.

    + intros.
      simpl in H0; split_ors; eauto.
      eapply safe_typ_eq in H0; split_ands; subst; discriminate.
    
Qed.
  

Lemma syntactically_safe_implies_next_cmd_safe'' :
  forall t (p : user_cmd t) ctx styp honestk u_id froms sents,
    syntactically_safe ctx p styp
    (* -> (forall kid, HonestKey ctx kid -> honestk $? kid = Some true) *)
    -> typechecker_sound ctx honestk
    -> exists cs,
        next_cmd_safe honestk cs u_id froms sents p.
Proof.
  Ltac pr :=
    repeat
      match goal with
      | [ H : nextAction _ _ |- _ ] => invert H
      | [ H : typechecker_sound _ _ |- _ ] => unfold typechecker_sound in H; split_ands
      | [ H : forall k, _ <-> _ |- _ $? ?k = _ ] =>
        specialize (H k); destruct H; split_ands
      | [ FKM : findKeysMessage _ $? _ = Some _ , H : (forall _ _, findKeysMessage _ $? _ = _ -> _)
          |- _ ] => specialize (H _ _ FKM)
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ |- _ /\ _ ] => simple apply conj
      | [ |- _ -> _ ] => intros
      end.
  
  induction 1; unfold next_cmd_safe; intros;
    split_ands.
    (* try solve [ *)
    (*       eexists; intros; pr; eauto *)
    (*       (* unfold typechecker_sound in *; *) *)
    (*       (* match goal with *) *)
    (*       (* | [ H : nextAction _ _ |- _ ] => invert H *) *)
    (*       (* end; eexists; eauto *) *)
    (*     ]. *)

  - specialize (IHsyntactically_safe H2); split_ex.
    eexists; intros.
    invert H4.
    specialize (H3 _ _ H8); eauto.

  - eexists; intros; pr; eauto.
  - eexists; intros; pr; eauto.
  - eexists; intros; pr; eauto.
    econstructor; econstructor; pr; eauto.
  - eexists; intros; pr; eauto.
    econstructor; econstructor; pr; eauto.
  - pr.
    specialize (H2 _ _ _ _ H); split_ex; subst.
    simpl in H0.
    specialize (H0 _ _ _ eq_refl H3 eq_refl eq_refl); split_ands.
    eexists; intros; pr; eauto.
    unfold msg_honestly_signed, msg_signing_key; context_map_rewrites.
    unfold honest_keyb.
    specialize (H1 (cipher_signing_key x1)); destruct H1; eauto.
    specialize (H1 H0); context_map_rewrites; trivial.

    econstructor; eauto.
    unfold msg_honestly_signed, msg_signing_key; context_map_rewrites.
    unfold honest_keyb.
    specialize (H1 (cipher_signing_key x1)); destruct H1; eauto.
    specialize (H1 H0); context_map_rewrites; trivial.
    
    (do 2 eexists); repeat simple apply conj; eauto.

    admit.
    admit.

Admitted.


(* Lemma syntactically_safe_implies_next_cmd_safe' : *)
(*   forall {t} (p : user_cmd t) pv sum sum' uid ks honestk cphrs all_cphrs sumsents froms n, *)
(*     syntactically_safe sum p pv sum' *)
(*     -> sum = {| me := uid ; *)
(*                hon_keys := ks ; *)
(*                sents := sumsents ; *)
(*                cnon := n ; *)
(*                cs := cphrs |} *)
(*     -> (forall k v, ks $? k = Some v -> honestk $? k = Some v \/ honestk $? k = Some true ) *)
(*     -> (forall k v, cphrs $? k = Some v -> all_cphrs $? k = Some v) *)
(*     -> next_cmd_safe honestk all_cphrs uid froms sumsents p. *)
(* Proof. *)
(*   intros. *)
(*   destruct sum. *)
(*   invert H0. *)
(*   eapply syntactically_safe_implies_next_cmd_safe'' in H; eauto. *)
(* Qed. *)

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
(* Lemma syntactically_safe_implies_next_cmd_safe : *)
(*   forall {A B} (U : universe A B), *)
(*     U_syntactically_safe U *)
(*     -> honest_cmds_safe U. *)
(* Proof. *)
(*   unfold U_syntactically_safe, honest_cmds_safe; intros. *)
(*   generalize (H _ _ H1 _ eq_refl); intros. *)
(*   split_ex; subst. *)

(*   pose proof (syntactically_safe_implies_next_cmd_safe'' _ _ _ H2). *)
(*   eapply syntactically_safe_implies_next_cmd_safe''. *)
(*   exact H2. *)
(*   unfold sum_init; reflexivity. *)
(*   intros * KH; eapply findUserKeys_has_user_key_or_better in KH; eauto. *)

(*   intros; eauto. *)
(* Qed. *)
