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
     PartialOrderReduction.

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
.

Fixpoint init_context (ks : list key_permission) : list safe_typ :=
  match ks with
  | []         => []
  | (kp :: kps) =>
    {| cmd_type := Base Access ; cmd_val := kp ; safetyTy := TyHonestKey |} :: init_context kps
  end.

Lemma foo : 
  forall cs cid c t (msg : crypto t) msg_to u_id k,
    msg_cipher_id msg = Some cid
    -> cs $? cid = Some c
    -> k = cipher_signing_key c
    -> msg_to = cipher_to_user c
    -> fst (cipher_nonce c) = Some u_id
    -> msg_to_this_user cs (Some msg_to) msg = true (* only send my messages *)
.
Proof.
  intros; subst.
  unfold msg_to_this_user, msg_destination_user.
  unfold msg_cipher_id in H; destruct msg; try discriminate.
  invert H; context_map_rewrites.
  destruct (cipher_to_user c ==n cipher_to_user c); subst; try contradiction; eauto.
Qed.

Inductive syntactically_safe (u_id : user_id) :
  list safe_typ -> forall t, user_cmd t -> ty -> Prop :=

| SafeBind : forall {t t'} context (cmd1 : user_cmd t') t1,
    syntactically_safe u_id context cmd1 t1
    -> forall (cmd2 : <<t'>> -> user_cmd t) t2,
      (forall a, syntactically_safe u_id ({| cmd_type := t' ; cmd_val := a ; safetyTy := t1 |} :: context) (cmd2 a) t2)
      -> syntactically_safe u_id context (Bind cmd1 cmd2) t2

| SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to,
    HonestKey context k__enc
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id)
    -> syntactically_safe u_id context (SignEncrypt k__sign k__enc msg_to msg) (TyMyCphr msg_to k__sign)

| SafeSign : forall context {t} (msg : message t) k msg_to,
    (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id /\ kp = false)
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
    econstructor; simpl.

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
  invert H0; simpl in *; split_ors; eauto 10.
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
    specialize (H _ _ H1); split_ands; split; eauto 8.
Qed.

Lemma step_user_steps_syntactically_safe :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' u_id ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> suid = Some u_id

      -> syntactically_safe u_id ctx cmd sty

      -> exists ctx',
          List.Forall (fun styp => List.In styp ctx') ctx
          /\ syntactically_safe u_id ctx' cmd' sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    try solve [ invert 1; intros; subst; eauto ];
    intros; subst; clean_context.

  - invert H25.
    eapply IHstep_user in H6; eauto; split_ex.
    eexists; split; swap 1 2; eauto.
    econstructor; eauto; eauto.
    intros.
    specialize (H7 a); eauto.

    eapply syntactically_safe_add_ctx; eauto.
    econstructor; eauto.
    rewrite Forall_forall in *; intros; eauto.

  - invert H24; eauto.
Qed.

Definition typechecker_sound (ctx : list safe_typ) (honestk : key_perms) (cs : ciphers) (u_id : user_id) :=
  (forall kid, HonestKey ctx kid <-> honestk $? kid = Some true)
/\ (forall t msg msg_to k,
      List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} ctx
      -> exists c_id c,
        msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ cipher_to_user c = msg_to
        /\ cipher_signing_key c = k
        /\ fst (cipher_nonce c) = Some u_id
        /\ HonestKey ctx k).

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
          -> typechecker_sound ctx honestk cs u_id
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
              /\ typechecker_sound ctx' honestk' cs' u_id
              /\ syntactically_safe u_id ctx' cmd' sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    invert 2;
    unfold typechecker_sound;
    intros; subst;
      autorewrite with find_user_keys;
      eauto 8.

  - clean_context.
    eapply IHstep_user in H32; eauto.
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

    intros; simpl in H2; split_ors; eauto.
    eapply safe_typ_eq in H2; split_ands; subst.
    invert H7.
    invert H31; eauto.

    specialize (e _ _ _ _ H8); split_ex; eauto 12.
    specialize (e _ _ _ _ H2); split_ex; eauto 12.
    
    intros; split; intros;
      specialize (i kid); invert i; eauto.

    invert H31; eauto.
    eapply HonestKey_split in H2; split_ors; eauto.

  - invert H2; split_ands.
    clear H10.
    generalize (H0 k); intros IFF; destruct IFF; eauto.
    assert (msg_pattern_safe (findUserKeys usrs') (Signed k true)) as MPS; eauto.
    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by
        (eauto using accepted_safe_msg_pattern_honestly_signed).

    pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ex.
    pose proof (msg_honestly_signed_signing_key_honest _ _ _ MHS H12).
    specialize (H5 _ H12); split_ands.
    specialize (H15 H14); split_ands.
    rewrite message_no_adv_private_merge; eauto.
    
    eexists; repeat simple apply conj; eauto.
    intros KID; specialize (H0 KID); destruct H0; split; intros; eauto.
    eapply HonestKey_split with (t := Crypto t0) in H18; eauto.
    split_ors; split_ex; eauto.

    intros.
    simpl in H17; split_ors; eauto.
    eapply safe_typ_eq in H17; split_ands; subst; discriminate.

    specialize (H9 _ _ _ _ H17); split_ex; eauto 12.

  - invert H2; split_ands.
    clear H10.
    generalize (H0 k__sign); intros IFF; destruct IFF; eauto.
    assert (msg_pattern_safe (findUserKeys usrs') (SignedEncrypted k__sign k__enc true)) as MPS; eauto.
    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) as MHS by
        (eauto using accepted_safe_msg_pattern_honestly_signed).

    pose proof (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); split_ex.
    pose proof (msg_honestly_signed_signing_key_honest _ _ _ MHS H12).
    specialize (H5 _ H12); split_ands.
    specialize (H15 H14); split_ands.
    rewrite message_no_adv_private_merge; eauto.
    
    eexists; repeat simple apply conj; eauto.
    intros KID; specialize (H0 KID); destruct H0; split; intros; eauto.
    eapply HonestKey_split with (t := Crypto t0) in H18; eauto.
    split_ors; split_ex; eauto.

    intros.
    simpl in H17; split_ors; eauto.
    eapply safe_typ_eq in H17; split_ands; subst; discriminate.

    specialize (H9 _ _ _ _ H17); split_ex; eauto 12.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros; specialize (i kid); destruct i; split; intros; eauto.
    eapply HonestKey_split_drop in H13; eauto; unfold not; intros; discriminate.

    intros.
    simpl in H6; split_ors; eauto.

    + eapply safe_typ_eq in H6; split_ands; subst.
      invert H6.
      invert H7.
      (do 2 eexists); repeat simple apply conj; eauto.

      specialize (i k); destruct i.
      assert (HonestKey ctx k) by eauto; eauto.
      
    + specialize (e _ _ _ _ H6); split_ex; subst.
      (do 2 eexists); repeat simple apply conj; eauto.

  - unfold honest_users_only_honest_keys in *.
    specialize (H12 _ _ H4 _ _ H3); simpl in *.
    encrypted_ciphers_prop.
    rewrite message_only_honest_merge; eauto.

    eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split with (t := Message t0) in H13; eauto.
    split_ors; eauto.
    
    intros.
    simpl in H5; split_ors; eauto.
    eapply safe_typ_eq in H5; split_ands; subst; discriminate.

    specialize (e _ _ _ _ H5); split_ex; eauto 12.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split_drop in H10; eauto; unfold not; intros; discriminate.

    intros.
    simpl in H3; split_ors; eauto.
    
    + eapply safe_typ_eq in H3; split_ands; subst.
      invert H3; invert H10; eauto.
      invert H4.

      (do 2 eexists); repeat simple apply conj; simpl; eauto.

      specialize (i k); destruct i;
        assert (HonestKey ctx k) by eauto; eauto.
      
    + specialize (e _ _ _ _ H3); split_ex; subst.
      (do 2 eexists); repeat simple apply conj; eauto.
    
  - unfold honest_users_only_honest_keys in *.
    specialize (H10 _ _ H5 _ _ H0); simpl in *.
    encrypted_ciphers_prop.

    eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros; eauto.
    eapply HonestKey_split with (t := UPair (Base Bool) (Message t0)) in H11; eauto.
    split_ors; eauto.
    simpl in *.
    apply safe_typ_eq in H11; split_ands.
    invert H11.
    invert H15.
    simpl in *.
    dependent destruction msg; simpl in *.
    specialize (H18 (fst acc) (snd acc)).
    rewrite add_eq_o in H18.
    specialize (H18 eq_refl); split_ands; eauto.
    auto.
    
    intros.
    simpl in H6; split_ors; eauto.
    eapply safe_typ_eq in H6; split_ands; subst; discriminate.

    specialize (e _ _ _ _ H6); split_ex; subst; eauto 12.
    
  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros.
    + eapply HonestKey_split with (t := Base Access) in H8; eauto.
      split_ors; eauto.
      * apply safe_typ_eq in H8; split_ands.
        invert H10.
        invert H12; eauto.
      * destruct (k_id ==n KID); subst; eauto.

    + destruct (k_id ==n KID); subst; eauto.

    + intros.
      simpl in H1; split_ors; eauto.
      eapply safe_typ_eq in H1; split_ands; subst; discriminate.

      specialize (e _ _ _ _ H1); split_ex; subst; eauto 12.

  - eexists; repeat simple apply conj; split_ands; eauto.
    intros KID; specialize (i KID); destruct i; split; intros.
    + eapply HonestKey_split with (t := Base Access) in H8; eauto.
      split_ors; eauto.
      * apply safe_typ_eq in H8; split_ands.
        invert H10.
        invert H12; eauto.
      * destruct (k_id ==n KID); subst; eauto.

    + destruct (k_id ==n KID); subst; eauto.

    + intros.
      simpl in H1; split_ors; eauto.
      eapply safe_typ_eq in H1; split_ands; subst; discriminate.

      specialize (e _ _ _ _ H1); split_ex; subst; eauto 12.
Qed.

Lemma step_na_return :
  forall {A B C D} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' r,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> @nextAction C D cmd (Return r)
      -> usrs = usrs'
        /\ adv = adv'
        /\ cs = cs'
        /\ gks = gks'
        /\ ks = ks'
        /\ qmsgs = qmsgs'
        /\ mycs = mycs'
        /\ froms = froms'
        /\ sents = sents'
        /\ cur_n = cur_n'
        /\ (forall cs'' (usrs'': honest_users A) (adv'' : user_data B) gks'' ks'' qmsgs'' mycs'' froms'' sents'' cur_n'',
              step_user lbl suid
                        (usrs'', adv'', cs'', gks'', ks'', qmsgs'', mycs'', froms'', sents'', cur_n'', cmd)
                        (usrs'', adv'', cs'', gks'', ks'', qmsgs'', mycs'', froms'', sents'', cur_n'', cmd')).
Proof.
  induction 1; inversion 1; inversion 1; intros; subst;
    match goal with
    | [ H : nextAction _ _ |- _ ] => invert H
    end; eauto.

  - eapply IHstep_user in H5; eauto; intuition (subst; eauto).
    econstructor; eauto.

  - invert H4.
    intuition idtac.
    econstructor.
Qed.

Lemma step_na_not_return :
  forall {A B C D} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) (cmd__n : user_cmd D) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n',

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
      -> nextAction cmd cmd__n
      -> (forall r, cmd__n <> Return r)
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

Hint Resolve syntactically_safe_honest_keys_preservation'.

Lemma syntactically_safe_honest_keys_preservation :
  forall {A B} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        cmd cmd' ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall C honestk honestk' (cmd__n cmd__n' : user_cmd C) u_id,
          suid = Some u_id
          -> nextAction cmd cmd__n
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmd;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> syntactically_safe u_id ctx cmd sty
          (* -> next_cmd_safe honestk cs u_id froms sents cmd *)
          -> typechecker_sound ctx honestk cs u_id
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
              /\ typechecker_sound ctx' honestk' cs' u_id
              /\ syntactically_safe u_id ctx' cmd' sty
.
Proof.
  intros; subst.

  specialize (nextAction_couldBe H3); intros.
  cases cmd__n; intros; try contradiction; clean_context.

  - eapply step_na_return in H3;
      eauto; split_ands; subst; eauto.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.

  - eapply step_na_not_return in H3; intros; eauto.
    split_ex; subst; eauto.

    unfold not; intros; discriminate.
Qed.

Lemma syntactically_safe_implies_next_cmd_safe'' :
  forall t (p : user_cmd t) ctx styp honestk u_id cs froms sents,
    syntactically_safe u_id ctx p styp
    -> typechecker_sound ctx honestk cs u_id
    -> next_cmd_safe honestk cs u_id froms sents p.
Proof.
  Ltac pr :=
    repeat
      match goal with
      | [ H : nextAction _ _ |- _ ] => invert H
      | [ H : typechecker_sound _ _ _ _ |- _ ] => unfold typechecker_sound in H; split_ands
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

  - invert H3; eapply IHsyntactically_safe; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
    econstructor; econstructor; pr; eauto.
  - intros; pr; eauto.
    econstructor; econstructor; pr; eauto.
  - pr; specialize (H1 _ _ _ _ H); split_ex; subst.
       
    unfold msg_honestly_signed, msg_signing_key; context_map_rewrites.
    unfold honest_keyb.
    specialize (H0 (cipher_signing_key x0)); destruct H0; eauto.
    specialize (H0 H6); context_map_rewrites; trivial.

    unfold msg_to_this_user, msg_destination_user; context_map_rewrites.
    destruct (cipher_to_user x0 ==n cipher_to_user x0); subst; try contradiction; trivial.

    econstructor; eauto.
    unfold msg_honestly_signed, msg_signing_key; context_map_rewrites.
    unfold honest_keyb.
    specialize (H0 (cipher_signing_key x0)); destruct H0; eauto.
    specialize (H0 H6); context_map_rewrites; trivial.
    
    (do 2 eexists); repeat simple apply conj; eauto.

    admit.

  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
  - intros; pr; eauto.
    
Admitted.

Lemma syntactically_safe_implies_safety :
  forall t__hon t__adv st st',
    U_syntactically_safe (fst st)
    -> (fst st).(all_ciphers) = $0
    -> @step t__hon t__adv st st'
    -> ~ safety st
    -> ~ safety st'.
Admitted.


Lemma safety_violation_step :
  forall t__hon t__adv st st',
    @step t__hon t__adv st st'
    -> ~ safety st
    -> ~ safety st'.
Proof.
  induct 1; unfold safety; simpl; intros.

Admitted.


Lemma safety_violation_steps :
  forall t__hon t__adv st st',
    (@step t__hon t__adv)^* st st'
    -> ~ safety st
    -> ~ safety st'.
Proof.
  induct 1; eauto using safety_violation_step.
Qed.
