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
     List.

From SPICY Require Import
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
     SafetyAutomation.

Set Implicit Arguments.
Import RealWorld RealWorldNotations.

Import SafetyAutomation.

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

Inductive syntactically_safe (u_id : user_id) (uids : list user_id) :
  list safe_typ -> forall t, user_cmd t -> ty -> Prop :=

| SafeBind : forall {t t'} context (cmd1 : user_cmd t') t1,
    syntactically_safe u_id uids context cmd1 t1
    -> forall (cmd2 : <<t'>> -> user_cmd t) t2,
      (forall a, syntactically_safe u_id uids ({| cmd_type := t' ; cmd_val := a ; safetyTy := t1 |} :: context) (cmd2 a) t2)
      -> syntactically_safe u_id uids context (Bind cmd1 cmd2) t2

| SafeEncrypt : forall context {t} (msg : message t) k__sign k__enc msg_to,
    HonestKey context k__enc
    -> HonestKey context k__sign
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id)
    -> msg_to <> u_id
    -> List.In msg_to uids
    -> syntactically_safe u_id uids context (SignEncrypt k__sign k__enc msg_to msg) (TyMyCphr msg_to k__sign)

| SafeSign : forall context {t} (msg : message t) k msg_to,
    HonestKey context k
    -> (forall k_id kp, findKeysMessage msg $? k_id = Some kp -> HonestKey context k_id /\ kp = false)
    -> msg_to <> u_id
    -> List.In msg_to uids
    -> syntactically_safe u_id uids context (Sign k msg_to msg) (TyMyCphr msg_to k)

| SafeRecvSigned : forall context t k,
    HonestKey context k
    -> syntactically_safe u_id uids context (@Recv t (Signed k true)) TyRecvCphr

| SafeRecvEncrypted : forall context t k__sign k__enc,
    HonestKey context k__sign
    -> syntactically_safe u_id uids context (@Recv t (SignedEncrypted k__sign k__enc true)) TyRecvCphr

| SafeSend : forall context t (msg : crypto t) msg_to k,
    (* ~ List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TySent |} context *)
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} context
    -> syntactically_safe u_id uids context (Send msg_to msg) TyDontCare

| SafeReturn : forall {A} context (a : << A >>) sty,
    List.In {| cmd_type := A ; cmd_val := a ; safetyTy := sty |} context
    -> syntactically_safe u_id uids context (Return a) sty

| SafeReturnUntyped : forall {A} context (a : << A >>),
    syntactically_safe u_id uids context (Return a) TyDontCare

| SafeGen : forall context,
    syntactically_safe u_id uids context Gen TyDontCare

| SafeDecrypt : forall context t (msg : crypto t),
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe u_id uids context (Decrypt msg) TyRecvMsg
| SafeVerify : forall context t k msg,
    List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} context
    -> syntactically_safe u_id uids context (@Verify t k msg) TyRecvMsg

| SafeGenerateSymKey : forall context usage,
    syntactically_safe u_id uids context (GenerateSymKey usage) TyHonestKey
| SafeGenerateAsymKey : forall context usage,
    syntactically_safe u_id uids context (GenerateAsymKey usage) TyHonestKey
.

Definition compute_ids' {V} (m : NatMap.t V) :=
  List.map (fun '(k,_) => k) (elements m).

Definition compute_ids {V} (m : NatMap.t V) :=
  List.map (fun '(k,_) => k) (elements (mapi (fun k v => k) m)).
(* fold (fun k _ l => k :: l) m []. *)

Lemma list_setoidlist_iff :
  forall {V} (l : list (nat * V)) k v,
    List.In (k,v) l <-> SetoidList.InA (@eq_key_elt V) (k,v) l.
Proof.
  induction l; split; intros;
    repeat match goal with
           | [ H : eq_key_elt _ _ |- _ ] => invert H; simpl in *; subst
           | [ H : (_,_) = (_,_) |- _ ] => invert H
           | [ H : List.In _ [] |- _ ] => invert H
           | [ H : SetoidList.InA _ _ [] |- _ ] => invert H
           | [ H : List.In _ (?a :: _) |- _ ] => destruct a; simpl in H; split_ors
           | [ H : SetoidList.InA _ _ (?a :: _) |- _ ] => destruct a; invert H
           end; eauto 3.
  - econstructor; red; eauto using Raw.PX.eqke_refl.
  - eapply IHl in H; eauto.
  - eapply IHl in H1; eauto.
Qed.

Lemma in_ids_in_m :
  forall V (m : NatMap.t V) k,
    List.In k (compute_ids m)
    -> exists v,
      m $? k = Some v.
Proof.
  unfold compute_ids; intros *.
  induction m using map_induction_bis; intros; Equal_eq; eauto.
  contradiction.

  destruct (k ==n x); subst.
  - eexists; clean_map_lookups; eauto.
  - assert (List.In k (List.map (fun '(k, _) => k) (elements (elt:=Map.key) (mapi (fun (k : Map.key) (_ : V) => k) m)))).

    rewrite in_map_iff in H0 |- *; split_ex.
    destruct x0; subst.
    exists (k,k1); split; eauto.
    rewrite list_setoidlist_iff in *.
    rewrite <- elements_mapsto_iff in *.
    rewrite mapi_mapsto_iff in *; eauto.
    split_ex; subst.
    eexists; rewrite find_mapsto_iff in *; clean_map_lookups; eauto.

    clean_map_lookups; eauto.
Qed.


Lemma readd_user_in :
  forall V (m : NatMap.t V) k v v',
    m $? k = Some v
    -> List.map (fun '(k,_) => k) (elements (mapi (fun k _ => k) (m $+ (k,v'))))
      = List.map (fun '(k,_) => k) (elements (mapi (fun k _ => k) m)).
Proof.
  intros.

  assert ( mapi (fun k _ => k) (m $+ (k,v')) = mapi (fun k _ => k) m ).
  apply map_eq_Equal; unfold Equal; intros.
  cases (m $? y);
    destruct (y ==n k); subst; clean_map_lookups; eauto;
      rewrite !mapi_o; eauto;
        clean_map_lookups; eauto.

  rewrite <- H0; trivial.
Qed.

Lemma compute_userids_readd_idempotent :
  forall A (usrs : honest_users A) uid u u',
    usrs $? uid = Some u
    -> compute_ids (usrs $+ (uid,u')) = compute_ids usrs.
Proof.
  unfold compute_ids; intros; eauto using readd_user_in.
Qed.

Lemma user_step_nochange_uids :
  forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : user_data B)
    gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
    step_user lbl u_id bd bd'
    -> forall (cmd : user_cmd C),
      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> forall cmd',
        bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> compute_ids usrs' = compute_ids usrs.
Proof.
  induction 1; inversion 1; inversion 1; intros; subst; eauto;
    repeat match goal with
           | [ H : ?us $? ?uid = Some _ |- ?us $? ?uid <> None ] => solve [ rewrite H; intro C; invert C ]
           end.

  clean_context.
  erewrite compute_userids_readd_idempotent by eauto.
  trivial.
Qed.

Definition U_syntactically_safe {A B} (U : RealWorld.universe A B) :=
  forall u_id u uids,
    U.(users) $? u_id = Some u
    -> uids = compute_ids U.(users)
    -> forall ctx,
      ctx = init_context (elements u.(key_heap))
      -> exists t,
        syntactically_safe u_id uids ctx u.(protocol) t.

Hint Constructors
     HonestKey
     syntactically_safe
  : core.

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
  forall ctx u_id uids A (cmd : user_cmd A) sty,
    syntactically_safe u_id uids ctx cmd sty
    -> forall ctx',
      List.Forall (fun styp => List.In styp ctx') ctx
      -> syntactically_safe u_id uids ctx' cmd sty.
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
    eapply H0 in H4; split_ands; subst; eauto.
Qed.

Definition typingcontext_sound (ctx : list safe_typ)
           (* (honestk : key_perms) *)
           {A} (usrs : honest_users A)
           (* (honestk : key_perms) *)
           (cs : ciphers)
           (* (ks : key_perms) *)
           (u_id : user_id) :=
  (forall kid, HonestKey ctx kid -> (findUserKeys usrs) $? kid = Some true)
(* /\ (forall kid, ks $? kid = Some true -> HonestKey ctx kid) *)
/\ (forall t msg msg_to k,
      List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := (TyMyCphr msg_to k) |} ctx
      -> exists c_id c,
        msg = SignedCiphertext c_id
        /\ cs $? c_id = Some c
        /\ cipher_to_user c = msg_to
        /\ cipher_signing_key c = k
        /\ fst (cipher_nonce c) = Some u_id
        /\ HonestKey ctx k
        (* clauses to ensure sends aren't stuck *)
        /\ u_id <> msg_to
        /\ (exists rec_u, usrs $? msg_to = Some rec_u)
        /\ (exists me, usrs $? u_id = Some me
               /\ incl [c_id] me.(c_heap)
               /\ keys_mine me.(key_heap) (findKeysCrypto cs msg))
  )
(* /\ (forall t msg, *)
(*       List.In {| cmd_type := Crypto t ; cmd_val := msg ; safetyTy := TyRecvCphr |} ctx *)
(*       -> forall kid kp, *)
(*         findKeysCrypto cs msg $? kid = Some kp -> HonestKey ctx kid) *)
.

(* Lemma in_userids_in_usrs : *)
(*   forall V (m : NatMap.t V) k, *)
(*     List.In k (List.map (fun '(k,_) => k) (elements m)) *)
(*     -> exists v, *)
(*       m $? k = Some v. *)
(* Proof. *)
(* Admitted. *)

Ltac process_ctx1 :=
  match goal with
  | [ H : ?x = ?x |- _ ] => clear H
  | [ H : Crypto _ = Crypto _ |- _ ] => invert H
  | [ H : TyMyCphr _ _  = _ |- _ ] => invert H
  | [ H : UPair _ _ = UPair _ _ |- _ ] => invert H
  | [ H : (_,_) = (_,_) |- _ ] => invert H
  | [ H : {| cmd_type := _ |} = {| cmd_type := _ |} |- _ ] => eapply safe_typ_eq in H; split_ex; subst; try discriminate
  | [ H : _ ~= _ |- _ ] => invert H
  | [ H : syntactically_safe _ _ _ (Return _) _ |- _ ] => invert H
  | [ H : syntactically_safe _ _ _ _ (TyMyCphr _ _) |- _ ] => invert H
  | [ H1 : ?m $? ?k = _ , H2 : ?m $? ?k = _ |- _ ] => clean_map_lookups
  | [ H : List.In _ (compute_ids _) |- _] =>
    apply in_ids_in_m in H; split_ex
  (* | [ H : (forall _ _ _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] => *)
  (*   specialize (H _ _ _ _ ARG); split_ex; subst *)
  (* | [ H : (forall _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] => *)
  (*   specialize (H _ _ ARG) *)
  | [ H : (forall _ _ _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] =>
    eapply H in ARG; split_ex; subst
  | [ H : (forall _ _, List.In _ ?ctx -> exists _ _, _), ARG : List.In _ ?ctx |- _ ] =>
    eapply H in ARG; split_ex
    (* specialize (H _ _ ARG) *)
  | [ H : HonestKey ({| cmd_type := ?cty |} :: _) ?kid |- context [ ?kid ] ] =>
    eapply (@HonestKey_split cty _ _ _ _ _ eq_refl) in H; split_ors
  | [ |- incl _ (c_heap _) ] => progress simpl
  | [ H : incl _ (c_heap _) |- _ ] => progress ( simpl in H )
  | [ |- keys_mine (key_heap _) _ ] => progress ( simpl )
  | [ H : keys_mine (key_heap _) _ |- _ ] => progress ( simpl in * )
  | [ H : List.In _ (_ :: _) |- _ ] => simpl in H; split_ors
  | [ HK : HonestKey ?ctx ?k, H : (forall _, HonestKey ?ctx _  -> _) |- _ ] =>
    match goal with
    | [ H : findUserKeys _ $? k = Some true |- _ ] => fail 1
    | _ => idtac
    end;
    generalize (H _ HK); intros
  (* (forall kid, HonestKey ctx kid -> (findUserKeys usrs) $? kid = Some true) *)
  (* | [ HK : HonestKey ?ctx _, H : (forall _, HonestKey ?ctx _  -> _) |- _ ] => *)
  (*   generalize (H _ HK); intros; clear HK *)
  | [ H : Some _ <> None -> ?non = (Some ?uid, ?curn) |- _ ] =>
    assert (non = (Some uid,curn)) by (eapply H; congruence); subst; clear H
                                                                
  | [ |- incl [?x] (?x :: _) ] =>
    let LIN := fresh "LIN"
    in  unfold incl; intros * LIN; simpl in LIN; split_ors; try contradiction; subst
  | [ |- keys_mine _ (match _ $+ (?k1,_) $? ?k2 with _ => _ end) ] =>
    (progress clean_map_lookups)
    || (destruct (k1 ==n k2); subst; clean_map_lookups)
  | [ |- keys_mine _ (match _ $+ (?k1,_) $? ?k2 with _ => _ end) ] =>
    (progress clean_map_lookups)
    || (destruct (k1 ==n k2); subst; clean_map_lookups)
  | [ |- _ $k++ _ $? _ = Some true ] => solve_perm_merges
  | [ |- exists _ _, _ ] => (do 2 eexists); repeat simple apply conj
  | [ |- exists _, _ ] => eexists; repeat simple apply conj
  end.

Ltac process_ctx := repeat process_ctx1.

Hint Constructors
     RealWorld.msg_accepted_by_pattern 
     RealWorld.honest_key
     RealWorld.msg_pattern_safe
  : core.
Hint Extern 1 (List.In _ _) => progress simpl : core.
Hint Extern 1 (_ $+ (_,_) $? _ = _) => progress clean_map_lookups : core.
Hint Extern 1 (_ $+ (?k1,_) $? ?k2 = _) =>
  solve [ destruct (k1 ==n k2); subst; clean_map_lookups; trivial ] : core.


(* Lemma syntactically_safe_nochange_usrs_ks_mycs : *)
(*   forall  *)

Lemma keys_mine_addln_keys :
  forall ks1 ks2 ks3,
    keys_mine ks1 ks3
    -> keys_mine (ks1 $k++ ks2) ks3.
Proof.
  unfold keys_mine; intros.
  apply H in H0; split_ors; split_ex; subst.
  - cases (ks2 $? k_id); destruct kp;
      try solve [ left; solve_perm_merges ].
    destruct b; solve_perm_merges; eauto.

  - right; split; eauto.
    solve_perm_merges.
Qed.

Lemma keys_mine_new_honestk :
  forall kid ks1 ks2,
    keys_mine ks1 ks2
    -> keys_mine (add_key_perm kid true ks1) ks2.
Proof.
  unfold keys_mine, add_key_perm; intros.
  apply H in H0.
  destruct (kid ==n k_id); subst;
    split_ors; clean_map_lookups;
      solve_perm_merges; eauto.

  destruct kp; eauto.
Qed.

Hint Resolve keys_mine_addln_keys keys_mine_new_honestk : core.
Hint Resolve incl_appr incl_tl : core.

Lemma syntactically_safe_honest_keys_preservation' :
  forall {A B C} suid lbl bd bd',

    step_user lbl suid bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall honestk cmdc cmdc' u_id usrs'' uids,
          suid = Some u_id
          -> uids = compute_ids usrs
          -> syntactically_safe u_id uids ctx cmd sty
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmdc;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> typingcontext_sound ctx usrs cs u_id
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> usrs'' = usrs' $+ (u_id, {| key_heap := ks';
                                        protocol := cmdc';
                                        msg_heap := qmsgs';
                                        c_heap   := mycs';
                                        from_nons := froms';
                                        sent_nons := sents';
                                        cur_nonce := cur_n' |})

          -> exists ctx',
              List.Forall (fun styp => List.In styp ctx') ctx
              /\ typingcontext_sound ctx' usrs'' cs' u_id
              /\ syntactically_safe u_id uids ctx' cmd' sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    invert 3;
    unfold typingcontext_sound;
    intros; subst;
      autorewrite with find_user_keys;
      try solve [
            split_ands; eexists; process_ctx; repeat simple apply conj; swap 1 4; intros; eauto;
            repeat (progress (process_ctx; eauto))
          ].

  - clean_context.
    eapply IHstep_user in H33; eauto.
    clear IHstep_user.
    split_ex.
    unfold typingcontext_sound in H1; split_ands.
    eexists; repeat simple apply conj; eauto.
    econstructor; eauto.
    intros.
    eapply syntactically_safe_add_ctx; eauto.
    econstructor; eauto.
    rewrite Forall_forall in *; eauto.

  - split_ex; clean_context.
    (* invert H; split_ands; clean_context. *)
    eapply H5 in H39; split_ex; subst.
    progress clean_map_lookups.
    eexists; process_ctx.
    repeat simple apply conj; swap 1 4; eauto.
    intros.
    destruct (msg_to ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.
    
  - split_ex; eexists; process_ctx; repeat simple apply conj; swap 1 4; intros; eauto;
      repeat (progress (process_ctx; eauto)).

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

      -> forall honestk u_id uids usrs'',
          suid = Some u_id
          -> uids = compute_ids usrs
          -> usrs $? u_id = Some {| key_heap := ks;
                                   protocol := cmd;
                                   msg_heap := qmsgs;
                                   c_heap   := mycs;
                                   from_nons := froms;
                                   sent_nons := sents;
                                   cur_nonce := cur_n |}
          -> syntactically_safe u_id uids ctx cmd sty
          -> typingcontext_sound ctx usrs cs u_id
          -> honestk  = findUserKeys usrs
          -> message_queue_ok honestk cs qmsgs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> honest_users_only_honest_keys usrs
          -> usrs'' = usrs' $+ (u_id, {| key_heap := ks';
                                        protocol := cmd';
                                        msg_heap := qmsgs';
                                        c_heap   := mycs';
                                        from_nons := froms';
                                        sent_nons := sents';
                                        cur_nonce := cur_n' |})

          -> exists ctx',
              List.Forall (fun styp => List.In styp ctx') ctx
              /\ typingcontext_sound ctx' usrs'' cs' u_id
              /\ syntactically_safe u_id uids ctx' cmd' sty
.
Proof.
  intros; subst; eapply syntactically_safe_honest_keys_preservation'; eauto.
Qed.

  Lemma syntactically_safe_adv_step_preservation :
  forall {A B C} lbl bd bd',

    step_user lbl None bd bd'

    -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
        (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
        froms froms' sents sents' cur_n cur_n' ctx sty,

      bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
      -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')

      -> forall u_id uids u u' cmda,
          uids = compute_ids usrs
          -> usrs $? u_id = Some u
          -> usrs' $? u_id = Some u'
          -> syntactically_safe u_id uids ctx u.(protocol) sty
          -> typingcontext_sound ctx usrs cs u_id
          -> adv = mkUserData ks cmda qmsgs mycs froms sents cur_n
          -> exists ctx',
              List.Forall (fun styp => List.In styp ctx') ctx
              /\ typingcontext_sound ctx' usrs' cs' u_id
              /\ syntactically_safe u_id uids ctx' u'.(protocol) sty
.
Proof.
  induction 1; inversion 1; inversion 1;
    intros;
    subst;
    clean_map_lookups;
    simpl in *;
    eauto.

  - destruct (rec_u_id ==n u_id); subst; clean_map_lookups; simpl.
    
    + eexists; repeat simple apply conj; swap 1 3; eauto.
      unfold typingcontext_sound in *; split_ex; repeat simple apply conj; process_ctx; eauto; intros.
      autorewrite with find_user_keys; process_ctx; eauto.
      destruct (u_id ==n msg_to);
        subst; clean_map_lookups; process_ctx; eauto.

    +  eexists; repeat simple apply conj; swap 1 3; eauto.
       unfold typingcontext_sound in *; split_ex; repeat simple apply conj; process_ctx; eauto; intros.
       autorewrite with find_user_keys; process_ctx; eauto.
       destruct (rec_u_id ==n msg_to);
         subst; clean_map_lookups; process_ctx; eauto.

  - eexists; repeat simple apply conj; swap 1 3; eauto.
    unfold typingcontext_sound in *; split_ex; repeat simple apply conj; process_ctx; eauto; intros.
    process_ctx; eauto.

  - eexists; repeat simple apply conj; swap 1 3; eauto.
    unfold typingcontext_sound in *; split_ex; repeat simple apply conj; process_ctx; eauto; intros.
    process_ctx; eauto.

Qed.

Definition syntactically_safe_U {A B} (U : universe A B) :=
  forall uid u uids,
    U.(users) $? uid = Some u
    -> uids = compute_ids U.(users)
    -> exists sty ctx,
      syntactically_safe uid uids ctx u.(protocol) sty
      /\ typingcontext_sound ctx U.(users) U.(all_ciphers) uid.

Lemma syntactically_safe_na :
  forall A uid uids ctx (p : user_cmd A) sty,
    syntactically_safe uid uids ctx p sty
    -> forall B (p__n : user_cmd B),
      nextAction p p__n
      -> exists sty', syntactically_safe uid uids ctx p__n sty'.
Proof.
  induction 1; try solve [ invert 1; eauto ]; intros.
Qed.

Lemma typingcontext_sound_ok_nochange_usrs_ks_mycs :
  forall A (usrs : honest_users A) uid uid' cs ks cmd qmsgs mycs froms sents n ctx,
    usrs $? uid = Some (mkUserData ks cmd qmsgs mycs froms sents n)
    -> typingcontext_sound ctx usrs cs uid'
    -> forall cmd' qmsgs' froms' sents' n',
        typingcontext_sound ctx
                            (usrs $+ (uid, mkUserData ks cmd' qmsgs' mycs froms' sents' n'))
                            cs uid'.
Proof.
  unfold typingcontext_sound; intros; eauto.
  destruct (uid ==n uid'); subst; clean_map_lookups;
    autorewrite with find_user_keys; split_ands; repeat simple apply conj; eauto.
  
  intros * LIN;
    eapply H1 in LIN; split_ex; subst;
      process_ctx; eauto.

  intros * LIN;
    eapply H1 in LIN; split_ex; subst; eauto.

  destruct (uid ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
    process_ctx; eauto.
Qed.

Hint Resolve typingcontext_sound_ok_nochange_usrs_ks_mycs : core.

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
          -> syntactically_safe u_id1 (compute_ids usrs) ctx__step cmd sty
          -> typingcontext_sound ctx__step usrs cs u_id1
          -> typingcontext_sound ctx usrs cs u_id2
          -> typingcontext_sound ctx (usrs' $+ (u_id1,
                                               mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n')) cs' u_id2.
Proof.
  induction 1; inversion 1; inversion 1;
    intros; subst; autorewrite with find_user_keys; eauto.

  - invert H30; eauto.
  - msg_queue_prop.
    unfold typingcontext_sound in *; repeat simple apply conj; intros; split_ands; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    
    assert (msg_pattern_safe (findUserKeys usrs') pat) by (invert H38; eauto).
    assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.
    unfold msg_honestly_signed in H13.
    destruct (msg_signing_key cs' msg); try discriminate.
    rewrite <- honest_key_honest_keyb in H13.
    specialize (H2 _ eq_refl); split_ands.
    specialize (H14 H13); split_ands.
    eapply H5 in H3; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups;
      process_ctx; eauto.

  - destruct (rec_u_id ==n u_id1); subst; clean_map_lookups; eauto.

    unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    eapply H4 in H9; split_ex; subst.
    destruct (rec_u_id ==n u_id2);
    destruct (rec_u_id ==n cipher_to_user x0);
      destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.

  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    eapply H7 in H12; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.

  - user_cipher_queues_prop.
    encrypted_ciphers_prop.

    unfold typingcontext_sound in *; repeat simple apply conj; intros; split_ands; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.

    eapply H10 in H4; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.

  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    apply H5 in H10; eauto; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.
    
  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    eapply H1 in H6; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.

  - unfold typingcontext_sound in *; split_ands; split; intros; eauto.
    autorewrite with find_user_keys; process_ctx; eauto.
    eapply H1 in H6; split_ex; subst.
    destruct (u_id1 ==n cipher_to_user x0); subst; clean_map_lookups; eauto;
      process_ctx; eauto.

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
      -> forall (cmd : user_cmd C) honestk ctx styp uids,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honestk = findUserKeys usrs
          -> uids = compute_ids usrs
          -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> keys_and_permissions_good gks usrs adv.(key_heap)
          -> syntactically_safe u_id uids ctx cmd styp
          -> typingcontext_sound ctx usrs cs u_id
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
    induction 1; inversion 2; invert 6; inversion 3; intros; subst;
      try discriminate;
      eauto 2;
      autorewrite with find_user_keys in *;
      try keys_and_permissions_prop;
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
      eapply H33 in FKM; split_ex; eauto.
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
      -> forall (cmd : user_cmd C) honestk uids,
          honestk = findUserKeys usrs
          -> uids = compute_ids usrs
          -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honest_users_only_honest_keys usrs
          -> forall ctx styp, syntactically_safe u_id uids ctx cmd styp
          -> typingcontext_sound ctx usrs cs u_id
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
    induction 1; inversion 4; inversion 6; intros;
      subst;
      autorewrite with find_user_keys.

    invert H16.
    eapply IHstep_user in H8; eauto.

    all : eauto; clean_context.

    - unfold honest_users_only_honest_keys in *; intros.
      destruct (u_id ==n u_id0); subst; clean_map_lookups; eauto;
        simpl in *;
        rewrite findUserKeys_readd_user_addnl_keys; eauto.

      specialize (H12 _ _ H29); simpl in *.

      assert (msg_pattern_safe (findUserKeys usrs') pat) by
          (unfold typingcontext_sound in *; split_ex; invert H24; eauto).
      
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
        specialize (H14 _ _ H1); split_ands; subst; clean_map_lookups; eauto.

      + generalize (msg_honestly_signed_has_signing_key_cipher_id _ _ _ MHS); intros; split_ands; split_ex.
        eapply msg_honestly_signed_signing_key_honest in MHS; eauto.
        unfold msg_cipher_id in H2; destruct msg; try discriminate;
          clean_context; simpl in *.
        cases (cs' $? c_id); try discriminate.
        clean_context; invert MHS.
        destruct c; simpl in *; clean_map_lookups; eauto.
        encrypted_ciphers_prop; eauto.
        specialize (H14 _ _ H1); split_ands; subst; clean_map_lookups; eauto.

      + eapply H12 in H0; eauto.
        solve_perm_merges; eauto.

    - unfold honest_users_only_honest_keys in *; intros.
      assert (rec_u_id <> u_id) by (unfold not; intros; subst; contradiction).
      destruct (u_id ==n u_id0); destruct (u_id ==n rec_u_id);
        subst;
        try contradiction;
        clean_map_lookups;
        simpl in *;
        eauto.

      + generalize H28; intros; eapply H11 in H28; eauto.
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

      specialize (H12 _ _ H29); simpl in *.
      apply merge_perms_split in H9; split_ors;
        match goal with
        | [ ARG : findKeysMessage _ $? _ = Some _, H : (forall _ _, findKeysMessage _ $? _ = Some _ -> _) |- _ ] =>
          specialize (H _ _ ARG)
        | [ H : (forall _ _, ?ks $? _ = Some _ -> _), ARG : ?ks $? _ = Some _ |- _ ] => specialize (H _ _ ARG)
        end; solve_perm_merges; eauto.
      
      eapply H12 in H6; eauto; solve_perm_merges; eauto.
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
          -> forall ctx styp uids, syntactically_safe u_id uids ctx cmd styp
          -> typingcontext_sound ctx usrs cs u_id
          -> uids = compute_ids usrs
          -> lbl = Action a
          -> forall cmd',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> forall cmdc cmdc' usrs'' ud',
                usrs $? u_id = Some {| key_heap := ks ; msg_heap := qmsgs ; protocol := cmdc ; c_heap := mycs ; from_nons := froms ; sent_nons := sents ; cur_nonce := cur_n |}
                -> ud' = {| key_heap := ks'; protocol := cmdc'; msg_heap := qmsgs' ; c_heap := mycs' ; from_nons := froms' ; sent_nons := sents' ; cur_nonce := cur_n' |}
                -> usrs'' = usrs' $+ (u_id, ud')
                -> encrypted_ciphers_ok (findUserKeys usrs'') cs' gks'.
  Proof.
    induction 1; inversion 4; inversion 5; intros; subst; try discriminate;
      eauto 2; autorewrite with find_user_keys;
        clean_context; eauto.

    invert H4.
    eapply IHstep_user in H9; eauto.

    unfold typingcontext_sound in *; split_ex.
    assert (msg_pattern_safe (findUserKeys usrs') pat) by
        (unfold typingcontext_sound in *; split_ex; invert H12; eauto).
    msg_queue_prop; eapply encrypted_ciphers_ok_addnl_pubk; auto.
    specialize_msg_ok; eauto.
  Qed.

  Lemma honest_labeled_step_user_cipher_queues_ok_ss :
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
              -> forall ctx styp uids, syntactically_safe u_id uids ctx cmd styp
              -> typingcontext_sound ctx usrs cs u_id
              -> uids = compute_ids usrs
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
          (unfold typingcontext_sound in *; split_ex; invert H37; eauto).

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

  Lemma honest_labeled_step_message_queues_ok_ss :
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
              -> forall ctx styp uids, syntactically_safe u_id uids ctx cmd styp
              -> typingcontext_sound ctx usrs cs u_id
              -> uids = compute_ids usrs
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
          (unfold typingcontext_sound in *; split_ex; invert H39; eauto).

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

      + eapply H27 in H20; split_ex; subst.
        eapply H18 in H15; split_ex; clean_map_lookups.

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

  Definition adv_goodness {A} (usrs : honest_users A)
             (cs : ciphers) (gks : keys) (msgs : queued_messages) (mycs : my_ciphers) :=
    Forall (fun sigm => match sigm with
                     | (existT _ _ m) =>
                       (* (forall cid, msg_cipher_id m = Some cid -> cs $? cid <> None) *)
                       (forall k kp,
                           findKeysCrypto cs m $? k = Some kp
                           -> gks $? k <> None /\ (kp = true -> (findUserKeys usrs) $? k <> Some true))
                     (* /\ (forall k, *)
                     (*       msg_signing_key cs m = Some k *)
                     (*       -> gks $? k <> None) *)
                     /\ (forall c_id, List.In c_id (findCiphers m) -> exists c, cs $? c_id = Some c)
                     end) msgs
  /\ Forall (fun cid => exists c, cs $? cid = Some c) mycs.

  Lemma adv_step_adv_no_honest_keys_ss :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> mycs = adv.(c_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> adv_no_honest_keys honestk ks
        -> keys_and_permissions_good gks usrs ks
        -> adv_goodness usrs cs gks qmsgs mycs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> adv_no_honest_keys honestk' ks'.
  Proof.
    induction 1; inversion 1; inversion 8; intros; subst;
      eauto 2; autorewrite with find_user_keys; eauto;
        try rewrite add_key_perm_add_private_key; clean_context;
          match goal with
          | [ H : keys_and_permissions_good _ _ _ |- _ ] => unfold keys_and_permissions_good in H; split_ands
          end.

    - invert H26; split_ex.
      eapply break_msg_queue_prop in H2; split_ex.
      unfold adv_no_honest_keys in *; intros.
      specialize (H24 k_id); intuition idtac.
      right; right; intuition eauto.
      eapply merge_perms_split in H9; split_ors; auto.
      eapply H2 in H9; split_ex; eauto.
      
    - assert (adv_no_honest_keys (findUserKeys usrs') (key_heap adv')) as ADV by assumption.
      specialize (ADV k__encid); split_ors; split_ands; try contradiction;
        encrypted_ciphers_prop; clean_map_lookups; intuition idtac;
          unfold adv_no_honest_keys; intros;
            specialize (H24 k_id); clean_map_lookups; intuition idtac;
              right; right; split; eauto; intros;
                eapply merge_perms_split in H10; split_ors;
                  try contradiction;
                  specialize (H19 _ _ H10); split_ex; split_ands; eauto.

    - eapply adv_no_honest_keys_after_new_adv_key; eauto.
    - eapply adv_no_honest_keys_after_new_adv_key; eauto.

  Qed.

  Lemma honest_labeled_step_adv_no_honest_keys_ss :
    forall {A B C} u_id suid cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd' a,
      step_user lbl suid bd bd'
      -> suid = Some u_id
      -> forall (cmd : user_cmd C) honestk,
          bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
          -> honestk = findUserKeys usrs
          -> message_queues_ok cs usrs gks
          -> encrypted_ciphers_ok honestk cs gks
          -> user_cipher_queues_ok cs honestk usrs
          -> adv_no_honest_keys honestk adv.(key_heap)
          -> forall cmd' honestk',
              bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
              -> lbl = Action a
              -> forall ctx styp uids, syntactically_safe u_id uids ctx cmd styp
              -> typingcontext_sound ctx usrs cs u_id
              -> uids = compute_ids usrs
              -> forall cmdc cmdc' usrs'',
                  usrs $? u_id = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
                  -> usrs'' = usrs' $+ (u_id, mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n')
                  -> honestk' = findUserKeys usrs''
                  -> adv_no_honest_keys honestk' adv'.(key_heap).
  Proof.
    induction 1; inversion 2; inversion 6; intros; subst;
      try discriminate;
      autorewrite with find_user_keys;
      clean_context.

    - invert H31.
      eapply IHstep_user in H6; eauto.

    - assert (msg_pattern_safe (findUserKeys usrs') pat) by (unfold typingcontext_sound in *; split_ex; invert H39; eauto).
      msg_queue_prop; specialize_msg_ok;
        unfold adv_no_honest_keys, message_no_adv_private in *;
        simpl in *;
        repeat
          match goal with
          | [ RW : honest_keyb ?honk ?kid = _ , H : if honest_keyb ?honk ?kid then _ else _ |- _] => rewrite RW in H
          | [ H : (forall k_id, findUserKeys _ $? k_id = None \/ _) |- (forall k_id, _) ] => intro KID; specialize (H KID)
          | [ |- context [ _ $k++ $0 ] ] => rewrite merge_keys_right_identity
          | [ FK : findKeysCrypto _ ?msg $? ?kid = Some _, H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)
              |- context [ _ $k++ findKeysCrypto _ ?msg $? ?kid] ] => specialize (H _ _ FK); split_ands; try solve_perm_merges
          | [ FK : findKeysCrypto _ ?msg $? ?kid = None |- context [ ?uks $k++ findKeysCrypto _ ?msg $? ?kid] ] =>
            split_ors; split_ands; solve_perm_merges
          | [ H : (forall k p, findKeysCrypto _ ?msg $? k = Some p -> _)  |- context [ _ $k++ findKeysCrypto ?cs ?msg $? ?kid] ] =>
            match goal with
            | [ H : findKeysCrypto cs msg $? kid = _ |- _ ] => fail 1
            | _ => cases (findKeysCrypto cs msg $? kid)
            end
          end; eauto.

      split_ors; split_ands; contra_map_lookup; eauto.

    - unfold typingcontext_sound in *; split_ex; invert H38; process_ctx.
      unfold adv_no_honest_keys in *; intros.
      specialize (H24 k_id).
      split_ex; subst; simpl in *.
      assert (List.In x mycs') by eauto.
      user_cipher_queues_prop.
      rewrite CipherTheory.cipher_honestly_signed_honest_keyb_iff in H12.
      encrypted_ciphers_prop; eauto.
      intuition idtac.
      right; right; split; eauto; intros.
      solve_perm_merges;
        specialize (H17 _ _ H18); split_ands; discriminate.
  Qed.

  Lemma adv_step_keys_good_ss :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C),
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> ks = adv.(key_heap)
        -> mycs = adv.(c_heap)
        -> adv_goodness usrs cs gks qmsgs mycs
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> keys_and_permissions_good gks usrs ks
        -> forall cmd',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> keys_and_permissions_good gks' usrs' ks'.
  Proof.
    induction 1; inversion 1; inversion 6; intros; subst; try discriminate;
      eauto; clean_context.

    - unfold keys_and_permissions_good in *; intuition eauto.
      unfold permission_heap_good in *; intros.
      cases (key_heap adv' $? k_id); eauto.
      hnf in H22; split_ex.
      eapply break_msg_queue_prop in H3; split_ex.
      cases (findKeysCrypto cs' msg $? k_id); solve_perm_merges.
      specialize (H3 _ _ H9); split_ex; subst.
      cases (gks' $? k_id); try contradiction; eauto.
    - destruct rec_u; simpl in *.
      eapply keys_and_permissions_good_readd_user_same_perms; eauto.
    - unfold keys_and_permissions_good in *; intuition eauto.
      unfold permission_heap_good in *; intros.
      eapply merge_perms_split in H5; split_ors; eauto.
      encrypted_ciphers_prop; clean_map_lookups; eauto.
      + specialize_msg_ok; split_ex; intuition eauto.
      + assert (permission_heap_good gks' (findUserKeys usrs')) by eauto.
        specialize_msg_ok; subst.
        specialize (H9 _ _ H20); eauto.

    - unfold keys_and_permissions_good in *; intuition eauto.
      destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
      rewrite Forall_natmap_forall in *; intros.
      eapply permission_heap_good_addnl_key; eauto.
    - unfold keys_and_permissions_good in *; intuition eauto.
      destruct (k_id ==n k_id0); subst; clean_map_lookups; eauto.
      rewrite Forall_natmap_forall in *; intros.
      eapply permission_heap_good_addnl_key; eauto.
  Qed.

  Lemma adv_step_message_queues_ok_ss :
    forall {A B C} cs cs' lbl (usrs usrs' : honest_users A) (adv adv' : user_data B)
      gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' bd bd',
      step_user lbl None bd bd'
      -> forall (cmd : user_cmd C) honestk,
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> honestk = findUserKeys usrs
        -> ks = adv.(key_heap)
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> encrypted_ciphers_ok honestk cs gks
        -> message_queues_ok cs usrs gks
        -> permission_heap_good gks honestk
        -> permission_heap_good gks ks
        -> adv_goodness usrs cs gks qmsgs mycs
        -> forall cmd' honestk',
            bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
            -> honestk' = findUserKeys usrs'
            -> message_queues_ok cs' usrs' gks'.
  Proof.
    induction 1; inversion 1; inversion 10; intros; subst;
      eauto 2; try discriminate; eauto;
        clean_context.
    
    unfold message_queues_ok in *;
      rewrite Forall_natmap_forall in *;
      intros.

    destruct (rec_u_id ==n k); subst; clean_map_lookups;
      eauto;
      autorewrite with find_user_keys;
      simpl; eauto.

    unfold message_queue_ok; eapply Forall_app.
    unfold message_queue_ok in *; econstructor; eauto.

    repeat (apply conj); intros; eauto.
    - specialize (H0 _ _ H); split_ors; split_ands; subst; eauto.
      specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
      specialize (H26 _ _ H0); unfold not; intros; split_ex; contra_map_lookup.
    - unfold not; intros.
      unfold keys_mine in *.
      destruct msg; simpl in *; try discriminate; clean_context.

      unfold adv_goodness in *; split_ex.
      rewrite Forall_forall in H5.

      assert (List.In cid (c_heap adv)) as LIN by eauto.
      specialize (H5 _ LIN); split_ex; split_ands; contra_map_lookup.
    - unfold msg_signing_key in *; destruct msg; try discriminate;
        cases (cs' $? c_id); try discriminate;
          clean_context.
      simpl in *; context_map_rewrites.

      encrypted_ciphers_prop; simpl in *; eauto;
        clean_context; intuition clean_map_lookups; eauto;
          unfold message_no_adv_private; intros; simpl in *; context_map_rewrites;
            repeat
              match goal with
              | [ ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] => is_var b; destruct b
              | [ H : (forall k, findKeysMessage ?msg $? k = Some ?b -> _), ARG : findKeysMessage ?msg $? _ = Some ?b |- _ ] =>
                specialize (H _ ARG)
              | [ H : honest_key ?honk ?k, H2 : ?honk $? ?k = Some true -> False |- _ ] => invert H; contradiction
              end; try contradiction; clean_map_lookups; eauto.
  Qed.

  Lemma honest_step_adv_goodness :
    forall {A B C} suid lbl bd bd',
      step_user lbl suid bd bd'

      -> forall u_id cs cs' (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd C)
          gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        suid = Some u_id
        -> bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> message_queues_ok cs usrs gks
        -> encrypted_ciphers_ok (findUserKeys usrs) cs gks
        -> user_cipher_queues_ok cs (findUserKeys usrs) usrs
        -> keys_and_permissions_good gks usrs adv.(key_heap)
        -> adv_goodness usrs cs gks adv.(msg_heap) adv.(c_heap)
        -> forall ctx styp uids, syntactically_safe u_id uids ctx cmd styp
        -> typingcontext_sound ctx usrs cs u_id
        -> uids = compute_ids usrs
        -> forall cmdc cmdc' usrs'',
            usrs $? u_id = Some (mkUserData ks cmdc qmsgs mycs froms sents cur_n)
            -> usrs'' = usrs' $+ (u_id, mkUserData ks' cmdc' qmsgs' mycs' froms' sents' cur_n')
            -> adv_goodness usrs'' cs' gks' adv'.(msg_heap) adv'.(c_heap).

  Proof.
    induction 1; inversion 2; inversion 1; intros; subst;
      eauto;
      unfold adv_goodness in *;
      autorewrite with find_user_keys; eauto;
        clean_context.

    - invert H30.
      eapply IHstep_user in H6; eauto.

    - assert (msg_pattern_safe (findUserKeys usrs') pat)
        by (unfold typingcontext_sound in *; invert H38; split_ex; eauto).
      assert (msg_honestly_signed (findUserKeys usrs') cs' msg = true) by eauto.
      split_ex; split; eauto.
      generalize H0; intros; eapply msg_honestly_signed_has_signing_key_cipher_id in H0; split_ex.
      msg_queue_prop.
      specialize_msg_ok.
      rewrite honestk_merge_new_msgs_keys_same; eauto.

    - simpl; autorewrite with find_user_keys.
      unfold typingcontext_sound in *; invert H37; split_ex.
      process_ctx.

      split_ex; split; eauto.
      rewrite Forall_app; econstructor; eauto.
      split; intros; eauto.

      + encrypted_ciphers_prop; simpl in *; clean_map_lookups.
        eapply H18 in H9; split_ex; subst; eauto.
        keys_and_permissions_prop.
        specialize (H20 _ _ H9); split_ex.
        unfold not; split; intros; clean_map_lookups.

      + simpl in *; split_ors; subst; try contradiction; eauto.

    - rewrite !Forall_forall in *; split_ex; split; intros; eauto.

      + destruct x; intros; eauto.
        eapply H5 in H8; eauto.
        unfold typingcontext_sound in *; invert H40; process_ctx; eauto.
        split_ex; split; intros; eauto.
        * unfold findKeysCrypto in *; context_map_rewrites; destruct c; eauto.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        * destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.

      + destruct (c_id ==n x); subst; clean_map_lookups; eauto.

    - unfold typingcontext_sound in *; invert H38; split_ex; process_ctx.
      split; eauto.
      user_cipher_queues_prop.
      encrypted_ciphers_prop.
      rewrite honestk_merge_new_msgs_keys_dec_same; eauto.

    - rewrite !Forall_forall in *; split_ex; split; intros; eauto.

      + destruct x; intros; eauto; simpl in *.
        eapply H3 in H6; eauto; split_ex.
        unfold typingcontext_sound in *; invert H38; process_ctx; eauto.
        split_ex; split; intros; eauto.
        * unfold findKeysCrypto in *; context_map_rewrites; destruct c; eauto.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
          eapply H14 in H4; split_ex; subst.
          eapply H9 in H4.
          keys_and_permissions_prop.
          eapply H18 in H4; split_ex; split; intros; clean_map_lookups.
          
        * destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.

      + destruct (c_id ==n x); subst; clean_map_lookups; eauto.

    - split_ex; split; eauto.
      
      rewrite !Forall_forall in *; split_ex; intros; eauto.
      destruct x; intros.
      eapply H0 in H2; split_ex; split; intros; eauto.
      eapply H2 in H4; split_ex; split; intros; eauto.

      destruct (k_id ==n k); subst; clean_map_lookups.
      destruct (k_id ==n k); subst; clean_map_lookups; eauto.

    - split_ex; split; eauto.
      
      rewrite !Forall_forall in *; split_ex; intros; eauto.
      destruct x; intros.
      eapply H0 in H2; split_ex; split; intros; eauto.
      eapply H2 in H4; split_ex; split; intros; eauto.

      destruct (k_id ==n k); subst; clean_map_lookups.
      destruct (k_id ==n k); subst; clean_map_lookups; eauto.

  Qed.

  Lemma adv_step_adv_goodness :
    forall {A B C} lbl bd bd',
      step_user lbl None bd bd'

      -> forall cs cs' (usrs usrs' : honest_users A) (adv adv' : user_data B) (cmd cmd' : user_cmd C)
          gks gks' ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n',

        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> qmsgs = adv.(msg_heap)
        -> mycs = adv.(c_heap)
        -> keys_and_permissions_good gks usrs ks
        -> adv_no_honest_keys (findUserKeys usrs) ks
        -> adv_goodness usrs cs gks qmsgs mycs
        -> adv_goodness usrs' cs' gks' qmsgs' mycs'.
  Proof.
    induction 1; inversion 1; inversion 1; intros; subst;
      eauto;
      unfold adv_goodness in *;
      autorewrite with find_user_keys;
      simpl;
      eauto;
      clean_context. 

    - split_ex.
      eapply break_msg_queue_prop in H; split_ex; split; eauto.
      clear H1; rewrite Forall_forall in *; intros.
      rewrite in_app_iff in H1; split_ors; eauto.

    (* Recv Drop rule *)
    (* - split_ex. *)
    (*   invert H; split; eauto. *)

    - split_ex; split;
        rewrite Forall_forall in *; intros.

      + destruct x; intros; eauto.
        eapply H5 in H8; split_ex; split; intros; eauto.

        * destruct c; simpl in *; eauto.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        * destruct c; simpl in *; try contradiction.
          specialize (H9 _ H10); split_ex.
          split_ors; subst; try contradiction.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        
      + simpl in *; split_ors; subst; eauto.
        eapply H7 in H8; split_ex.
        destruct (c_id ==n x); subst; clean_map_lookups; eauto.

    - split_ex; split;
        rewrite Forall_forall in *; intros.

      + destruct x; intros; eauto.
        eapply H3 in H6; split_ex; split; intros; eauto.

        * destruct c; simpl in *; eauto.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
          split.
          ** unfold keys_and_permissions_good in H34; split_ex.
             specialize (H2 _ _ H8).
             unfold permission_heap_good in H11; split_ors; eauto; unfold not; intros;
               eapply H11 in H2; split_ex; clean_map_lookups.

          ** specialize (H35 k); intros; subst; unfold not; intros.
             specialize (H2 _ _ H8).
             split_ors; clean_map_lookups; eauto.
          
        * destruct c; simpl in *; try contradiction.
          specialize (H7 _ H8); split_ex.
          split_ors; subst; try contradiction.
          destruct (c_id ==n c_id0); subst; clean_map_lookups; eauto.
        
      + simpl in *; split_ors; subst; eauto.
        eapply H5 in H6; split_ex.
        destruct (c_id ==n x); subst; clean_map_lookups; eauto.
        
    - split_ex; split; eauto.
      rewrite Forall_forall in *; eauto; intros.
      destruct x; intros.
      eapply H0 in H2; eauto.
      split_ex; split; intros; eauto.
      eapply H2 in H4; eauto; split_ex; split; eauto.
      destruct (k ==n k_id); subst; clean_map_lookups; eauto.

    - split_ex; split; eauto.
      rewrite Forall_forall in *; eauto; intros.
      destruct x; intros.
      eapply H0 in H2; eauto.
      split_ex; split; intros; eauto.
      eapply H2 in H4; eauto; split_ex; split; eauto.
      destruct (k ==n k_id); subst; clean_map_lookups; eauto.
  Qed.

  Definition goodness_predicates {A B} (U : universe A B) : Prop :=
    let honestk := findUserKeys U.(users)
    in  encrypted_ciphers_ok honestk U.(all_ciphers) U.(all_keys)
      /\ keys_and_permissions_good U.(all_keys) U.(users) U.(adversary).(key_heap)
      /\ user_cipher_queues_ok U.(all_ciphers) honestk U.(users)
      /\ message_queues_ok U.(all_ciphers) U.(users) U.(all_keys)
      /\ honest_users_only_honest_keys U.(users)
      /\ adv_goodness U.(users) U.(all_ciphers) U.(all_keys) U.(adversary).(msg_heap) U.(adversary).(c_heap)
      /\ adv_no_honest_keys honestk U.(adversary).(key_heap).
      (* /\ adv_cipher_queue_ok U.(all_ciphers) U.(users) U.(adversary).(c_heap) *)
      (* /\ adv_message_queue_ok U.(users) U.(all_ciphers) U.(all_keys) U.(adversary).(msg_heap). *)

  Lemma goodness_preservation_stepU :
    forall {A B} (U U' : universe A B) suid lbl,
      step_universe suid U lbl U'
      -> syntactically_safe_U U
      -> goodness_predicates U
      -> goodness_predicates U'.
  Proof.
    intros.

    invert H.

    - unfold goodness_predicates, syntactically_safe_U in *; simpl in *.
      destruct lbl0, U, userData;
        unfold build_data_step in *; simpl in *;
          specialize (H0 _ _ _ H2 eq_refl); split_ex; simpl in *.
    
      + autorewrite with find_user_keys; repeat simple apply conj; eauto.

        eapply silent_user_step_encrypted_ciphers_ok; eauto.
        eapply honest_silent_step_keys_good; eauto.
        eapply honest_silent_step_user_cipher_queues_ok; eauto.
        eapply honest_silent_step_message_queues_ok; eauto; keys_and_permissions_prop; eauto.
        eapply honest_users_only_honest_keys_honest_steps; eauto.
        eapply honest_step_adv_goodness; eauto.
        eapply honest_silent_step_adv_no_honest_keys; eauto.

      + repeat simple apply conj.
        eapply honest_labeled_step_encrypted_ciphers_ok; eauto.
        eapply honest_labeled_step_keys_and_permissions_good; eauto.
        eapply honest_labeled_step_user_cipher_queues_ok_ss; eauto.
        eapply honest_labeled_step_message_queues_ok_ss; eauto.
        eapply honest_users_only_honest_keys_honest_steps; eauto.
        eapply honest_step_adv_goodness; eauto.
        eapply honest_labeled_step_adv_no_honest_keys_ss; eauto.

    - simpl.
      unfold goodness_predicates, build_data_step in *;
        destruct U, adversary;
        split_ex; simpl in *.

      repeat simple apply conj.

      eapply adv_step_encrypted_ciphers_ok; eauto.
      eapply adv_step_keys_good_ss; eauto.
      eapply adv_step_user_cipher_queues_ok; eauto.

      unfold keys_and_permissions_good in *; split_ex.
      eapply adv_step_message_queues_ok_ss; eauto.

      eapply honest_users_only_honest_keys_adv_steps; eauto.
      eapply adv_step_adv_goodness; eauto.
      eapply adv_step_adv_no_honest_keys_ss; eauto.
  Qed.

  (* Lemma goodness_preservation_step : *)
  (*   forall t__hon t__adv (st st' : universe t__hon t__adv * IdealWorld.universe t__hon) b, *)
  (*     step st st' *)
  (*     -> lameAdv b (fst st).(adversary) *)
  (*     -> syntactically_safe_U (fst st) *)
  (*     -> goodness_predicates (fst st) *)
  (*     -> goodness_predicates (fst st'). *)
  (* Proof. *)
  (*   inversion 1; intros; subst; simpl in *; eapply goodness_preservation_stepU; eauto. *)
  (* Qed. *)

  Lemma step_user_nochange_that_user_in_honest_users :
    forall {A B C} suid lbl bd bd',
      step_user lbl suid bd bd'
      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n',
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> forall u_id1 ud1,
            suid = Some u_id1
            -> usrs $? u_id1 = Some ud1
            -> usrs' $? u_id1 = Some ud1.
  Proof.
    induction 1; inversion 1; inversion 1;
      intros; subst; eauto.
  Qed.

  Lemma step_back_into_other_user :
    forall {A B C} suid lbl bd bd',
      step_user lbl suid bd bd'
      -> forall cs cs' (usrs usrs': honest_users A) (adv adv' : user_data B) gks gks'
          (cmd cmd' : user_cmd C) ks ks' qmsgs qmsgs' mycs mycs'
          froms froms' sents sents' cur_n cur_n',
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> forall cmdc u_id1 u_id2 ks2 cmdc2 qmsgs2 mycs2 froms2 sents2 cur_n2,
            suid = Some u_id1
            -> u_id1 <> u_id2
            -> usrs $? u_id1 = Some {| key_heap := ks;
                                      protocol := cmdc;
                                      msg_heap := qmsgs;
                                      c_heap   := mycs;
                                      from_nons := froms;
                                      sent_nons := sents;
                                      cur_nonce := cur_n |}
            -> usrs' $? u_id2 = Some {| key_heap := ks2;
                                       protocol := cmdc2;
                                       msg_heap := qmsgs2;
                                       c_heap   := mycs2;
                                       from_nons := froms2;
                                       sent_nons := sents2;
                                       cur_nonce := cur_n2 |}
            -> usrs $? u_id2 = Some {| key_heap := ks2;
                                      protocol := cmdc2;
                                      msg_heap := qmsgs2;
                                      c_heap   := mycs2;
                                      from_nons := froms2;
                                      sent_nons := sents2;
                                      cur_nonce := cur_n2 |}
              \/ exists m qmsgs2',
                qmsgs2 = qmsgs2' ++ [m]
                /\ usrs $? u_id2 = Some {| key_heap := ks2;
                                          protocol := cmdc2;
                                          msg_heap := qmsgs2';
                                          c_heap   := mycs2;
                                          from_nons := froms2;
                                          sent_nons := sents2;
                                          cur_nonce := cur_n2 |}.
  Proof.
    induction 1; inversion 1; inversion 1;
      intros; subst; eauto.

    destruct (rec_u_id ==n u_id2); subst; clean_map_lookups; eauto.
    destruct rec_u; eauto.
  Qed.

  Lemma impact_from_other_user_step :
    forall {A B C} lbl suid1 bd bd',
      step_user lbl suid1 bd bd'
                
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
          u_id1 u_id2 ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C),
        
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> suid1 = Some u_id1
        -> u_id1 <> u_id2
        -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
            usrs $? u_id2 = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists m,
              usrs' $? u_id2 = Some (mkUserData ks2 cmd2 (qmsgs2 ++ m) mycs2 froms2 sents2 cur_n2).
  Proof.
    induct 1; inversion 1; inversion 2; intros; subst;
      clean_context;
      match goal with
      | [ H : (_,_,_,_,_,_,_,_,_,_,_) = (_,_,_,_,_,_,_,_,_,_,_) |- _ ] => invert H
      end;
      clean_map_lookups;
      try solve [ exists []; rewrite app_nil_r; trivial ];
      eauto.

    destruct (rec_u_id ==n u_id2); subst; clean_map_lookups;
      repeat simple apply conj; trivial; eauto.
    exists []; rewrite app_nil_r; trivial.
  Qed.

  Lemma impact_from_adv_step :
    forall {A B C} lbl bd bd',
      step_user lbl None bd bd'
                
      -> forall (usrs usrs' : honest_users A) (adv adv' : user_data B) cs cs' gks gks'
          u_id ks ks' qmsgs qmsgs' mycs mycs' froms froms' sents sents' cur_n cur_n' (cmd cmd' : user_cmd C),
        
        bd = (usrs, adv, cs, gks, ks, qmsgs, mycs, froms, sents, cur_n, cmd)
        -> bd' = (usrs', adv', cs', gks', ks', qmsgs', mycs', froms', sents', cur_n', cmd')
        -> forall cmda, adv = mkUserData ks cmda qmsgs mycs froms sents cur_n
        -> forall ks2 qmsgs2 mycs2 froms2 sents2 cur_n2 cmd2,
            usrs' $? u_id = Some (mkUserData ks2 cmd2 qmsgs2 mycs2 froms2 sents2 cur_n2)
            -> exists qmsgs2' m,
                qmsgs2' ++ m = qmsgs2
             /\  usrs $? u_id = Some (mkUserData ks2 cmd2 qmsgs2' mycs2 froms2 sents2 cur_n2).
  Proof.
    induction 1; inversion 1; inversion 1; intros; subst;
      eauto;
      try solve [ exists qmsgs2; exists []; rewrite app_nil_r; eauto ].

    simpl in *; clean_context.
    destruct (rec_u_id ==n u_id); subst; clean_map_lookups.
    exists rec_u.(msg_heap); exists [existT crypto t0 msg]; split; eauto; destruct rec_u; trivial.
    exists qmsgs2; exists[]; rewrite app_nil_r; eauto.
  Qed.

  Lemma syntactically_safe_U_preservation_stepU :
    forall A B (U U' : universe A B) suid lbl,
      step_universe suid U lbl U'
      -> goodness_predicates U
      -> syntactically_safe_U U
      -> syntactically_safe_U U'.
  Proof.
    intros * STEP GOOD SS.
    invert STEP.

    unfold syntactically_safe_U, build_data_step in *; destruct U; destruct userData;
      simpl in *; intros.
    unfold goodness_predicates in *; split_ex; simpl in *.
    msg_queue_prop; subst.

    pose proof (step_user_nochange_that_user_in_honest_users H0 eq_refl eq_refl eq_refl H).
    erewrite compute_userids_readd_idempotent by eauto.
    erewrite user_step_nochange_uids by eauto.

    destruct (u_id ==n uid); subst; clean_map_lookups; simpl.
    - specialize (SS _ _ _ H eq_refl); split_ex; simpl in *.
      eapply syntactically_safe_honest_keys_preservation in H0; eauto.
      split_ex; eauto.

    - generalize H0; intros STEP.
      destruct u; generalize STEP; intros STEP'.
      eapply step_back_into_other_user in STEP; simpl; eauto.
      
      split_ors; split_ex; subst.
      + subst.
        generalize (SS _ _ _ H eq_refl); intros; split_ex.
        specialize (SS _ _ _ H11 eq_refl); split_ex; simpl in *.
        (do 2 eexists); split; eauto.
        eapply typingcontext_sound_other_user_step; eauto.
      + subst.
        generalize (SS _ _ _ H eq_refl); intros; split_ex.
        specialize (SS _ _ _ H12 eq_refl); split_ex; simpl in *.
        (do 2 eexists); split; eauto.
        eapply typingcontext_sound_other_user_step; eauto.

    - unfold buildUniverseAdv; simpl.
      unfold syntactically_safe_U in *; intros; simpl in *.
      destruct U, adversary; unfold build_data_step in *; simpl in *.
      destruct u; simpl in *.
      subst; erewrite user_step_nochange_uids by eauto.
      pose proof (impact_from_adv_step H _ eq_refl eq_refl eq_refl H0); split_ex.
      generalize (SS _ _ _ H2 eq_refl); simpl; intros; split_ex; eauto.
      eapply syntactically_safe_adv_step_preservation in H; eauto; simpl in *; split_ex; eauto.
  Qed.

End PredicatePreservation.
