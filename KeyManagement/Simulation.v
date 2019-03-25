From Coq Require Import
     List
     Eqdep
     Program.Equality (* for dependent induction *)
.


Require Import MyPrelude Users Common MapLtac. 

Require IdealWorld
        RealWorld.

Import IdealWorld.IdealNotations
       RealWorld.RealWorldNotations.

Set Implicit Arguments.

Ltac invert H :=
  (MyPrelude.invert H || (inversion H; clear H));
  repeat match goal with
         (* | [ x : _ |- _ ] => subst x *)
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
         end.

Hint Resolve in_eq in_cons.

Definition rstepSilent {A B : Type} (U1 U2 : RealWorld.universe A B) :=
  RealWorld.step_universe U1 Silent U2.

Definition istepSilent {A : Type} (U1 U2 : IdealWorld.universe A) :=
  IdealWorld.lstep_universe U1 Silent U2.

Inductive chan_key : Set :=
| Public (ch_id : IdealWorld.channel_id)
| Auth (ch_id : IdealWorld.channel_id): forall k,
    k.(RealWorld.keyUsage) = RealWorld.Signing -> chan_key
| Enc  (ch_id : IdealWorld.channel_id) : forall k,
    k.(RealWorld.keyUsage) = RealWorld.Encryption -> chan_key
| AuthEnc (ch_id : IdealWorld.channel_id) : forall k1 k2,
      k1.(RealWorld.keyUsage) = RealWorld.Signing
    -> k2.(RealWorld.keyUsage) = RealWorld.Encryption
    -> chan_key
.

Inductive msg_eq : forall t__r t__i,
    RealWorld.message t__r
    -> IdealWorld.message t__i * IdealWorld.channel_id * IdealWorld.channels * IdealWorld.permissions -> Prop :=

(* Still need to reason over visibility of channel -- plaintext really means everyone can see it *)
| PlaintextMessage' : forall content ch_id cs ps,
    ps $? ch_id = Some (IdealWorld.construct_permission true true) ->
    msg_eq (RealWorld.Plaintext content) (IdealWorld.Content content, ch_id, cs, ps)
.

Definition check_cipher (ch_id : IdealWorld.channel_id)
  :=
    forall A B ch_id k (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs (*do we need these??*) chans perms,
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end.
    
Definition chan_key_ok :=
  forall A B ch_id (im : IdealWorld.message A) (rm : RealWorld.message B) cphrs chan_keys (*do we need these??*) chans perms,
    match chan_keys $? ch_id with
    | None => False
    | Some (Public _)   => msg_eq rm (im,ch_id,chans,perms)
    | Some (Auth _ k _) =>
      (* check_cipher ch_id k im rm cphrs chans perms *)
      match rm with
      | RealWorld.Ciphertext cphr_id =>
        match cphrs $? cphr_id with
        | None => False
        | Some (RealWorld.Cipher cphr_id k_id msg) =>
          RealWorld.keyId k = k_id /\ msg_eq msg (im,ch_id,chans,perms)
        end
      | _ => False
      end
    | Some (Enc  _ k _) => False
    | Some (AuthEnc _ k1 k2 _ _) => False
    end.


Inductive action_matches :
    RealWorld.action -> IdealWorld.action -> Prop :=
| Inp : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps p x y z,
      rw = (RealWorld.Input msg1 p x y z)
    -> iw = IdealWorld.Input msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
| Out : forall t__r t__i (msg1 : RealWorld.message t__r) (msg2 : IdealWorld.message t__i) rw iw ch_id cs ps x,
      rw = RealWorld.Output msg1 x
    -> iw = IdealWorld.Output msg2 ch_id cs ps
    -> msg_eq msg1 (msg2, ch_id, cs, ps)
    -> action_matches rw iw
.

Definition simulates {A B : Type}
           (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop)
           (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) :=

(*  call spoofable *)

  (forall U__r U__i,
      R U__r U__i
      -> forall U__r',
        rstepSilent U__r U__r'
        -> exists U__i',
          istepSilent ^* U__i U__i'
          /\ R U__r' U__i')

  /\ (forall U__r U__i,
        R U__r U__i
        -> forall a1 U__r',
          RealWorld.step_universe U__r (Action a1) U__r' (* excludes adversary steps *)
          -> exists a2 U__i' U__i'',
            istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R U__r' U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__r.(RealWorld.adversary)) a1 = true
    (* and adversary couldn't have constructed message seen in a1 *)
    )

  /\ R U__r U__i.

Definition refines {A B : Type} (U1 : RealWorld.universe A B)(U2 : IdealWorld.universe A) :=
  exists R, simulates R U1 U2.

Infix "<|" := refines (no associativity, at level 70).


(* Inductive couldGenerate : forall {A B}, RealWorld.universe A B -> list RealWorld.action -> Prop := *)
(* | CgNothing : forall {A B} (u : RealWorld.universe A), *)
(*     couldGenerate u [] *)
(* | CgSilent : forall {A} {u u' : RealWorld.universe A} tr, *)
(*     RealWorld.lstep_universe u Silent u' *)
(*     -> couldGenerate u' tr *)
(*     -> couldGenerate u tr *)
(* | CgAction : forall {A} a (u u' : RealWorld.universe A) tr, *)
(*     RealWorld.lstep_universe u (Action a) u' *)
(*     -> couldGenerate u' tr *)
(*     -> couldGenerate u (a :: tr). *)


Section SingleAdversarySimulates.

  (* If we have a simulation proof, we know that:
   *   1) No receives could have accepted spoofable messages
   *   2) Sends we either of un-spoofable, or were 'public' and are safely ignored
   *
   * This should mean we can write some lemmas that say we can:
   *   safely ignore all adversary messages (wipe them from the universe) -- Adam's suggestion, I am not exactly sure how...
   *   or, prove an appended simulation relation, but I am not sure how to generically express this
   *)

  Section AdversaryHelpers.
    Import RealWorld.

    Definition ADV := 10.

    Definition add_adversary {A B} (U__r : universe A B) (advcode : user_cmd B) :=
      addAdversaries U__r ($0 $+ (ADV, {| key_heap := $0
                                      ; msg_heap := []
                                      ; protocol := advcode |})).

    Fixpoint msg_safe {t} (msg : message t) : bool :=
      match msg with
      | Plaintext _ => false
      | KeyMessage _ => false
      | MsgPair m1 m2 => msg_safe m1 && msg_safe m2
      | Ciphertext _ => true
      | Signature _ _ => true
      end.

    Definition exm_safe (msg : exmsg) : bool :=
      match msg with
      | Exm m => true
      end.

    Definition clean_messages (msgs : queued_messages) :=
      List.filter exm_safe msgs.

    Definition clean_users {A} ( usrs : honest_users A ) :=
      map (fun u_d => {| key_heap := u_d.(key_heap)
                    ; protocol := u_d.(protocol)
                    ; msg_heap := clean_messages u_d.(msg_heap) |}) usrs.

    Definition honest_cipher (adv_keys : keys) (c : cipher) :=
      match c with
      | Cipher _ k_id _ =>
        match adv_keys $? k_id with
        | Some (SymKey _) => false
        | Some (AsymKey _ true) => false
        | _ => true
        end
      end.

    Definition clean_cipher_fold_fn (adv_keys : keys) (k : key_identifier) (v : cipher) (cs : ciphers) :=
      if honest_cipher adv_keys v then cs $+ (k,v) else cs.

    Lemma honest_cipher_proper_morphism :
      forall ks,
        Morphisms.Proper
          (Morphisms.respectful eq (Morphisms.respectful eq (Morphisms.respectful eq eq)))
          (clean_cipher_fold_fn ks).
    Proof.
      unfold Morphisms.Proper, Morphisms.respectful; intros; subst; reflexivity.
    Qed.

    Lemma honest_cipher_transpose_key :
      forall ks,
        transpose_neqkey eq (clean_cipher_fold_fn ks).
    Proof.
      unfold transpose_neqkey; intros.
      unfold clean_cipher_fold_fn.
      case (honest_cipher ks e); eauto.
      case (honest_cipher ks e'); eauto.
      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n k); intro; subst.
      - rewrite add_eq_o by trivial. rewrite add_neq_o by auto. rewrite add_eq_o by trivial. auto.
      - rewrite add_neq_o by auto.
        case (y ==n k'); intros; subst.
        do 2 rewrite add_eq_o by trivial. trivial.
        do 3 rewrite add_neq_o by auto. trivial.
    Qed.

    Definition clean_ciphers (adv_keys : keys) (cs : ciphers) :=
      fold (clean_cipher_fold_fn adv_keys) cs $0.

    Definition strip_adversary {A B} (U__r : universe A B) : universe A B :=
      {| users       := U__r.(users)
       ; adversary   := $0
       ; all_ciphers := clean_ciphers (findUserKeys U__r.(adversary)) U__r.(all_ciphers)
      |}.

    Lemma cipher_is_Cipher :
      forall v : cipher,
        match v with
        | RealWorld.Cipher _ _ _ => true
        end = true.
    Proof.
      destruct v; auto.
    Qed.

    Lemma clean_ciphers_nokeys_idempotent :
      forall cs,
        clean_ciphers $0 cs = cs.
    Proof.
      intros.
      unfold clean_ciphers, clean_cipher_fold_fn, honest_cipher.
      simpl.
      apply P.fold_rec; intros.

      apply elements_Empty in H.
      apply map_eq_elements_eq. auto.

      intros. subst.
      apply map_eq_Equal. unfold Equal; intros.
      destruct e. eauto.

    Qed.

  End AdversaryHelpers.

  Section RealWorldLemmas.
    Import RealWorld.

    Hint Resolve honest_cipher_proper_morphism honest_cipher_transpose_key.

    Lemma univ_components :
      forall {A B} (U__r : universe A B),
        {| users       := users U__r
         ; adversary   := adversary U__r
         ; all_ciphers := all_ciphers U__r
        |} = U__r.
      intros. destruct U__r; simpl; trivial.
    Qed.

    Lemma adduserkeys_keys_idempotent :
      forall {A} (us : user_list (user_data A)) ks uid ud,
        us $? uid = Some ud
        -> exists ud', addUserKeys us ks $? uid = Some ud'.
    Proof.
      intros.
      (* eexists. *)
      unfold addUserKeys.
      apply find_mapsto_iff in H.
      eexists.
      rewrite <- find_mapsto_iff.
      rewrite map_mapsto_iff.
      eexists; intuition. eassumption.
    Qed.




    (* Lemma clean_ciphers_doesn't_make_unaccepted_msg_accepted : *)
    (*   forall {t} cs pat ks (msg : message t), *)
    (*     msg_accepted_by_pattern cs pat msg = false *)
    (*     -> msg_accepted_by_pattern (clean_ciphers ks cs) pat msg = false. *)
    (* Proof. *)
    (*   intro. intro. *)
    (*   intro. *)
    (*   induction pat; destruct msg; eauto. *)
    (*   destruct msg; induction pat; eauto. *)
    (*   - unfold msg_accepted_by_pattern in H. *)
    (*     fold (@msg_accepted_by_pattern t1) in H. fold (@msg_accepted_by_pattern t2) in H. *)
    (*     SearchAbout (_ && _ = false). *)
    (*     apply andb_false_elim in H; invert H. *)
    (*     apply IHpat1; eauto. *)



    (*   - admit. *)
    (*   -  *)



    (*   unfold msg_accepted_by_pattern in * *)



    Lemma honest_step_advuniv_implies_honest_step_origuniv :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s adv_keys,
          adv_keys = findUserKeys adv
          -> cs__s = clean_ciphers adv_keys cs
          -> bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd' cs__s',
              cs__s' = clean_ciphers adv_keys cs'
              -> bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> step_user (B:=B) u_id lbl (usrs, $0, cs__s, ks, qmsgs, cmd) (usrs', $0, cs__s', ks', qmsgs', cmd').
    Proof.
      induction 1; inversion 3; inversion 2; subst.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
      -
        (* eapply StepRecv. *)

        (* H3 : msg_accepted_by_pattern cs' pat msg = true *)
        (* ============================ *)
        (* step_user u_id (Action (Input msg pat u_id ks cs')) (usrs', $0, clean_ciphers (findUserKeys adv') cs', ks, Exm msg :: qmsgs', Recv pat) *)
        (*   (usrs', $0, clean_ciphers (findUserKeys adv') cs', ks $++ findKeys msg, qmsgs', Return msg) *)
        admit.

      - econstructor; eauto.

        (* H1 : msg_accepted_by_pattern cs' pat msg = false *)
        (* ============================ *)
        (* msg_accepted_by_pattern (clean_ciphers (findUserKeys adv') cs') pat msg = false *)

        admit.

      - econstructor; eauto; unfold addUserKeys; m_equal; trivial.
      - econstructor; eauto.

      (* Two goals: *)

      (* H0 : ks' $? keyId k = Some k *)
      (* H1 : ~ In (elt:=cipher) c_id cs *)
      (* H2 : encryptMessage k msg c_id = Some cipherMsg *)
      (* ============================ *)
      (* ~ In (elt:=cipher) c_id (clean_ciphers (findUserKeys adv') cs) *)
        admit.

      (* H0 : ks' $? keyId k = Some k *)
      (* H1 : ~ In (elt:=cipher) c_id cs *)
      (* H2 : encryptMessage k msg c_id = Some cipherMsg *)
      (* ============================ *)
      (* clean_ciphers (findUserKeys adv') (cs $+ (c_id, cipherMsg)) = clean_ciphers (findUserKeys adv') cs $+ (c_id, cipherMsg) *)
        admit.

      - econstructor; eauto.

      (* H0 : ks $? key_id k = Some (AsymKey k true) \/ ks $? key_id k = Some (SymKey k) *)
      (* H6 : (usrs', adv', cs', ks, qmsgs', Decrypt (Ciphertext c_id)) = (usrs', adv', cs', ks, qmsgs', Decrypt (Ciphertext c_id)) *)
      (* H : cs' $? c_id = Some (Cipher c_id (key_id k) msg) *)
      (* ============================ *)
      (* clean_ciphers (findUserKeys adv') cs' $? c_id = Some (Cipher c_id (key_id k) msg) *)
        admit.

      - econstructor; eauto.

      (* H0 : ks' $? keyId k = Some k *)
      (* H1 : ~ In (elt:=cipher) c_id cs *)
      (* H2 : signMessage k msg c_id = Some cipherMsg *)
      (* H6 : (usrs', adv', cs, ks', qmsgs', Sign k msg) = (usrs', adv', cs, ks', qmsgs', Sign k msg) *)
      (* ============================ *)
      (* ~ In (elt:=cipher) c_id (clean_ciphers (findUserKeys adv') cs) *)
        admit.

      (* H0 : ks' $? keyId k = Some k *)
      (* H1 : ~ In (elt:=cipher) c_id cs *)
      (* H2 : signMessage k msg c_id = Some cipherMsg *)
      (* H6 : (usrs', adv', cs, ks', qmsgs', Sign k msg) = (usrs', adv', cs, ks', qmsgs', Sign k msg) *)
      (* ============================ *)
      (* clean_ciphers (findUserKeys adv') (cs $+ (c_id, cipherMsg)) = clean_ciphers (findUserKeys adv') cs $+ (c_id, cipherMsg) *)
        admit.

      - econstructor; eauto.

        (* H : ks' $? keyId k = Some k *)
        (* H0 : cs' $? c_id = Some (Cipher c_id k_id msg) *)
        (* ============================ *)
        (* clean_ciphers (findUserKeys adv') cs' $? c_id = Some (Cipher c_id k_id msg) *)
        admit.
    Admitted.

    Lemma enc_cipher_has_key :
      forall {t} k (msg : message t) c_id cipherMsg,
        encryptMessage k msg c_id = Some cipherMsg
        -> cipherMsg = Cipher c_id (keyId k) msg
        /\ (exists cryp_key, k = SymKey cryp_key \/ k = AsymKey cryp_key false).
    Proof.
      intros.
      unfold encryptMessage in H.
      case_eq k; intros; rewrite H0 in H.
      - case_eq (usage k0); intro; rewrite H1 in H; invert H; eauto.
      - case_eq has_private_access; intro; rewrite H1 in H;
          case_eq (usage k0); intro; rewrite H2 in H || invert H; invert H; eauto.
    Qed.

    Lemma sign_cipher_has_key :
      forall {t} k (msg : message t) c_id cipherMsg,
        signMessage k msg c_id = Some cipherMsg
        -> cipherMsg = Cipher c_id (keyId k) msg
          /\ (exists cryp_key, k = SymKey cryp_key \/ k = AsymKey cryp_key true).
    Proof.
      intros.
      unfold signMessage in H.

      case_eq k; intros; rewrite H0 in H.
      - case_eq (usage k0); intro; rewrite H1 in H; invert H; eauto.
      - case_eq has_private_access; intro; rewrite H1 in H;
          case_eq (usage k0); intro; rewrite H2 in H || invert H; invert H; eauto.
    Qed.

    (* Specialize to single adversary.  This means that in the following proof, we assume
     * that, since we are stepping the adversary, then
     *   ks =  adv keys at beginning
     *   ks' = adv keys at the end
     *)
    Lemma adv_step_implies_no_new_ciphers_after_cleaning :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C) cs__s,
            bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> cs__s = clean_ciphers ks cs
          (* -> (forall k_id v, MapsTo k_id v ks -> MapsTo k_id v adv_keys) *)
          -> forall cmd' cs__s',
                bd' = (usrs', adv', cs', ks', qmsgs', cmd')
              -> cs__s' = clean_ciphers ks' cs'
              -> cs__s = cs__s'.
    Proof.
      induction 1; inversion 1; inversion 2; subst; eauto.

      - admit.

      -  admit.
         
      -  admit.

      - intros; subst.
        unfold clean_ciphers; simpl.
        rewrite fold_add; simpl; eauto.

        unfold clean_cipher_fold_fn; assert (honest_cipher ks' cipherMsg = false).
        apply sign_cipher_has_key in H2; invert H2; subst; simpl.
        invert H3. rewrite H0. invert H; eauto.
        rewrite H; trivial.

    Admitted.

    Lemma user_step_adds_no_users :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', ks', qmsgs', cmd')
            -> forall u_id' u_d,
              usrs' $? u_id' = Some u_d
              -> usrs $? u_id' <> None.
    Proof.
      induction 1; inversion 1; inversion 1; intros; subst; eauto;
        repeat match goal with
               | [ H : ?us $? ?uid = Some _ |- ?us $? ?uid <> None ] => solve [ rewrite H; intro C; invert C ]
               end.

      case (u_id' ==n rec_u_id); intro.
      - subst. rewrite H1; intro C; invert C.
      - rewrite add_neq_o in H11 by auto.
        rewrite H11; intro C; invert C.
    Qed.

    Lemma user_step_adds_removes_no_adversaries :
      forall {A B C} cs cs' lbl u_id (usrs usrs' : honest_users A) (adv adv' : adversaries B) ks ks' qmsgs qmsgs' bd bd',
        step_user u_id lbl bd bd'
        -> forall (cmd : user_cmd C),
          bd = (usrs, adv, cs, ks, qmsgs, cmd)
          -> forall cmd',
            bd' = (usrs', adv', cs', ks', qmsgs', cmd')
            -> (forall u_id',
                  adv' $? u_id' <> None
                  <-> adv $? u_id' <> None).
    Proof.
      induction 1; inversion 1; inversion 1; intros; subst; eauto;
        unfold iff; constructor; intro; eauto.

      - unfold addUserKeys in H. rewrite <- in_find_iff in H.
        rewrite map_in_iff in H. apply in_find_iff; eauto.

      - unfold addUserKeys; apply in_find_iff.
        rewrite <- in_find_iff in H.
        rewrite map_in_iff; eauto.
    Qed.

    Lemma adv_step_stays_in_R :
      forall {A B} (U__i : IdealWorld.universe A) (U__r : universe A B) (R : universe A B -> IdealWorld.universe A -> Prop)
              (cmd : user_cmd B) lbl u_id userData (usrs : honest_users A) (adv : adversaries B) cs ks qmsgs,
        U__r.(adversary) $? u_id = Some userData
        -> (forall u_id', u_id' <> u_id -> U__r.(adversary) $? u_id' = None) (* single adversary *)
        -> step_user u_id lbl
                    (build_data_step U__r userData)
                    (usrs, adv, cs, ks, qmsgs, cmd)
        -> R (strip_adversary U__r) U__i
        -> R (strip_adversary (buildUniverseAdv usrs adv cs u_id {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) U__i.
    Proof.
      intros.

      pose proof H1 as STEP.
      unfold build_data_step in STEP.
      eapply adv_step_implies_no_new_ciphers_after_cleaning in STEP; eauto.

      unfold buildUniverseAdv, strip_adversary, updateUserList in *; simpl in *.

      assert (U__r.(adversary) = $0 $+ (u_id,userData)).
      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n u_id); intro.
      subst. rewrite H. rewrite add_eq_o by trivial; trivial.
      specialize (H0 _ n). rewrite H0. rewrite add_neq_o by auto. eauto.

      assert (findUserKeys U__r.(adversary) = userData.(key_heap)).
      rewrite H3; unfold findUserKeys, fold, Raw.fold; simpl; rewrite empty_add_idempotent; trivial.

      rewrite H4 in H2; rewrite STEP in H2.

      assert (findUserKeys (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})) = ks).
      pose proof H1 as NOADD; unfold build_data_step in NOADD.

      (* eapply user_step_adds_removes_no_adversaries in NOADD. *)
      (* unfold iff in NOADD; invert NOADD. *)

      assert (adv $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |}) = $0 $+ (u_id, {| key_heap := ks; protocol := cmd; msg_heap := qmsgs |})).
      apply map_eq_Equal; unfold Equal; intros.
      case (y ==n u_id); intros.
      subst; do 2 rewrite add_eq_o by trivial; trivial.
      do 2 rewrite add_neq_o by auto; simpl. specialize (H0 _ n).
      eapply user_step_adds_removes_no_adversaries with (u_id' := y) in NOADD; eauto.
      unfold iff in NOADD; invert NOADD.
      case_eq (adv $? y); intros.
      assert (adv $? y <> None). unfold not; intro. rewrite H7 in H8. invert H8.
      assert (adversary U__r $? u_id <> None); unfold not. intro. rewrite H9 in H; invert H.
      admit.
      rewrite empty_o; trivial.
      rewrite H5. unfold findUserKeys.
      rewrite fold_add; eauto.
      simpl. unfold fold, Raw.fold; simpl. rewrite empty_add_idempotent. eauto.

      admit. admit. admit.

      rewrite H5. admit.

    Admitted.

  End RealWorldLemmas.

  Hint Constructors RealWorld.step_user.

  Hint Extern 1 (rstepSilent _ (strip_adversary _)) => 
    unfold RealWorld.buildUniverse, RealWorld.buildUniverseAdv, strip_adversary,
           updateUserList, RealWorld.findUserKeys;
      simpl.

  Hint Extern 1 (rstepSilent _ _) => eapply RealWorld.StepUser.
  Hint Extern 1 (RealWorld.step_user _ _ (RealWorld.build_data_step _ _) _) =>
    progress unfold RealWorld.build_data_step.

  Hint Extern 1 (RealWorld.step_user _ _ (_, _, _ , RealWorld.protocol _) _) => 
    match goal with
    | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H
    end.

  Hint Extern 1 (_ = _) => progress m_equal.
  Hint Extern 1 (_ = _) => progress f_equal.
  Hint Extern 1 (_ = _) =>
    progress unfold RealWorld.build_data_step, RealWorld.buildUniverse, updateUserList; simpl.
  Hint Extern 1 (_ = _) =>
    match goal with
    | [ H : RealWorld.adversary _ = _ |- _ ] => rewrite <- H
    end.
  Hint Extern 1 (_ = RealWorld.adversary _) => solve [ symmetry ; assumption ].


  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i
          -> forall U__r' : RealWorld.universe A B,
            rstepSilent U__r U__r'
            -> exists U__i' : IdealWorld.universe A, (istepSilent) ^* U__i U__i' /\ R U__r' U__i')
      -> R (strip_adversary U__ra) U__i
      -> forall U__ra',
          rstepSilent U__ra U__ra'
          -> exists U__i', istepSilent ^* U__i U__i'
                   /\ R (strip_adversary U__ra') U__i'.
  Proof.
    simpl.
    intros.
    invert H1.

    (* Honest step *)
    - simpl.
      (* specialize (H _ _ H0). *)
      assert (UNIV_STEP :
                rstepSilent
                  (strip_adversary U__ra)
                  (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).
      eapply RealWorld.StepUser; eauto.
      eapply honest_step_advuniv_implies_honest_step_origuniv; eauto.
      smash_universe.
      unfold strip_adversary; smash_universe.
      simpl. admit.

      eapply H; eauto.

    - exists U__i. constructor.
      eapply TrcRefl.
      eapply adv_step_stays_in_R; eauto.
      intros.
      admit. (* single adversary assumption *)

  Admitted.

  Lemma simulates_with_adversary_loud :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) (R : RealWorld.universe A B -> IdealWorld.universe A -> Prop),
      (forall (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
          R U__r U__i ->
          forall (a1 : RealWorld.action) (U__r' : RealWorld.universe A B),
            RealWorld.step_universe U__r (Action a1) U__r' ->
            exists (a2 : IdealWorld.action) (U__i' U__i'' : IdealWorld.universe A),
              (istepSilent) ^* U__i U__i' /\
              IdealWorld.lstep_universe U__i' (Action a2) U__i'' /\
              action_matches a1 a2 /\ R U__r' U__i'' /\
              RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__r)) a1 = true)
      -> R (strip_adversary U__ra) U__i
      -> forall a1 U__ra',
          RealWorld.step_universe U__ra (Action a1) U__ra'
          -> exists a2 U__i' U__i'',
            (istepSilent) ^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a2) U__i''
            /\ action_matches a1 a2
            /\ R (strip_adversary U__ra') U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys (RealWorld.adversary U__ra)) a1 = true.
  Proof.
    simpl.
    intros.
    invert H1. 

    assert (UNIV_STEP :
              RealWorld.step_universe
                (strip_adversary U__ra)
                (Action a1)
                (strip_adversary (RealWorld.buildUniverse usrs adv cs u_id
                                                            {| RealWorld.key_heap := ks
                                                             ; RealWorld.protocol := cmd
                                                             ; RealWorld.msg_heap := qmsgs |})) ).

    eapply RealWorld.StepUser; eauto.
    eapply honest_step_advuniv_implies_honest_step_origuniv; simpl; eauto.
    unfold strip_adversary; simpl; smash_universe. simpl.
    admit.

    specialize (H _ _ H0 _ _ UNIV_STEP).

    destruct H as [a2].
    destruct H as [U__i'].
    destruct H as [U__i''].
    destruct H. destruct H1. destruct H4. destruct H5.
    exists a2; exists U__i'; exists U__i''; intuition; eauto.

    unfold RealWorld.findUserKeys, strip_adversary, fold in H6; simpl in H6.

    admit.

  Admitted.

  Lemma fun_cipher_match :
    (fun (k : key) (v : RealWorld.cipher) (m : t RealWorld.cipher) =>
       if match v with
          | RealWorld.Cipher _ _ _ => true
          end then m $+ (k, v) else m)
      = 
    (fun (k : key) (v : RealWorld.cipher) (m : t RealWorld.cipher) =>
       m $+ (k, v)).
  Proof.
    simpl.
    (* rewrite cipher_is_Cipher. *)
  Admitted.
      
  Theorem simulates_ok_with_adversary :
    forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A),
      U__r <| U__i
      -> U__r.(RealWorld.adversary) = $0
      -> forall U__ra advcode,
          U__ra = add_adversary U__r advcode
          -> U__ra <| U__i.
  Proof.
    intros.
    inversion H as [R SIM].
    inversion SIM as [H__silent H__l].
    inversion H__l as [H__loud R__start]; clear H__l.

    unfold refines.
    exists (fun ur ui => R (strip_adversary ur) ui); unfold simulates.
    propositional;
      eauto using simulates_with_adversary_silent, simulates_with_adversary_loud.
    - rewrite H1; unfold strip_adversary, add_adversary; simpl.
      rewrite H0. rewrite empty_add_idempotent.
      unfold RealWorld.findUserKeys, fold; simpl. rewrite empty_add_idempotent.

      rewrite clean_ciphers_nokeys_idempotent.
      rewrite <- H0; rewrite univ_components. auto.
  Qed.

End SingleAdversarySimulates.
