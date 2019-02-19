Require Import Frap.
Require Import Common RealWorld Simulation.
Require IdealWorld.

Set Implicit Arguments.



Definition add_adv_msg {K V} (k : K)(v : V)(m : fmap K (list V)) : fmap K (list V) :=
  match m $? k with
  | None => m $+ (k, [v])
  | Some vs => m $+ (k, v :: vs)
  end.

Lemma add_adv_msg_get :
  forall {K V} (m : fmap K (list V)) k v,
    exists vs, (add_adv_msg k v m) $? k = Some (v :: vs)
          /\ match m $? k with
            | None     => vs = []
            | Some vs' => vs = vs'
            end.
Proof.
  intros.
  unfold add_adv_msg.
  cases (m $? k); eauto.
Qed.

Inductive step_user : forall A, user_id -> rlabel -> data_step0 A -> data_step0 A -> Prop :=

(* Plumbing *)
| StepBindRecur : forall {r r'} u_id advk advk'
                     cs cs' ks ks' msgs msgs'
                     uks uks' lbl (cmd1 cmd1' : user_cmd r) (cmd2 : r -> user_cmd r'),
      step_user u_id lbl (advk, cs, ks, msgs, uks, cmd1) (advk', cs', ks', msgs', uks', cmd1')
    -> step_user u_id lbl (advk, cs, ks, msgs, uks, Bind cmd1 cmd2) (advk', cs', ks', msgs', uks', Bind cmd1' cmd2)
| StepBindProceed : forall {r r'} u_id advk cs ks msgs uks (v : r') (cmd : r' -> user_cmd r),
    step_user u_id Silent (advk, cs, ks, msgs, uks, Bind (Return v) cmd) (advk, cs, ks, msgs, uks, cmd v)

(* Comms  *)
| StepRecv : forall {A} u_id advk cs ks qmsgs qmsgs' uks (msg : message A) pat msgs newkeys,
    qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
    -> findKeys msg = newkeys
    -> msg_accepted_by_pattern cs pat msg = true
    -> step_user u_id (Action (Input msg pat u_id uks cs))
                 (advk, cs, ks, qmsgs, uks, Recv pat)
                 (advk, cs, ks, qmsgs', updateKeyHeap newkeys uks, Return msg)

| StepRecvDrop : forall {A} u_id advk cs ks qmsgs qmsgs' uks (msg : message A) pat msgs,
      qmsgs $? u_id = Some (Exm msg :: msgs) (* we have a message waiting for us! *)
    -> qmsgs' = match msgs with [] => qmsgs $- u_id | _ => qmsgs $+ (u_id,msgs) end
    (* Hrm, when I am dropping the message, do I want to process keys?? *)
    (* -> findKeys msg = newkeys *)
    -> msg_accepted_by_pattern cs pat msg = false
    -> step_user u_id Silent
                 (advk, cs, ks, qmsgs,  uks, Recv (A := A) pat)
                 (advk, cs, ks, qmsgs', uks, Recv pat)

(* Augment attacker's keys with those available through messages sent, including traversing through ciphers already known by attacker, etc. *)
| StepSend : forall {A} u_id advk advk' cs ks qmsgs rec_u_id uks newkeys (msg : message A),
    findKeys msg = newkeys
    -> advk' = updateKeyHeap newkeys advk
    -> step_user u_id (Action (Output msg u_id))
               (advk,  cs, ks, qmsgs, uks, Send rec_u_id msg)
               (advk', cs, ks, multiMapAdd rec_u_id (Exm msg) qmsgs, uks, Return tt)

(* Encryption / Decryption *)
| StepEncrypt : forall {A} u_id advk cs ks qmsgs uks (msg : message A) k k_id c_id cipherMsg,
    keyId k = k_id
    -> uks $? k_id = Some k
    -> ~(c_id \in (dom cs))
    -> encryptMessage k msg c_id = Some cipherMsg
    -> step_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Encrypt k msg)
                 (advk, cs $+ (c_id, cipherMsg), ks, qmsgs, uks, Return (Ciphertext c_id))

| StepDecrypt : forall {A} u_id advk cs ks qmsgs uks (msg : message A) k_id k c_id newkeys,
    cs $? c_id = Some (Cipher c_id k_id msg)
    -> ( uks $? k_id = Some (AsymKey k true) (* check we have access to private key *)
      \/ uks $? k_id = Some (SymKey k) )
    -> k.(key_id) = k_id
    -> findKeys msg = newkeys
    -> step_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Decrypt (Ciphertext c_id))
                 (advk, cs, ks, qmsgs, updateKeyHeap newkeys uks, Return msg)

(* Signing / Verification *)
| StepSign : forall {A} u_id advk cs ks qmsgs uks (msg : message A) k k_id c_id cipherMsg,
    uks $? k_id = Some k
    -> keyId k = k_id
    -> ~(c_id \in (dom cs))
    -> signMessage k msg c_id = Some cipherMsg
    -> step_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, Sign k msg)
                 (advk, cs $+ (c_id, cipherMsg), ks, qmsgs, uks, Return (Ciphertext c_id))

| StepVerify : forall {A} u_id advk cs ks qmsgs uks (msg : message A) k_id k c_id newkeys,
    (* k is in your key heap *)
    uks $? (keyId k) = Some k
    (* return true or false whether k was used to sign the message *)
    -> cs $? c_id = Some (Cipher c_id k_id msg)
    -> findKeys msg = newkeys (* TODO do we really want this, should have been gotten via recieve???  find keys that might be in message *)
    -> step_user u_id Silent
                 (advk, cs, ks, qmsgs, uks, (Verify k (Ciphertext c_id)))
                 (advk, cs, ks, qmsgs, updateKeyHeap newkeys uks, Return (if (k_id ==n (keyId k)) then true else false))

| StepAdvSend : forall {A} u_id advk cs ks qmsgs qmsgs' uks (msg : message A) pat,
    qmsgs' = add_adv_msg u_id (Exm msg) qmsgs
    -> step_user u_id Silent
                (* (advk, cs, ks, qmsgs,  uks, cmd) *)
                (* (advk, cs, ks, qmsgs', uks, cmd) *)
                (advk, cs, ks, qmsgs,  uks, Recv (A := A) pat)
                (advk, cs, ks, qmsgs', uks, Recv pat)

.

Inductive step_universe {A} : universe A -> rlabel -> universe A -> Prop :=
| StepUser : forall U u_id userData uks advk cs ks qmsgs lbl (cmd' : user_cmd A),
    In (u_id,userData) U.(users)
    -> step_user u_id lbl
                (U.(adversary), U.(all_ciphers), U.(all_keys), U.(users_msg_buffer),
                 userData.(key_heap), userData.(protocol))
                (advk, cs, ks, qmsgs, uks, cmd')
    -> step_universe U lbl (updateUniverse U advk cs ks qmsgs u_id uks cmd')
.



Lemma universe_user_updated {A} (U : universe A) :
  forall U' u_id u_dat u_dat' (cmd : user_cmd A) aks cs ks msgs ukeys,
      In (u_id,u_dat) U.(users)
    -> U' = updateUniverse U aks cs ks msgs u_id ukeys cmd
    -> u_dat' = {| key_heap := ukeys ;
                  protocol := cmd ;
               |}
    -> In (u_id,u_dat') U'.(users).
Proof.
  intros.
  subst.
  unfold updateUniverse; simplify.
  eapply update_inserted; eauto.
Qed.


Theorem 

(*
 * What is the API of "idealized LOCKMA"?

 **** Add non deterministic choice operation
 **** Implement ping protocol where client quantifies over input msg to be sent, receives a response, and returns test of equality.
      --> Prove that no adversary can impact this result
      --> What is the real final theorem statement for this protocol, with explicit adversary (assume one for now) modeled
      --> Need to distinguish which process has returned which result
      --> Any trace in real world (with adv) can be produced in ideal world (with no adv)
      --> anything that can happen real world with adv can happen in real world without adv, we mean here final results of honest participants
      --> SPECIALIZE TO TWO PARTY PROTOCOLS FOR NOW

  Prove that for 
 *)

Theorem simulation_sound {A : Type} (U1 : universe A) (U2 : IdealWorld.universe A) :
  U1 <| U2
  -> (U1 ++ [adv]) <| (U2)


  (* -> exists R : RealWorld.universe A -> IdealWorld.universe A -> Prop, *)
  (*   (forall U1 U2, *)
  (*       R U1 U2 *)
  (*       -> forall U1', *)
  (*         step_universe U1 Silent U1' *)
  (*         -> exists U1'' U2', *)
  (*             rstepSilent^* U1' U1'' *)
  (*           /\ istepSilent^* U2 U2' *)
  (*           /\ R U1'' U2') *)

  (* /\ (forall U1 U2, *)
  (*       R U1 U2 *)
  (*       -> forall a1 U1', *)
  (*         step_universe U1 (Action a1) U1' *)
  (*         -> exists a2 U1'' U2' U2'', *)
  (*             rstepSilent^* U1' U1'' *)
  (*           /\ istepSilent^* U2 U2' *)
  (*           /\ IdealWorld.lstep_universe U2' (Action a2) U2'' *)
  (*           /\ action_matches a1 a2 *)
  (*           /\ R U1'' U2'' *)
  (*           /\ RealWorld.action_adversary_safe U1.(RealWorld.adversary) a1 = true *)
    ).
Proof.
  intro Rfns.
  inversion Rfns as [R Sim].
  inversion Sim as [StepSil StepLd].
  clear Rfns Sim (* for now *) StepLd.
  exists R.
 
  Ltac fixer1 :=
    match goal with
    | [H: _ = protocol _ |- lstep_user _ _ _ _] => progress rewrite <- H
    end.

  constructor.

  Ltac poseU :=
    match goal with
    | [ |- exists u1 u2, rstepSilent^* ?U _ /\ _ /\ _ ] => remember U as UU
    end.

  - intros. invert H0. invert H2.
    + simpl.
      pose proof (StepSil U0 U3 H) as step. admit.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (StepSil U0 U3 H) as step;
        poseU;
        exists UU;
        pose (step UU) as step1;
        destruct step1; subst; econstructor; eauto; repeat fixer1; econstructor; eauto.

    + pose proof (add_adv_msg_get (users_msg_buffer U0) u_id (Exm msg)) as usr_msgs.
      destruct usr_msgs as [msgs]. destruct H2.

      eexists. exists U3. (* We are going to end up back where we started *)
      propositional.
      2:auto.
      2:eassumption.

      (* Now for the actual work *)
      eapply TrcFront. eapply LStepUser'.
      eapply universe_user_updated; eauto.
      simpl.
      3: eapply TrcRefl; eauto. (* No more steps *)
      eapply LStepRecvDrop.
      rewrite H2; reflexivity. reflexivity.

      admit. (* need to specify the msg shape *)

      unfold updateUniverse; simpl.

      destruct U0; f_equal; simplify.

      * remember ({| key_heap := key_heap userData; protocol := Recv pat |}) as UD.
        rewrite <- (update_identity_idem u_id UD) with (usrs := users); eauto.
        rewrite <- (update_identity_idem u_id UD) with (usrs := users); eauto.

        simpl.
        admit. (* need kekys_uniq U0.(users) *)
        (* need UD = userData *)
        assert (UDEQ: UD = userData). destruct userData. simpl in *. rewrite HeqUD. f_equal; eauto.
        rewrite UDEQ; eauto.
        admit. (* need kekys_uniq U0.(users) *)
        assert (UDEQ: UD = userData). destruct userData. simpl in *. rewrite HeqUD. f_equal; eauto.
        rewrite UDEQ; eauto.

      * cases (users_msg_buffer $? u_id).
        maps_equal.
        cases (k ==n u_id). subst. rewrite Heq. 
        admit. admit.
        subst. simpl. unfold add_adv_msg. rewrite Heq. rewrite addRemoveKey; eauto.

  - (* loud steps  *) admit.

Admitted.      







Theorem sim_sound:
(* Definition data_step0 (A : Type) : Type :=  *)
  (*   adversary_knowledge * ciphers * keys * queued_messages * fmap nat key * user_cmd A. *)
  forall {A} u_id (cmd1 cmd2 : user_cmd A) aks aks' cs cs' ks ks' msgs msgs' ukeys ukeys',
    step_user u_id Silent (aks,cs,ks,msgs,ukeys,cmd1) (aks',cs',ks',msgs',ukeys',cmd2)
    -> exists aks'' cs'' ks'' msgs'' ukeys'' cmd'',
        (lstep_user u_id Silent) (aks,cs,ks,msgs,ukeys,cmd1) (aks'',cs'',ks'',msgs'',ukeys'',cmd'')
      /\ (lstep_user u_id Silent)^* (aks'',cs'',ks'',msgs'',ukeys'',cmd'') (aks',cs',ks',msgs',ukeys',cmd2)
.
Proof.
  induct 1.
  - simpl.
    destruct IHstep_user as [aks'' IHstep_user].
    destruct IHstep_user as [cs'' IHstep_user].
    destruct IHstep_user as [ks'' IHstep_user].
    destruct IHstep_user as [msgs'' IHstep_user].
    destruct IHstep_user as [ukeys'' IHstep_user].
    destruct IHstep_user as [cmd'' IHstep_user].
    destruct IHstep_user.

    do 6 eexists.
    constructor.
    (* 2:eapply LStepBindRecur. *)
    (* inversion H0; subst. *)
    (* eapply TrcRefl. *)
    (* (* have cmd0 --> y -->* cmd'', need that under Bind *) admit. *)
    admit. admit.

  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
  - do 6 eexists.
    constructor; [|eapply TrcRefl]. econstructor; eauto.
  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
  - 
  - do 6 eexists.
    constructor; [|eapply TrcRefl]; econstructor; eauto.
    



    eapply TrcFront; [ | eapply TrcRefl]. eapply LStepBindRecur.
    inversion IHstep_user. 


  Inductive step_user : forall A, user_id -> rlabel -> data_step0 A -> data_step0 A -> Prop :=




Theorem sim_sound :
  forall {A} (U1 U2 : universe A),
    step_universe U1 Silent U2
    -> rstepSilent^* U1 U2.
Proof.
  


Theorem simulation_sound {A : Type} (U1 : universe A) (U2 : IdealWorld.universe A) :
  U1 <| U2
  -> exists R : RealWorld.universe A -> IdealWorld.universe A -> Prop,
    (forall U1 U2,
        R U1 U2
        -> forall U1',
          step_universe U1 Silent U1'
          -> exists U2',
            istepSilent^* U2 U2'
            /\ R U1' U2').
Proof.
  intro Rfns.
  inversion Rfns as [R Sim].
  inversion Sim as [StepSil StepLd].
  clear Rfns Sim (* for now *) StepLd.
  exists R.
 
  Ltac fixer1 :=
    match goal with
    | [H: _ = protocol _ |- lstep_user _ _ _ _] => progress rewrite <- H
    end.

  intros.
  invert H0.
  invert H2.

  - eapply StepSil; eauto. econstructor; eauto. repeat fixer1; eapply LStepBindRecur.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  - eapply StepSil; eauto; econstructor; eauto; repeat fixer1; econstructor; eauto.
  -  eapply StepSil. eauto.

    ; eauto; econstructor; eauto; repeat fixer1. econstructor.



      
  -> forall l U1' U2' U2'',
    step_universe U1 l U1'
    -> istepSilent^* U2 U2'
      /\ IdealWorld.lstep_universe U2' (Action a2) U2''


    
  -> forall l U1',
    step_universe U1 l U1'
    -> exists U1'' U2',
      rstepSilent^* U1' U1''
      /\ U1'' <| U2'.
Proof.


  forall l,
    step_universe U1 l U2
    -> exists U1',
      rstepSilent^* U1 U1'
      /\ lstep_universe U1 l U2.
Proof.
  induction 1.
  invert H0.
  - admit.
  - admit.
  - 
