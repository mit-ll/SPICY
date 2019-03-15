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

  Definition ADV := 10.

  Definition add_adversary {A B} (U__r : RealWorld.universe A B) (advcode : RealWorld.user_cmd B) :=
    RealWorld.addAdversaries U__r ($0 $+ (ADV, {| RealWorld.key_heap := $0
                                              ; RealWorld.msg_heap := []
                                              ; RealWorld.protocol := advcode |})).

  Definition strip_adversary {A B} (U__r : RealWorld.universe A B) : RealWorld.universe A B :=
    {| RealWorld.users       := U__r.(RealWorld.users)
     ; RealWorld.adversary   := $0
     ; RealWorld.all_ciphers := U__r.(RealWorld.all_ciphers)
     |}.


  (* Lemma adversary_univ_loud_step_implies_stripped_nonadv_step : *)
  (*   forall {A B} (U__r U__ra : RealWorld.universe A B) advcode, *)
  (*       U__ra = add_adversary U__r advcode *)
  (*     -> U__r.(RealWorld.adversary) = $0 *)
  (*     -> forall U__r' U__ra' a, *)
  (*         RealWorld.lstep_universe U__ra (Action a) U__ra' *)
  (*       -> U__r' = strip_adversary U__ra' *)
  (*       -> RealWorld.lstep_universe U__r (Action a) U__r'. *)
  (* Proof. *)
  (*   intros. *)
  (*   invert H1. *)
  (*   invert H4. *)

  (*   (* Bind *) *)
  (*   - admit. *)

  (*   (* Recv *) *)
  (*   - eapply RealWorld.LStepUser'; eauto. *)
  (*     unfold RealWorld.universe_data_step; simpl. *)
  (*     match goal with *)
  (*     | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H *)
  (*     end. *)
  (*     eapply RealWorld.LStepRecv'; eauto. *)
  (*     unfold strip_adversary, RealWorld.updateUniverse; simpl. *)
  (*     eapply real_univ_eq_fields_eq; auto. *)

  (*   (* Send *) *)
  (*   - eapply RealWorld.LStepUser'; eauto. *)
  (*     unfold RealWorld.universe_data_step; simpl. *)
  (*     match goal with *)
  (*     | [ H : _ = RealWorld.protocol _ |- _ ] => rewrite <- H *)
  (*     end. *)
  (*     eapply RealWorld.LStepSend; eauto. *)
  (*     unfold RealWorld.updateUniverse, strip_adversary; simpl. *)
  (*     rewrite H0.  *)
  (*     smash_universe. *)
  (* Admitted. *)


  Lemma honest_step_advuniv_implies_honest_step_origuniv :
    forall {A B} (U__r : RealWorld.universe A B) u_id userData advcode gs adv adv' uks cmd,
      RealWorld.step_user u_id Silent (RealWorld.build_data_step (add_adversary U__r advcode) userData) (gs, adv, uks, cmd)
      -> U__r.(RealWorld.adversary) = $0
      -> RealWorld.users (add_adversary U__r advcode) $? u_id = Some userData
      -> adv' = $0
      -> RealWorld.step_user u_id Silent (RealWorld.build_data_step U__r userData) (gs, adv', uks, cmd).
  Proof.
    intros.
    invert H.
    - admit.
    - admit.
    - unfold RealWorld.build_data_step. 

  Admitted.

  Section RealWorldLemmas.
    Import RealWorld.

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


  (* Lemma simulates_with_adversary_silent : *)
  (*  forall {A B} (U__r : RealWorld.universe A B) (U__i : IdealWorld.universe A) R, *)
  (*      simulates R U__r U__i *)
  (*    -> U__r.(RealWorld.adversary) = $0 *)
  (*    -> forall U__ra U__ra' advcode, *)
  (*        U__ra = add_adversary U__r advcode *)
  (*        -> rstepSilent U__ra U__ra' *)
  (*        -> exists U__i', *)
  (*            istepSilent ^* U__i U__i' *)
  (*            /\ R (strip_adversary U__ra') U__i'. *)
  (*  Proof. *)
  (*    intros. *)
  (*    inversion H  as [H__silent H__l]; clear H. *)
  (*    inversion H__l as [H__loud R__start]; clear H__l; clear H__loud. *)

  (*    invert H2. *)
  
  (*    (* Honest step *)  *)
  (*    - invert H3; unfold RealWorld.build_data_step; simpl; *)
  (*        [ | specialize (H__silent U__r U__i R__start); eapply H__silent .. ]; *)
  (*        eauto 9. *)
  (*      + admit. *)
  
  (*    (* Adversary step *)  *)
  (*    - invert H3; unfold RealWorld.build_data_step; simpl; *)
  (*        [ | unfold strip_adversary, RealWorld.buildUniverseAdv, updateUserList; *)
  (*              simpl; *)
  (*              exists U__i; *)
  (*              rewrite <- H0; *)
  (*              try rewrite univ_components; *)
  (*              intuition .. *)
  (*        ]. *)

  (*      + admit. *)
  (*      + admit. (* need to swipe ciphers *) *)
  (*      + admit. (* need to swipe ciphers *) *)
  
  (*  Admitted. *)
  
  Lemma simulates_with_adversary_silent :
    forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) R,
      simulates R (strip_adversary U__ra) U__i
      -> forall U__ra',
        rstepSilent U__ra U__ra'
        -> exists U__i',
          istepSilent ^* U__i U__i'
          /\ R (strip_adversary U__ra') U__i'.
  Proof.
    intros.
    inversion H  as [H__silent H__l]; clear H.
    inversion H__l as [H__loud R__start]; clear H__l; clear H__loud.

    invert H0.

    (* Honest step *) 
    - invert H1; unfold RealWorld.build_data_step; simpl;
        [ | specialize (H__silent (strip_adversary U__ra) U__i R__start); eapply H__silent .. ];
        eauto 9.
      + admit.

    (* Adversary step *) 
    - invert H1; unfold RealWorld.build_data_step; simpl; [
        | unfold strip_adversary, RealWorld.buildUniverseAdv, updateUserList;
            simpl;
            exists U__i;
            match goal with | [ H : R (strip_adversary _) _ |- _ ] => progress unfold strip_adversary in H; simpl in H end;
            intuition ..
        ].

        + admit.
        + admit. (* something with send.. *)
        + admit. (* need to swipe ciphers *)
        + admit. (* need to swipe ciphers *)

    Admitted.

    Lemma simulates_with_adversary_loud :
      forall {A B} (U__ra : RealWorld.universe A B) (U__i : IdealWorld.universe A) R,
        simulates R (strip_adversary U__ra) U__i
        -> forall U__ra' a__ra,
          RealWorld.step_universe U__ra (Action a__ra) U__ra' (* excludes adversary steps *)
          -> exists a__i U__i' U__i'',
              istepSilent^* U__i U__i'
            /\ IdealWorld.lstep_universe U__i' (Action a__i) U__i''
            /\ action_matches a__ra a__i
            /\ R (strip_adversary U__ra') U__i''
            /\ RealWorld.action_adversary_safe (RealWorld.findUserKeys U__ra.(RealWorld.adversary)) a__ra = true.
    Proof.

      intros.
      inversion H  as [H__silent H__l]; clear H.
      inversion H__l as [H__loud R__start]; clear H__l; clear H__silent.

      match goal with
      | [ H : RealWorld.step_universe _ _ _ |- _] => invert H
      end.

      match goal with
      | [ H : RealWorld.step_user _ _ _ _ |- _] => invert H
      end; 
        unfold RealWorld.build_data_step; simpl;
          [ | specialize (H__loud (strip_adversary U__ra) U__i R__start) ..
          ].

      - admit.
      - admit.
      - admit.

      (* - unfold RealWorld.buildUniverse, updateUserList; simpl. *)
      (*   unfold RealWorld.findUserKeys,fold in H__loud; simpl in H__loud. *)
      (*   eapply H__loud. *)

      (* (* Hint Extern 1 (step_universe _ _ _) => eapply RealWorld.StepUser. *) *)

      (* - simpl in *. *)
      (*   unfold strip_adversary, RealWorld.buildUniverse, updateUserList; simpl. *)
      (*   eapply RealWorld.StepUser; eauto. *)

      (* - simpl in *. *)
      (*   unfold strip_adversary, RealWorld.buildUniverse, updateUserList; simpl. *)
      (*   eapply RealWorld.StepUser. exact H. eauto. *)
      (*   unfold RealWorld.buildUniverse, updateUserList; simpl. *)
      (*   rewrite H0; smash_universe. *)

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
    propositional.
    - eapply simulates_with_adversary_silent; eauto. unfold simulates; eauto.
    - eapply simulates_with_adversary_loud; eauto. unfold simulates; eauto.
    - rewrite H1;
        unfold strip_adversary, add_adversary; simpl;
          rewrite <- H0; rewrite univ_components; eauto.
  Qed.

End SingleAdversarySimulates.
