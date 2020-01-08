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
 *  as specifically authorized by the U.S. Government may violate any copyrights that exist in this work. *)
From Coq
     Require Import Eqdep String Arith Omega Program Bool.

Require Import StepRelations.

(* From Frap *)
(*      Require Import Sets Relations. *)
(* From Frap *)
(*      Require Import Map Var Invariant ModelCheck. *)
(* Export String Arith Sets Relations Map Var Invariant Bool ModelCheck. *)

(* Export String Arith Sets Relations Bool. *)
Export String Arith StepRelations Bool.

Require Import List.
Export List ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Ltac inductN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => dependent induction H
              | S ?n' => inductN n'
            end
        | _ => intro; inductN n
      end
  end.

Ltac same_structure x y :=
  match x with
  | ?f ?a1 ?b1 ?c1 ?d1 =>
    match y with
    | f ?a2 ?b2 ?c2 ?d2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2; same_structure d1 d2
    | _ => fail 2
    end
  | ?f ?a1 ?b1 ?c1 =>
    match y with
    | f ?a2 ?b2 ?c2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2
    | _ => fail 2
    end
  | ?f ?a1 ?b1 =>
    match y with
    | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
    | _ => fail 2
    end
  | ?f ?a1 =>
    match y with
    | f ?a2 => same_structure a1 a2
    | _ => fail 2
    end
  | _ =>
    match y with
    | ?f ?a1 ?b1 ?c1 ?d1 =>
      match x with
      | f ?a2 ?b2 ?c2 ?d2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2; same_structure d1 d2
      | _ => fail 2
      end
    | ?f ?a1 ?b1 ?c1 =>
      match x with
      | f ?a2 ?b2 ?c2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2
      | _ => fail 2
      end
    | ?f ?a1 ?b1 =>
      match x with
      | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
      | _ => fail 2
      end
    | ?f ?a1 =>
      match x with
      | f ?a2 => same_structure a1 a2
      | _ => fail 2
      end
    | _ => idtac
    end
  end.

Ltac instantiate_obvious1 H :=
  match type of H with
  | _ ++ _ = _ ++ _ -> _ => fail 1
  | ?x = ?y -> _ =>
    (same_structure x y; specialize (H eq_refl))
    || (has_evar (x, y); fail 3)
  | JMeq.JMeq ?x ?y -> _ =>
    (same_structure x y; specialize (H JMeq.JMeq_refl))
    || (has_evar (x, y); fail 3)
  | forall x : ?T, _ =>
    match type of T with
    | Prop => fail 1
    | _ =>
      let x' := fresh x in
      evar (x' : T);
      let x'' := eval unfold x' in x' in specialize (H x''); clear x';
        instantiate_obvious1 H
    end
  end.

Ltac instantiate_obvious H :=
  match type of H with
    | context[@eq string _  _] => idtac
    | _ => repeat instantiate_obvious1 H
  end.

Ltac instantiate_obviouses :=
  repeat match goal with
         | [ H : _ |- _ ] => instantiate_obvious H
         end.

Ltac induct e := (inductN e || dependent induction e); instantiate_obviouses.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac invert0 e := invert e; fail.
Ltac invert1 e := invert0 e || (invert e; []).
Ltac invert2 e := invert1 e || (invert e; [|]).

Ltac propositional := intuition idtac.

Ltac linear_arithmetic := intros;
    repeat match goal with
           | [ |- context[max ?a ?b] ] =>
             let Heq := fresh "Heq" in destruct (Max.max_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ _ : context[max ?a ?b] |- _ ] =>
             let Heq := fresh "Heq" in destruct (Max.max_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ |- context[min ?a ?b] ] =>
             let Heq := fresh "Heq" in destruct (Min.min_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ _ : context[min ?a ?b] |- _ ] =>
             let Heq := fresh "Heq" in destruct (Min.min_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           end; omega.

Ltac equality := intuition congruence.

Ltac cases E :=
  ((is_var E; destruct E)
   || match type of E with
      | {_} + {_} => destruct E
      | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
      end);
  repeat match goal with
         | [ H : _ = left _ |- _ ] => clear H
         | [ H : _ = right _ |- _ ] => clear H
         end.

Global Opaque max min.

Infix "==n" := eq_nat_dec (no associativity, at level 50).
Infix "<=?" := le_lt_dec.

(* Export Frap.Map. *)
(* Ltac maps_equal := Frap.Map.M.maps_equal; simplify. *)

(* Ltac first_order := firstorder idtac. *)

(* Lemma eq_iff : forall P Q, *)
(*     P = Q *)
(*     -> (P <-> Q). *)
(* Proof. *)
(*   equality. *)
(* Qed. *)

(* Ltac sets0 := Sets.sets ltac:(simpl in *; intuition (subst; auto; try equality; try linear_arithmetic)). *)

(* Ltac sets := propositional; *)
(*   try match goal with *)
(*       | [ |- @eq (?T -> Prop) _ _ ] => *)
(*         change (T -> Prop) with (set T) *)
(*       end; *)
(*   try match goal with *)
(*       | [ |- @eq (set _) _ _ ] => *)
(*         let x := fresh "x" in *)
(*         apply sets_equal; intro x; *)
(*         repeat match goal with *)
(*                | [ H : @eq (set _) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H; *)
(*                                                 apply eq_iff in H *)
(*                end *)
(*       end; sets0; *)
(*   try match goal with *)
(*       | [ H : @eq (set ?T) _ _, x : ?T |- _ ] => *)
(*         repeat match goal with *)
(*                | [ H : @eq (set T) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H; *)
(*                                                  apply eq_iff in H *)
(*                end; *)
(*           solve [ sets0 ] *)
(*       end. *)

Remove Hints absurd_eq_true trans_eq_bool.
