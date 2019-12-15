Require Import Formula FindVal.


(** Pure SAT solver. *)
Definition solver (p : form) :bool:=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

(** Exercise 2.6*)
(**
   Difference between satisfiable and solver.
   satisfiable is a property of a boolean formula, solver is a method to find out whether a formula is satisfiable. If solver returns true then we can conclude that the formula is satisfiable.
 **)

Module Test_solver.
  Definition x := (var (Id "x")).
  Definition y := (var (Id "y")).

(** Exercise 2.7*)
  Lemma test_pos_1: solver (land (lor x (not y)) (lor (not x) y) ) =true.
  Proof.
    reflexivity.
  Qed.
  
  Lemma test_pos_2: solver (mapsto (not y) (lor x y) ) =true.  
  Proof.
    reflexivity.
  Qed.
  
  Lemma test_neg_1: solver (land (land x (not x)) (boolv true)) = false.
  Proof.
    reflexivity.
  Qed.
  
  Lemma test_neg_2: solver (land  (not x) (boolv false)) = false.
  Proof.
    reflexivity.
  Qed.
     
End Test_solver.


Lemma find_interp: forall p V, find_valuation p=Some V -> interp V p=true.
Proof.
  intros.
  unfold find_valuation in H;
  unfold try_valuation in H.
  induction (enum_valuation (collect_var p)).
  - discriminate H. (*valuation list is empty*)
  - destruct (interp a p) eqn: E1.
    + inversion H. (* interp a p = true => a = V*)
      rewrite H1 in E1.
      assumption.
    + apply IHl. (* interp a p = false*)
      apply H. (* use hypothesis from induction*)
Qed.
  
  
  
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof.
  intros.
  unfold satisfiable.
  unfold solver in H.
  destruct (find_valuation p) eqn:E in H. (*return of find_valuation*)
  - exists v. (*Some v*)
    apply find_interp in E.
    assumption.
  - discriminate H. (*None*)
Qed.
