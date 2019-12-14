Require Import Formula FindVal.
Require Setoid. 


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

(*
Lemma find_val_rec : forall p v v' l, interp v p = true \/ (interp v p = false /\ try_valuation l p= Some v' ) ->  (exists V, try_valuation (v::l) p=Some V).
Proof.
  intros.
  destruct H.
  - exists v.
    unfold try_valuation.
    now rewrite H.
  - exists v'.
    unfold try_valuation.
    destruct H.
    rewrite H.
    unfold try_valuation in H0.
    assumption.
Qed.


  

Lemma and_solver: forall p1 p2 V, find_valuation (land p1 p2)=Some V -> satisfiable p1.
Proof.
  intros.
    unfold find_valuation in H.
    unfold try_valuation in H.
    induction (enum_valuation (collect_var (land p1 p2))). 
    + discriminate H.
    +  destruct (interp a (land p1 p2)) eqn: E1.
       * unfold satisfiable.
         exists a.
         apply and_interp in E1.
         destruct E1.
         assumption.
       * apply IHl. (*why it works?*)
         apply H.
Qed.*)


Lemma find_interp_land: forall p1 p2 V, find_valuation (land p1 p2)=Some V -> interp V p1=true /\ interp V p2=true.
Proof.
  intros.
  unfold find_valuation in H.
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (land p1 p2))).
  - discriminate H. (*valuation list is empty*)
  - destruct (interp a (land p1 p2)) eqn: E1.
    + inversion H. (* interp a (land p1 p2) = true => a = V*)
      apply split_interp_land in E1.
      (*split  (interp a (land p1 p2)) into  (interp a  p1) and (interp a  p2)*)
      rewrite H1 in E1.
      assumption.
    + apply IHl. (* interp a (land p1 p2) = false*)
      apply H. (* use hypothesis from induction*)
Qed.



Lemma find_interp_lor: forall p1 p2 V, find_valuation (lor p1 p2)=Some V -> interp V p1=true \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation in H.
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (lor p1 p2))).
  - discriminate H. (*valuation list is empty*)
  - destruct (interp a (lor p1 p2)) eqn: E1.
    + inversion H. (* interp a (lor p1 p2) = true => a = V*)
      apply split_interp_lor in E1.
      (*split  (interp a (lor p1 p2)) into  (interp a  p1) and (interp a  p2)*)
      rewrite H1 in E1.
      assumption.
    + apply IHl. (* interp a (lor p1 p2) = false*)
      apply H. (* use hypothesis from induction*)
Qed.



Lemma find_interp_mapsto: forall p1 p2 V, find_valuation (mapsto p1 p2)=Some V -> interp V p1=false \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation in H.
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (mapsto p1 p2))).
  - discriminate H. (*valuation list is empty*)
  - destruct (interp a (mapsto p1 p2)) eqn: E1.
    + inversion H. (* interp a (mapsto p1 p2) = true => a = V*)
      apply split_interp_mapsto in E1.
      (*split  (interp a (mapsto p1 p2)) into  (interp a  p1) and (interp a  p2)*)
      rewrite H1 in E1.
      assumption.
    + apply IHl. (* interp a (lor p1 p2) = false*)
      apply H. (* use hypothesis from induction*)
Qed. 



Lemma find_interp_not: forall p V, find_valuation (not p)=Some V -> interp V p=false.
Proof.
  intros.
  unfold find_valuation in H.
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (not p))).
  - discriminate H. (*valuation list is empty*)
  - destruct (interp a (not p)) eqn: E1.
    + inversion H. (* interp a (land p1 p2) = true => a = V*)
      apply split_interp_not in E1.
      (*split  (interp a (not p)) into  (interp a  p) *)
      rewrite H1 in E1.
      assumption.
    + apply IHl. (* interp a (mapsto p1 p2) = false*)
      apply H. (* use hypothesis from induction*)
Qed.
  

(*
Lemma and_satisfiable : forall p1 p2, satisfiable p1 -> satisfiable p2 -> satisfiable (land p1 p2).
Proof.
  intros.
  unfold satisfiable in H, H0.
  unfold satisfiable.
  setoid_rewrite  <-land_interp_interp.
  destruct H,H0.
  
didn't work because the lemma is false!
*)
  
  
  
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof.
  intros.
  destruct p; (* not induction*)
    unfold satisfiable;
    unfold solver in H.
  - (*var*)
    exists (override empty_valuation i true). (* find a witness*)
    simpl.
    unfold override.
    now rewrite  <-  eqb_id_refl.
  - (*bool*)
    destruct (find_valuation (boolv b)) eqn:E in H;
      (try discriminate H).
    unfold find_valuation in E.  
    simpl in E.
    destruct b.    
    now exists v.
    discriminate E.
  -  (*land*)
    destruct (find_valuation (land p1 p2)) eqn:E in H;
      (try discriminate H).
    exists v.
    apply split_interp_land.
    apply find_interp_land in E.
    assumption.
  - (*lor*)
    destruct (find_valuation (lor p1 p2)) eqn:E in H;
      try(discriminate H).
    exists v.
    apply split_interp_lor.
    apply find_interp_lor in E.
    assumption.
  - (* mapsto*)   
    destruct (find_valuation (mapsto p1 p2)) eqn:E in H;
      try(discriminate H).
    exists v.
    apply split_interp_mapsto.
    apply find_interp_mapsto in E.
    assumption.
  - (* not*)   
    destruct (find_valuation (not p)) eqn:E in H;
      try(discriminate H).
    exists v.
    apply split_interp_not.
    apply find_interp_not in E.
    assumption.
Qed.

    
