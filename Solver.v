Require Import Formula Find.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Import ListNotations.
Require Setoid. 


Definition solver (p : form) :Datatypes.bool:=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.




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


Lemma land_find_interp: forall p1 p2 V, find_valuation (land p1 p2)=Some V -> interp V p1=true /\ interp V p2=true.
Proof.
  intros.
  split;unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (land p1 p2)));
    try(discriminate H);
    try(  destruct (interp a (land p1 p2)) eqn: E1);
    
       try(inversion H;
         apply land_interp_interp in E1;
         destruct E1;
         rewrite <-H1;
         assumption);
       try(apply IHl; (*why it works?*)
         apply H).
Qed.



Lemma lor_find_interp: forall p1 p2 V, find_valuation (lor p1 p2)=Some V -> interp V p1=true \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (lor p1 p2))).
    - discriminate H.
    - destruct (interp a (lor p1 p2)) eqn: E1.
    
       + inversion H.
         apply lor_interp_interp in E1.
         rewrite <-H1;
           assumption.
         
     +   try(apply IHl; (*why it works?*)
         apply H).
Qed.



Lemma mapsto_find_interp: forall p1 p2 V, find_valuation (mapsto p1 p2)=Some V -> interp V p1=false \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (mapsto p1 p2))).
    - discriminate H.
    - destruct (interp a (mapsto p1 p2)) eqn: E1.
    
       + inversion H.
         apply mapsto_interp_interp in E1.
         rewrite <-H1;
           assumption.
         
     +   try(apply IHl; (*why it works?*)
         apply H).
Qed.




Lemma not_find_interp: forall p V, find_valuation (not p)=Some V -> interp V p=false.
Proof.
  intros.
  unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (not p))).
    - discriminate H.
    - destruct (interp a (not p)) eqn: E1.
    
       + inversion H.
         apply not_interp_interp in E1.
         rewrite <-H1;
           assumption.
         
     +   try(apply IHl; (*why it works?*)
         apply H).
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
  destruct p;unfold satisfiable;unfold solver in H.
  - (*var*)
    exists (override empty_valuation i true).
    simpl.
    unfold override.
    now rewrite  <- beq_id_refl.
  - (*bool*)
    destruct (find_valuation (bool b)) eqn:E in H;(try discriminate H).
    unfold find_valuation in E.  
    simpl in E.
    destruct b.    
    now exists v.
    discriminate E.
  -  (*land*)
    destruct (find_valuation (land p1 p2)) eqn:E in H;(try discriminate H).
    exists v.
    apply land_interp_interp.
    apply land_find_interp in E.
    assumption.
  - (*lor*)
    destruct (find_valuation (lor p1 p2)) eqn:E in H;try(discriminate H).
    exists v.
    apply lor_interp_interp.
    apply lor_find_interp in E.
    assumption.
  - (* mapsto*)   
    destruct (find_valuation (mapsto p1 p2)) eqn:E in H;try(discriminate H).
    exists v.
    apply mapsto_interp_interp.
    apply mapsto_find_interp in E.
    assumption.
  - (* not*)   
    destruct (find_valuation (not p)) eqn:E in H;try(discriminate H).
    exists v.
    apply not_interp_interp.
    apply not_find_interp in E.
    assumption.
Qed.
