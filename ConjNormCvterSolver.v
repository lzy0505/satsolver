Require Import Formula Find FormOptSolver.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Import ListNotations.


Fixpoint or_clus_cnf (C A : form)  : form :=
  match A with
  | land B1 B2 => land (or_clus_cnf C B1) (or_clus_cnf C B2)
  | _ => lor A C
  end.

Fixpoint or_cnf_cnf (A1 A2 : form)  : form :=
  match A1 with
  | land B1 B2 => land (or_cnf_cnf B1 A2) (or_cnf_cnf B2 A2)
  | _ => or_clus_cnf A1 A2
  end.



Fixpoint conj_norm_converter (p :form) : form :=
  match  p with
  | land B1 B2 => land (conj_norm_converter B1) (conj_norm_converter B2)
  | lor B1 B2 => or_cnf_cnf (conj_norm_converter B1) (conj_norm_converter B2)
  | _ => p
  end.




Definition A := (Id "A").
Definition B := (Id "B").
Definition C := (Id "C").
Definition D := (Id "D").
Definition E := (Id "E").

Definition f := (lor (lor (land  (not (var A)) (var B)) (var C) ) (land (var D) (var E))).

Eval compute in (conj_norm_converter f).


(*TODO*)
Lemma converter_land : forall (V : valuation) (p1 p2:form), interp V (neg_norm_converter false (land p1 p2)) =interp V (neg_norm_converter false p1) && interp V (neg_norm_converter false p2)  .
Proof.
  intros.
  destruct p1 eqn:P1, p2 eqn:P2;unfold neg_norm_converter;rewrite <-land_interp;try reflexivity.
Qed.


Lemma converter_lor : forall (V : valuation) (p1 p2:form), interp V (neg_norm_converter false (lor p1 p2)) =interp V (neg_norm_converter false p1) || interp V (neg_norm_converter false p2)  .
Proof.
  intros.
  destruct p1 eqn:P1, p2 eqn:P2;unfold neg_norm_converter;rewrite <-lor_interp;try reflexivity.
Qed.


Lemma mapsto_interp: forall (V : valuation) (p1 p2:form), interp V (mapsto p1 p2) = negb (interp V  p1) ||(interp V  p2).
Proof.
  intros.
  destruct p1,p2;(try unfold interp;reflexivity).
  Qed.  


Lemma converter_mapsto : forall (V : valuation) (p1 p2:form), interp V (neg_norm_converter false (mapsto p1 p2)) = (negb (interp V (neg_norm_converter false p1))) || interp V (neg_norm_converter false p2)  .
Proof.
  intros.
  destruct p1 eqn:P1, p2 eqn:P2;unfold neg_norm_converter;rewrite <-mapsto_interp;try reflexivity.
  Qed.


Lemma not_interp: forall (V : valuation) (p:form), interp V (not  p) = negb (interp V  p) .
Proof.
  intros.
  destruct p;(try unfold interp;reflexivity).
  Qed.  


Lemma converter_not_1 : forall (V : valuation) (p:form), interp V (neg_norm_converter false (not p)) = interp V (neg_norm_converter true p).
Proof.
  intros.
  destruct p eqn:P;unfold neg_norm_converter;try (rewrite <-not_interp);try reflexivity.
Qed.

Lemma bool_interp: forall(V : valuation) (b:Datatypes.bool), negb (interp V (bool b)) = interp V (bool (negb b)).
Proof.
  intros.
  unfold interp.
  reflexivity.
Qed.

Lemma negb_swap : forall (a b : Datatypes.bool), negb a = b -> a = negb b.
Proof.
  intros.
  rewrite <-H.
  Search negb.
  apply negb_involutive_reverse.
Qed.

Lemma converter_not_2:forall (V : valuation) (p:form),  negb (interp V (neg_norm_converter false p)) =
                                                        interp V (neg_norm_converter true p).
Proof.
  intros.
  induction p;try (unfold neg_norm_converter;  reflexivity).
  - unfold neg_norm_converter;destruct b;reflexivity.
  - rewrite converter_land.
    try (apply negb_swap in IHp1; apply negb_swap in IHp2; rewrite IHp1; rewrite IHp2;simpl).
     rewrite negb_andb. now repeat  rewrite <- negb_involutive_reverse.
  - rewrite converter_lor.
    try (apply negb_swap in IHp1; apply negb_swap in IHp2; rewrite IHp1; rewrite IHp2;simpl).
    rewrite negb_orb. now repeat  rewrite <- negb_involutive_reverse.
  - rewrite converter_mapsto.
    apply negb_swap in IHp2.  rewrite IHp2;simpl.
    rewrite negb_orb. now repeat  rewrite <- negb_involutive_reverse.
  - rewrite converter_not_1. simpl. apply negb_swap in IHp. symmetry. assumption.
Qed.     

  
Lemma converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (neg_norm_converter false p).
Proof.
  induction p;try (unfold neg_norm_converter; reflexivity).
  - rewrite converter_land.
    rewrite land_interp.
    rewrite IHp1, IHp2.
    reflexivity.
  - rewrite converter_lor.
    rewrite lor_interp.
    rewrite IHp1, IHp2.
    reflexivity.
  - rewrite converter_mapsto.
    rewrite mapsto_interp.
    rewrite IHp1, IHp2.
    reflexivity.
  - rewrite converter_not_1.
    rewrite not_interp.
    rewrite IHp.
    destruct p; try (unfold neg_norm_converter;rewrite not_interp;reflexivity);try (apply converter_not_2).
  Qed.
  



(*
Doesn't work.
Recursive call to neg_norm_converter has principal argument equal
to "lor (not p1) (not p2)" instead of
one of the following variables: "f" "p1"
"p2".

Fixpoint neg_norm_converter (p :form) : form :=
  match p with
  | var _ => p
  | bool _ => p
  | land p1 p2 => land (neg_norm_converter p1) (neg_norm_converter p2)
  | lor p1 p2 => lor (neg_norm_converter p1) (neg_norm_converter p2)
  | mapsto p1 p2 => mapsto (neg_norm_converter p1) (neg_norm_converter p2)
  | not (var _ ) => p
  | not (bool true) => bool false
  | not (bool false) => bool true            
  | not (land p1 p2) => (neg_norm_converter (lor (not p1) (not p2))) 
  | not (lor p1 p2) => land  (neg_norm_converter (not p1))  (neg_norm_converter (not p2))
  | not (mapsto p1 p2) => land  (neg_norm_converter  p1)  (neg_norm_converter (not p2))                     
  | not (not p1) => (neg_norm_converter p1)
  end.*)

Fixpoint is_neg_normal  (p : form) : Datatypes.bool :=
  match p with
  | var _ => true
  | bool _ => true
  | land p1 p2 =>  is_neg_normal p1 && is_neg_normal p2
  | lor p1 p2 =>  is_neg_normal p1 && is_neg_normal p2
  | mapsto p1 p2 =>  is_neg_normal p1 && is_neg_normal p2  
  | not (var _ ) => true
  | not (bool _) => false
  | not (land _ _) => false
  | not (lor _ _) => false
  | not (mapsto _ _) => false
  | not (not _) => false                   
  end.


Lemma true_false : forall (p:form),is_neg_normal (neg_norm_converter true p) =  is_neg_normal (neg_norm_converter false p).
  Proof.
    intros.
    induction  p;
      try reflexivity;
      try (destruct b; reflexivity).
     - simpl.
       now rewrite IHp1, IHp2.
     - simpl.
       now rewrite IHp1, IHp2.
     - simpl.
       now rewrite IHp2.
     - simpl. symmetry. assumption.
Qed.
     
    

Lemma converter_correctness_2: forall (p:form), is_neg_normal (neg_norm_converter false  p) = true.
Proof.
  intro.
  induction p;
    try (unfold neg_norm_converter;  reflexivity);
    try (unfold neg_norm_converter; unfold is_neg_normal;
    unfold neg_norm_converter, is_neg_normal in IHp1, IHp2;
    rewrite IHp1; rewrite IHp2;
    reflexivity).
  - simpl.
    now rewrite true_false.
Qed.

(*  Can't just prove  is_neg_normal (neg_norm_converter true p) = true ->   is_neg_normal (neg_norm_converter false p) =true
it will cause cycle prove!
if you want to prove this , you need prove is_neg_normal (neg_norm_converter false p) = true ->   is_neg_normal (neg_norm_converter true p) =true
 if you do so ,you need to prove the first one.

induction  p;
      try reflexivity;
      try (destruct b; reflexivity);
      try (simpl;
           simpl in IHp;
           symmetry in IHp;
           apply andb_true_eq  in IHp;
           destruct IHp;
           symmetry in H, H0;
           apply IHp1 in H;
           apply IHp2 in H0;
           now rewrite H,H0).
    + simpl;
        simpl in IHp;
        symmetry in IHp;
        apply andb_true_eq  in IHp;
        destruct IHp;
        symmetry in H, H0;
        apply IHp2 in H0;
        now rewrite H,H0.
    + simpl;simpl in IHp.
cycle!!
       induction  p;
      try reflexivity;
      try (destruct b; reflexivity).
      * simpl;
           simpl in IHp;
           symmetry in IHp;
           apply andb_true_eq  in IHp;
           destruct IHp;
           symmetry in H, H0;
        apply IHp1 in H;
           apply IHp2 in H0.
             now rewrite H,H0.
           try(  intro; assumption).
           try(  intro; assumption).
           try(  intro; assumption).
       *  simpl;
           simpl in IHp;
           symmetry in IHp;
           apply andb_true_eq  in IHp;
           destruct IHp;
           symmetry in H, H0;
        apply IHp1 in H;
           apply IHp2 in H0.
             now rewrite H,H0.
           try(  intro; assumption).
           try(  intro; assumption).
           try(  intro; assumption).
       *simpl;
           simpl in IHp;
           symmetry in IHp;
           apply andb_true_eq  in IHp;
           destruct IHp;
           symmetry in H, H0.
           apply IHp2 in H0.
           now rewrite H,H0.
           try(  intro; assumption).
       *  simpl;
            simpl in IHp, IHp0, IHp1. ???*)



Definition solver (p : form) :Datatypes.bool:=
  match find_valuation (neg_norm_converter false p) with
  | Some _ => true
  | None => false
  end.




Lemma land_find_interp: forall p1 p2 V, find_valuation (neg_norm_converter false (land p1 p2))=Some V -> interp V p1=true /\ interp V p2=true.
Proof.
  intros.
  split;
    unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (neg_norm_converter false (land p1 p2)))); (*add optimizer*)
    try (discriminate H);
    try (rewrite <-converter_correctness in H;
         destruct (interp a (land p1 p2)) eqn: E1); (*rewrite to the old proof*)
    try(inversion H;
        apply land_interp_interp in E1;
        destruct E1;
        rewrite <-H1;
        assumption);
    try(apply IHl; (*why it works?*)
        apply H).
  Qed.
 




Lemma lor_find_interp: forall p1 p2 V, find_valuation (neg_norm_converter false (lor p1 p2))=Some V -> interp V p1=true \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (neg_norm_converter false (lor p1 p2)))). (*add optimizer*)
  - discriminate H.
  - rewrite <-converter_correctness in H.
    destruct (interp a (lor p1 p2)) eqn: E1.
    + inversion H.
      apply lor_interp_interp in E1.
      rewrite <-H1.
      assumption.
    + apply IHl. (*why it works?*)
      apply H.
Qed.




Lemma mapsto_find_interp: forall p1 p2 V, find_valuation (neg_norm_converter false (mapsto p1 p2))=Some V -> interp V p1=false \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation,try_valuation in H.
  induction (enum_valuation (collect_var (neg_norm_converter false (mapsto p1 p2)))).
    - discriminate H.
    - rewrite <-converter_correctness in H.
      destruct (interp a (mapsto p1 p2)) eqn: E1.    
       + inversion H.
         apply mapsto_interp_interp in E1.
         rewrite <-H1.
         assumption.
       + apply IHl. (*why it works?*)
         apply H.
Qed.



Lemma not_find_interp: forall p V, find_valuation (neg_norm_converter false (not p))=Some V -> interp V p=false.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (neg_norm_converter false (not p)))).
  - discriminate H.
  - rewrite <-converter_correctness in H.
    destruct (interp a (not p)) eqn: E1.
    + inversion H.
      apply not_interp_interp in E1.
      rewrite <-H1.
      assumption.
    + apply IHl. (*why it works?*)
      apply H.
Qed.


 
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
    destruct (find_valuation (neg_norm_converter false (bool b))) eqn:E in H;(try discriminate H).
    unfold find_valuation in E.  
    simpl in E.
    destruct b.    
    now exists v.
    discriminate E.
  -  (*land*)
    destruct (find_valuation (neg_norm_converter false (land p1 p2))) eqn:E in H;(try discriminate H).
    exists v.
    apply land_interp_interp.
    apply land_find_interp in E.
    assumption.
  - (*lor*)
    destruct (find_valuation (neg_norm_converter false (lor p1 p2))) eqn:E in H;try(discriminate H).
    exists v.
    apply lor_interp_interp.
    apply lor_find_interp in E.
    assumption.
  - (* mapsto*)   
    destruct (find_valuation (neg_norm_converter false (mapsto p1 p2))) eqn:E in H;try(discriminate H).
    exists v.
    apply mapsto_interp_interp.
    apply mapsto_find_interp in E.
    assumption.
  - (* not*)   
    destruct (find_valuation (neg_norm_converter false (not p))) eqn:E in H;try(discriminate H).
    exists v.
    apply not_interp_interp.
    apply not_find_interp in E.
    assumption.
Qed.  
