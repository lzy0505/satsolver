Require Import Formula Find FormOptSolver NegNormCvtrSolver.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Import ListNotations.
Require Import Btauto.


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



Fixpoint neg_conj_converter (p :form) : form :=
  match  p with
  | land B1 B2 => land (neg_conj_converter B1) (neg_conj_converter B2)
  | lor B1 B2 => or_cnf_cnf (neg_conj_converter B1) (neg_conj_converter B2)
  | _ => p
  end.




Definition A := (Id "A").
Definition B := (Id "B").
Definition C := (Id "C").
Definition D := (Id "D").
Definition E := (Id "E").

Definition f := (lor (lor (land  (not (var A)) (var B)) (var C) ) (land (var D) (var E))).

Eval compute in (neg_conj_converter f).

Lemma or_clus_cnf_correctness: forall (V : valuation) (p1 p2:form), interp V (or_clus_cnf p1 p2) = interp V  p2 || interp V  p1.
Proof.
  intros.
  induction p2; simpl;try reflexivity.
  - rewrite IHp2_1.
    rewrite IHp2_2.
    btauto.
Qed.


Lemma or_cnf_cnf_correctness: forall (V : valuation) (p1 p2:form), interp V (or_cnf_cnf p1 p2) = interp V  p2 || interp V  p1.
Proof.
  intros.
  induction p1;simpl;try reflexivity;try apply or_clus_cnf_correctness.
  - rewrite IHp1_1.
    rewrite IHp1_2.
    btauto.
Qed.


Definition conj_norm_converter ( p :form) : form :=
  neg_conj_converter (neg_norm_converter false p).



Lemma neg_conj_converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (neg_conj_converter p).
Proof.
  
  induction p;try reflexivity.
  - simpl.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
  - simpl.
    rewrite or_cnf_cnf_correctness.
    rewrite IHp1, IHp2.
    btauto.
Qed.


Lemma conj_converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (conj_norm_converter p).
Proof.
  intros.
  unfold conj_norm_converter.
  transitivity (interp V  (neg_norm_converter false p)).
  apply converter_correctness.
  apply neg_conj_converter_correctness.
Qed.



Fixpoint is_disj_normal (p : form) : Datatypes.bool :=
  match p with
  | land p1 p2 =>  false
  | lor p1 p2 =>  is_disj_normal p1 && is_disj_normal p2
  | mapsto _ _ => false
  | _ => true                
  end.

Fixpoint is_conj_normal (p : form) : Datatypes.bool :=
  match p with
  | land p1 p2 =>  is_conj_normal p1 && is_conj_normal p2
  | lor p1 p2 =>  is_disj_normal  p1 && is_disj_normal p2
  | mapsto _ _ => false
  | _ => true                
  end.

Eval compute in (is_conj_normal  (lor (var B) (var A))).

Definition real_is_conj_normal (p : form) : Datatypes.bool :=
  is_conj_normal p && is_neg_normal p.


Lemma disj_conj :forall (p:form), is_disj_normal p = true -> is_conj_normal p = true.
Proof.
  intros.
  destruct p;try reflexivity.
  - simpl in H. discriminate H.
  - simpl in H. simpl. assumption.
  - simpl in H. simpl. assumption.
Qed.
 

Lemma disj_eq:forall (p1 p2:form), is_conj_normal (or_clus_cnf p1 p2) = is_disj_normal p1 && is_conj_normal p2.
Proof.
  intros.
  induction p2;simpl;try reflexivity;try btauto.
  - rewrite IHp2_1, IHp2_2.
    btauto.
Qed.

Lemma conj_eq:forall (p1 p2:form), is_conj_normal (or_cnf_cnf p1 p2) = is_conj_normal p1 && is_conj_normal p2.
Proof.
  intros.
  induction p1;simpl;try(rewrite disj_eq;reflexivity).
  - rewrite IHp1_1, IHp1_2.
    btauto.
Qed.


(*got stucked here if use equivalent:
is_conj_normal (or_cnf_cnf p1 p2) =true <-> is_conj_normal p1 =true && is_conj_normal p2=true
*)
Lemma not_conj : forall (p:form), is_conj_normal (neg_conj_converter (neg_norm_converter false p))= is_conj_normal (neg_conj_converter (neg_norm_converter true p)).
  Proof.
    intros.
    induction p;simpl.
    - reflexivity.
    - destruct b;reflexivity.
    - rewrite conj_eq.
      rewrite IHp1, IHp2.
      reflexivity.
    - rewrite conj_eq.
      rewrite IHp1, IHp2.
      reflexivity.
    - rewrite conj_eq.
      rewrite IHp1, IHp2.
      reflexivity.
    - symmetry in IHp.
      assumption.
Qed.

 

Lemma conj_converter_correctness_2: forall (p:form), is_conj_normal (conj_norm_converter  p) = true.
Proof.
  intro.
  induction p;
    try (reflexivity);
    unfold conj_norm_converter;
    simpl;
    try(try (rewrite conj_eq);
        unfold conj_norm_converter in IHp1, IHp2;
        rewrite IHp1, IHp2;
        reflexivity).
  - (*mapsto case, handle the not with not_conj*)
    rewrite conj_eq.
    unfold conj_norm_converter in IHp1.
    rewrite not_conj in IHp1.
    rewrite IHp1.
    assumption.
  - (*not case, handle the not with not_conj*)
    unfold conj_norm_converter in IHp.
    rewrite not_conj in IHp.
    assumption.
Qed.


Lemma disj_eq_2:forall (p1 p2:form), is_neg_normal (or_clus_cnf p1 p2) = is_neg_normal p1 && is_neg_normal p2.
Proof.
  intros.
  induction p2;simpl;try reflexivity;try btauto.
  - rewrite IHp2_1, IHp2_2.
    btauto.
Qed.


Lemma conj_eq_2:forall (p1 p2:form), is_neg_normal (or_cnf_cnf p1 p2) = is_neg_normal p1 && is_neg_normal p2.
Proof.
  intros.
  induction p1;simpl;try(rewrite disj_eq_2;reflexivity).
  - rewrite IHp1_1, IHp1_2.
    btauto.
Qed.


Lemma not_conj_2 : forall (p:form), is_neg_normal (neg_conj_converter (neg_norm_converter false p))= is_neg_normal (neg_conj_converter (neg_norm_converter true p)).
  Proof.
    intros.
    induction p;simpl;
      try (try(destruct b);
           reflexivity);
      try (rewrite conj_eq_2;
           rewrite IHp1, IHp2;
           reflexivity).
    - symmetry in IHp.
      assumption.
Qed.

Lemma conj_converter_correctness_3: forall (p:form), is_neg_normal (conj_norm_converter  p) = true.
Proof.
  intros.
  induction p;
    try (reflexivity);
    unfold conj_norm_converter;
    simpl;
    try(try (rewrite conj_eq_2);
        unfold conj_norm_converter in IHp1, IHp2;
        rewrite IHp1, IHp2;
        reflexivity).
  - rewrite conj_eq_2.
    unfold conj_norm_converter in IHp1.
    rewrite not_conj_2 in IHp1.
    rewrite IHp1.
    assumption.
  - (*not case, handle the not with not_conj*)
    unfold conj_norm_converter in IHp.
    rewrite not_conj_2 in IHp.
    assumption.
Qed.

Lemma conj_converter_correctness_real: forall (p:form), real_is_conj_normal (conj_norm_converter  p) = true.
Proof.
  intros.
  unfold real_is_conj_normal.
  rewrite conj_converter_correctness_2.
  now rewrite conj_converter_correctness_3.
Qed.

(*TODO*)

Definition solver (p : form) :Datatypes.bool:=
  match find_valuation (conj_norm_converter p) with
  | Some _ => true
  | None => false
  end.


Lemma land_find_interp: forall p1 p2 V, find_valuation (conj_norm_converter  (land p1 p2))=Some V -> interp V p1=true /\ interp V p2=true.
Proof.
  intros.
  split;
    unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (conj_norm_converter  (land p1 p2)))); (*add optimizer*)
    try (discriminate H);
    try (rewrite <-conj_converter_correctness in H;
         destruct (interp a (land p1 p2)) eqn: E1); (*rewrite to the old proof*)
    try(inversion H;
        apply land_interp_interp in E1;
        destruct E1;
        rewrite <-H1;
        assumption);
    try(apply IHl; (*why it works?*)
        apply H).
  Qed.
 




Lemma lor_find_interp: forall p1 p2 V, find_valuation (conj_norm_converter (lor p1 p2))=Some V -> interp V p1=true \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (conj_norm_converter (lor p1 p2)))). (*add optimizer*)
  - discriminate H.
  - rewrite <-conj_converter_correctness in H.
    destruct (interp a (lor p1 p2)) eqn: E1.
    + inversion H.
      apply lor_interp_interp in E1.
      rewrite <-H1.
      assumption.
    + apply IHl. (*why it works?*)
      apply H.
Qed.




Lemma mapsto_find_interp: forall p1 p2 V, find_valuation (conj_norm_converter (mapsto p1 p2))=Some V -> interp V p1=false \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation,try_valuation in H.
  induction (enum_valuation (collect_var (conj_norm_converter (mapsto p1 p2)))).
    - discriminate H.
    - rewrite <-conj_converter_correctness in H.
      destruct (interp a (mapsto p1 p2)) eqn: E1.    
       + inversion H.
         apply mapsto_interp_interp in E1.
         rewrite <-H1.
         assumption.
       + apply IHl. (*why it works?*)
         apply H.
Qed.



Lemma not_find_interp: forall p V, find_valuation (conj_norm_converter (not p))=Some V -> interp V p=false.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (conj_norm_converter (not p)))).
  - discriminate H.
  - rewrite <-conj_converter_correctness in H.
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
  destruct p;
    unfold satisfiable;
    unfold solver in H. 
  - (*var*)
    exists (override empty_valuation i true).
    simpl.
    unfold override.
    now rewrite  <- beq_id_refl.
  - (*bool*)
    destruct (find_valuation (conj_norm_converter (bool b))) eqn:E in H;
      (try discriminate H).
    unfold find_valuation in E.  
    simpl in E.
    destruct b.    
    now exists v.
    discriminate E.
  -  (*land*)
    destruct (find_valuation (conj_norm_converter (land p1 p2))) eqn:E in H;
      (try discriminate H).
    exists v.
    apply land_interp_interp.
    apply land_find_interp in E.
    assumption.
  - (*lor*)
    destruct (find_valuation (conj_norm_converter (lor p1 p2))) eqn:E in H;
      try(discriminate H).
    exists v.
    apply lor_interp_interp.
    apply lor_find_interp in E.
    assumption.
  - (* mapsto*)   
    destruct (find_valuation (conj_norm_converter (mapsto p1 p2))) eqn:E in H;
      try(discriminate H).
    exists v.
    apply mapsto_interp_interp.
    apply mapsto_find_interp in E.
    assumption.
  - (* not*)   
    destruct (find_valuation (conj_norm_converter (not p))) eqn:E in H;
      try(discriminate H).
    exists v.
    apply not_interp_interp.
    apply not_find_interp in E.
    assumption.
Qed.  
