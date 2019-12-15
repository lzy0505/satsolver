Require Import Formula FindVal NNFCvtrSolver.
Require Import Btauto.

(** Combine a disjunction form with a cnf*)
Fixpoint or_disj_cnf (C A : form)  : form :=
  match A with (* A is in cnf*)
  | land B1 B2 => land (or_disj_cnf C B1) (or_disj_cnf C B2) (*distrubute C*)
  | _ => lor A C (* A doesn't have land, just or!*)
  end.

(** Combine two cnfs. *)
Fixpoint or_cnf_cnf (A1 A2 : form)  : form :=
  match A1 with (*A1 is in cnf*)
  | land B1 B2 => land (or_cnf_cnf B1 A2) (or_cnf_cnf B2 A2) (*distribute A2*)
  | _ => or_disj_cnf A1 A2 (* A1 only has disjunction*)
  end.


(** Conversion from nnf to cnf. *)
Fixpoint nnf_cnf_converter (p :form) : form :=
  match  p with
  | land B1 B2 => land (nnf_cnf_converter B1) (nnf_cnf_converter B2) (*ok, convert sub-formulas*)
  | lor B1 B2 => or_cnf_cnf (nnf_cnf_converter B1) (nnf_cnf_converter B2) (*convert sub-formulas, and do or with or_cnf_cnf*)
  | _ => p
  end.


Module Test_cnf_converter.

Definition A := (Id "A").
Definition B := (Id "B").
Definition C := (Id "C").
Definition D := (Id "D").
Definition E := (Id "E").

Definition f := (lor (lor (land  (not (var A)) (var B)) (var C) ) (land (var D) (var E))).

Eval compute in (nnf_cnf_converter f).

End Test_cnf_converter.

(** or_disj_cnf works like normal lor. *)
Lemma or_disj_cnf_correctness: forall (V : valuation) (p1 p2:form), interp V (or_disj_cnf p1 p2) = interp V  p2 || interp V  p1.
Proof.
  intros.
  induction p2; simpl;
    try reflexivity.
  - rewrite IHp2_1. (* p2 = land p2_1 p2_2*)
    rewrite IHp2_2.
    btauto.
Qed.

(** or_cnf_cnf works like normal lor. *)
Lemma or_cnf_cnf_correctness: forall (V : valuation) (p1 p2:form), interp V (or_cnf_cnf p1 p2) = interp V  p2 || interp V  p1.
Proof.
  intros.
  induction p1;simpl;
    try reflexivity;
    try apply or_disj_cnf_correctness.
  - rewrite IHp1_1. (* p1 = land p1_1 p1_2*)
    rewrite IHp1_2.
    btauto.
Qed.

(** Real cnf converter. First do nnf conversion, then cnf. *)
Definition cnf_converter ( p :form) : form :=
  nnf_cnf_converter (nnf_converter false p).

(** Part conversion doesn't change interpretation. *)
Lemma nnf_cnf_converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (nnf_cnf_converter p).
Proof.
  intros.
  induction p;try reflexivity.
  - simpl. (*land*)
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
  - simpl. (*lor*)
    rewrite or_cnf_cnf_correctness.
    rewrite IHp1, IHp2.
    btauto.
Qed.

(** Whole conversion doesn't change interpretation. *)
Lemma cnf_converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (cnf_converter p).
Proof.
  intros.
  unfold cnf_converter.
  transitivity (interp V  (nnf_converter false p)).
  (*prove interp V p = interp V (nnf_converter false p) *)
  apply nnf_converter_correctness.
  apply nnf_cnf_converter_correctness.
Qed.


(** Check formula only has disjunction. *)
Fixpoint is_disj (p : form) : bool :=
  match p with
  | land p1 p2 =>  false
  | lor p1 p2 =>  is_disj p1 && is_disj p2
  | mapsto _ _ => false
  | _ => true                
  end.

(** Check formula is in cnf. *)
Fixpoint is_cnf (p : form) : bool :=
  match p with
  | land p1 p2 =>  is_cnf p1 && is_cnf p2
  | lor p1 p2 =>  is_disj  p1 && is_disj p2
  | mapsto _ _ => false
  | _ => true                
  end.

(** Check formula is in cnf and nnf. *)
Definition real_is_cnf (p : form) : bool :=
  is_cnf p && is_nnf p.

(** Conditions to use or_disj_cnf. *)
Lemma cnf_eq_disj_cnf:forall (p1 p2:form), is_cnf (or_disj_cnf p1 p2) = is_disj p1 && is_cnf p2.
Proof.
  intros.
  induction p2;simpl;try reflexivity;try btauto.
  - rewrite IHp2_1, IHp2_2. (* land *)
    btauto.
Qed.

(** Conditions to use or_cnf_cnf. *)
Lemma cnf_eq_cnf_cnf:forall (p1 p2:form), is_cnf (or_cnf_cnf p1 p2) = is_cnf p1 && is_cnf p2.
Proof.
  intros.
  induction p1;simpl;try(rewrite cnf_eq_disj_cnf;reflexivity).
  - rewrite IHp1_1, IHp1_2. (*land*)
    btauto.
Qed.


(*got stucked here if use equivalent:
is_conj_normal (or_cnf_cnf p1 p2) =true <-> is_cnf p1 =true && is_cnf p2=true
 *)

(** true/false doesn't effect is_cnf. *)
Lemma is_cnf_neg : forall (p:form), is_cnf (nnf_cnf_converter (nnf_converter false p))= is_cnf (nnf_cnf_converter (nnf_converter true p)).
  Proof.
    intros.
    induction p;simpl.
    - reflexivity. (*var*)
    - destruct b;reflexivity. (*boolv*)
    - rewrite cnf_eq_cnf_cnf. (*land*)
      rewrite IHp1, IHp2.
      reflexivity.
    - rewrite cnf_eq_cnf_cnf. (*lor*)
      rewrite IHp1, IHp2.
      reflexivity.
    - rewrite cnf_eq_cnf_cnf. (*mapsto*)
      rewrite IHp1, IHp2.
      reflexivity.
    - symmetry in IHp. (*not*)
      assumption.
Qed.

(** Conversion is correct. *) 
Lemma cnf_converter_cnf_correctness: forall (p:form), is_cnf (cnf_converter  p) = true.
Proof.
  intro.
  induction p;
    try (reflexivity);
    unfold cnf_converter;
    simpl.
  - unfold cnf_converter in IHp1, IHp2. (*land *)
    rewrite IHp1, IHp2.
    reflexivity.
  - rewrite cnf_eq_cnf_cnf. (*lor *)
    unfold cnf_converter in IHp1, IHp2.
    rewrite IHp1, IHp2.
    reflexivity.
  - (*mapsto case, handle the not with is_cnf_neg*)
    rewrite cnf_eq_cnf_cnf.
    unfold cnf_converter in IHp1.
    rewrite is_cnf_neg in IHp1.
    rewrite IHp1.
    assumption.
  - (*not case, handle the not with is_cnf_neg*)
    unfold cnf_converter in IHp.
    rewrite is_cnf_neg in IHp.
    assumption.
Qed.

(** or_disj_cnf keeps is_nnf. *)
Lemma disj_cnf_keep_nnf:forall (p1 p2:form), is_nnf (or_disj_cnf p1 p2) = is_nnf p1 && is_nnf p2.
Proof.
  intros.
  induction p2;simpl;
    try reflexivity;
    try btauto.
  - rewrite IHp2_1, IHp2_2. (* land *)
    btauto.
Qed.

(** or_cnf_cnf keeps is_nnf. *)
Lemma cnf_cnf_keep_nnf:forall (p1 p2:form), is_nnf (or_cnf_cnf p1 p2) = is_nnf p1 && is_nnf p2.
Proof.
  intros.
  induction p1;simpl;
    try(rewrite disj_cnf_keep_nnf;reflexivity).
  - rewrite IHp1_1, IHp1_2. (*land*)
    btauto.
Qed.

(** true/false doesn't effect is_nnf. *)
Lemma is_nnf_neg_cnf : forall (p:form), is_nnf (nnf_cnf_converter (nnf_converter false p))= is_nnf (nnf_cnf_converter (nnf_converter true p)).
  Proof.
    intros.
    induction p;simpl;
      try (try(destruct b); (*var and boolv *)
           reflexivity);
      try (rewrite cnf_cnf_keep_nnf; (*land lor mapsto*)
           rewrite IHp1, IHp2;
           reflexivity).
    - symmetry in IHp. (*not*)
      assumption.
Qed.

(** Conversion is correct for nnf. *)
Lemma cnf_converter_nnf_correctness: forall (p:form), is_nnf (cnf_converter  p) = true.
Proof.
  intros.
  induction p;
    try (reflexivity);
    unfold cnf_converter;
    simpl;
    try(try (rewrite cnf_cnf_keep_nnf); (* land lor*)
        unfold cnf_converter in IHp1, IHp2;
        rewrite IHp1, IHp2;
        reflexivity).
  - rewrite cnf_cnf_keep_nnf. (*mapsto case, handle the not with is_nnf_neg_cnf*)
    unfold cnf_converter in IHp1.
    rewrite is_nnf_neg_cnf in IHp1.
    rewrite IHp1.
    assumption.
  - (*not case, handle the not with is_nnf_neg_cnf*)
    unfold cnf_converter in IHp.
    rewrite is_nnf_neg_cnf in IHp.
    assumption.
Qed.

(** Conversion is really correct.*)
Lemma cnf_converter_correctness_real: forall (p:form), real_is_cnf (cnf_converter  p) = true.
Proof.
  intros.
  unfold real_is_cnf.
  rewrite cnf_converter_cnf_correctness.
  now rewrite cnf_converter_nnf_correctness.
Qed.


(** Integration *)
Definition solver (p : form) : bool:=
  match find_valuation (cnf_converter p) with
  | Some _ => true
  | None => false
  end.


Lemma find_interp: forall p V, find_valuation (cnf_converter p)=Some V -> interp V p=true.
Proof.
  intros.
  unfold find_valuation in H;
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (cnf_converter p))). (*change here*)
  - discriminate H. (*valuation list is empty*)
  - rewrite <-cnf_converter_correctness in H.
    destruct (interp a p) eqn: E1.
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
  destruct (find_valuation (cnf_converter p)) eqn:E in H. (*return of find_valuation*) (*change here*)
  - exists v. (*Some v*)
    apply find_interp in E.
    assumption.
  - discriminate H. (*None*)
Qed.
