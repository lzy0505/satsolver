Require Import Formula FindVal NNFCvtrSolver.
Require Import Btauto.

(** Combine a clause with a cnf*)
Fixpoint or_clause_cnf (clause cnf : form)  : form :=
  match cnf with 
  | land cnf1 cnf2 => land (or_clause_cnf clause cnf1) (or_clause_cnf clause cnf2) (*distrubute clause*)
  | _ => lor cnf clause (* cnf is clause*)
  end.

(** Combine two cnfs. *)
Fixpoint or_cnf_cnf (cnf1 cnf2 : form)  : form :=
  match cnf1 with 
  | land cnf11 cnf12 => land (or_cnf_cnf cnf11 cnf2) (or_cnf_cnf cnf12 cnf2) (*distribute cnf2*)
  | _ => or_clause_cnf cnf1 cnf2 (* cnf1 is clause *)
  end.


(** Conversion from nnf to cnf. *)
Fixpoint nnf_cnf_converter (p :form) : form :=
  match  p with
  | land p1 p2 => land (nnf_cnf_converter p1) (nnf_cnf_converter p2) (*ok, convert sub-formulas*)
  | lor p1 p2 => or_cnf_cnf (nnf_cnf_converter p1) (nnf_cnf_converter p2) (*convert sub-formulas, and do or with or_cnf_cnf*)
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

(** or_clause_cnf works like normal lor. *)
Lemma or_clause_cnf_correctness: forall (V : valuation) (p1 p2:form), interp V (or_clause_cnf p1 p2) = interp V  p2 || interp V  p1.
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
    try apply or_clause_cnf_correctness.
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


Fixpoint is_clause (p : form) : bool :=
  match p with
  | var _ => true
  | boolv _ => true
  | land p1 p2 =>  false
  | lor p1 p2 =>  is_clause p1 && is_clause p2
  | mapsto _ _ => false
  | not (var _ ) => true (*only return true here*)
  | not (boolv _) => false
  | not (land _ _) => false
  | not (lor _ _) => false
  | not (mapsto _ _) => false
  | not (not _) => false               
  end.


Fixpoint is_cnf (p : form) : bool :=
  match p with
  | land p1 p2 =>  is_cnf p1 && is_cnf p2
  | lor p1 p2 =>  is_clause  p1 && is_clause p2
  | _ => is_clause p                
  end.


(** Conditions to use or_clause_cnf. *)
Lemma cnf_eq_clause_cnf:forall (p1 p2:form), is_cnf (or_clause_cnf p1 p2) = is_clause p1 && is_cnf p2.
Proof.
  intros.
  induction p2;try reflexivity; try (simpl;btauto).
  - simpl. rewrite IHp2_1, IHp2_2. (* land *)
    btauto.
Qed.

(** Conditions to use or_cnf_cnf. *)
Lemma cnf_eq_cnf_cnf:forall (p1 p2:form), is_cnf (or_cnf_cnf p1 p2) = is_cnf p1 && is_cnf p2.
Proof.
  intros.
  induction p1;simpl;try(rewrite cnf_eq_clause_cnf;reflexivity).
  - rewrite IHp1_1, IHp1_2. (*land*)
    btauto.
Qed.


(*got stucked here if use equivalent:
is_conj_normal (or_cnf_cnf p1 p2) =true <-> is_cnf p1 =true /\ is_cnf p2=true
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
