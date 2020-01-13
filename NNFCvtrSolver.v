Require Import Formula FindVal OptSolver.
Require Import Btauto.



Fixpoint nnf_converter (hn :Datatypes.bool) (p :form) : form :=
  match hn, p with
  | false, var _ =>  p
  | true, var _ => (not  p)
  | false, boolv _ => p
  | true, boolv true => boolv false
  | true, boolv false => boolv true   
  | false, land p1 p2 => land (nnf_converter false p1) (nnf_converter false p2)
  | true, land p1 p2 =>  lor (nnf_converter true  p1) (nnf_converter true  p2)
  | false, lor p1 p2 => lor (nnf_converter false p1) (nnf_converter false p2)
  | true, lor p1 p2 =>  land (nnf_converter true  p1) (nnf_converter true  p2)
  | false, mapsto p1 p2 => lor (nnf_converter true p1) (nnf_converter false p2)
  | true, mapsto p1 p2 => land  (nnf_converter false p1)  (nnf_converter true p2)   
  | false, not p1  => (nnf_converter true p1)
  | true, not p1  => (nnf_converter false p1)
  end.

Definition x := (Id "x").
Definition y := (Id "y").

Definition f :=  (mapsto (land (var x) (var y)) (var y)).

Eval compute in (nnf_converter false f).


(** Boolean argument works well.*)
Lemma converter_neg:forall (V : valuation) (p:form),  negb (interp V (nnf_converter false p)) = interp V (nnf_converter true p).
Proof.
  intros.
  induction p;
    try reflexivity.
  - destruct b;reflexivity. (* boolv *)
  - simpl. (* land *)
    rewrite <-IHp1, <-IHp2.
    btauto.
  - simpl. (* lor *)
    rewrite <-IHp1, <-IHp2.
    btauto.
  - simpl. (* mapsto *)
    rewrite <-IHp1, <-IHp2.
    btauto.
  - simpl. (* not *)
    rewrite <-IHp.
    btauto.
Qed.     

(** Interpretations are same. *)
Lemma nnf_converter_correctness: forall (V : valuation) (p:form), interp V p = interp V (nnf_converter false p).
Proof.
  induction p;try reflexivity.
  - simpl. (* land *)
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl. (* lor *)
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl. (* mapsto *)
    rewrite IHp1, IHp2.
    rewrite converter_neg.
    reflexivity.
  - simpl. (* not *)
    rewrite IHp.
    apply converter_neg.
  Qed.
  



(** Check formula is in NNF form. *)
Fixpoint is_nnf  (p : form) : bool :=
  match p with
  | var _ => true
  | boolv _ => true
  | land p1 p2 =>  is_nnf p1 && is_nnf p2
  | lor p1 p2 =>  is_nnf p1 && is_nnf p2
  | mapsto p1 p2 =>  false  
  | not (var _ ) => true (*only return true here*)
  | not (boolv _) => false
  | not (land _ _) => false
  | not (lor _ _) => false
  | not (mapsto _ _) => false
  | not (not _) => false                   
  end.


(** true/false doesn't matter! *)
Lemma is_nnf_neg : forall (p:form), is_nnf (nnf_converter true p) =  is_nnf (nnf_converter false p).
  Proof.
    intros.
    induction  p;
      try reflexivity;(*var*)
      try (destruct b; reflexivity);(*boolv*)
      try(simpl;
          now rewrite IHp1, IHp2). (* land lor mapsto*)
     - simpl. symmetry. assumption. (*not*)
Qed.
     
    
(** Conversion is correct. *)
Lemma nnf_converter_correctness_2: forall (p:form), is_nnf (nnf_converter false  p) = true.
Proof.
  intro.
  induction p;
    try reflexivity.
  - simpl. (*land*)
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl. (* lor*)
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl. (*mapsto*)
    rewrite is_nnf_neg.
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl. (*not*)
    now rewrite is_nnf_neg.    
Qed.



(** Integtation *)
Definition solver (p : form) :bool:=
  match find_valuation (nnf_converter false p) with
  | Some _ => true
  | None => false
  end.


Lemma find_interp: forall p V, find_valuation (nnf_converter false p)=Some V -> interp V p=true.
Proof.
  intros.
  unfold find_valuation in H;
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (nnf_converter false p))). (*change here*)
  - discriminate H. (*valuation list is empty*)
  - rewrite <-nnf_converter_correctness in H.
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
  destruct (find_valuation (nnf_converter false p)) eqn:E in H. (*return of find_valuation*) (*change here*)
  - exists v. (*Some v*)
    apply find_interp in E.
    assumption.
  - discriminate H. (*None*)
Qed.
