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



(** Check formula is in NNF form. *)
Inductive is_nnf : form -> Prop :=
| var : forall i, is_nnf (var i)
| boolv : forall b, is_nnf (boolv b)
| land: forall p1 p2, is_nnf p1 -> is_nnf p2 -> is_nnf (land p1 p2)
| lor: forall p1 p2, is_nnf p1 -> is_nnf p2 -> is_nnf (lor p1 p2)
| not: forall i, is_nnf (not (var i))
.
  
(** true/false doesn't matter! *)
(* can't do split at beginning*)
Lemma is_nnf_neg : forall (p:form), is_nnf (nnf_converter true p) <-> is_nnf (nnf_converter false p).
  Proof.
    intros.
    induction  p;simpl;
    constructor;intros;
      try (inversion H; (*land lor mapsto*)
        apply IHp1 in H2;
        apply IHp2 in H3;
        constructor;
        assumption);
      try constructor; (*var*)
      try (apply IHp in H; (*not*)
        assumption).
    - destruct b;constructor. (*bool*)
  Qed.
  
    
(** Conversion is correct. *)
Lemma nnf_converter_correctness_2: forall (p:form), is_nnf (nnf_converter false  p).
Proof.
  intro.
  induction p;simpl.
  - constructor.
  - constructor.
  - constructor;assumption.
  - constructor;assumption.
  - apply is_nnf_neg in IHp1.
    constructor;assumption.
  - apply is_nnf_neg.
    assumption.
Qed.

