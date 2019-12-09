Require Import Id.
From Coq Require Import Bool.Bool.
Export Id.
Export Bool.Bool.

(*alias*)
Definition id := Id.id. (*Type of id*)
Definition Id := Id.Id. (*Constructor of id*)

(*Definition of formula*)
Inductive form :=
| var : id-> form
| bool : bool ->form
| land : form -> form -> form
| lor : form -> form -> form
| mapsto : form -> form -> form
| not : form -> form.


(*Definition of valuation*)
Definition valuation := id -> Datatypes.bool.
Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation) (x : id) (b : Datatypes.bool) : valuation :=
  fun y => if beq_id x y then b else V y.

(*Interprete the formula with valuation*)
Fixpoint interp (V : valuation) (p : form) : Datatypes.bool :=
  match p with
  | var i => (V i)
  | bool b => b
  | land f1 f2 => andb (interp V f1) (interp V f2)
  | lor f1 f2 => orb (interp V f1) (interp V f2)
  | mapsto f1 f2 => orb  (negb (interp V f1)) (interp V f2)
  | not f => negb (interp V f)
  end.

Module Test_override.
 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

 Check (land (lor x (not y)) (lor (not x) y) ).
 Check (mapsto (not y) (lor x y) ).
 Check (land (land x (not x)) (bool true)).

 Definition context := override (override empty_valuation (Id "x") false) (Id "y") true.

End Test_override.


Lemma land_interp_interp: forall p1 p2 V, interp V p1=true /\ interp V p2=true <-> interp V (land p1 p2)=true.
Proof.
  intros.
  split.
  - intro.
    destruct H.
     unfold interp.
     unfold interp in H,H0.
     now rewrite H,H0.
  - intro.
    split;

    unfold interp in H;
      symmetry in  H;
      apply Bool.andb_true_eq in H;
      destruct H;
      unfold interp;
      symmetry;
      assumption.
      
Qed.

Lemma lor_interp_interp: forall p1 p2 V, interp V p1=true \/ interp V p2=true <-> interp V (lor p1 p2)=true.
Proof.
  intros.
  split.
  - intro.
    destruct H.
     unfold interp.
     unfold interp in H.
     rewrite H. reflexivity.
     unfold interp.
     unfold interp in H.
     rewrite H. Search orb. apply Bool.orb_true_r.
  - intro.

    unfold interp in H.
    Search orb.
    apply Bool.orb_prop in H.
   
      unfold interp;
      assumption.
      
Qed.


Lemma mapsto_interp_interp: forall p1 p2 V, interp V p1=false \/ interp V p2=true <-> interp V (mapsto p1 p2)=true.
Proof.
  intros.
  split.
  - intro.
    destruct H.
     unfold interp.
     unfold interp in H.
     rewrite H. reflexivity.
     unfold interp.
     unfold interp in H.
     rewrite H. apply Bool.orb_true_r.
  - intro.

    unfold interp in H.
    Search orb.
    apply Bool.orb_prop in H.
    destruct H.
    + left.
      
      unfold interp.
      Search negb.
      now apply Bool.negb_true_iff.
    + right.
      unfold interp.
      assumption.
Qed.



Lemma not_interp_interp: forall p V, interp V p=false  <-> interp V (not p)=true.
Proof.
  intros.
  split.
  - intro.
     unfold interp.
     unfold interp in H.
     rewrite H. reflexivity.
  - intro.

    unfold interp in H.

    unfold interp.
    now apply Bool.negb_true_iff.
Qed.
