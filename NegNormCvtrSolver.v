Require Import Formula Find FormOptSolver.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Import ListNotations.


Fixpoint neg_norm_converter (hn :Datatypes.bool) (p :form) : form :=
  match hn, p with
  | false, var _ =>  p
  | true, var _ => (not  p)
  | false, bool _ => p
  | true, bool true => bool false
  | true, bool false => bool true   
  | false, land p1 p2 => land (neg_norm_converter false p1) (neg_norm_converter false p2)
  | true, land p1 p2 =>  lor (neg_norm_converter true  p1) (neg_norm_converter true  p2)
  | false, lor p1 p2 => lor (neg_norm_converter false p1) (neg_norm_converter false p2)
  | true, lor p1 p2 =>  land (neg_norm_converter true  p1) (neg_norm_converter true  p2)
  | false, mapsto p1 p2 => mapsto (neg_norm_converter false  p1) (neg_norm_converter false p2)
  | true, mapsto p1 p2 => land  (neg_norm_converter false p1)  (neg_norm_converter true p2)   
  | false, not p1  => (neg_norm_converter true p1)
  | true, not p1  => (neg_norm_converter false p1)
  end.

Definition x := (Id "x").
Definition y := (Id "y").

Definition f := (not (land (var x) (lor (not (var x)) (var y)))).

Eval compute in (neg_norm_converter false f).

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
