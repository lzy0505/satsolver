Require Import Id Formula.
From Coq Require Import Bool.Bool.


Fixpoint formula_optimizer (p : form): form :=
  match p with
  | var _ => p
  | bool _  => p
  | land (var x) (bool true) => (var x)
  | land (var x) (bool false) => (bool false)
  | land (bool true) (var x) => (var x) 
  | land (bool false) (var x) => (bool false)                                
  | land p1 p2 => land (formula_optimizer p1) (formula_optimizer p2)
  | lor (var x) (bool true) => (bool true)
  | lor (var x) (bool false) => (var x) 
  | lor (bool true) (var x) => (bool true)
  | lor (bool false) (var x) => (var x) 
  | lor p1 p2 => lor (formula_optimizer p1) (formula_optimizer p2)
  | mapsto p1 p2 => mapsto (formula_optimizer p1) (formula_optimizer p2)
  | not p => not (formula_optimizer p)
  end.


Lemma land_interp : forall (V : valuation) (p1 p2 : form),interp V  (land p1 p2) = interp V  p1 && interp V p2.
Proof.
  intros.
  destruct p1,p2;(try unfold interp;reflexivity).
  Qed.
  
  
Lemma opt_land : forall (V : valuation) (p1 p2 : form),interp V (formula_optimizer (land p1 p2)) = interp V (formula_optimizer p1) && interp V (formula_optimizer p2).
  Proof.
    intros.
    destruct p1 eqn:P1 , p2 eqn:P2;(try unfold formula_optimizer; try apply land_interp);(try destruct b;unfold interp);try (symmetry;apply andb_true_r);try (symmetry;apply andb_true_l);(try symmetry;apply andb_false_r);(try symmetry;apply andb_false_l).
  Qed.


Lemma lor_interp : forall (V : valuation) (p1 p2 : form),interp V  (lor p1 p2) = interp V  p1 || interp V p2.
Proof.
  intros.
  destruct p1,p2;(try unfold interp;reflexivity).
  Qed.
  
  
Lemma opt_lor : forall (V : valuation) (p1 p2 : form),interp V (formula_optimizer (lor p1 p2)) = interp V (formula_optimizer p1) || interp V (formula_optimizer p2).
  Proof.
    intros.
    destruct p1 eqn:P1 , p2 eqn:P2;(try unfold formula_optimizer; try apply lor_interp);(try destruct b;unfold interp);try (symmetry;apply orb_true_r); try (symmetry;apply orb_true_l); try (symmetry;apply orb_false_l). try (symmetry;apply orb_false_r).
Qed.

      
Lemma optimizer_correctness:forall (V : valuation) (p : form), (interp V p) =  (interp V (formula_optimizer p)).

Proof.
  intros.
  
  induction p;try reflexivity.
  - destruct p1  eqn:P1, p2  eqn:P2;(try reflexivity);rewrite  land_interp;rewrite opt_land;try(unfold formula_optimizer; reflexivity);try(rewrite IHp1; rewrite IHp2;reflexivity).
  - destruct p1  eqn:P1, p2  eqn:P2;(try reflexivity);rewrite  lor_interp;rewrite opt_lor;try(unfold formula_optimizer; reflexivity);try(rewrite IHp1; rewrite IHp2;reflexivity).
  - unfold formula_optimizer. unfold interp.
    unfold formula_optimizer in IHp1, IHp2.
    unfold interp in IHp1, IHp2.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
  - unfold formula_optimizer. unfold interp.
     unfold formula_optimizer in IHp.
     unfold interp in IHp.
     rewrite IHp.
     reflexivity.
Qed.       
