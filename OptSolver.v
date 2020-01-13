Require Import Formula FindVal.
Require Import Btauto.


Definition andf (p1 p2 : form): form :=
  match p1,p2 with
  | (var x), (boolv true) => (var x)
  | (var x), (boolv false) => (boolv false)
  | (boolv true), (var x) => (var x)
  | (boolv false), (var x) => (boolv false) 
  | _, _ => land p1 p2
  end.

Definition orf (p1 p2 : form): form :=
  match p1,p2 with
  | (var x), (boolv true) => (boolv true)
  | (var x), (boolv false) => (var x) 
  | (boolv true), (var x) => (boolv true)
  | (boolv false), (var x) => (var x) 
  | _, _ => lor p1 p2
  end.
  

Fixpoint formula_optimizer (p : form): form :=
  match p with
  | var _ => p
  | boolv _  => p           
  | land p1 p2 => andf (formula_optimizer p1) (formula_optimizer p2)
  | lor p1 p2 => orf (formula_optimizer p1) (formula_optimizer p2)
  | mapsto p1 p2 => mapsto (formula_optimizer p1) (formula_optimizer p2)
  | not p => not (formula_optimizer p)
  end.


Lemma interp_opt_land :forall (V : valuation) (p1 p2 : form), interp V (andf p1 p2) = interp V p1 && interp V p2.
Proof.
  intros.
  destruct p1 eqn:P1 , p2 eqn:P2;try reflexivity;try (destruct b;simpl;btauto).
Qed.
  
 

Lemma interp_opt_lor :forall (V : valuation) (p1 p2 : form), interp V (orf p1 p2) = interp V p1 || interp V p2.
Proof.
  intros.
  destruct p1 eqn:P1 , p2 eqn:P2;try reflexivity;try (destruct b;simpl;btauto).
Qed.


      
Lemma optimizer_correctness:forall (V : valuation) (p : form), (interp V p) =  (interp V (formula_optimizer p)).
Proof.
  intros.
  induction p;try reflexivity;simpl. 
  - rewrite interp_opt_land. (*land *)
    rewrite <-IHp1, <-IHp2.
    reflexivity.
  - rewrite interp_opt_lor. (*lor*)
    rewrite <-IHp1, <-IHp2.
    reflexivity.
  - simpl. (*mapsto, just rewrite*)
    rewrite IHp1, IHp2.
    reflexivity.
  - simpl.
    rewrite IHp.
    reflexivity.
Qed.       


(** Integration with solver*)

Definition solver (p : form) :bool:=
  match find_valuation (formula_optimizer p) with (*change here*)
  | Some _ => true
  | None => false
  end.


Lemma find_interp: forall p V, find_valuation (formula_optimizer p)=Some V -> interp V p=true.
Proof.
  intros.
  unfold find_valuation in H;
  unfold try_valuation in H.
  induction (enum_valuation (collect_var (formula_optimizer p))). (*change here*)
  - discriminate H. (*valuation list is empty*)
  - rewrite <-optimizer_correctness in H.
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
  destruct (find_valuation (formula_optimizer p)) eqn:E in H. (*return of find_valuation*) (*change here*)
  - exists v. (*Some v*)
    apply find_interp in E.
    assumption.
  - discriminate H. (*None*)
Qed.
