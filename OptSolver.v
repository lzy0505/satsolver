Require Import Formula FindVal.
Require Import Btauto.


Fixpoint formula_optimizer (p : form): form :=
  match p with
  | var _ => p
  | boolv _  => p
  | land (var x) (boolv true) => (var x)
  | land (var x) (boolv false) => (boolv false)
  | land (boolv true) (var x) => (var x) 
  | land (boolv false) (var x) => (boolv false)                                
  | land p1 p2 => land (formula_optimizer p1) (formula_optimizer p2)
  | lor (var x) (boolv true) => (boolv true)
  | lor (var x) (boolv false) => (var x) 
  | lor (boolv true) (var x) => (boolv true)
  | lor (boolv false) (var x) => (var x) 
  | lor p1 p2 => lor (formula_optimizer p1) (formula_optimizer p2)
  | mapsto p1 p2 => mapsto (formula_optimizer p1) (formula_optimizer p2)
  | not p => not (formula_optimizer p)
  end.


  
Lemma interp_opt_land : forall (V : valuation) (p1 p2 : form),interp V (formula_optimizer (land p1 p2)) = interp V (formula_optimizer p1) && interp V (formula_optimizer p2).
  Proof.
    intros.
    destruct p1 eqn:P1 , p2 eqn:P2;
      unfold formula_optimizer;
      try reflexivity; (*trivial cases, form is not changed*)
      try (destruct b; (*boolv case*)
       unfold interp);
      try (btauto). (*land and lor cases*)
    Qed.
(**      
      try (symmetry;apply andb_true_l);
      try (symmetry;apply andb_false_r);
      try (symmetry;apply andb_false_l).
*)



  
Lemma interp_opt_lor : forall (V : valuation) (p1 p2 : form),interp V (formula_optimizer (lor p1 p2)) = interp V (formula_optimizer p1) || interp V (formula_optimizer p2).
Proof.
    intros.
    destruct p1 eqn:P1 , p2 eqn:P2;
      unfold formula_optimizer;
      try reflexivity; (*trivial cases, form is not changed*)
      try (destruct b; (*boolv case*)
           unfold interp);
      try (btauto). (*land and lor cases*)
  Qed.
(**     
        try (symmetry;apply orb_true_r);
        try (symmetry;apply orb_true_l);
        try (symmetry;apply orb_false_l).
        try (symmetry;apply orb_false_r).
*)

      
Lemma optimizer_correctness:forall (V : valuation) (p : form), (interp V p) =  (interp V (formula_optimizer p)).
Proof.
  intros.
  induction p;try reflexivity. 
  - rewrite interp_opt_land. (*land *)
    rewrite <-IHp1, <-IHp2.
    reflexivity.
  - rewrite interp_opt_lor. (*lor*)
    rewrite <-IHp1, <-IHp2.
    reflexivity.
  - unfold formula_optimizer. (*mapsto, just rewrite*)
    unfold interp.
    unfold formula_optimizer in IHp1, IHp2.
    unfold interp in IHp1, IHp2.
    rewrite IHp1, IHp2.
    reflexivity.
  - unfold formula_optimizer. (*not, just rewrite*)
    unfold interp.
    unfold formula_optimizer in IHp.
    unfold interp in IHp.
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
