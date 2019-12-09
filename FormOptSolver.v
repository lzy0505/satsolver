Require Import Formula Find.



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






Definition solver (p : form) :Datatypes.bool:=
  match find_valuation (formula_optimizer p) with
  | Some _ => true
  | None => false
  end.




Lemma land_find_interp: forall p1 p2 V, find_valuation (formula_optimizer (land p1 p2))=Some V -> interp V p1=true /\ interp V p2=true.
Proof.
  intros.
  split;
    unfold find_valuation in H;
    unfold try_valuation in H;
    induction (enum_valuation (collect_var (formula_optimizer (land p1 p2)))); (*add optimizer*)
    try (discriminate H);
    try (rewrite <-optimizer_correctness in H;
         destruct (interp a (land p1 p2)) eqn: E1); (*rewrite to the old proof*)
    try(inversion H;
        apply land_interp_interp in E1;
        destruct E1;
        rewrite <-H1;
        assumption);
    try(apply IHl; (*why it works?*)
        apply H).
  Qed.
 




Lemma lor_find_interp: forall p1 p2 V, find_valuation (formula_optimizer  (lor p1 p2))=Some V -> interp V p1=true \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (formula_optimizer (lor p1 p2)))). (*add optimizer*)
  - discriminate H.
  - rewrite <-optimizer_correctness in H.
    destruct (interp a (lor p1 p2)) eqn: E1.
    + inversion H.
      apply lor_interp_interp in E1.
      rewrite <-H1.
      assumption.
    + apply IHl. (*why it works?*)
      apply H.
Qed.




Lemma mapsto_find_interp: forall p1 p2 V, find_valuation (formula_optimizer (mapsto p1 p2))=Some V -> interp V p1=false \/ interp V p2=true.
Proof.
  intros.
  unfold find_valuation,try_valuation in H.
  induction (enum_valuation (collect_var (formula_optimizer (mapsto p1 p2)))).
    - discriminate H.
    - rewrite <-optimizer_correctness in H.
      destruct (interp a (mapsto p1 p2)) eqn: E1.    
       + inversion H.
         apply mapsto_interp_interp in E1.
         rewrite <-H1.
         assumption.
       + apply IHl. (*why it works?*)
         apply H.
Qed.



Lemma not_find_interp: forall p V, find_valuation (formula_optimizer(not p))=Some V -> interp V p=false.
Proof.
  intros.
  unfold find_valuation, try_valuation in H.
  induction (enum_valuation (collect_var (formula_optimizer (not p)))).
  - discriminate H.
  - rewrite <-optimizer_correctness in H.
    destruct (interp a (not p)) eqn: E1.
    + inversion H.
      apply not_interp_interp in E1.
      rewrite <-H1.
      assumption.
    + apply IHl. (*why it works?*)
      apply H.
Qed.


(*Can't prove! Lemma solver_opt : forall p, find p = find (formula_optimizer p).*)
  
  
Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof.
  intros.
  destruct p;unfold satisfiable;unfold solver in H. 
  - (*var*)
    exists (override empty_valuation i true).
    simpl.
    unfold override.
    now rewrite  <- beq_id_refl.
  - (*bool*)
    destruct (find_valuation (formula_optimizer (bool b))) eqn:E in H;(try discriminate H).
    unfold find_valuation in E.  
    simpl in E.
    destruct b.    
    now exists v.
    discriminate E.
  -  (*land*)
    destruct (find_valuation (formula_optimizer(land p1 p2))) eqn:E in H;(try discriminate H).
    exists v.
    apply land_interp_interp.
    apply land_find_interp in E.
    assumption.
  - (*lor*)
    destruct (find_valuation (formula_optimizer(lor p1 p2))) eqn:E in H;try(discriminate H).
    exists v.
    apply lor_interp_interp.
    apply lor_find_interp in E.
    assumption.
  - (* mapsto*)   
    destruct (find_valuation (formula_optimizer(mapsto p1 p2))) eqn:E in H;try(discriminate H).
    exists v.
    apply mapsto_interp_interp.
    apply mapsto_find_interp in E.
    assumption.
  - (* not*)   
    destruct (find_valuation (formula_optimizer(not p))) eqn:E in H;try(discriminate H).
    exists v.
    apply not_interp_interp.
    apply not_find_interp in E.
    assumption.
Qed.      
                  
                  

    
    
     
  
