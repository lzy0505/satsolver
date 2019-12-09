Require Import Id Formula Extension.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Import ListNotations.
Require Setoid. 


Definition satisfiable (p : form) : Prop:=
  exists V : valuation, interp V p = true.

Module Test_satisfiable.

 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

 Lemma test1 : satisfiable (land (lor x (not y)) (lor (not x) y)).
 Proof.
   unfold satisfiable.
   now exists (override (override empty_valuation (Id "x") false) (Id "y") false).
Qed.
              
 Lemma test2 : satisfiable (mapsto (not y) (lor x y)).
 Proof.
   unfold satisfiable.
   now exists (override (override empty_valuation (Id "x") true) (Id "y") false).
 Qed.

End Test_satisfiable.

Fixpoint collect_var (p : form) : (set id):=
  match p with
  | var i => (set_add  id_eq_dec i nil)
  | bool _ => nil
  | land f1 f2 => set_union id_eq_dec (collect_var f1)  (collect_var f2)
  | lor f1 f2 => set_union  id_eq_dec (collect_var f1) (collect_var f2)
  | mapsto f1 f2 => set_union id_eq_dec (collect_var f1) (collect_var f2)
  | not f => (collect_var f)
  end.


Module Test_collect_var.

 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

Compute (set_add id_eq_dec (Id "x") nil).
 
Eval compute in (collect_var (land (lor x (not y)) (lor (not x) y))).



End Test_collect_var.

(*
Can't defined in the following generator way

Fixpoint next_valuation (V : valuation) (l : list id) : option valuation :=
  match l with
  | nil => None
  | x::xs => if negb (V x)
             then Some (override V x true)
             else next_valuation (override V x false) xs
  end.

Module Test''.

 Definition x := (Id "x").
 Definition y := (Id "y").
 Definition z := (Id "z").
 
 Definition apply_test (ov : option valuation) (i :id) :option Datatypes.bool :=
   match ov with
   |Some v => Some (v i)
   |None => None
   end.

 Fixpoint apply_list  (ov : option valuation) (l :list id) : list (option Datatypes.bool):=
   match l with 
   |nil => []
   | x :: xs => (apply_test ov x) :: (apply_list ov xs)
   end.
 
Eval compute in (apply_list (next_valuation (override (override (override empty_valuation x true) y false)z true ) [x;y;z]) [x;y;z]).

Fixpoint all_valuation (V : option valuation) (l: list id) (n : nat) : list (list (option Datatypes.bool)):=
  match n with
  | 0 => []
  | S n' =>
    match V with
    |Some v => (apply_list V l) :: (all_valuation (next_valuation v l) l n')
    |None => []
    end
  end.



Eval compute in (all_valuation (Some empty_valuation) [x;y;z] 10).

End Test''.

Fixpoint try_valuation (v: valuation) (p:form) (l :list id) : option valuation :=
  if interp v p
  then Some v
  else match (next_valuation v l) with
       | None => None
       | Some v' => try_valuation v' p l
       end.
Error!
*)

Fixpoint add_id (lv: list valuation) (i:id) : list valuation :=
   match lv with
  | nil => []
  | v::vs => [(override v i true);(override v i false)] ++ (add_id vs i)
   end.

Fixpoint enum_valuation (l : list id) : list valuation :=
  match l with
  | nil => [empty_valuation]
  | x::xs => add_id (enum_valuation xs) x
  end.
             
Module Test_enum_valuation.

 Definition x := (Id "x").
 Definition y := (Id "y").
 Definition z := (Id "z").

 

 Fixpoint apply_list  (v : valuation) (l :list id) : list Datatypes.bool:=
   match l with 
   |nil => []
   | x :: xs => (v x) :: (apply_list v xs)
   end.

 Fixpoint all_valuations (lv : list valuation) (l: list id) : list (list Datatypes.bool):=
    match lv with
    |nil => []
    |v :: vs =>
     (apply_list v l) :: (all_valuations vs l)
  end.
 
 Eval compute in (all_valuations (add_id [(override (override empty_valuation x true) y false);(override (override empty_valuation x false) y false);(override (override empty_valuation x true) y true);(override (override empty_valuation x false) y true)] z) [x;y;z]).

 Eval compute in (all_valuations (enum_valuation [x;y;z]) [x;y;z]).
End Test_enum_valuation.

Fixpoint try_valuation (lv: list valuation) (p : form) : option valuation :=
  match lv with
  | nil => None
  | v::vs => if interp v p then Some v
             else try_valuation vs p
  end.


Definition find_valuation (p : form) : option valuation :=
  let ids := collect_var p in
  let vals := (enum_valuation ids) in
  try_valuation vals p.

Module Test_find_valuation.
 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

 Definition apply_test (ov : option valuation) (i :id) :option Datatypes.bool :=
   match ov with
   |Some v => Some (v i)
   |None => None
   end.

Fixpoint apply_list  (ov : option valuation) (l :list id) : list (option Datatypes.bool):=
   match l with 
   |nil => []
   | x :: xs => (apply_test ov x) :: (apply_list ov xs)
   end.

Definition find_valuation' (p : form) : list (option Datatypes.bool) :=
  let ids := collect_var p in
  let vals := (enum_valuation ids) in
  apply_list (try_valuation vals p) ids.
 
 Eval compute in (find_valuation' (land (land x (not x)) (bool true))). 

End Test_find_valuation.


Definition solver (p : form) :Datatypes.bool:=
  match find_valuation (formula_optimizer p) with
  | Some _ => true
  | None => false
  end.




(*
Lemma find_val_rec : forall p v v' l, interp v p = true \/ (interp v p = false /\ try_valuation l p= Some v' ) ->  (exists V, try_valuation (v::l) p=Some V).
Proof.
  intros.
  destruct H.
  - exists v.
    unfold try_valuation.
    now rewrite H.
  - exists v'.
    unfold try_valuation.
    destruct H.
    rewrite H.
    unfold try_valuation in H0.
    assumption.
Qed.


  

Lemma and_solver: forall p1 p2 V, find_valuation (land p1 p2)=Some V -> satisfiable p1.
Proof.
  intros.
    unfold find_valuation in H.
    unfold try_valuation in H.
    induction (enum_valuation (collect_var (land p1 p2))). 
    + discriminate H.
    +  destruct (interp a (land p1 p2)) eqn: E1.
       * unfold satisfiable.
         exists a.
         apply and_interp in E1.
         destruct E1.
         assumption.
       * apply IHl. (*why it works?*)
         apply H.
Qed.*)

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


(*Lemma solver_opt : forall p, find p = find (formula_optimizer p).*)
  
  
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
                  
                  

    
    
     
  
