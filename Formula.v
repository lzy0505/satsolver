Require Import Bool.Bool.
Require Import Strings.String.
Export Bool.Bool.
Export Strings.String.

(** Identifier of the var is implement with string. *)
Inductive id  :=
| Id : string -> id.

(** TODO*)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** Define the equality on id. *)
Definition eqb_id  (i1 i2:id): bool :=
  match i1 with
  | Id x => match i2 with
            | Id y => eqb_string x y (*use equality on string*)
            end
  end.

(** Equality on Ids is decidable. *)
Lemma id_eq_dec : forall a b : id, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a,b.
  decide equality.
  apply string_dec.
Defined. (* TODO make defined, since we will unfold it*)

(** Exercise 2.1 *)
(** Define formula. *)
Inductive form :=
| var : id-> form
| boolv : bool ->form
| land : form -> form -> form
| lor : form -> form -> form
| mapsto : form -> form -> form
| not : form -> form.


(** Define valuation of the formula. *)
Definition valuation := id -> bool.
Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation) (x : id) (b : bool) : valuation :=
  fun y => if eqb_id x y then b else V y.

(** Exercise 2.3 *)
(** Interprete the formula with valuation. *)
Fixpoint interp (V : valuation) (p : form) : bool :=
  match p with
  | var i => (V i)
  | boolv b => b
  | land f1 f2 => andb (interp V f1) (interp V f2)
  | lor f1 f2 => orb (interp V f1) (interp V f2)
  | mapsto f1 f2 => orb  (negb (interp V f1)) (interp V f2)
  | not f => negb (interp V f)
  end.

(** Exercise 2.2 *)
Module Test_override.
 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

 Check (land (lor x (not y)) (lor (not x) y) ).
 Check (mapsto (not y) (lor x y) ).
 Check (land (land x (not x)) (boolv true)).

 Definition context := override (override empty_valuation (Id "x") false) (Id "y") true.

End Test_override.

(** 
    Define a tactic that we use a lot.
    For a bool equaltion as a && b = ture in the assumption, 
    it can be splited into a = true and b = true
 **)
Ltac split_andb_true H :=
  symmetry in H;
  apply andb_true_eq in H;
  destruct H as [H H0];
  symmetry in  H,H0.




(** 
    Helper lemmas for interp, which define the equavalence between interperation of a formula and its sub-formula(s).
    We can expend the interperation on a formula if it has sub-formula(s). 
 **)

Lemma split_interp_land: forall p1 p2 V, interp V p1=true /\ interp V p2=true <-> interp V (land p1 p2)=true.
Proof.
  split;
    intros;
    unfold interp in H.
  - (* -> *)
    destruct H.
    (* has interp p1 = true, interp p2 = true*)
    unfold interp.
    unfold interp in H0.
    now rewrite H,H0.
  - (* <- *)
    split;(*proofs for both sub-forms are same*)
    split_andb_true H;
    assumption.
Qed.

Lemma split_interp_lor: forall p1 p2 V, interp V p1=true \/ interp V p2=true <-> interp V (lor p1 p2)=true.
Proof.
  split;
    intros;
    unfold interp in H.
  - (* -> *)
    destruct H;
      unfold interp;
      rewrite H.
    + reflexivity. (*has true || x = true*)
    + apply orb_true_r. (*has x || true = true, need a lemma*)
  - (* -> *)
    apply orb_prop in H. (*convert from a || b = true -> a=true \/ b =true*)
    assumption.
Qed.


Lemma split_interp_mapsto: forall p1 p2 V, interp V p1=false \/ interp V p2=true <-> interp V (mapsto p1 p2)=true.
Proof.
  split;
    intros;
    unfold interp in H.
  - (* -> *) (*same as lor, since mapsto x y = lor (not x) y*)
    destruct H;
      unfold interp;
      rewrite H.
    + reflexivity.
    + apply orb_true_r.
  - (* <- *)
    apply orb_prop in H.
    destruct H.
    + left. (*handle not*)
      apply negb_true_iff. (*a= false -> negb a =true*)
      assumption.
    + right.
      assumption.
Qed.


Lemma split_interp_not: forall p V, interp V p=false  <-> interp V (not p)=true.
Proof.
  split;
    intros;
    unfold interp in H;
    unfold interp.
  - (* -> *)   
    rewrite H.
    reflexivity.
  - (* <- *)
    unfold interp.
    apply negb_true_iff. (*same as mapsto*)
    assumption.
Qed.

(**Define satisfiable of a formula*)
Definition satisfiable (p : form) : Prop:=
  exists V : valuation, interp V p = true.

Module Test_satisfiable.
  Definition x := (var (Id "x")).
  Definition y := (var (Id "y")).
  
  (** Exercise 2.4 *)
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
