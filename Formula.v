Require Import Id.
From Coq Require Import Bool.Bool.

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
