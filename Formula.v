Require Import Bool.Bool.
Require Import Strings.String.
Export Bool.Bool.
Export Strings.String.

(** Identifier of the var is implement with string. *)
Inductive id  :=
| Id : string -> id.

(** equality of string (from LF) *)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** Define the equality on id. *)
Definition eqb_id  (i1 i2:id): bool :=
  match i1, i2 with
  |Id x, Id y => eqb_string x y (*use equality on string*)
  end.

(** Equality on Ids is decidable. *)
Lemma id_eq_dec : forall a b : id, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a,b.
  decide equality.
  apply string_dec.
Defined. (* Defined, since we will unfold it*)

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
