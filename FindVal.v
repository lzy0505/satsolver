Require Import Formula.
Require Import Lists.ListSet.
Require Import Lists.List.
Import Lists.List.ListNotations. 

(** Collect different variables into a list set.*)
Fixpoint collect_var (p : form) : (set id):=
  match p with
  | var i => (set_add  id_eq_dec i nil)
  | boolv _ => nil
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


(** Add a new id into the enum of valuation for k ids, ruturn enum of valuation for k+1 ids.*)
Fixpoint add_id (lv: list valuation) (i:id) : list valuation :=
   match lv with
  | nil => []
  | v::vs => [(override v i true);(override v i false)] ++ (add_id vs i)
   (*for each v, we add a true and a false, get two new v_s.*)
   end.

(** Generate a enum of valuation from a list of ids.*)
Fixpoint enum_valuation (l : list id) : list valuation :=
  match l with
  | nil => [empty_valuation]
  | x::xs => add_id (enum_valuation xs) x
  end.
             
Module Test_enum_valuation.

 Definition x := (Id "x").
 Definition y := (Id "y").
 Definition z := (Id "z").

(** Get bool values of a list of variables from a valuation. *)
 Fixpoint apply_list  (v : valuation) (l :list id) : list bool:=
   match l with 
   |nil => []
   | x :: xs => (v x) :: (apply_list v xs)
   end.

(** Show values of a list of variables from a list of valuations.*) 
 Fixpoint all_valuations (lv : list valuation) (l: list id) : list (list Datatypes.bool):=
    match lv with
    |nil => []
    |v :: vs =>
     (apply_list v l) :: (all_valuations vs l)
  end.
 
 Eval compute in (all_valuations (add_id [(override (override empty_valuation x true) y false);(override (override empty_valuation x false) y false);(override (override empty_valuation x true) y true);(override (override empty_valuation x false) y true)] z) [x;y;z]).

 Eval compute in (all_valuations (enum_valuation [x;y;z]) [x;y;z]).
End Test_enum_valuation.

(** Try to interpret a formula with a list of valuations, if one of them makes formula true, return it.*)
Fixpoint try_valuation (lv: list valuation) (p : form) : option valuation :=
  match lv with
  | nil => None
  | v::vs => if interp v p then Some v
             else try_valuation vs p
  end.


(** Exercise 2.5*)
(** 
    Find a possible valuation that makes formual true.
    Collect variables, generate all valuations and try them.
**)
Definition find_valuation (p : form) : option valuation :=
  let ids := collect_var p in
  let vals := (enum_valuation ids) in
  try_valuation vals p.

Module Test_find_valuation.
 Definition x := (var (Id "x")).
 Definition y := (var (Id "y")).

 Definition apply_test (ov : option valuation) (i :id) :option bool :=
   match ov with
   |Some v => Some (v i)
   |None => None
   end.

 Fixpoint apply_list  (ov : option valuation) (l :list id) : list (option bool):=
   match l with 
   |nil => []
   | x :: xs => (apply_test ov x) :: (apply_list ov xs)
   end.
 (**A variant that can show values in the found valuation.*)
 Definition find_valuation' (p : form) : list (option bool) :=
   let ids := collect_var p in
   let vals := (enum_valuation ids) in
   apply_list (try_valuation vals p) ids.
 
 Eval compute in (find_valuation' (land (land x (not x)) (boolv true))). 

End Test_find_valuation.
