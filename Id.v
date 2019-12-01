From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
Require Export Strings.String.
Require Export Lists.List.
Require Import Morphisms Setoid.


Inductive id : Type :=
| Id (n : string).


(*Check (Id "x").*)

(*Maps.v*)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** Now we need a few basic properties of string equality... *)
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

(** The following useful property follows from an analogous
    lemma about strings: *)

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

(** Similarly: *)

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.



Definition beq_id  (i1 i2:id): bool :=
  match i1 with
  | Id x => match i2 with
            | Id y => eqb_string x y
            end
  end.
(*
Definition eq_id  (i1 i2:id): Prop :=
  if beq_id i1 i2 then True else False.

Theorem beq_id_true_iff : forall x y : id,
    beq_id x y = true <-> x = y.
Proof.
   intros x y.
   unfold beq_id.
   destruct x, y.
     split.
     - intro. 
       rewrite eqb_string_true_iff in H.
       now rewrite H.
   - intro.  rewrite eqb_string_true_iff. inversion H.  reflexivity.
Qed.



Theorem beq_id_false_iff : forall x y : id,
    beq_id x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Lemma eqb_spec i1 i2 : Bool.reflect (i1 = i2) (beq_id i1 i2).
Proof.
  destruct (beq_id i1 i2) eqn:E.
  - apply ReflectT.
    rewrite beq_id_true_iff in E.
    assumption.
  - apply ReflectF.
    rewrite beq_id_false_iff in E.
    assumption.
Qed.

Definition id_eq_dec' : forall a b : id, {eq_id a b} + {~eq_id a b}.
Proof.
  intros.
  unfold eq_id.
  unfold beq_id.
  destruct a, b.
  destruct (eqb_string n n0).
  left. exact I.
  right. unfold not.
  auto.
Defined.

Theorem eq_id_is_eq n m : eq_id n m <-> n = m.
Proof.
  split.
  - intro.
    unfold eq_id in H.
    destruct (beq_id n m) eqn:E.
    rewrite beq_id_true_iff in E.
    assumption.
    contradiction H.
  - intro. unfold eq_id.
    destruct (beq_id n m) eqn:E.
    exact I.
    rewrite beq_id_false_iff in E.
    destruct E.
    assumption.
    Qed.

*)

Lemma id_eq_dec : forall a b : id, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a,b.
  decide equality.
  apply string_dec.
Defined.

(*



Theorem beq_id_refl : forall i : id, true = beq_id i i.
Proof.
  intros.
  unfold  beq_id.
  destruct (id_eq_dec i i) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Lemma id_eq_refl: forall x : id, id_eq x x.
Proof.
  intro.
  unfold id_eq.
  rewrite <- beq_id_refl.
  reflexivity.
Defined.


Theorem beq_id_sym_t : forall i1 i2 : id, true = beq_id i1 i2 -> true = beq_id i2 i1.
Proof.
  intros.
  unfold  beq_id.
  destruct (id_eq_dec i2 i1) as [|Hs].
  - reflexivity.
  - destruct Hs.
    unfold beq_id in H .
    destruct (id_eq_dec i1 i2) in H.
    auto.
    discriminate H.
Qed.

Theorem beq_id_sym_f : forall i1 i2 : id, false = beq_id i1 i2 -> false = beq_id i2 i1.
Proof.
  intros.
  unfold  beq_id.
  destruct (id_eq_dec i2 i1) as [Hs|].
  
  - destruct Hs.
    now rewrite <-beq_id_refl in H.
  - reflexivity.
Qed.

Theorem beq_id_sym : forall i1 i2 : id,  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros.
  destruct (beq_id i1 i2) eqn:H.
  -  apply beq_id_sym_t.
     auto.
  - apply beq_id_sym_f.
    auto.
    Qed.


Lemma id_eq_sym: forall x y : id, id_eq x y -> id_eq y x.
Proof.
  intros.
  unfold id_eq.
  destruct (beq_id y x) eqn: E.
  -  rewrite <-beq_id_true_iff.
     assumption.
  -  rewrite <-beq_id_false_iff.
     assumption.
Defined.

Lemma id_eq_trans: forall x y z : id, id_eq x y -> id_eq y z -> id_eq x z.
Proof.
  intros.
  unfold id_eq.
  destruct (beq_id x z) eqn: E.
  -  rewrite <-beq_id_true_iff.
     assumption.
  -  rewrite <-beq_id_false_iff.
     assumption.
Defined.




Instance id_eq_equiv : (Equivalence id_eq):=
  {
   Equivalence_Reflexive  := id_eq_refl;
   Equivalence_Symmetric := id_eq_sym;
   Equivalence_Transitive  := id_eq_trans 
  }.
 *)
(*TODO need optimize*)

