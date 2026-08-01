(**
  Monotonicity of first-order term evaluation.

  This ports [Foundation/FirstOrder/Arithmetic/Basic/Monotone.lean].  The Coq
  statement is strictly more general: the comparison relation is explicit and
  need not be a global order or satisfy any order laws.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record first_order_structure_monotone
    (L : language) (M : Type) (le : M -> M -> Prop)
    (S : first_order_structure L M) : Prop := {
  structure_func_monotone : forall k (f : language_func L k)
      (v w : Fin.t k -> M),
    (forall i, le (v i) (w i)) ->
    le (structure_func S f v) (structure_func S f w)
}.

Theorem semiterm_val_monotone : forall
    (L : language) (M X : Type) (n : nat)
    (le : M -> M -> Prop) (S : first_order_structure L M),
  first_order_structure_monotone le S ->
  forall (t : semiterm L X n)
         (bound_left bound_right : Fin.t n -> M)
         (free_left free_right : X -> M),
    (forall i, le (bound_left i) (bound_right i)) ->
    (forall x, le (free_left x) (free_right x)) ->
    le (semiterm_val S bound_left free_left t)
       (semiterm_val S bound_right free_right t).
Proof.
  intros L M X n le S Hmon t.
  induction t as [i | x | k f v IH];
    intros bound_left bound_right free_left free_right Hbound Hfree;
    cbn [semiterm_val].
  - apply Hbound.
  - apply Hfree.
  - apply (structure_func_monotone Hmon). intro i.
    apply IH; assumption.
Qed.

Corollary semiterm_val_monotone_free : forall
    (L : language) (M X : Type) (n : nat)
    (le : M -> M -> Prop) (S : first_order_structure L M),
  first_order_structure_monotone le S ->
  (forall a, le a a) ->
  forall (t : semiterm L X n) (bound : Fin.t n -> M)
         (free_left free_right : X -> M),
    (forall x, le (free_left x) (free_right x)) ->
    le (semiterm_val S bound free_left t)
       (semiterm_val S bound free_right t).
Proof.
  intros L M X n le S Hmon Hrefl t bound free_left free_right Hfree.
  apply (semiterm_val_monotone Hmon); auto.
Qed.

Corollary semiterm_val_monotone_bound : forall
    (L : language) (M X : Type) (n : nat)
    (le : M -> M -> Prop) (S : first_order_structure L M),
  first_order_structure_monotone le S ->
  (forall a, le a a) ->
  forall (t : semiterm L X n)
         (bound_left bound_right : Fin.t n -> M) (free : X -> M),
    (forall i, le (bound_left i) (bound_right i)) ->
    le (semiterm_val S bound_left free t)
       (semiterm_val S bound_right free t).
Proof.
  intros L M X n le S Hmon Hrefl t bound_left bound_right free Hbound.
  apply (semiterm_val_monotone Hmon); auto.
Qed.
