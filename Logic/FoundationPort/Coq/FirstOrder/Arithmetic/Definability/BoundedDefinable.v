(**
  Term-bounded functions and their closure laws.

  This begins the port of
  [Foundation/FirstOrder/Arithmetic/Definability/BoundedDefinable.lean].
  The comparison relation and structure are explicit, and a bound carries its
  witnessing term in [Type].  Composition therefore avoids the source's
  noncomputable extraction of a finite family of existential witnesses.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Monotone.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record arithmetic_bounded_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (le : M -> M -> Prop) (f : (Fin.t k -> M) -> M) : Type := {
  arithmetic_bounded_term : semiterm oring_language M k;
  arithmetic_bounded_spec : forall v,
    le (f v) (semiterm_val Str v (fun x => x) arithmetic_bounded_term)
}.

Arguments arithmetic_bounded_term {M k Str le f} _.
Arguments arithmetic_bounded_spec {M k Str le f} _ _.

Definition arithmetic_bounded_function_one {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 1 -> M => f (v Fin.F1)).

Definition arithmetic_bounded_function_two {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 2 -> M => f (v Fin.F1) (v (Fin.FS Fin.F1))).

Definition arithmetic_bounded_function_three {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M -> M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 3 -> M => f (v Fin.F1) (v (Fin.FS Fin.F1))
      (v (Fin.FS (Fin.FS Fin.F1)))).

Definition arithmetic_bounded_variable {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (i : Fin.t k) :
    arithmetic_bounded_function Str le (fun v => v i).
Proof.
  refine {| arithmetic_bounded_term := Semiterm_bvar i |}.
  intro v. apply Hrefl.
Defined.

Definition arithmetic_bounded_constant {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (c : M) :
    arithmetic_bounded_function Str le (fun _ : Fin.t k -> M => c).
Proof.
  refine {| arithmetic_bounded_term := Semiterm_fvar c |}.
  intro v. apply Hrefl.
Defined.

Definition arithmetic_bounded_term_function {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (t : semiterm oring_language M k) :
    arithmetic_bounded_function Str le
      (fun v => semiterm_val Str v (fun x => x) t).
Proof.
  refine {| arithmetic_bounded_term := t |}.
  intro v. apply Hrefl.
Defined.

(** Exact bound-term substitution is the common core of retraction and
    composition. *)
Definition arithmetic_bounded_substitute_bound {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (t : Fin.t k -> semiterm oring_language M m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M =>
        f (fun i => semiterm_val Str v (fun x => x) (t i))).
Proof.
  refine {| arithmetic_bounded_term :=
    rew_apply (rew_subst t) (arithmetic_bounded_term Hf) |}.
  intro v. rewrite semiterm_val_substitute.
  apply arithmetic_bounded_spec.
Defined.

Definition arithmetic_bounded_retraction {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f) (e : Fin.t k -> Fin.t m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M => f (fun i => v (e i))).
Proof.
  exact (arithmetic_bounded_substitute_bound Hf
    (fun i => @Semiterm_bvar oring_language M m (e i))).
Defined.

Definition arithmetic_bounded_term_retraction {M : Type} {k m}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (t : semiterm oring_language M k)
    (e : Fin.t k -> Fin.t m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M =>
        semiterm_val Str (fun i => v (e i)) (fun x => x) t) :=
  arithmetic_bounded_retraction
    (arithmetic_bounded_term_function Str (le := le) Hrefl t) e.

(** Composition only needs reflexivity and transitivity of the comparison and
    pointwise monotonicity of interpreted function symbols. *)
Definition arithmetic_bounded_compose {M : Type} {k l}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : (Fin.t l -> M) -> M} {g : Fin.t l -> (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (Hg : forall i, arithmetic_bounded_function Str le (g i)) :
    arithmetic_bounded_function Str le (fun v => f (fun i => g i v)).
Proof.
  refine {| arithmetic_bounded_term :=
    rew_apply (rew_subst (fun i => arithmetic_bounded_term (Hg i)))
      (arithmetic_bounded_term Hf) |}.
  intro v. eapply Htrans.
  - apply (arithmetic_bounded_spec Hf (fun i => g i v)).
  - rewrite semiterm_val_substitute.
    apply (semiterm_val_monotone_bound Hmon Hrefl).
    intro i. apply (arithmetic_bounded_spec (Hg i) v).
Defined.

Record arithmetic_definably_bounded_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (le : M -> M -> Prop) (f : (Fin.t k -> M) -> M) : Type := {
  arithmetic_definably_bounded_bound :
    arithmetic_bounded_function Str le f;
  arithmetic_definably_bounded_definition :
    arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol f
}.
