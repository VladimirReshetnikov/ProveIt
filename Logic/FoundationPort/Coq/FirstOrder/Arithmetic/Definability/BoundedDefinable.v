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
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy Monotone.
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

Definition arithmetic_bounded_compose_one {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : M -> M} {g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function_one Str le f)
    (Hg : arithmetic_bounded_function Str le g) :
    arithmetic_bounded_function Str le (fun v => f (g v)).
Proof.
  apply (arithmetic_bounded_compose Hrefl Htrans Hmon Hf
    (g := fun _ => g)).
  intro i. exact Hg.
Defined.

Definition arithmetic_bounded_compose_two {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : M -> M -> M} {g h : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function_two Str le f)
    (Hg : arithmetic_bounded_function Str le g)
    (Hh : arithmetic_bounded_function Str le h) :
    arithmetic_bounded_function Str le (fun v => f (g v) (h v)).
Proof.
  apply (arithmetic_bounded_compose Hrefl Htrans Hmon Hf
    (g := fin_two g h)).
  intro i. refine (@Fin.caseS' 1 i
    (fun j => arithmetic_bounded_function Str le (fin_two g h j)) Hg _).
  intro j. refine (@Fin.caseS' 0 j
    (fun q => arithmetic_bounded_function Str le (fin_two g h (Fin.FS q)))
    Hh _).
  intros q; inversion q.
Defined.

Definition fin_graph_reindex {k m} (e : Fin.t k -> Fin.t m) :
    Fin.t (S k) -> Fin.t (S m) :=
  fun i => @Fin.caseS' k i (fun _ => Fin.t (S m))
    Fin.F1 (fun j => Fin.FS (e j)).

Lemma fin_graph_reindex_zero : forall k m (e : Fin.t k -> Fin.t m),
  fin_graph_reindex e Fin.F1 = Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_graph_reindex_succ : forall k m (e : Fin.t k -> Fin.t m) i,
  fin_graph_reindex e (Fin.FS i) = Fin.FS (e i).
Proof. reflexivity. Qed.

Record arithmetic_definably_bounded_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (le : M -> M -> Prop) (f : (Fin.t k -> M) -> M) : Type := {
  arithmetic_definably_bounded_bound :
    arithmetic_bounded_function Str le f;
  arithmetic_definably_bounded_definition :
    arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol f
}.

Definition arithmetic_definably_bounded_variable {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (i : Fin.t k) :
    arithmetic_definably_bounded_function Str le (fun v => v i) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_variable Str (le := le) Hrefl i;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_projection (Str := Str) HEq
        arithmetic_sigma_zero_symbol i |}.

Definition arithmetic_definably_bounded_constant {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (c : M) :
    arithmetic_definably_bounded_function Str le
      (fun _ : Fin.t k -> M => c) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_constant Str (le := le) Hrefl c;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_parameter_constant (Str := Str) HEq
        arithmetic_sigma_zero_symbol c |}.

Definition arithmetic_definably_bounded_term {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (t : semiterm oring_language M k) :
    arithmetic_definably_bounded_function Str le
      (fun v => semiterm_val Str v (fun x => x) t) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_term_function Str (le := le) Hrefl t;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_term_graph (Str := Str) HEq
        arithmetic_sigma_zero_symbol t |}.

Definition arithmetic_bounded_of_pointwise_eq {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (Hfg : forall v, f v = g v) : arithmetic_bounded_function Str le g.
Proof.
  refine {| arithmetic_bounded_term := arithmetic_bounded_term Hf |}.
  intro v. rewrite <- Hfg. apply arithmetic_bounded_spec.
Defined.

Definition arithmetic_definably_bounded_of_pointwise_eq {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_definably_bounded_function Str le f)
    (Hfg : forall v, f v = g v) :
    arithmetic_definably_bounded_function Str le g.
Proof.
  destruct Hf as [Hbound Hdef]. constructor.
  - exact (arithmetic_bounded_of_pointwise_eq Hbound Hfg).
  - apply (arithmetic_sorted_definable_of_iff Hdef).
    intro w. rewrite <- (Hfg (fun i => w (Fin.FS i))). reflexivity.
Defined.

Definition arithmetic_definably_bounded_retraction {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_definably_bounded_function Str le f)
    (e : Fin.t k -> Fin.t m) :
    arithmetic_definably_bounded_function Str le
      (fun v : Fin.t m -> M => f (fun i => v (e i))).
Proof.
  destruct Hf as [Hbound Hdef]. constructor.
  - exact (arithmetic_bounded_retraction Hbound e).
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_retraction Hdef (fin_graph_reindex e))).
    intro v. reflexivity.
Defined.
