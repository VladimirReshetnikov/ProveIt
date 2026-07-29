From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

(** Abel--Ruffini in the explicit radical-expression language formalized by
    the Mathematical Components Abel development.  An [algterm rat] is built
    from rational constants, zero, one, roots of unity, addition,
    multiplication, negation, inversion, natural powers, and radicals.
    Thus [radical_formula_solves p] says that every complex root of [p] has an
    expression using precisely those operations. *)

Module LeanProofs.
Module PolynomialFormulasAbelRuffini.

Definition radical_formula_solves (p : {poly rat}) : Prop :=
  {in root (map_poly ratrC p), forall x,
    exists f : algterm rat, algT_eval ratrC f = x}.

(** This is intentionally a nonuniform overapproximation of a formula in the
    coefficients: it permits a different term for every polynomial and every
    root, and each term may use arbitrary rational constants.  Impossibility
    for this larger class therefore implies impossibility for any single
    coefficient-wise radical formula. *)

Lemma radical_formula_solvesP (p : {poly rat}) (p_neq0 : p != 0) :
  solvable_by_radical_poly p <-> radical_formula_solves p.
Proof. exact: solvable_formula p_neq0. Qed.

(** The explicit irreducible quintic used by the Abel development. *)
Definition quintic_counterexample : {poly rat} := poly_example.

Lemma size_quintic_counterexample : size quintic_counterexample = 6%N.
Proof. exact: size_poly_example. Qed.

Lemma quintic_counterexample_neq0 : quintic_counterexample != 0.
Proof. exact: poly_example_neq0. Qed.

Lemma monic_quintic_counterexample : quintic_counterexample \is monic.
Proof. exact: poly_example_monic. Qed.

Theorem quintic_not_solvable_by_radicals :
  ~ solvable_by_radical_poly quintic_counterexample.
Proof. exact: example_not_solvable_by_radicals. Qed.

Theorem quintic_no_radical_formula :
  ~ radical_formula_solves quintic_counterexample.
Proof.
move=> formula.
apply: quintic_not_solvable_by_radicals.
exact: (radical_formula_solvesP quintic_counterexample_neq0).2 formula.
Qed.

(** Multiplication by a power of [X] raises the degree while retaining every
    root of the quintic.  For [n >= 5], this polynomial has degree exactly
    [n]. *)
Definition padded_counterexample (n : nat) : {poly rat} :=
  quintic_counterexample * 'X^(n - 5).

Lemma size_padded_counterexample n : (5 <= n)%N ->
  size (padded_counterexample n) = n.+1.
Proof.
move=> n_ge5.
rewrite /padded_counterexample
        (size_mulXn _ quintic_counterexample_neq0).
by rewrite size_quintic_counterexample addnS (subnK n_ge5).
Qed.

Lemma padded_counterexample_neq0 n : (5 <= n)%N ->
  padded_counterexample n != 0.
Proof.
move=> n_ge5.
by rewrite -size_poly_eq0 (size_padded_counterexample n_ge5).
Qed.

Lemma monic_padded_counterexample n : padded_counterexample n \is monic.
Proof.
by rewrite /padded_counterexample
           (monicMl _ monic_quintic_counterexample) monicXn.
Qed.

Lemma padded_contains_quintic_roots n x :
  x \in root (map_poly ratrC quintic_counterexample) ->
  x \in root (map_poly ratrC (padded_counterexample n)).
Proof.
move/rootP=> quintic_root.
apply/rootP.
by rewrite /padded_counterexample rmorphM hornerM quintic_root mul0r.
Qed.

Theorem padded_no_radical_formula n :
  ~ radical_formula_solves (padded_counterexample n).
Proof.
move=> formula.
apply: quintic_no_radical_formula.
move=> x quintic_root.
exact: formula x (padded_contains_quintic_roots n quintic_root).
Qed.

Theorem padded_not_solvable_by_radicals n (n_ge5 : (5 <= n)%N) :
  ~ solvable_by_radical_poly (padded_counterexample n).
Proof.
move=> solvable.
apply: (@padded_no_radical_formula n).
exact: (radical_formula_solvesP
          (padded_counterexample_neq0 n_ge5)).1 solvable.
Qed.

(** For every degree greater than four there is a rational polynomial of that
    exact degree whose roots cannot all be expressed by algebraic operations
    and radicals. *)
Theorem degree_gt_four_counterexample n (n_gt4 : (4 < n)%N) :
  exists p : {poly rat},
    size p = n.+1 /\ p \is monic /\ ~ radical_formula_solves p.
Proof.
exists (padded_counterexample n); split.
- exact: size_padded_counterexample n_gt4.
- split.
  + exact: @monic_padded_counterexample n.
  + exact: @padded_no_radical_formula n.
Qed.

Definition radical_formula_solves_degree (n : nat) : Prop :=
  forall p : {poly rat},
    size p = n.+1 -> p \is monic -> radical_formula_solves p.

Definition solvable_by_radicals_degree (n : nat) : Prop :=
  forall p : {poly rat},
    size p = n.+1 -> p \is monic -> solvable_by_radical_poly p.

Theorem not_every_degree_gt_four_solvable_by_radicals
    n (n_gt4 : (4 < n)%N) :
  ~ solvable_by_radicals_degree n.
Proof.
move=> solves_degree.
apply: (@padded_not_solvable_by_radicals n n_gt4).
exact: solves_degree (padded_counterexample n)
          (size_padded_counterexample n_gt4)
          (@monic_padded_counterexample n).
Qed.

Theorem no_radical_formula_degree_gt_four n (n_gt4 : (4 < n)%N) :
  ~ radical_formula_solves_degree n.
Proof.
move=> solves_degree.
have [p [p_degree [monic_p no_formula]]] :=
  degree_gt_four_counterexample n_gt4.
exact: no_formula (solves_degree p p_degree monic_p).
Qed.

End PolynomialFormulasAbelRuffini.
End LeanProofs.
