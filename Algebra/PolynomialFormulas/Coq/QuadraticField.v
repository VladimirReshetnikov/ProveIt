From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The complete quadratic formula over an arbitrary MathComp field.

    The hypotheses [(2 : F) != 0] and [a != 0] state exactly when the
    displayed denominator is invertible.  A square root [s] is supplied
    together with its defining equation; no algebraic-closure or hidden
    square-root-choice assumption is used.  Besides proving that both
    displayed values are roots, we prove the exact factorization and that
    every root is one of those two values. *)
Module PolynomialFormulasQuadraticField.

Import GRing.Theory.
Local Open Scope ring_scope.

Section QuadraticField.

Variable F : fieldType.

Definition linear_value (a b x : F) : F := a * x + b.

Definition linear_solution (a b : F) : F := - b / a.

Lemma linear_solution_correct a b (a_neq0 : a != 0) :
  linear_value a b (linear_solution a b) = 0.
Proof.
rewrite /linear_value /linear_solution [a * _]mulrC divfK //.
exact: addNr.
Qed.

Theorem linear_value_eq_zero_iff a b x (a_neq0 : a != 0) :
  linear_value a b x = 0 <-> x = linear_solution a b.
Proof.
split.
- move=> hzero.
  rewrite /linear_value in hzero.
  have hax : a * x = - b.
    apply: (addrI b).
    by rewrite [b + a * x]addrC hzero subrr.
  apply: (mulfI a_neq0).
  rewrite hax /linear_solution [a * _]mulrC divfK //.
- move=> ->.
  exact: linear_solution_correct a_neq0.
Qed.

Definition quadratic_value (a b c x : F) : F :=
  a * x ^+ 2 + b * x + c.

Definition quadratic_discriminant (a b c : F) : F :=
  b ^+ 2 - 4%:R * a * c.

Definition quadratic_denominator (a : F) : F := 2%:R * a.

Definition quadratic_root_plus (a b s : F) : F :=
  (- b + s) / quadratic_denominator a.

Definition quadratic_root_minus (a b s : F) : F :=
  (- b - s) / quadratic_denominator a.

(** Local bridge from MathComp's packed operations to Stdlib [ring]. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma quadratic_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma quadratic_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma quadratic_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma quadratic_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma quadratic_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma quadratic_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma quadratic_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring quadratic_field_ring : quadratic_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma quadratic_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma quadratic_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
have h2 : (2%:R : F) = 1 + 1 := quadratic_two_natrE.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -h2.
  exact: (@natrD F 2 1).
rewrite -h3.
exact: (@natrD F 3 1).
Qed.

Lemma quadratic_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Ltac finish_quadratic_field_ring :=
  repeat first
    [ rewrite quadratic_two_natrE
    | rewrite quadratic_four_natrE
    | rewrite quadratic_expr2
    | rewrite quadratic_ring_addE
    | rewrite quadratic_ring_mulE
    | rewrite quadratic_ring_subE
    | rewrite quadratic_ring_oppE
    | rewrite quadratic_ring_zeroE
    | rewrite quadratic_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma quadratic_denominator_neq0 a
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0) :
  quadratic_denominator a != 0.
Proof.
rewrite /quadratic_denominator.
exact: mulf_neq0 two_neq0 a_neq0.
Qed.

Lemma quadratic_denominator_mul_root_plus a b s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0) :
  quadratic_denominator a * quadratic_root_plus a b s = - b + s.
Proof.
have hden := quadratic_denominator_neq0 (a := a) two_neq0 a_neq0.
rewrite /quadratic_root_plus [quadratic_denominator a * _]mulrC.
exact: (divfK hden (- b + s)).
Qed.

Lemma quadratic_denominator_mul_root_minus a b s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0) :
  quadratic_denominator a * quadratic_root_minus a b s = - b - s.
Proof.
have hden := quadratic_denominator_neq0 (a := a) two_neq0 a_neq0.
rewrite /quadratic_root_minus [quadratic_denominator a * _]mulrC.
exact: (divfK hden (- b - s)).
Qed.

(** Vieta's sum identity for the two displayed formula values. *)
Lemma quadratic_formula_sum a b s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0) :
  a * (quadratic_root_plus a b s + quadratic_root_minus a b s) = - b.
Proof.
apply: (mulfI two_neq0).
transitivity
  (quadratic_denominator a * quadratic_root_plus a b s +
   quadratic_denominator a * quadratic_root_minus a b s).
- rewrite /quadratic_denominator.
  finish_quadratic_field_ring.
- rewrite (quadratic_denominator_mul_root_plus
      (a := a) b s two_neq0 a_neq0)
    (quadratic_denominator_mul_root_minus
      (a := a) b s two_neq0 a_neq0).
  finish_quadratic_field_ring.
Qed.

(** Vieta's product identity, derived only from the supplied square-root
    equation after clearing the common nonzero denominator. *)
Lemma quadratic_formula_product a b c s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  a * quadratic_root_plus a b s * quadratic_root_minus a b s = c.
Proof.
have hden := quadratic_denominator_neq0 (a := a) two_neq0 a_neq0.
apply: (mulfI (mulf_neq0 hden hden)).
transitivity
  (a *
    (quadratic_denominator a * quadratic_root_plus a b s) *
    (quadratic_denominator a * quadratic_root_minus a b s)).
- finish_quadratic_field_ring.
- rewrite (quadratic_denominator_mul_root_plus
      (a := a) b s two_neq0 a_neq0)
    (quadratic_denominator_mul_root_minus
      (a := a) b s two_neq0 a_neq0).
  transitivity (a * (b ^+ 2 - s ^+ 2)).
  + finish_quadratic_field_ring.
  + rewrite hs /quadratic_discriminant /quadratic_denominator.
    finish_quadratic_field_ring.
Qed.

(** Exact two-linear-factor identity for every input [x]. *)
Theorem quadratic_formula_factorization a b c s x
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  quadratic_value a b c x =
    a * (x - quadratic_root_plus a b s) *
      (x - quadratic_root_minus a b s).
Proof.
have hsum := quadratic_formula_sum
  (a := a) b s two_neq0 a_neq0.
have hprod := quadratic_formula_product
  (a := a) (b := b) (c := c) (s := s) two_neq0 a_neq0 hs.
transitivity
  (a * x ^+ 2 -
    a * (quadratic_root_plus a b s + quadratic_root_minus a b s) * x +
    a * quadratic_root_plus a b s * quadratic_root_minus a b s).
- rewrite /quadratic_value hsum hprod.
  finish_quadratic_field_ring.
- finish_quadratic_field_ring.
Qed.

Theorem quadratic_formula_plus a b c s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  quadratic_value a b c (quadratic_root_plus a b s) = 0.
Proof.
rewrite (quadratic_formula_factorization
  (a := a) (b := b) (c := c) (s := s)
  (quadratic_root_plus a b s) two_neq0 a_neq0 hs).
finish_quadratic_field_ring.
Qed.

Theorem quadratic_formula_minus a b c s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  quadratic_value a b c (quadratic_root_minus a b s) = 0.
Proof.
rewrite (quadratic_formula_factorization
  (a := a) (b := b) (c := c) (s := s)
  (quadratic_root_minus a b s) two_neq0 a_neq0 hs).
finish_quadratic_field_ring.
Qed.

Theorem quadratic_formula_roots a b c s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  quadratic_value a b c (quadratic_root_plus a b s) = 0 /\
  quadratic_value a b c (quadratic_root_minus a b s) = 0.
Proof.
split.
- exact: quadratic_formula_plus two_neq0 a_neq0 hs.
- exact: quadratic_formula_minus two_neq0 a_neq0 hs.
Qed.

(** Exhaustiveness: no other field element can be a root.  This remains
    correct when [s = 0], in which case the two displayed values coincide. *)
Theorem quadratic_value_eq_zero_iff a b c s x
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  quadratic_value a b c x = 0 <->
    x = quadratic_root_plus a b s \/
    x = quadratic_root_minus a b s.
Proof.
rewrite (quadratic_formula_factorization
  (a := a) (b := b) (c := c) (s := s) x
  two_neq0 a_neq0 hs).
split.
- move=> hproduct.
  have hproductb :
      a * (x - quadratic_root_plus a b s) *
        (x - quadratic_root_minus a b s) == 0.
    apply/eqP.
    exact: hproduct.
  move: hproductb.
  rewrite !mulf_eq0 (negPf a_neq0) /= !subr_eq0.
  move/orP=> [/eqP hx | /eqP hx].
  + by left.
  + by right.
- move=> [-> | ->]; finish_quadratic_field_ring.
Qed.

(** The same statement through MathComp's polynomial and [root] APIs. *)
Definition quadratic_polynomial (a b c : F) : {poly F} :=
  a *: 'X^2 + b *: 'X + c%:P.

Lemma quadratic_polynomial_horner a b c x :
  (quadratic_polynomial a b c).[x] = quadratic_value a b c x.
Proof.
by rewrite /quadratic_polynomial /quadratic_value
  !hornerD !hornerZ !hornerXn !hornerX !hornerC.
Qed.

Theorem quadratic_polynomial_factorization_horner a b c s x
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  (quadratic_polynomial a b c).[x] =
    a * (x - quadratic_root_plus a b s) *
      (x - quadratic_root_minus a b s).
Proof.
rewrite quadratic_polynomial_horner.
exact: (quadratic_formula_factorization
  (a := a) (b := b) (c := c) (s := s) x
  two_neq0 a_neq0 hs).
Qed.

Theorem quadratic_polynomial_formula_roots a b c s
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  root (quadratic_polynomial a b c) (quadratic_root_plus a b s) /\
  root (quadratic_polynomial a b c) (quadratic_root_minus a b s).
Proof.
split; apply/rootP; rewrite quadratic_polynomial_horner.
- exact: quadratic_formula_plus two_neq0 a_neq0 hs.
- exact: quadratic_formula_minus two_neq0 a_neq0 hs.
Qed.

Theorem quadratic_polynomial_root_iff a b c s x
    (two_neq0 : (2%:R : F) != 0) (a_neq0 : a != 0)
    (hs : s ^+ 2 = quadratic_discriminant a b c) :
  root (quadratic_polynomial a b c) x <->
    x = quadratic_root_plus a b s \/
    x = quadratic_root_minus a b s.
Proof.
rewrite rootE quadratic_polynomial_horner.
split.
- move/eqP=> hzero.
  exact: (proj1
    (quadratic_value_eq_zero_iff
      (a := a) (b := b) (c := c) (s := s) x
      two_neq0 a_neq0 hs) hzero).
- move=> hroot; apply/eqP.
  exact: (proj2
    (quadratic_value_eq_zero_iff
      (a := a) (b := b) (c := c) (s := s) x
      two_neq0 a_neq0 hs) hroot).
Qed.

Print Assumptions quadratic_formula_factorization.
Print Assumptions quadratic_formula_roots.
Print Assumptions quadratic_value_eq_zero_iff.
Print Assumptions quadratic_polynomial_factorization_horner.
Print Assumptions quadratic_polynomial_root_iff.

End QuadraticField.

End PolynomialFormulasQuadraticField.
