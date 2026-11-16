import Mathlib

/-!
# Finite algebra for Gauss hypergeometric identities

This companion is an **uncompiled formalization outline**.  It is deliberately
split into (i) definitions and small lemmas with proof terms below and (ii) a
`Planned` namespace whose declarations are axioms specifying the exact theorem
statements to be replaced by proofs.  Consequently this file is not evidence
for the analytic theorems in the paper, even if it elaborates after import-path
adjustments.

The intended eventual use is two-stage:

1. prove the finite statements over `ℚ`/`ℂ` in Mathlib as a development aid;
2. re-express the cleared-denominator statements in ProveIt's embedded iPRA
   calculus `Prf PRAAx`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace HypergeometricFinite

/-- Rising factorial `(a)_n`, with the multiplication order chosen for simple
primitive-recursive equations. -/
def rising {R : Type*} [Semiring R] (a : R) : ℕ → R
  | 0 => 1
  | n + 1 => rising a n * (a + n)

@[simp] theorem rising_zero {R : Type*} [Semiring R] (a : R) : rising a 0 = 1 := rfl

@[simp] theorem rising_succ {R : Type*} [Semiring R] (a : R) (n : ℕ) :
    rising a (n + 1) = rising a n * (a + n) := rfl

/-- Product presentation of the rising factorial. -/
theorem rising_eq_prod_range {R : Type*} [CommSemiring R] (a : R) (n : ℕ) :
    rising a n = ∏ k ∈ range n, (a + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rising_succ, ih]
      simp [prod_range_succ, mul_comm]

/-- Vanishing after a zero factor. -/
theorem rising_eq_zero_of_factor_zero {R : Type*} [CommSemiring R]
    {a : R} {m n : ℕ} (hm : m < n) (hzero : a + m = 0) : rising a n = 0 := by
  rw [rising_eq_prod_range]
  exact Finset.prod_eq_zero (mem_range.mpr hm) hzero

/-- The rational `n`th coefficient of `₂F₁(a,b;c;z)`, without `z^n`. -/
def coeff (a b c : ℚ) (n : ℕ) : ℚ :=
  rising a n * rising b n / (rising c n * n.factorial)

/-- The rational `n`th series term. -/
def term (a b c z : ℚ) (n : ℕ) : ℚ := coeff a b c n * z ^ n

/-- A finite hypergeometric prefix. -/
def prefix (a b c z : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, term a b c z n

@[simp] theorem coeff_zero (a b c : ℚ) : coeff a b c 0 = 1 := by
  simp [coeff, rising]

@[simp] theorem term_zero (a b c z : ℚ) : term a b c z 0 = 1 := by
  simp [term]

@[simp] theorem prefix_zero (a b c z : ℚ) : prefix a b c z 0 = 0 := by
  simp [prefix]

@[simp] theorem prefix_succ (a b c z : ℚ) (N : ℕ) :
    prefix a b c z (N + 1) = prefix a b c z N + term a b c z N := by
  simp [prefix, sum_range_succ]

/-- Coefficient list of a polynomial represented in increasing degree. -/
abbrev PolyCoeffs := List ℚ

/-- Truncated Cauchy product, sufficient for finite formal-power-series checks. -/
def convCoeff (p q : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), p k * q (n - k)

/-- Formal derivative coefficient. -/
def derivCoeff (p : ℕ → ℚ) (n : ℕ) : ℚ := (n + 1) * p (n + 1)

/-- Coefficient form of the Gauss differential operator
`z(1-z)y'' + (c-(a+b+1)z)y' - ab y`. -/
def gaussResidualCoeff (a b c : ℚ) (u : ℕ → ℚ) (n : ℕ) : ℚ :=
  (n + 1) * (c + n) * u (n + 1) - (a + n) * (b + n) * u n

/-- A finite certificate for a branch-free rational identity. -/
structure FiniteIdentityCertificate where
  lhs : ℕ → ℚ
  rhs : ℕ → ℚ
  cutoff : ℕ
  checked : ∀ n < cutoff, lhs n = rhs n

/-- A rational geometric-tail certificate. -/
structure GeometricTailCertificate where
  A r : ℚ
  cutoff : ℕ → ℕ
  A_nonneg : 0 ≤ A
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  tail_bound : ∀ q : ℕ, A * r ^ cutoff q / (1 - r) ≤ (2 : ℚ) ^ (-(q : ℤ))

namespace Planned

/-!
The declarations below are theorem targets.  They are written as `axiom`s so
that no proof hole is disguised by `sorry`.  Each should eventually be
replaced by a theorem and an audited proof.
-/

/-- Exact coefficient ratio after clearing nonzero denominators. -/
axiom coeff_succ_ratio (a b c : ℚ) (n : ℕ)
    (hc : rising c (n + 1) ≠ 0) :
    coeff a b c (n + 1) * ((c + n) * (n + 1)) =
      coeff a b c n * ((a + n) * (b + n))

/-- Coefficients of the hypergeometric series satisfy the Gauss ODE recurrence. -/
axiom gauss_residual_zero (a b c : ℚ) (n : ℕ)
    (hc : rising c (n + 1) ≠ 0) :
    gaussResidualCoeff a b c (coeff a b c) n = 0

/-- Termination when a numerator parameter is a nonpositive integer. -/
axiom coeff_eq_zero_of_neg_nat_left (m n : ℕ) (b c : ℚ)
    (hmn : m < n) : coeff (-(m : ℚ)) b c n = 0

/-- Symmetry of the two numerator parameters. -/
axiom coeff_swap (a b c : ℚ) (n : ℕ) : coeff a b c n = coeff b a c n

/-- Formal differentiation identity. -/
axiom deriv_coeff_identity (a b c : ℚ) (n : ℕ)
    (hc : c ≠ 0) (hden : rising c (n + 1) ≠ 0) :
    derivCoeff (coeff a b c) n = (a * b / c) * coeff (a + 1) (b + 1) (c + 1) n

/-- Euler's transformation as a formal-power-series coefficient identity. -/
axiom euler_transform_coeff (a b c : ℚ) (n : ℕ) :
    coeff a b c n =
      convCoeff (fun k => rising (a + b - c) k / k.factorial)
        (coeff (c - a) (c - b) c) n

/-- First Pfaff transformation as a formal-power-series coefficient identity.
The finite sum is the coefficient of
`(1-z)^(-a) F(a,c-b;c; z/(z-1))`. -/
axiom pfaff_transform_coeff (a b c : ℚ) (N : ℕ) :
    coeff a b c N =
      ∑ j ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ j * coeff a (c - b) c j *
          rising (a + j) (N - j) / (N - j).factorial

/-- Finite Chu--Vandermonde summation. -/
axiom chu_vandermonde (m : ℕ) (b c : ℚ)
    (hden : rising c (m + 1) ≠ 0) :
    prefix (-(m : ℚ)) b c 1 (m + 1) = rising (c - b) m / rising c m

/-- The basic coefficientwise contiguous relation
`θF = a(F(a+1)-F)`. -/
axiom contiguous_a (a b c : ℚ) (n : ℕ) :
    (n : ℚ) * coeff a b c n =
      a * (coeff (a + 1) b c n - coeff a b c n)

/-- Finite J-fraction eliminant: convergents are ratios of contiguous
hypergeometric prefixes.  The exact numerator/denominator recurrence is given
in Section 9 of the report. -/
axiom gauss_finite_continued_fraction
    (a b c z : ℚ) (N : ℕ) : True

/-- Fuss--Catalan coefficient used by the Glasser family. -/
def fussCatalan (k n : ℕ) : ℚ :=
  (((k + 1) * n).factorial : ℚ) /
    ((n.factorial : ℚ) * ((k * n + 1).factorial : ℚ))

/-- Formal algebraic equation for the Fuss--Catalan series, stated
coefficientwise. -/
axiom fuss_catalan_equation (k n : ℕ) : True

/-- Coefficient recurrence for the cubic radical branch
`Y + x^2 Y^3 = 1`. -/
axiom cubic_radical_recurrence (n : ℕ) : True

end Planned

end HypergeometricFinite
