import FabiusFunction.FabiusInverse
import FabiusFunction.DyadicSpecializations
import Mathlib.Analysis.Real.Sqrt

/-!
# The inverse Fabius function at the quarter anchor

The inverse-frontier report singles out the dyadic anchor `x = 1 / 4`.  Its
exact bounded Fabius value is `5 / 72`, and the local finite-prefix equation
predicted by the reciprocal-sinc calculation is the quadratic

`z + 4 z^2 = (4 / 9) Q`.

This file records the part of that calculation which is already completely
algebraic, while keeping the still-analytic spline input honest and explicit.

* `fabiusReal_quarter` and `fabiusInv_five_div_seventy_two` give the exact
  value and inverse value for every bounded solution of the Fabius equations.
  Reflection supplies the companion three-quarter identities.
* `quarterInverseGerm` is the nonnegative square-root branch of the local
  quadratic.  Its equation, sign, sharp elementary upper bound, both algebraic
  roots, and uniqueness on the increasing side of the parabola are proved.
* `IsQuarterLocalPolynomial` isolates exactly the analytic premise needed
  from a finite spline.  Once a function has the report's local polynomial,
  the radical is its unique quarter-level displacement in that local branch.
* `quarterPrefixDisplacement` specializes the germ to `Q = 4^-n`.  Its
  displacement automatically lies in the full plateau radius `2^-n`, so a
  local left inverse gives the report's finite-depth quantile formula without
  any asymptotic argument.

There is deliberately no assertion here that `fabiusUniformSpline n` has the
required local polynomial.  That is the remaining analytic/Thue--Morse
plateau theorem; `IsQuarterLocalPolynomial` is designed to be discharged by
that theorem once it is available.

The companion module `QuarterCatalanGerm` packages the report's Catalan
coefficients as the unique zero-constant formal-power-series solution of the
same quadratic, while deliberately leaving real-series convergence separate.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-! ## The exact limiting quarter and three-quarter anchors -/

/-- Every bounded Fabius function takes the exact value `5 / 72` at `1 / 4`.

This is the first nontrivial inverse-dyadic value, extracted from the general
exact evaluator `fabiusAtInverseTwoPow_cast`. -/
theorem fabiusReal_quarter (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (1 / 4) = 5 / 72 :=
  fabiusReal_one_quarter F hF

/-- The exact quarter quantile of every bounded Fabius function:
`F^{-1}(5 / 72) = 1 / 4`. -/
theorem fabiusInv_five_div_seventy_two (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF (5 / 72) = 1 / 4 := by
  rw [← fabiusReal_quarter F hF]
  exact fabiusInv_fabiusReal F hF (by norm_num)

/-- Reflection of the quarter value: `F(3 / 4) = 67 / 72`. -/
theorem fabiusReal_three_quarters (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (3 / 4) = 67 / 72 := by
  have h := hF.symmetry_all ((1 : ℝ) / 4)
  rw [fabiusReal_quarter F hF] at h
  norm_num at h ⊢
  exact h

/-- The reflected exact quantile: `F^{-1}(67 / 72) = 3 / 4`. -/
theorem fabiusInv_sixty_seven_div_seventy_two
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusInv F hF (67 / 72) = 3 / 4 := by
  rw [← fabiusReal_three_quarters F hF]
  exact fabiusInv_fabiusReal F hF (by norm_num)

/-! ## The exact algebraic inverse germ -/

/-- The small real branch of
`z + 4 z^2 = (4 / 9) Q`, normalized by `quarterInverseGerm 0 = 0`.

For the order-`n` finite Fabius spline the frontier report takes `Q = 4^-n`.
-/
def quarterInverseGerm (Q : ℝ) : ℝ :=
  (Real.sqrt (1 + (64 / 9) * Q) - 1) / 8

/-- The exact quarter inverse germ vanishes at the unperturbed parameter. -/
@[simp]
theorem quarterInverseGerm_zero : quarterInverseGerm 0 = 0 := by
  norm_num [quarterInverseGerm]

/-- The square-root branch is nonnegative on the natural parameter ray. -/
theorem quarterInverseGerm_nonneg {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ quarterInverseGerm Q := by
  have hrad : 0 ≤ 1 + (64 / 9 : ℝ) * Q := by positivity
  have hsquare := Real.sq_sqrt hrad
  have hsqrt := Real.sqrt_nonneg (1 + (64 / 9 : ℝ) * Q)
  rw [quarterInverseGerm]
  nlinarith

/-- The exact quadratic equation defining the quarter inverse germ. -/
theorem quarterInverseGerm_equation {Q : ℝ} (hQ : 0 ≤ Q) :
    quarterInverseGerm Q + 4 * quarterInverseGerm Q ^ 2 = (4 / 9) * Q := by
  have hrad : 0 ≤ 1 + (64 / 9 : ℝ) * Q := by positivity
  have hsquare := Real.sq_sqrt hrad
  rw [quarterInverseGerm]
  nlinarith

/-- Positive parameters give a strictly positive displacement. -/
theorem quarterInverseGerm_pos {Q : ℝ} (hQ : 0 < Q) :
    0 < quarterInverseGerm Q := by
  have hnonneg := quarterInverseGerm_nonneg hQ.le
  have heq := quarterInverseGerm_equation hQ.le
  by_contra h
  have hz : quarterInverseGerm Q = 0 := le_antisymm (le_of_not_gt h) hnonneg
  rw [hz] at heq
  nlinarith

/-- Dropping the nonnegative quadratic term gives the elementary sharp-at-zero
bound `Delta(Q) ≤ (4 / 9) Q`. -/
theorem quarterInverseGerm_le_four_div_nine_mul {Q : ℝ} (hQ : 0 ≤ Q) :
    quarterInverseGerm Q ≤ (4 / 9) * Q := by
  have hnonneg := quarterInverseGerm_nonneg hQ
  have heq := quarterInverseGerm_equation hQ
  nlinarith [sq_nonneg (quarterInverseGerm Q)]

/-- The quadratic `z ↦ z + 4 z^2` is injective on the whole increasing
branch `[-1/8, ∞)`.  This version is independent of the square-root formula
and is useful for higher-level local-polynomial arguments. -/
theorem quarterQuadratic_injOn_vertex {z w c : ℝ}
    (hz : -1 / 8 ≤ z) (hw : -1 / 8 ≤ w)
    (hzEq : z + 4 * z ^ 2 = c) (hwEq : w + 4 * w ^ 2 = c) :
    z = w := by
  have hfactor : (z - w) * (1 + 4 * (z + w)) = 0 := by
    nlinarith [hzEq, hwEq]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hzVertex : z = -1 / 8 := by nlinarith
    have hwVertex : w = -1 / 8 := by nlinarith
    linarith

/-- Complete classification of the two algebraic roots.  The first disjunct
is the small/nonnegative branch; the other root lies at most `-1/4`. -/
theorem quarterQuadratic_eq_iff {Q z : ℝ} (hQ : 0 ≤ Q) :
    z + 4 * z ^ 2 = (4 / 9) * Q ↔
      z = quarterInverseGerm Q ∨ z = -1 / 4 - quarterInverseGerm Q := by
  have hgerm := quarterInverseGerm_equation hQ
  constructor
  · intro hz
    have hfactor :
        (z - quarterInverseGerm Q) *
          (1 + 4 * (z + quarterInverseGerm Q)) = 0 := by
      nlinarith [hz, hgerm]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · exact hgerm
    · nlinarith [hgerm]

/-- On the increasing side of the parabola, the quadratic equation selects
the square-root germ uniquely. -/
theorem eq_quarterInverseGerm_of_quadratic {Q z : ℝ}
    (hQ : 0 ≤ Q) (hz : -1 / 8 ≤ z)
    (heq : z + 4 * z ^ 2 = (4 / 9) * Q) :
    z = quarterInverseGerm Q := by
  exact quarterQuadratic_injOn_vertex hz
    (by linarith [quarterInverseGerm_nonneg hQ]) heq
    (quarterInverseGerm_equation hQ)

/-! ## The precise finite-spline premise and its consequences -/

/-- `P` has the quarter-anchor local polynomial predicted by the
reciprocal-sinc calculation, on nonnegative displacements up to `radius`.

This predicate is intentionally local.  It contains no assertion that `P` is
a Fabius spline, is monotone, or possesses an inverse; those independent
facts can be supplied only where they are actually available. -/
def IsQuarterLocalPolynomial (P : ℝ → ℝ) (Q radius : ℝ) : Prop :=
  ∀ z ∈ Icc (0 : ℝ) radius,
    P (1 / 4 + z) = 5 / 72 + z + 4 * z ^ 2 - (4 / 9) * Q

namespace IsQuarterLocalPolynomial

/-- Once the square-root displacement lies inside the local interval, the
local polynomial takes the exact quarter output `5 / 72` there. -/
theorem value_at_quarterInverseGerm {P : ℝ → ℝ} {Q radius : ℝ}
    (hlocal : IsQuarterLocalPolynomial P Q radius)
    (hQ : 0 ≤ Q) (hradius : quarterInverseGerm Q ≤ radius) :
    P (1 / 4 + quarterInverseGerm Q) = 5 / 72 := by
  rw [hlocal _ ⟨quarterInverseGerm_nonneg hQ, hradius⟩]
  nlinarith [quarterInverseGerm_equation hQ]

/-- Conversely, every point of the local nonnegative branch which maps to
`5 / 72` is exactly the square-root displacement. -/
theorem eq_quarterInverseGerm_of_value_eq {P : ℝ → ℝ} {Q radius z : ℝ}
    (hlocal : IsQuarterLocalPolynomial P Q radius)
    (hQ : 0 ≤ Q) (hz : z ∈ Icc (0 : ℝ) radius)
    (hvalue : P (1 / 4 + z) = 5 / 72) :
    z = quarterInverseGerm Q := by
  have hformula := hlocal z hz
  rw [hvalue] at hformula
  apply eq_quarterInverseGerm_of_quadratic hQ (by linarith [hz.1])
  nlinarith

/-- Exact uniqueness statement for the quarter level inside the local
nonnegative branch. -/
theorem value_eq_five_div_seventy_two_iff
    {P : ℝ → ℝ} {Q radius z : ℝ}
    (hlocal : IsQuarterLocalPolynomial P Q radius)
    (hQ : 0 ≤ Q) (hradius : quarterInverseGerm Q ≤ radius)
    (hz : z ∈ Icc (0 : ℝ) radius) :
    P (1 / 4 + z) = 5 / 72 ↔ z = quarterInverseGerm Q := by
  constructor
  · exact eq_quarterInverseGerm_of_value_eq hlocal hQ hz
  · rintro rfl
    exact value_at_quarterInverseGerm hlocal hQ hradius

end IsQuarterLocalPolynomial

/-! ## Geometric finite-depth specialization -/

/-- The report's exact order-`n` quarter displacement, with `Q = 4^-n`. -/
def quarterPrefixDisplacement (n : ℕ) : ℝ :=
  quarterInverseGerm (((4 : ℝ) ^ n)⁻¹)

/-- Closed radical form of the finite-depth displacement. -/
theorem quarterPrefixDisplacement_eq (n : ℕ) :
    quarterPrefixDisplacement n =
      (Real.sqrt (1 + (64 / 9) * ((4 : ℝ) ^ n)⁻¹) - 1) / 8 := rfl

/-- Every finite-depth quarter displacement is strictly positive. -/
theorem quarterPrefixDisplacement_pos (n : ℕ) :
    0 < quarterPrefixDisplacement n := by
  exact quarterInverseGerm_pos (by positivity)

/-- The finite-depth displacement satisfies its exact quadratic equation. -/
theorem quarterPrefixDisplacement_equation (n : ℕ) :
    quarterPrefixDisplacement n + 4 * quarterPrefixDisplacement n ^ 2 =
      (4 / 9) * ((4 : ℝ) ^ n)⁻¹ := by
  exact quarterInverseGerm_equation (by positivity)

/-- The algebraic root always lies inside the report's local plateau radius
`2^-n`.  Thus no additional large-`n` argument is needed at the quarter
anchor once the local polynomial itself has been established. -/
theorem quarterPrefixDisplacement_le_inv_two_pow (n : ℕ) :
    quarterPrefixDisplacement n ≤ ((2 : ℝ) ^ n)⁻¹ := by
  refine (quarterInverseGerm_le_four_div_nine_mul (Q := ((4 : ℝ) ^ n)⁻¹)
    (by positivity)).trans ?_
  calc
    (4 / 9 : ℝ) * ((4 : ℝ) ^ n)⁻¹ =
        (4 / 9 : ℝ) / (4 : ℝ) ^ n :=
      (div_eq_mul_inv (4 / 9 : ℝ) ((4 : ℝ) ^ n)).symm
    _ ≤ 1 / (2 : ℝ) ^ n := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hbase : (4 / 9 : ℝ) ≤ (2 : ℝ) ^ n :=
        (by norm_num : (4 / 9 : ℝ) ≤ 1).trans
          (one_le_pow₀ (by norm_num))
      have hpow : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
        calc
          (4 : ℝ) ^ n = ((2 : ℝ) * 2) ^ n := by norm_num
          _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [mul_pow]
      rw [one_mul, hpow]
      exact mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = ((2 : ℝ) ^ n)⁻¹ := one_div _

/-- The exact quarter value of any finite approximant satisfying the report's
local polynomial on the natural radius.  This is the algebraic half of the
finite-prefix theorem. -/
theorem quarterPrefix_value_of_localPolynomial {P : ℝ → ℝ} (n : ℕ)
    (hlocal : IsQuarterLocalPolynomial P (((4 : ℝ) ^ n)⁻¹)
      (((2 : ℝ) ^ n)⁻¹)) :
    P (1 / 4 + quarterPrefixDisplacement n) = 5 / 72 := by
  exact hlocal.value_at_quarterInverseGerm (by positivity)
    (quarterPrefixDisplacement_le_inv_two_pow n)

/-- Exact finite-depth quantile transfer.  If `G` is a left inverse of `P` on
the quarter plateau and `P` has the required local polynomial there, then
`G(5/72)` is the report's radical, with no limiting argument.

The two hypotheses deliberately separate the analytic work: `hlocal` is the
Thue--Morse plateau/local-polynomial theorem, while `hleft` is local inverse
uniqueness (typically supplied by monotonicity). -/
theorem quarterPrefix_quantile_of_localPolynomial
    {P G : ℝ → ℝ} (n : ℕ)
    (hlocal : IsQuarterLocalPolynomial P (((4 : ℝ) ^ n)⁻¹)
      (((2 : ℝ) ^ n)⁻¹))
    (hleft : ∀ x ∈ Icc (1 / 4 : ℝ) (1 / 4 + ((2 : ℝ) ^ n)⁻¹),
      G (P x) = x) :
    G (5 / 72) =
      1 / 4 +
        (Real.sqrt (1 + (64 / 9) * ((4 : ℝ) ^ n)⁻¹) - 1) / 8 := by
  have hvalue := quarterPrefix_value_of_localPolynomial n hlocal
  have hnonneg := (quarterPrefixDisplacement_pos n).le
  have hle := quarterPrefixDisplacement_le_inv_two_pow n
  calc
    G (5 / 72) = G (P (1 / 4 + quarterPrefixDisplacement n)) := by rw [hvalue]
    _ = 1 / 4 + quarterPrefixDisplacement n :=
      hleft _ ⟨by linarith, by linarith⟩
    _ = _ := by rw [quarterPrefixDisplacement_eq]

end

end Fabius
