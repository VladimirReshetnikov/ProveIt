import IntegerPoints.IwaniecMozzochiSection13PairCount
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# The finite Hölder step in Iwaniec--Mozzochi Section 13

This file isolates the unconditional first step in the estimate of `bigB`.
The form `bigB` is a scalar multiple of a finite sum of norms over the
endpoint-safe numerator and denominator ranges.  Finite Cauchy--Schwarz gives
the fourth-power bound in terms of the corresponding second moment.

No large-sieve estimate is asserted here.  The most general theorem retains
the exact cardinality of the coprime `(a,c)` index set.  On `0 ≤ A` and
`1 ≤ C`, its cardinality is at most `(2A)(2C) = 4AC`, which yields the explicit
coefficient `16 G^4 A^2 C^(-2)` appearing in the paper-shaped corollary.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## The exact index set and second moment -/

/-- The exact `(a,c)` index set in `bigB`: the endpoint-safe numerator range
`A / 4 ≤ a < 2A`, the half-open denominator range `C ≤ c < 2C`, and the
coprimality condition. -/
noncomputable def section13BigBIndexSet (A C : ℝ) : Finset (ℕ × ℕ) :=
  (fareyMajorantNumerators A ×ˢ fareyDenominators C).filter
    fun q : ℕ × ℕ => Nat.Coprime q.1 q.2

/-- The nonnegative summand of `bigB` attached to one pair `(a,c)`. -/
noncomputable def section13BigBSummand
    (x K L t₁ t₂ : ℝ) (q : ℕ × ℕ) : ℝ :=
  ‖imBilinearForm
      (xCoeff x q.1 q.2 0) (xCoeff x q.1 q.2 1)
      (xCoeff x q.1 q.2 2) (xCoeff x q.1 q.2 3)
      t₁ t₂ K L‖

/-- The exact second moment over the same endpoint-safe coprime `(a,c)` index
set as `bigB`.  This is the finite sum that is subsequently estimated by the
double large sieve; no such estimate is part of this definition. -/
noncomputable def section13BigBSecondMoment
    (x A C K L t₁ t₂ : ℝ) : ℝ :=
  ∑ q ∈ section13BigBIndexSet A C,
    section13BigBSummand x K L t₁ t₂ q ^ 2

/-- A sum over the flattened coprime pair set is exactly the nested sum used
in the definition of `bigB`. -/
private theorem section13_sum_indexSet_eq_nested
    (A C : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ section13BigBIndexSet A C, f q) =
      ∑ a ∈ fareyMajorantNumerators A,
        ∑ c ∈ (fareyDenominators C).filter (fun c => Nat.Coprime a c),
          f (a, c) := by
  classical
  simp only [section13BigBIndexSet, Finset.sum_filter, Finset.sum_product]

/-- `bigB` written as a scalar times one sum over its exact pair index set. -/
theorem section13_bigB_eq_indexSum
    (x G A C K L t₁ t₂ : ℝ) :
    bigB x G A C K L t₁ t₂ =
      G / C * ∑ q ∈ section13BigBIndexSet A C,
        section13BigBSummand x K L t₁ t₂ q := by
  unfold bigB
  rw [section13_sum_indexSet_eq_nested]
  rfl

/-- The exact second moment is nonnegative. -/
theorem section13BigBSecondMoment_nonneg
    (x A C K L t₁ t₂ : ℝ) :
    0 ≤ section13BigBSecondMoment x A C K L t₁ t₂ := by
  unfold section13BigBSecondMoment
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Finite Cauchy--Schwarz -/

/-- The unconditional finite Cauchy/Hölder step with the exact cardinality of
the `(a,c)` range.  It is valid for arbitrary real scale parameters, including
empty ranges; no positivity or analytic-spacing hypothesis is required. -/
theorem section13_bigB_fourth_le_indexCard_sq_mul_secondMoment_sq
    (x G A C K L t₁ t₂ : ℝ) :
    bigB x G A C K L t₁ t₂ ^ 4 ≤
      (G / C) ^ 4 * ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
        section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
  classical
  have hcauchy :
      (∑ q ∈ section13BigBIndexSet A C,
          section13BigBSummand x K L t₁ t₂ q) ^ 2 ≤
        ((section13BigBIndexSet A C).card : ℝ) *
          ∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  have hfourth :
      (∑ q ∈ section13BigBIndexSet A C,
          section13BigBSummand x K L t₁ t₂ q) ^ 4 ≤
        ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q ^ 2) ^ 2 := by
    calc
      (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q) ^ 4 =
          ((∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q) ^ 2) ^ 2 := by ring
      _ ≤ (((section13BigBIndexSet A C).card : ℝ) *
          ∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q ^ 2) ^ 2 :=
        pow_le_pow_left₀
          (sq_nonneg (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q)) hcauchy 2
      _ = ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q ^ 2) ^ 2 := by ring
  calc
    bigB x G A C K L t₁ t₂ ^ 4 =
        (G / C) ^ 4 *
          (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q) ^ 4 := by
      rw [section13_bigB_eq_indexSum, mul_pow]
    _ ≤ (G / C) ^ 4 * ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          (∑ q ∈ section13BigBIndexSet A C,
            section13BigBSummand x K L t₁ t₂ q ^ 2) ^ 2 := by
      have hfactor : 0 ≤ (G / C) ^ 4 := by
        nlinarith [sq_nonneg ((G / C) ^ 2)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hfourth hfactor
    _ = (G / C) ^ 4 * ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
      rfl

/-! ## An explicit range-cardinality factor -/

/-- The half-open denominator interval `[C,2C)` contains at most `2C`
natural numbers when `C ≥ 1`.  The factor two, rather than one, is necessary
for a uniform real-endpoint statement. -/
theorem section13_fareyDenominators_card_le_two_mul {C : ℝ}
    (hC : 1 ≤ C) :
    ((fareyDenominators C).card : ℝ) ≤ 2 * C := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hceilOrder : ⌈C⌉₊ ≤ ⌈2 * C⌉₊ :=
    Nat.ceil_mono (by linarith)
  have hceilUpper : (⌈2 * C⌉₊ : ℝ) < 2 * C + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceilLower : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  unfold fareyDenominators
  rw [Nat.card_Ico, Nat.cast_sub hceilOrder]
  linarith

/-- On `0 ≤ A` and `1 ≤ C`, the exact coprime pair index set has cardinality
at most `(2A)(2C) = 4AC`. -/
theorem section13BigBIndexSet_card_le_four_mul {A C : ℝ}
    (hA : 0 ≤ A) (hC : 1 ≤ C) :
    ((section13BigBIndexSet A C).card : ℝ) ≤ 4 * A * C := by
  classical
  have hsubset :
      section13BigBIndexSet A C ⊆
        fareyMajorantNumerators A ×ˢ fareyDenominators C := by
    unfold section13BigBIndexSet
    exact Finset.filter_subset _ _
  have hcardNat := Finset.card_le_card hsubset
  have hnum := eq1312_fareyMajorantNumerators_card_le hA
  have hden := section13_fareyDenominators_card_le_two_mul hC
  calc
    ((section13BigBIndexSet A C).card : ℝ) ≤
        (((fareyMajorantNumerators A ×ˢ fareyDenominators C).card : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    _ = ((fareyMajorantNumerators A).card : ℝ) *
        ((fareyDenominators C).card : ℝ) := by simp
    _ ≤ (2 * A) * (2 * C) :=
      mul_le_mul hnum hden (Nat.cast_nonneg _) (by positivity)
    _ = 4 * A * C := by ring

/-- The paper-shaped finite Hölder bound with an explicit constant.  The
hypothesis `1 ≤ C` is what permits the endpoint-safe denominator range to be
bounded by `2C`; the exact-cardinality theorem above has no such restriction.

This is only the finite Cauchy--Schwarz step.  Estimating the second moment is
the separate double-large-sieve obligation. -/
theorem section13_bigB_fourth_le_sixteen_mul_secondMoment_sq
    {x G A C K L t₁ t₂ : ℝ}
    (hA : 0 ≤ A) (hC : 1 ≤ C) :
    bigB x G A C K L t₁ t₂ ^ 4 ≤
      16 * G ^ 4 * A ^ 2 / C ^ 2 *
        section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hcard := section13BigBIndexSet_card_le_four_mul hA hC
  have hcardSq : ((section13BigBIndexSet A C).card : ℝ) ^ 2 ≤
      (4 * A * C) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hfactor : 0 ≤ (G / C) ^ 4 :=
    by positivity
  have hmomentSq :
      0 ≤ section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := sq_nonneg _
  calc
    bigB x G A C K L t₁ t₂ ^ 4 ≤
        (G / C) ^ 4 * ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 :=
      section13_bigB_fourth_le_indexCard_sq_mul_secondMoment_sq
        x G A C K L t₁ t₂
    _ ≤ (G / C) ^ 4 * (4 * A * C) ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardSq hfactor) hmomentSq
    _ = 16 * G ^ 4 * A ^ 2 / C ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
      field_simp [hC0.ne']; ring

end

end LeanProofs.IntegerPoints
