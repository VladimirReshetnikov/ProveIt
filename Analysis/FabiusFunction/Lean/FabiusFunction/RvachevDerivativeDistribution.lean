import FabiusFunction.GlobalBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Cell distributions of the derivatives of Rvachev's function

The closed derivative formula for `rvachevUp` becomes especially transparent
after partitioning `[-1, 1]` into its `2 ^ n` natural dyadic cells.  On every
cell the `n`-th derivative is one affine copy of `rvachevUp`, multiplied by the
sharp scale `2 ^ (n + 1).choose 2` and by the corresponding Thue--Morse sign.

This module records that cell coordinate and then packages its principal
measure-theoretic consequence: composing the absolute derivative with any
continuous test function has exactly the same interval integral as composing
the original profile with the rescaled test function.  The theorem is
Banach-valued, includes order zero, and is the reusable core behind all
absolute-moment and rearrangement-invariant norm identities.

## Main results

* `iteratedDeriv_rvachev_cell` is the exact cellwise derivative tiling.
* `iteratedDeriv_rvachev_cell_zero` gives every signed cell-midpoint extremum.
* `abs_iteratedDeriv_rvachev_cell` removes the Thue--Morse sign.
* `intervalIntegral_comp_iteratedDeriv_rvachev` is the signed finite-mixture
  identity for Banach-valued continuous test functions.
* `intervalIntegral_comp_abs_iteratedDeriv_rvachev` is the Banach-valued
  continuous-test-function distribution identity.
* `intervalIntegral_comp_normalized_abs_iteratedDeriv_rvachev` is its
  normalized equimeasurability form.
* `map_normalized_abs_iteratedDeriv_rvachev_restrict_Icc` is the corresponding
  equality of Borel pushforward measures.
* `intervalIntegral_abs_iteratedDeriv_rvachev_rpow` gives every nonnegative
  real absolute moment, including the order-zero boundary under Lean's
  `0 ^ 0 = 1` convention.
-/

set_option autoImplicit false

open Finset MeasureTheory Set
open scoped BigOperators

namespace Fabius

/-- The affine coordinate carrying `[-1, 1]` onto the `k`-th cell of the
level-`n` partition of `[-1, 1]`.

The useful range is `k < 2 ^ n`; the definition itself is deliberately total
in both natural indices. -/
noncomputable def rvachevDerivativeCell (n k : ℕ) (y : ℝ) : ℝ :=
  -1 + (2 * (k : ℝ) + 1 + y) / (2 : ℝ) ^ n

/-- The cell coordinate is an affine dilation about its midpoint. -/
theorem rvachevDerivativeCell_eq_div_add (n k : ℕ) (y : ℝ) :
    rvachevDerivativeCell n k y =
      y / (2 : ℝ) ^ n + rvachevDerivativeCell n k 0 := by
  unfold rvachevDerivativeCell
  ring_nf

/-- The right endpoint of one derivative cell is the left endpoint of the
next, including all levels and indices. -/
theorem rvachevDerivativeCell_one_eq_succ_neg_one (n k : ℕ) :
    rvachevDerivativeCell n k 1 = rvachevDerivativeCell n (k + 1) (-1) := by
  unfold rvachevDerivativeCell
  norm_num [Nat.cast_add]
  ring

/-- The left endpoint of the first derivative cell is `-1`. -/
@[simp]
theorem rvachevDerivativeCell_zero_neg_one (n : ℕ) :
    rvachevDerivativeCell n 0 (-1) = -1 := by
  simp [rvachevDerivativeCell]

/-- The left endpoint after all `2 ^ n` cells is `1`. -/
@[simp]
theorem rvachevDerivativeCell_two_pow_neg_one (n : ℕ) :
    rvachevDerivativeCell n (2 ^ n) (-1) = 1 := by
  unfold rvachevDerivativeCell
  norm_num

/-- Every valid affine cell coordinate lies in the support interval
`[-1, 1]`.  Both cell endpoints are included. -/
theorem rvachevDerivativeCell_mem_Icc (n k : ℕ) (hk : k < 2 ^ n)
    {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    rvachevDerivativeCell n k y ∈ Icc (-1 : ℝ) 1 := by
  have hscale : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hkNat : k + 1 ≤ 2 ^ n := Nat.succ_le_iff.mpr hk
  have hkReal : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hkNat
  have hnum : 0 ≤ 2 * (k : ℝ) + 1 + y := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [hy.1]
  constructor
  · unfold rvachevDerivativeCell
    have hdiv := div_nonneg hnum hscale.le
    linarith
  · unfold rvachevDerivativeCell
    have hdiv : (2 * (k : ℝ) + 1 + y) / (2 : ℝ) ^ n ≤ 2 := by
      rw [div_le_iff₀ hscale]
      norm_num at hkReal ⊢
      nlinarith [hy.2, hkReal]
    linarith

/-- **Exact derivative tiling on one cell.**  On the `k`-th level-`n`
cell, the `n`-th derivative of `rvachevUp` is the original profile in the
cell coordinate, multiplied by the sharp derivative scale and by the
`k`-th Thue--Morse sign.

The statement includes `n = 0`, `k = 0`, and both cell endpoints. -/
theorem iteratedDeriv_rvachev_cell (F : BoundedFabius) (hF : IsFabius F)
    (n k : ℕ) (hk : k < 2 ^ n) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    iteratedDeriv n (rvachevUp F) (rvachevDerivativeCell n k y) =
      2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k * rvachevUp F y := by
  rw [iteratedDeriv_rvachev F hF n _
    (rvachevDerivativeCell_mem_Icc n k hk hy)]
  have hscale : (2 : ℝ) ^ n ≠ 0 := by positivity
  have harg : (2 : ℝ) ^ n * (rvachevDerivativeCell n k y + 1) =
      2 * (k : ℝ) + (y + 1) := by
    unfold rvachevDerivativeCell
    field_simp
    ring
  rw [harg, extendedFabius_two_mul_add F hF k (y + 1)
    (by constructor <;> linarith [hy.1, hy.2])]
  ring_nf

/-- At the midpoint of every level-`n` cell, the `n`-th derivative attains
the sharp scale with the corresponding Thue--Morse sign.  This includes the
single midpoint at order zero. -/
theorem iteratedDeriv_rvachev_cell_zero
    (F : BoundedFabius) (hF : IsFabius F) (n k : ℕ) (hk : k < 2 ^ n) :
    iteratedDeriv n (rvachevUp F) (rvachevDerivativeCell n k 0) =
      2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k := by
  simpa only [rvachevUp_zero F hF, mul_one] using
    iteratedDeriv_rvachev_cell F hF n k hk
      (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)

/-- The absolute cell profile is independent of the Thue--Morse sign. -/
theorem abs_iteratedDeriv_rvachev_cell (F : BoundedFabius) (hF : IsFabius F)
    (n k : ℕ) (hk : k < 2 ^ n) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    |iteratedDeriv n (rvachevUp F) (rvachevDerivativeCell n k y)| =
      2 ^ (n + 1).choose 2 * rvachevUp F y := by
  rw [iteratedDeriv_rvachev_cell F hF n k hk hy, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1).choose 2),
    abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (rvachevUp_nonneg F y)]
  ring

/-- **Signed continuous-test-function derivative distribution identity.**
The distribution of the `n`-th derivative on `[-1,1]` is the uniform finite
mixture of the `2 ^ n` Thue--Morse-signed copies of the original profile,
multiplied by the sharp derivative scale.

The codomain may be any real Banach space.  This all-order formulation also
records the order-zero boundary exactly; pairing the signs for positive order
gives the usual symmetric Rademacher-mixture law. -/
theorem intervalIntegral_comp_iteratedDeriv_rvachev
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F) (H : ℝ → E) (hH : Continuous H)
    (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, H (iteratedDeriv n (rvachevUp F) x)) =
      ((2 : ℝ) ^ n)⁻¹ •
        ∑ k ∈ range (2 ^ n),
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) := by
  let g : ℝ → E := fun x ↦ H (iteratedDeriv n (rvachevUp F) x)
  have hderiv : Continuous (iteratedDeriv n (rvachevUp F)) :=
    (rvachev_contDiff F hF).continuous_iteratedDeriv n
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hg : Continuous g := by
    dsimp only [g]
    exact hH.comp hderiv
  have hcell : ∀ k < 2 ^ n,
      (∫ x in rvachevDerivativeCell n k (-1)..
          rvachevDerivativeCell n (k + 1) (-1), g x) =
        ((2 : ℝ) ^ n)⁻¹ •
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) := by
    intro k hk
    rw [← rvachevDerivativeCell_one_eq_succ_neg_one n k,
      rvachevDerivativeCell_eq_div_add n k (-1),
      rvachevDerivativeCell_eq_div_add n k 1]
    calc
      (∫ x in (-1 : ℝ) / (2 : ℝ) ^ n + rvachevDerivativeCell n k 0..
          1 / (2 : ℝ) ^ n + rvachevDerivativeCell n k 0, g x) =
          ((2 : ℝ) ^ n)⁻¹ •
            ∫ y in (-1 : ℝ)..1,
              g (y / (2 : ℝ) ^ n + rvachevDerivativeCell n k 0) := by
        symm
        exact intervalIntegral.inv_smul_integral_comp_div_add
          g ((2 : ℝ) ^ n) (rvachevDerivativeCell n k 0)
      _ = ((2 : ℝ) ^ n)⁻¹ •
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro y hy
        have hyIcc : y ∈ Icc (-1 : ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
        dsimp only [g]
        rw [← rvachevDerivativeCell_eq_div_add n k y]
        exact congrArg H (iteratedDeriv_rvachev_cell F hF n k hk hyIcc)
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (f := g) (a := fun k ↦ rvachevDerivativeCell n k (-1))
    (n := 2 ^ n) (fun k _ ↦ hg.intervalIntegrable _ _)
  change (∫ x in (-1 : ℝ)..1, g x) = _
  calc
    (∫ x in (-1 : ℝ)..1, g x) =
        ∑ k ∈ range (2 ^ n),
          ∫ x in rvachevDerivativeCell n k (-1)..
            rvachevDerivativeCell n (k + 1) (-1), g x := by
      simpa using hpartition.symm
    _ = ∑ k ∈ range (2 ^ n),
        ((2 : ℝ) ^ n)⁻¹ •
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) := by
      apply sum_congr rfl
      intro k hk
      exact hcell k (mem_range.mp hk)
    _ = ((2 : ℝ) ^ n)⁻¹ •
        ∑ k ∈ range (2 ^ n),
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) := by
      rw [smul_sum]

/-- **Continuous-test-function derivative distribution identity.**  For any
continuous function with values in a real Banach space, integrating it against
the absolute `n`-th derivative on `[-1,1]` is the same as integrating it
against the original Rvachev profile multiplied by the sharp derivative
scale.

This is stronger than any single moment or norm identity: the codomain may be
an arbitrary real Banach space, and the theorem includes `n = 0`. -/
theorem intervalIntegral_comp_abs_iteratedDeriv_rvachev
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F) (H : ℝ → E) (hH : Continuous H)
    (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, H |iteratedDeriv n (rvachevUp F) x|) =
      ∫ y in (-1 : ℝ)..1,
        H (2 ^ (n + 1).choose 2 * rvachevUp F y) := by
  have h := intervalIntegral_comp_iteratedDeriv_rvachev F hF
    (fun t ↦ H |t|) (hH.comp continuous_abs) n
  calc
    (∫ x in (-1 : ℝ)..1, H |iteratedDeriv n (rvachevUp F) x|) =
        ((2 : ℝ) ^ n)⁻¹ •
          ∑ k ∈ range (2 ^ n),
            ∫ y in (-1 : ℝ)..1,
              H |2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
                rvachevUp F y| := h
    _ = ((2 : ℝ) ^ n)⁻¹ •
        ∑ _k ∈ range (2 ^ n),
          ∫ y in (-1 : ℝ)..1,
            H (2 ^ (n + 1).choose 2 * rvachevUp F y) := by
      congr 1
      apply sum_congr rfl
      intro k _hk
      apply intervalIntegral.integral_congr
      intro y _hy
      change H |2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
        rvachevUp F y| = H (2 ^ (n + 1).choose 2 * rvachevUp F y)
      congr 1
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1).choose 2),
        abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (rvachevUp_nonneg F y)]
      ring
    _ = ∫ y in (-1 : ℝ)..1,
        H (2 ^ (n + 1).choose 2 * rvachevUp F y) := by
      rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      norm_num

/-- Normalized absolute derivatives have the same continuous-test-function
integrals as `rvachevUp` itself.  This is the interval-integral form of exact
absolute equimeasurability. -/
theorem intervalIntegral_comp_normalized_abs_iteratedDeriv_rvachev
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F) (H : ℝ → E) (hH : Continuous H)
    (n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        H (((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
          |iteratedDeriv n (rvachevUp F) x|)) =
      ∫ y in (-1 : ℝ)..1, H (rvachevUp F y) := by
  have hscale : (2 : ℝ) ^ (n + 1).choose 2 ≠ 0 := by positivity
  have h := intervalIntegral_comp_abs_iteratedDeriv_rvachev F hF
    (fun t ↦ H (((2 : ℝ) ^ (n + 1).choose 2)⁻¹ * t))
    (hH.comp (continuous_const.mul continuous_id)) n
  simpa only [inv_mul_cancel_left₀ hscale] using h

/-- **Exact absolute equimeasurability as a pushforward identity.**  Under
Lebesgue measure restricted to `[-1,1]`, the normalized absolute `n`-th
derivative and `rvachevUp` have exactly the same Borel distribution.

Unlike the continuous-test formulation above, this equality immediately
transports arbitrary measurable level sets and all measure-theoretic function
space properties.  It includes order zero. -/
theorem map_normalized_abs_iteratedDeriv_rvachev_restrict_Icc
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    Measure.map
        (fun x : ℝ ↦ ((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
          |iteratedDeriv n (rvachevUp F) x|)
        (volume.restrict (Icc (-1 : ℝ) 1)) =
      Measure.map (rvachevUp F) (volume.restrict (Icc (-1 : ℝ) 1)) := by
  let A : ℝ → ℝ := fun x ↦ ((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
    |iteratedDeriv n (rvachevUp F) x|
  have hderiv : Continuous (iteratedDeriv n (rvachevUp F)) :=
    (rvachev_contDiff F hF).continuous_iteratedDeriv n
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hA : Continuous A := by
    dsimp only [A]
    exact continuous_const.mul hderiv.abs
  have hup : Continuous (rvachevUp F) := (rvachev_contDiff F hF).continuous
  let μ : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  letI : IsFiniteMeasure (Measure.map A μ) := μ.isFiniteMeasure_map A
  letI : IsFiniteMeasure (Measure.map (rvachevUp F) μ) :=
    μ.isFiniteMeasure_map (rvachevUp F)
  change Measure.map A μ = Measure.map (rvachevUp F) μ
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro H
  rw [MeasureTheory.integral_map_of_stronglyMeasurable hA.measurable
      H.continuous.stronglyMeasurable,
    MeasureTheory.integral_map_of_stronglyMeasurable hup.measurable
      H.continuous.stronglyMeasurable]
  dsimp only [μ]
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), A]
    using intervalIntegral_comp_normalized_abs_iteratedDeriv_rvachev
      F hF H H.continuous n

/-- **All nonnegative real absolute moments.**  The `p`-th absolute moment of
the `n`-th derivative on `[-1,1]` is the corresponding moment of `rvachevUp`
times the exact scale raised to `p`.

The report needs `0 < p`; the stronger hypothesis `0 ≤ p` is natural in
Lean and includes `p = 0`, where both integrands use `0 ^ 0 = 1`. -/
theorem intervalIntegral_abs_iteratedDeriv_rvachev_rpow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (∫ x in (-1 : ℝ)..1, |iteratedDeriv n (rvachevUp F) x| ^ p) =
      (2 ^ (n + 1).choose 2) ^ p *
        ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ p := by
  calc
    (∫ x in (-1 : ℝ)..1, |iteratedDeriv n (rvachevUp F) x| ^ p) =
        ∫ y in (-1 : ℝ)..1,
          (2 ^ (n + 1).choose 2 * rvachevUp F y) ^ p :=
      intervalIntegral_comp_abs_iteratedDeriv_rvachev F hF
        (fun t : ℝ ↦ t ^ p) (Real.continuous_rpow_const hp) n
    _ = (2 ^ (n + 1).choose 2) ^ p *
        ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ p := by
      simp_rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1).choose 2)
        (rvachevUp_nonneg F _)]
      exact intervalIntegral.integral_const_mul _ _

end Fabius
