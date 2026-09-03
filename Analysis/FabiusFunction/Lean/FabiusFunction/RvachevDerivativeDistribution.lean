import FabiusFunction.GlobalBounds
import FabiusFunction.ThueMorseBooleanCube
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
measure-theoretic consequences.  Absolute derivatives are exactly
equimeasurable with the rescaled original profile at every order.  At every
positive order, sharply normalized signed derivatives have the symmetric
half-mixture of the original profile and its reflection.  The continuous-test
forms are Banach-valued, and their pushforward forms transport arbitrary
Borel distributional statements.

## Main results

* `iteratedDeriv_rvachev_cell` is the exact cellwise derivative tiling.
* `iteratedDeriv_rvachev_cell_zero` gives every signed cell-midpoint extremum.
* `abs_iteratedDeriv_rvachev_cell` removes the Thue--Morse sign.
* `intervalIntegral_comp_iteratedDeriv_rvachev` is the signed finite-mixture
  identity for Banach-valued continuous test functions.
* `intervalIntegral_iteratedDeriv_rvachev_pow` gives every signed natural
  moment in a single all-order Boolean-cube formula; its even and positive-
  order odd corollaries are the report's parity laws.
* `intervalIntegral_comp_normalized_iteratedDeriv_rvachev` gives the exact
  positive-order signed half-mixture law for Banach-valued continuous tests.
* `map_normalized_iteratedDeriv_rvachev_restrict_Icc` upgrades that law to an
  equality of Borel pushforward measures.
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

/-- **All signed natural moments, including derivative order zero.**  The
`m`-th signed moment of the `n`-th derivative is the base moment multiplied
by the sharp derivative scale and by the Boolean-cube weight enumerator
`(1 + (-1) ^ m) ^ n`.

This formula deliberately keeps the factor `0 ^ 0` when `n = 0` and `m` is
odd.  Lean's convention `0 ^ 0 = 1` then gives the original signed moment,
whereas every positive derivative order has vanishing odd moments. -/
theorem intervalIntegral_iteratedDeriv_rvachev_pow
    (F : BoundedFabius) (hF : IsFabius F) (n m : ℕ) :
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv n (rvachevUp F) x) ^ m) =
      ((2 : ℝ) ^ n)⁻¹ * (1 + (-1 : ℝ) ^ m) ^ n *
        ((2 : ℝ) ^ (n + 1).choose 2) ^ m *
          ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m := by
  have h := intervalIntegral_comp_iteratedDeriv_rvachev F hF
    (fun t : ℝ ↦ t ^ m) (continuous_id.pow m) n
  calc
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv n (rvachevUp F) x) ^ m) =
        ((2 : ℝ) ^ n)⁻¹ *
          ∑ k ∈ range (2 ^ n),
            ∫ y in (-1 : ℝ)..1,
              (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
                rvachevUp F y) ^ m := by
      simpa only [smul_eq_mul] using h
    _ = ((2 : ℝ) ^ n)⁻¹ *
        ∑ k ∈ range (2 ^ n),
          ((2 : ℝ) ^ (n + 1).choose 2) ^ m *
            (((-1 : ℝ) ^ m) ^ binaryWeight k) *
              ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m := by
      congr 1
      apply sum_congr rfl
      intro k _hk
      have hsign :
          (((-1 : ℝ) ^ binaryWeight k) ^ m) =
            ((-1 : ℝ) ^ m) ^ binaryWeight k := by
        simp only [← pow_mul, Nat.mul_comm]
      calc
        (∫ y in (-1 : ℝ)..1,
            (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
              rvachevUp F y) ^ m) =
            ∫ y in (-1 : ℝ)..1,
              (((2 : ℝ) ^ (n + 1).choose 2) ^ m *
                (((-1 : ℝ) ^ m) ^ binaryWeight k)) *
                  (rvachevUp F y) ^ m := by
          apply intervalIntegral.integral_congr
          intro y _hy
          change
            (2 ^ (n + 1).choose 2 * (-1 : ℝ) ^ binaryWeight k *
                rvachevUp F y) ^ m =
              (((2 : ℝ) ^ (n + 1).choose 2) ^ m *
                (((-1 : ℝ) ^ m) ^ binaryWeight k)) *
                  (rvachevUp F y) ^ m
          rw [mul_pow, mul_pow, hsign]
        _ = ((2 : ℝ) ^ (n + 1).choose 2) ^ m *
              (((-1 : ℝ) ^ m) ^ binaryWeight k) *
                ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m := by
          exact intervalIntegral.integral_const_mul _ _
    _ = ((2 : ℝ) ^ n)⁻¹ *
        (((2 : ℝ) ^ (n + 1).choose 2) ^ m *
          (∑ k ∈ range (2 ^ n), ((-1 : ℝ) ^ m) ^ binaryWeight k) *
            ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m) := by
      rw [← sum_mul, ← mul_sum]
    _ = ((2 : ℝ) ^ n)⁻¹ * (1 + (-1 : ℝ) ^ m) ^ n *
        ((2 : ℝ) ^ (n + 1).choose 2) ^ m *
          ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m := by
      rw [sum_pow_binaryWeight_eq_one_add_pow]
      ring

/-- Every even signed natural moment of an iterated Rvachev derivative is
the corresponding base moment multiplied by the sharp scale to that power.
This includes derivative order zero and moment order zero. -/
theorem intervalIntegral_iteratedDeriv_rvachev_pow_of_even
    (F : BoundedFabius) (hF : IsFabius F) (n m : ℕ) (hm : Even m) :
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv n (rvachevUp F) x) ^ m) =
      ((2 : ℝ) ^ (n + 1).choose 2) ^ m *
        ∫ y in (-1 : ℝ)..1, (rvachevUp F y) ^ m := by
  rw [intervalIntegral_iteratedDeriv_rvachev_pow F hF n m,
    Even.neg_one_pow hm]
  norm_num

/-- Every odd signed natural moment of a positive-order iterated Rvachev
derivative vanishes.  The positive-order hypothesis is essential: at order
zero the formula reduces to the generally nonzero base odd moment. -/
theorem intervalIntegral_iteratedDeriv_rvachev_pow_eq_zero_of_odd
    (F : BoundedFabius) (hF : IsFabius F) (n m : ℕ) (hn : 0 < n)
    (hm : Odd m) :
    (∫ x in (-1 : ℝ)..1, (iteratedDeriv n (rvachevUp F) x) ^ m) = 0 := by
  rw [intervalIntegral_iteratedDeriv_rvachev_pow F hF n m,
    Odd.neg_one_pow hm]
  simp [Nat.ne_of_gt hn]

/-- **Normalized signed derivatives have the exact symmetric two-component
mixture law.**  At every positive derivative order, integrating a continuous
Banach-valued test against the sharply normalized derivative is the average
of the same test against `rvachevUp` and against its negative.

The positive-order hypothesis is essential: at order zero the left side is
the unsymmetrized original profile. -/
theorem intervalIntegral_comp_normalized_iteratedDeriv_rvachev
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F) (H : ℝ → E) (hH : Continuous H)
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (-1 : ℝ)..1,
        H (((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
          iteratedDeriv n (rvachevUp F) x)) =
      (2 : ℝ)⁻¹ •
        ((∫ y in (-1 : ℝ)..1, H (rvachevUp F y)) +
          ∫ y in (-1 : ℝ)..1, H (-rvachevUp F y)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let P : E := ∫ y in (-1 : ℝ)..1, H (rvachevUp F y)
  let N : E := ∫ y in (-1 : ℝ)..1, H (-rvachevUp F y)
  let J : ℕ → E := fun k ↦
    ∫ y in (-1 : ℝ)..1,
      H ((-1 : ℝ) ^ binaryWeight k * rvachevUp F y)
  have hscale : (2 : ℝ) ^ (m + 1 + 1).choose 2 ≠ 0 := by positivity
  have h := intervalIntegral_comp_iteratedDeriv_rvachev F hF
    (fun t ↦ H (((2 : ℝ) ^ (m + 1 + 1).choose 2)⁻¹ * t))
    (hH.comp (continuous_const.mul continuous_id)) (m + 1)
  have hnormalized :
      (∫ x in (-1 : ℝ)..1,
          H (((2 : ℝ) ^ (m + 1 + 1).choose 2)⁻¹ *
            iteratedDeriv (m + 1) (rvachevUp F) x)) =
        ((2 : ℝ) ^ (m + 1))⁻¹ • ∑ k ∈ range (2 ^ (m + 1)), J k := by
    calc
      (∫ x in (-1 : ℝ)..1,
          H (((2 : ℝ) ^ (m + 1 + 1).choose 2)⁻¹ *
            iteratedDeriv (m + 1) (rvachevUp F) x)) =
          ((2 : ℝ) ^ (m + 1))⁻¹ •
            ∑ k ∈ range (2 ^ (m + 1)),
              ∫ y in (-1 : ℝ)..1,
                H (((2 : ℝ) ^ (m + 1 + 1).choose 2)⁻¹ *
                  (2 ^ (m + 1 + 1).choose 2 *
                    (-1 : ℝ) ^ binaryWeight k * rvachevUp F y)) := h
      _ = ((2 : ℝ) ^ (m + 1))⁻¹ • ∑ k ∈ range (2 ^ (m + 1)), J k := by
        congr 1
        apply sum_congr rfl
        intro k _hk
        dsimp only [J]
        apply intervalIntegral.integral_congr
        intro y _hy
        field_simp
  rw [hnormalized]
  have hpair :
      ∑ k ∈ range (2 ^ (m + 1)), J k =
        ∑ k ∈ range (2 ^ m), (P + N) := by
    rw [pow_succ, mul_comm, sum_range_two_mul]
    apply sum_congr rfl
    intro k _hk
    simp only [J, binaryWeight_two_mul, binaryWeight_two_mul_add_one]
    rcases Nat.even_or_odd (binaryWeight k) with he | ho
    · simp [P, N, Even.neg_one_pow he, pow_succ]
    · simp [P, N, Odd.neg_one_pow ho, pow_succ, add_comm]
  rw [hpair, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  dsimp only [P, N]
  norm_num [pow_succ]

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

/-- **Exact signed derivative law as a pushforward identity.**  Under
Lebesgue measure restricted to `[-1,1]`, every positive-order sharply
normalized Rvachev derivative has the symmetric half-mixture of the
`rvachevUp` law and its reflection.

The positive-order hypothesis is essential: at order zero the normalized
derivative has the unsymmetrized `rvachevUp` law. -/
theorem map_normalized_iteratedDeriv_rvachev_restrict_Icc
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n) :
    Measure.map
        (fun x : ℝ ↦ ((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
          iteratedDeriv n (rvachevUp F) x)
        (volume.restrict (Icc (-1 : ℝ) 1)) =
      ((2 : NNReal)⁻¹) •
        (Measure.map (rvachevUp F) (volume.restrict (Icc (-1 : ℝ) 1)) +
          Measure.map (fun y : ℝ ↦ -rvachevUp F y)
            (volume.restrict (Icc (-1 : ℝ) 1))) := by
  let A : ℝ → ℝ := fun x ↦ ((2 : ℝ) ^ (n + 1).choose 2)⁻¹ *
    iteratedDeriv n (rvachevUp F) x
  have hderiv : Continuous (iteratedDeriv n (rvachevUp F)) :=
    (rvachev_contDiff F hF).continuous_iteratedDeriv n
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hA : Continuous A := by
    dsimp only [A]
    exact continuous_const.mul hderiv
  have hup : Continuous (rvachevUp F) := (rvachev_contDiff F hF).continuous
  have hneg : Continuous (fun y : ℝ ↦ -rvachevUp F y) := hup.neg
  let μ : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  letI : IsFiniteMeasure (Measure.map A μ) := μ.isFiniteMeasure_map A
  letI : IsFiniteMeasure (Measure.map (rvachevUp F) μ) :=
    μ.isFiniteMeasure_map (rvachevUp F)
  letI : IsFiniteMeasure (Measure.map (fun y : ℝ ↦ -rvachevUp F y) μ) :=
    μ.isFiniteMeasure_map (fun y : ℝ ↦ -rvachevUp F y)
  change Measure.map A μ =
    ((2 : NNReal)⁻¹) •
      (Measure.map (rvachevUp F) μ +
        Measure.map (fun y : ℝ ↦ -rvachevUp F y) μ)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro H
  rw [MeasureTheory.integral_map_of_stronglyMeasurable hA.measurable
      H.continuous.stronglyMeasurable,
    MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_add_measure (H.integrable _) (H.integrable _),
    MeasureTheory.integral_map_of_stronglyMeasurable hup.measurable
      H.continuous.stronglyMeasurable,
    MeasureTheory.integral_map_of_stronglyMeasurable hneg.measurable
      H.continuous.stronglyMeasurable]
  dsimp only [μ]
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      A, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_ofNat] using
    intervalIntegral_comp_normalized_iteratedDeriv_rvachev
      F hF H H.continuous n hn

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
