import Surreal.Surcomplex.TriangleFlatGap

/-!
# The full strong expansion for relative triangle flatness

The inverse-sine series at the square root of the exact gap parameter
factors into its square-root scale and a strongly summable series in
the parameter itself. This proves `trigonometry:eq:flatexpansion` in
`trigonometry:thm:flatrelative`, with an exact finite fourth-order
normalized remainder. All sums and parameters are actual surreals.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The ordinary coefficient series after removing the inverse-sine square-root scale. -/
def flatAngleSeries : PowerSeries ℝ :=
  PowerSeries.mk (fun n => (Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1)))

@[simp] theorem coeff_flatAngleSeries (n : ℕ) :
    PowerSeries.coeff n flatAngleSeries =
      (Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1)) :=
  PowerSeries.coeff_mk _ _

/-- The normalized flat-angle coefficient family is strongly summable at any actual infinitesimal. -/
theorem stronglySummable_flatAngleSeries (q : SignSequence.{u})
    (hq : SignSequence.IsInfinitesimal q) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) * q ^ n) :=
  SignSequence.stronglySummable_coeff_mul_powers q hq _

/-- The normalized square-root inverse-sine expansion is an actual strong sum. -/
theorem arcsinFunction_sqrt_eq_strongSum (q : SignSequence.{u}) (hpos : 0 ≤ q)
    (hq : SignSequence.IsInfinitesimal q) :
    arcsinFunction (SignSequence.sqrt q) = SignSequence.sqrt q *
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) * q ^ n)
        (stronglySummable_flatAngleSeries q hq) := by
  have hs := SignSequence.infinitesimal_sqrt hpos hq
  have hsum := SignSequence.strongSum_const_mul
    (stronglySummable_flatAngleSeries q hq) (SignSequence.sqrt q)
  have he : (fun n : ℕ => SignSequence.sqrt q *
      (SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) * q ^ n)) =
      (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
          SignSequence.sqrt q ^ (2 * n + 1)) := by
    funext n
    rw [pow_succ, pow_mul, SignSequence.sqrt_sq hpos]
    ring
  simp only [he] at hsum
  rw [arcsinFunction_eq_strongSum _ hs]
  exact hsum

namespace Triangle

/-- The complete strong inverse-sine series in the exact relative-flatness parameter. -/
theorem angleSupplement_eq_strongSum (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    T.angleSupplement.val = 2 * SignSequence.sqrt T.flatParameter *
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
          T.flatParameter ^ n) (stronglySummable_flatAngleSeries T.flatParameter hq) := by
  rw [T.angleSupplement_eq_two_arcsin_sqrt,
    arcsinFunction_sqrt_eq_strongSum T.flatParameter T.flatParameter_mem.1.le hq]
  ring

/-- The normalized factor is evaluation of the explicit ordinary coefficient power series. -/
theorem angleSupplement_eq_powerSeries (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    T.angleSupplement.val = 2 * SignSequence.sqrt T.flatParameter *
      SignSequence.powerSeriesEvaluation T.flatParameter hq flatAngleSeries := by
  rw [T.angleSupplement_eq_strongSum hq, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_flatAngleSeries]

/-- The displayed cubic normalized expansion has an exact finite fourth-order remainder. -/
theorem angleSupplement_expansion (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      SignSequence.standardPart E = 35 / 1152 ∧
        T.angleSupplement.val = 2 * SignSequence.sqrt T.flatParameter *
          (1 + T.flatParameter / 6 + 3 * T.flatParameter ^ 2 / 40 +
            5 * T.flatParameter ^ 3 / 112 + T.flatParameter ^ 4 * E) := by
  obtain ⟨E, hE, he, hval⟩ := SignSequence.exists_finite_powerSeries_remainder
    T.flatParameter hq flatAngleSeries 4
  norm_num [coeff_flatAngleSeries, Finset.sum_range_succ,
    Nat.centralBinom, Nat.choose_succ_succ, map_div₀, map_ofNat] at he hval
  refine ⟨E, hE, he, ?_⟩
  rw [T.angleSupplement_eq_powerSeries hq, hval]
  ring

/-- Dividing by the positive square-root scale gives the same exact normalized expansion. -/
theorem angleSupplement_div_two_sqrt_expansion (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      SignSequence.standardPart E = 35 / 1152 ∧
        T.angleSupplement.val / (2 * SignSequence.sqrt T.flatParameter) =
          1 + T.flatParameter / 6 + 3 * T.flatParameter ^ 2 / 40 +
            5 * T.flatParameter ^ 3 / 112 + T.flatParameter ^ 4 * E := by
  obtain ⟨E, hE, he, hval⟩ := T.angleSupplement_expansion hq
  refine ⟨E, hE, he, ?_⟩
  rw [hval, mul_div_cancel_left₀ _
    (mul_pos (by norm_num) (SignSequence.sqrt_pos T.flatParameter_mem.1)).ne']

/-- Removing the exact square-root scale leaves a finite factor of standard part one. -/
theorem angleSupplement_leading_factor (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    ∃ U : SignSequence.{u}, SignSequence.IsFinite U ∧ SignSequence.standardPart U = 1 ∧
      T.angleSupplement.val = 2 * SignSequence.sqrt T.flatParameter * U := by
  refine ⟨SignSequence.powerSeriesEvaluation T.flatParameter hq flatAngleSeries,
    SignSequence.isFinite_powerSeriesEvaluation T.flatParameter hq _, ?_,
    T.angleSupplement_eq_powerSeries hq⟩
  simp [flatAngleSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Relative equivalence to twice the square root means an actual infinitesimal normalized error. -/
theorem infinitesimal_angleSupplement_div_two_sqrt_sub_one (T : Triangle.{u})
    (hq : SignSequence.IsInfinitesimal T.flatParameter) :
    SignSequence.IsInfinitesimal
      (T.angleSupplement.val / (2 * SignSequence.sqrt T.flatParameter) - 1) := by
  obtain ⟨U, hU, hu, he⟩ := T.angleSupplement_leading_factor hq
  rw [he, mul_div_cancel_left₀ _
    (mul_pos (by norm_num) (SignSequence.sqrt_pos T.flatParameter_mem.1)).ne']
  simpa only [hu, map_one] using SignSequence.infinitesimal_sub_standardPart hU

/-- The source's relative-gap criterion supplies strong summability of the normalized series. -/
theorem stronglySummable_flatExpansion_of_relativeGap (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hgap : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
        T.flatParameter ^ n) := by
  apply stronglySummable_flatAngleSeries
  exact T.infinitesimal_angleSupplement_iff_flatParameter.mp
    ((T.infinitesimal_angleSupplement_iff_relativeGap hB hC).mpr hgap)

/-- The literal strong expansion under the original largest-side and relative-gap hypotheses. -/
theorem angleSupplement_eq_strongSum_of_relativeGap (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hgap : SignSequence.IsInfinitesimal T.relativeGap) :
    T.angleSupplement.val = 2 * SignSequence.sqrt T.flatParameter *
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
          T.flatParameter ^ n) (T.stronglySummable_flatExpansion_of_relativeGap hB hC hgap) :=
  T.angleSupplement_eq_strongSum (T.infinitesimal_angleSupplement_iff_flatParameter.mp
    ((T.infinitesimal_angleSupplement_iff_relativeGap hB hC).mpr hgap))

end Triangle

end
end Surreal.Surcomplex
