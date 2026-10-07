import GowersSzemeredi.Proofs18QuadraticDensityIncrement

/-! A closed starting threshold for the quadratic density increment.
All constants are defined by finite arithmetic operations and real powers;
no existential large-modulus witness is used by the quantitative theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The two concrete power conditions needed for quadratic discrepancy. -/
def quadraticDensityThreshold (alpha : Real) : Real :=
  max ((4 : Real) ^ (cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1)⁻¹)
    ((quadraticRefinementConstant alpha) ^ (quadraticDiscrepancyExponent alpha)⁻¹)

/-- The fixed refinement constant is strictly positive. -/
theorem quadraticRefinementConstant_pos (alpha : Real) :
    0 < quadraticRefinementConstant alpha := by
  unfold quadraticRefinementConstant
  exact mul_pos (section5LocalRefinementConstant_pos _ _) (by positivity)

/-- The closed threshold implies both power conditions, with equality
allowed at the threshold. -/
theorem quadraticDensityThreshold_power_bounds {alpha x : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hx : quadraticDensityThreshold alpha ≤ x) :
    4 ≤ x ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 ∧
      quadraticRefinementConstant alpha ≤ x ^ quadraticDiscrepancyExponent alpha := by
  have he := (quadratic_frequency_exponent_bounds hα hαone).1
  have hs : 0 < quadraticDiscrepancyExponent alpha := div_pos he (by norm_num)
  have hfirst := (le_max_left _ _).trans hx
  have hsecond := (le_max_right _ _).trans hx
  constructor
  · calc
      (4 : Real) = ((4 : Real) ^ (cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1)⁻¹) ^
          cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 :=
        (Real.rpow_inv_rpow (by norm_num) he.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hfirst he.le
  · calc
      quadraticRefinementConstant alpha =
          ((quadraticRefinementConstant alpha) ^ (quadraticDiscrepancyExponent alpha)⁻¹) ^
            quadraticDiscrepancyExponent alpha :=
        (Real.rpow_inv_rpow (quadraticRefinementConstant_pos alpha).le hs.ne').symm
      _ ≤ _ := Real.rpow_le_rpow
        (Real.rpow_nonneg (quadraticRefinementConstant_pos alpha).le _) hsecond hs.le

/-- A convenient single-exponential upper bound for the closed threshold.
Its exponent uses only the explicit refinement constant and size exponent. -/
theorem quadraticDensityThreshold_le_exp (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticDensityThreshold alpha ≤
      Real.exp ((4 + quadraticRefinementConstant alpha) / quadraticDiscrepancyExponent alpha) := by
  let e := cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1
  let s := quadraticDiscrepancyExponent alpha
  let C := quadraticRefinementConstant alpha
  have he : 0 < e := (quadratic_frequency_exponent_bounds hα hαone).1
  have hs : 0 < s := div_pos he (by norm_num)
  have hC : 0 < C := quadraticRefinementConstant_pos alpha
  have hse : s ≤ e := by
    change e / 4096 ≤ e
    exact div_le_self he.le (by norm_num)
  have hinv : e⁻¹ ≤ s⁻¹ := (inv_le_inv₀ he hs).2 hse
  unfold quadraticDensityThreshold
  apply max_le
  · rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 4)]
    apply Real.exp_le_exp.mpr
    change Real.log 4 * e⁻¹ ≤ (4 + C) / s
    calc
      _ ≤ 4 * e⁻¹ := mul_le_mul_of_nonneg_right (Real.log_le_self (by norm_num)) (inv_nonneg.mpr he.le)
      _ ≤ 4 * s⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ (4 + C) * s⁻¹ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC.le) (inv_nonneg.mpr hs.le)
      _ = _ := (div_eq_mul_inv _ _).symm
  · rw [Real.rpow_def_of_pos (quadraticRefinementConstant_pos alpha)]
    apply Real.exp_le_exp.mpr
    change Real.log C * s⁻¹ ≤ (4 + C) / s
    calc
      _ ≤ C * s⁻¹ := mul_le_mul_of_nonneg_right (Real.log_le_self hC.le) (inv_nonneg.mpr hs.le)
      _ ≤ (4 + C) * s⁻¹ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) (inv_nonneg.mpr hs.le)
      _ = _ := (div_eq_mul_inv _ _).symm

/-- Explicit-threshold quadratic discrepancy for every disc-valued function. -/
theorem quadratic_nonuniformity_discrepancy_partition_explicit
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticDensityThreshold alpha ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 2) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (N : Real) ^ quadraticDiscrepancyExponent alpha ≤ averageCellSize (fun j ↦ (R j).carrier) ∧
      quadraticDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
  obtain ⟨hlarge, hbudget⟩ := quadraticDensityThreshold_power_bounds hα hαone hN
  exact quadratic_nonuniformity_discrepancy_partition_of_power_bounds alpha hα hαone N
    hlarge hbudget f hf hnot

/-- Explicit-threshold quadratic density increment, without an assumed
inverse theorem or an opaque sufficiently-large modulus. -/
theorem quadratic_nonuniformity_density_increment_explicit
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticDensityThreshold alpha ≤ N)
    (A : Finset (ZMod N)) (hnot : ¬ UniformSetOfDegree A alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  obtain ⟨M, P, hpart, hproper, havg, hdis⟩ :=
    quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N hN
      (balanced A) (balanced_discValued A) hnot
  have hβ : 0 ≤ quadraticDiscrepancyParameter alpha := by
    unfold quadraticDiscrepancyParameter
    positivity
  obtain ⟨j, hsize, hinc⟩ := density_increment_of_discrepancy_partition A P _ _ hβ hpart havg hdis
  exact ⟨P j, hproper j, hsize, hinc⟩

end LeanProofs.GowersSzemeredi
