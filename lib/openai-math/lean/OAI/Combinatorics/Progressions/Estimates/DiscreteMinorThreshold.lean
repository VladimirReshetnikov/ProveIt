import OAI.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
import OAI.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial

namespace OAI


namespace Erdos3

theorem discrete_scalarCube_minor_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (hN : 0 < N)
    (s : I → J) (hs : Function.Injective s) (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (u : ℝ) (hu : 0 < u) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ u) ≤
      (integerScalarCubeDensityCap I) ^ Fintype.card J *
        (multivariateSublevelConstant N (Fintype.card I) *
          ((u + coordinateDeterminantVariation I (Fin N) / L) *
            (Fintype.card I + 1 : ℝ) ^ N) ^ (((N * Fintype.card I : ℕ) : ℝ)⁻¹)) := by
  have h := polynomial_grid_sublevel_bound_of_value hN Fintype.card_pos
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL))
    (scalarCubeGrid e) (scalarCubeGrid_injective e) L hL (scalarCubeGrid_bounds e)
    (scalarCubeMinorPolynomial e s)
    (coordinateMatrixPolynomial_degree (fun i j => e (s j, some i)))
    ((integerScalarCubeDensityCap I) ^ Fintype.card J)
    (coordinateDeterminantVariation I (Fin N)) u
    (pow_nonneg (integerScalarCubeDensityCap_pos I).le _) (coordinateDeterminantVariation_nonneg I (Fin N)) hu
    (scalarCubeGrid_weight_le e L hL hsize)
    (coordinateMatrixPolynomial_variation (fun i j => e (s j, some i)))
    (scalarCubeMinorTestPoint e s) (scalarCubeMinorTestPoint_bound e s)
    (by rw [scalarCubeMinorPolynomial_test_value e s hs]; norm_num)
  simpa only [scalarCubeMinorPolynomial_grid_eval] using h


noncomputable def discreteScalarMinorThreshold (I J : Type*) [Fintype I] [Fintype J]
    (N : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * Fintype.card I) 1
    ((integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I))
    ((Fintype.card I + 1 : ℝ) ^ N) η

theorem discreteScalarMinorThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    0 < discreteScalarMinorThreshold I J N η := by
  apply polynomialSublevelThreshold_pos
  · exact mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
      (multivariateSublevelConstant_pos hN _).le
  · positivity
  · exact hη

theorem discrete_minor_threshold_probability {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (hN : 0 < N)
    (s : I → J) (hs : Function.Injective s) (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (η : ℝ) (hη : 0 < η)
    (hmesh : coordinateDeterminantVariation I (Fin N) / L ≤ discreteScalarMinorThreshold I J N η) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ discreteScalarMinorThreshold I J N η) ≤ η / 2 := by
  let C := (integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I)
  let S := (Fintype.card I + 1 : ℝ) ^ N
  let κ := discreteScalarMinorThreshold I J N η
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    (multivariateSublevelConstant_pos hN _).le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hκ : 0 < κ := discreteScalarMinorThreshold_pos I J hN hη
  have h := discrete_scalarCube_minor_probability_le e hN s hs L hL hsize κ hκ
  calc
    _ ≤ C * ((κ + coordinateDeterminantVariation I (Fin N) / L) * S) ^
        (((N * Fintype.card I : ℕ) : ℝ)⁻¹) := by simpa only [C, S, mul_assoc] using h
    _ ≤ C * (2 * κ * S) ^ (((N * Fintype.card I : ℕ) : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow
      · exact mul_nonneg (add_nonneg hκ.le
          (div_nonneg (coordinateDeterminantVariation_nonneg I (Fin N)) (Nat.cast_nonneg L))) hS
      · apply mul_le_mul_of_nonneg_right _ hS
        dsimp [κ]
        linarith
      · positivity
    _ ≤ η / 2 := by
      have ht := polynomialSublevelThreshold_total_bound (m := 1)
        (Nat.mul_pos hN (Fintype.card_pos (α := I))) hC hS hη
      simpa only [Nat.cast_one, one_mul, κ, discreteScalarMinorThreshold, C, S] using ht

theorem exists_discrete_minor_length (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (hN : 0 < N)
    (s : I → J) (hs : Function.Injective s) (η : ℝ) (hη : 0 < η) :
    ∃ L₀ : ℕ, Fintype.card I + 1 ≤ L₀ ∧ ∀ (L : ℕ) (hL : 0 < L), L₀ ≤ L →
      (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (fun x => |normalizedScalarCubeMinor s x| ≤ discreteScalarMinorThreshold I J N η) ≤ η / 2 := by
  let κ := discreteScalarMinorThreshold I J N η
  let K := coordinateDeterminantVariation I (Fin N)
  have hκ : 0 < κ := discreteScalarMinorThreshold_pos I J hN hη
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge (max (Fintype.card I + 1 : ℝ) (K / κ))
  have hsize : Fintype.card I + 1 ≤ L₀ := by exact_mod_cast (le_max_left _ _).trans hL₀
  refine ⟨L₀, hsize, fun L hL hlarge => ?_⟩
  apply discrete_minor_threshold_probability e hN s hs L hL (hsize.trans hlarge) η hη
  change K / (L : ℝ) ≤ κ
  apply (div_le_iff₀ (by exact_mod_cast hL)).mpr
  have hlarge' : (L₀ : ℝ) ≤ L := by exact_mod_cast hlarge
  have h := (div_le_iff₀ hκ).mp ((le_max_right _ _).trans (hL₀.trans hlarge'))
  simpa only [mul_comm] using h

end Erdos3

end OAI
