import OAI.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
import OAI.Combinatorics.Progressions.Probability.CubeMinorProbability

namespace OAI

section

namespace Erdos3

noncomputable def cubeMinorProbabilityConstant (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) : ℝ :=
  scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * multivariateSublevelConstant N d

noncomputable def cubeMinorProbabilityScale (O : Type*) [Fintype O] (N d : ℕ) (c₀ : ℝ) : ℝ :=
  (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O

theorem cubeMinorProbabilityConstant_pos (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < cubeMinorProbabilityConstant O α h N d :=
  mul_pos (pow_pos (scalarCubeDomainDensity_pos α) _) (multivariateSublevelConstant_pos hN d)

theorem cubeMinorProbabilityScale_pos (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < cubeMinorProbabilityScale O N d c₀ := by
  unfold cubeMinorProbabilityScale
  positivity

noncomputable def cubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d) (cubeMinorProbabilityScale O N d c₀) η

theorem cubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    0 < cubeMinorThreshold J O α h N d c₀ η :=
  polynomialSublevelThreshold_pos _ _ (cubeMinorProbabilityConstant_pos O α h hN d).le
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem cubeMinorThreshold_le_half (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    cubeMinorThreshold J O α h N d c₀ η ≤ 1 / 2 :=
  polynomialSublevelThreshold_le_half _ _ (cubeMinorProbabilityConstant_pos O α h hN d).le
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

theorem cubeMinorThreshold_log_inv (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    Real.log (cubeMinorThreshold J O α h N d c₀ η)⁻¹ =
      Real.log 2 + Real.log (1 + cubeMinorProbabilityScale O N d c₀) +
        (N * d : ℕ) * Real.log (1 + 2 * cubeMinorProbabilityConstant O α h N d *
          (Fintype.card J + 1 : ℝ) / η) :=
  polynomialSublevelThreshold_log_inv _ _ (cubeMinorProbabilityConstant_pos O α h hN d).le
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem exists_cube_minor_thresholds {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    (d : ℕ) (hd : 0 < d) (hdeg : Fintype.card O * (h - 1) ≤ d)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|) :
    ∃ sel : J → O → Option α, ∀ η : ℝ, 0 < η →
      (∑ j, (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| <
          2 * cubeMinorThreshold J O α h N d c₀ η}) ≤ η / 2 := by
  choose sel hsel using (fun j => exists_allocated_cube_minor_probability_bound
    (c j) sets hsets h hh hcard (block j) (hblock j) e hN hc₀ (hc j))
  refine ⟨sel, ?_⟩
  intro η hη
  let K := cubeMinorProbabilityConstant O α h N d
  let scale := cubeMinorProbabilityScale O N d c₀
  let κ := cubeMinorThreshold J O α h N d c₀ η
  have hK : 0 < K := cubeMinorProbabilityConstant_pos O α h hN d
  have hscale : 0 < scale := cubeMinorProbabilityScale_pos O N d hc₀
  have hκ : 0 < κ := cubeMinorThreshold_pos J O α h hN d hc₀ hη
  have hp (j : J) : (blockCubeMeasure B (Fin h) α).real
      {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| < 2 * κ} ≤
        K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
    have hm : (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| < 2 * κ} ≤
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| ≤ 2 * κ} := by
      apply measureReal_mono
      · intro a ha
        change |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| ≤ 2 * κ
        exact le_of_lt ha
      · exact measure_ne_top _ _
    apply hm.trans
    have hb := hsel j d hd hdeg (2 * κ) (by positivity)
    simpa only [K, scale, cubeMinorProbabilityConstant, cubeMinorProbabilityScale, mul_div_assoc] using hb
  calc
    _ ≤ ∑ _j : J, K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = (Fintype.card J : ℝ) * K * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hK.le hscale.le hη

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def cubeMinorVariableCount (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) : ℕ :=
  Fintype.card O * (h * (Fintype.card α + 1))

def cubeMinorDegree (O : Type*) [Fintype O] (h : ℕ) : ℕ :=
  max 1 (Fintype.card O * (h - 1))

noncomputable def canonicalCubeMinorThreshold (J O α : Type*)
    [Fintype J] [Fintype O] [Fintype α] [DecidableEq α] (h : ℕ) (c₀ η : ℝ) : ℝ :=
  cubeMinorThreshold J O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ η

theorem canonicalCubeMinorThreshold_pos (J O α : Type*)
    [Fintype J] [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    {h : ℕ} (hh : 0 < h) {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    0 < canonicalCubeMinorThreshold J O α h c₀ η :=
  cubeMinorThreshold_pos J O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hη

theorem canonicalCubeMinorThreshold_le_half (J O α : Type*)
    [Fintype J] [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    {h : ℕ} (hh : 0 < h) {c₀ η : ℝ} (hc₀ : 0 < c₀) (hη : 0 < η) :
    canonicalCubeMinorThreshold J O α h c₀ η ≤ 1 / 2 :=
  cubeMinorThreshold_le_half J O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hη

theorem exists_canonical_cube_minor_thresholds {B O J α : Type*}
    [Fintype B] [Fintype O] [Nonempty O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|) :
    ∃ sel : J → O → Option α, ∀ η : ℝ, 0 < η →
      (∑ j, (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a| <
          2 * canonicalCubeMinorThreshold J O α h c₀ η}) ≤ η / 2 := by
  apply exists_cube_minor_thresholds c sets hsets h hh hcard block hblock
    (booleanBlockParameterEquiv O α h) (boolean_minor_parameter_count_pos O α hh)
    (cubeMinorDegree O h) _ _ hc₀ hc
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  · exact le_max_right _ _

end Erdos3

end

end OAI
