import OAI.Combinatorics.Progressions.Probability.AmbientTentMass

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem ambientTentMass_pos {G J : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [Fintype J]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : G →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q) :
    0 < ambientTentMass μ f q :=
  lt_of_lt_of_le (by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity)
    (ambientTentMass_lower μ f hf hq)

theorem ambientTentMass_inv_le {G J : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [Fintype J]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : G →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q) :
    1 / ambientTentMass μ f q ≤ 2 * (q : ℝ) ^ Fintype.card J := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hl := (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ) ^ Fintype.card J)).mp
    (ambientTentMass_lower μ f hf hq)
  apply (div_le_iff₀ (ambientTentMass_pos μ f hf hq)).mpr
  nlinarith

noncomputable def normalizedAmbientTent {G J : Type*} [MeasurableSpace G] [Fintype J]
    (μ : Measure G) (f : G → J → UnitAddCircle) (q : ℕ) (x : J → UnitAddCircle) : ℝ :=
  ambientTorusTent q x / ambientTentMass μ f q

theorem normalizedAmbientTent_lipschitz {G J : Type*} [MeasurableSpace G] [Fintype J]
    (μ : Measure G) (f : G → J → UnitAddCircle) (q : ℕ)
    (hz : 0 < ambientTentMass μ f q)
    (hinv : 1 / ambientTentMass μ f q ≤ 2 * (q : ℝ) ^ Fintype.card J) :
    LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1)) (normalizedAmbientTent μ f q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  simp only [NNReal.coe_pow, NNReal.coe_natCast]
  change |ambientTorusTent q x / ambientTentMass μ f q -
    ambientTorusTent q y / ambientTentMass μ f q| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hz]
  have h := (ambientTorusTent_lipschitz (J := J) q).dist_le_mul x y
  rw [Real.dist_eq] at h
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  calc
    _ ≤ (((q : ℝ) / 4) * dist x y) / ambientTentMass μ f q := by
      apply div_le_div_of_nonneg_right _ hz.le
      simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] using h
    _ = ((q : ℝ) / 4 * (1 / ambientTentMass μ f q)) * dist x y := by ring
    _ ≤ ((q : ℝ) / 4 * (2 * (q : ℝ) ^ Fintype.card J)) * dist x y := by gcongr
    _ ≤ (q : ℝ) ^ (Fintype.card J + 1) * dist x y := by
      rw [pow_succ]
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      nlinarith [pow_nonneg hq (Fintype.card J)]

theorem exists_normalized_ambient_tent {G J : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [Fintype J]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : G →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q) :
    ∃ F : (J → UnitAddCircle) → ℝ,
      (∀ x, 0 ≤ F x ∧ F x ≤ 2 * (q : ℝ) ^ Fintype.card J) ∧
      LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1)) F ∧
      (∀ x, F x ≠ 0 → ‖x‖ < 4 / (q : ℝ)) ∧
      Integrable (fun x => F (f x)) μ ∧ (∫ x, F (f x) ∂μ) = 1 := by
  have hz := ambientTentMass_pos μ f hf hq
  have hi := ambientTentMass_inv_le μ f hf hq
  refine ⟨normalizedAmbientTent μ f q, ?_, normalizedAmbientTent_lipschitz μ f q hz hi, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (ambientTorusTent_range q x).1 hz.le, ?_⟩
    exact (div_le_div_of_nonneg_right (ambientTorusTent_range q x).2 hz.le).trans hi
  · intro x hx
    apply ambientTorusTent_support hq x
    intro he
    exact hx (by simp only [normalizedAmbientTent, he, zero_div])
  · exact (ambientTorusTent_integrable μ f hf q).div_const _
  · change (∫ x, ambientTorusTent q (f x) / ambientTentMass μ f q ∂μ) = 1
    rw [integral_div]
    exact div_self hz.ne'

end Erdos3

end

end OAI
