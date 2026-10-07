import Mathlib.Analysis.InnerProductSpace.PiL2
import OAI.Combinatorics.Progressions.Estimates.NormalizedVectorLipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem euclidean_norm_le_card_add_one_mul {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    ‖v‖ ≤ (Fintype.card I + 1 : ℝ) * M := by
  have hsq : ‖v‖ ^ 2 ≤ (Fintype.card I : ℝ) * M ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (Fintype.card I : ℝ) ≤ (Fintype.card I + 1 : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hbound := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
  nlinarith [norm_nonneg v, mul_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card I + 1) hM]

theorem lipschitzWith_complex_vector {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {K : ℝ≥0} (hu : ∀ i, LipschitzWith K (u i)) :
    LipschitzWith ((Fintype.card I + 1 : ℝ≥0) * K)
      (fun x => (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have h := euclidean_norm_le_card_add_one_mul
    ((WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I) - WithLp.toLp 2 (fun i => u i y))
    (M := (K : ℝ) * dist x y) (by positivity) (fun i => by
      simpa only [PiLp.sub_apply, PiLp.toLp_apply, dist_eq_norm] using (hu i).dist_le_mul x y)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_assoc] using h

theorem normalize_complex_unit_smul {I : Type*} [Fintype I]
    (c : ℂ) (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ I) :
    NormedSpace.normalize (c • v) = c • NormedSpace.normalize v := by
  unfold NormedSpace.normalize
  rw [norm_smul, hc, one_mul]
  exact smul_comm _ _ _

theorem exists_normalized_complex_family {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {rho K : ℝ≥0} (hrho : 0 < rho)
    (hLip : ∀ i, LipschitzWith K (u i)) (hlower : ∀ x, ∃ i, (rho : ℝ) ≤ ‖u i x‖) :
    ∃ v : I → X → ℂ,
      (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖v i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (2 / rho * ((Fintype.card I + 1 : ℝ≥0) * K)) (v i)) ∧
      ∀ x y c, ‖c‖ = 1 → (∀ i, u i x = c * u i y) → ∀ i, v i x = c * v i y := by
  let U (x : X) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => u i x)
  have hnorm (x : X) : (rho : ℝ) ≤ ‖U x‖ := by
    obtain ⟨i, hi⟩ := hlower x
    exact hi.trans (PiLp.norm_apply_le (U x) i)
  have hne (x : X) : U x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hrho (hnorm x))
  have hone (x : X) : ‖NormedSpace.normalize (U x)‖ = 1 := NormedSpace.norm_normalize (hne x)
  let v (i : I) (x : X) := NormedSpace.normalize (U x) i
  have hvLip := lipschitzWith_normalize U hrho (lipschitzWith_complex_vector u hLip) hnorm
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [← EuclideanSpace.norm_sq_eq, hone, one_pow]
  · intro i x
    exact (PiLp.norm_apply_le (NormedSpace.normalize (U x)) i).trans_eq (hone x)
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (PiLp.dist_apply_le (NormedSpace.normalize (U x)) (NormedSpace.normalize (U y)) i).trans
      (hvLip.dist_le_mul x y)
  · intro x y c hc hu i
    have heq : U x = c • U y := by
      ext j
      exact hu j
    change NormedSpace.normalize (U x) i = c * NormedSpace.normalize (U y) i
    rw [heq, normalize_complex_unit_smul c hc]
    rfl

end Erdos3

end

end OAI
