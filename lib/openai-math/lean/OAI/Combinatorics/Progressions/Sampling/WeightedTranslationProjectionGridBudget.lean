import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

universe u v

private theorem projection_dimension_cost (d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p + (p + 1) ^ d ≤ (p + 2) ^ (d + 1) := by
  have hpow : 1 ≤ (p + 2) ^ d := one_le_pow₀ (by linarith)
  calc
    p + (p + 1) ^ d ≤ p * (p + 2) ^ d + (p + 2) ^ d := by
      exact add_le_add (by nlinarith) (pow_le_pow_left₀ (by linarith) (by linarith) d)
    _ = (p + 1) * (p + 2) ^ d := by ring
    _ ≤ (p + 2) * (p + 2) ^ d := by gcongr; linarith
    _ = (p + 2) ^ (d + 1) := by rw [pow_succ]; ring

theorem projection_grid_power_le_exp (d n r H m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p + (p + 1) ^ d) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (p + 1)) (hm : (m : ℝ) ≤ Real.exp p) :
    ((H ^ (n * r) * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (d + 4)) := by
  have ht : 1 ≤ p + 2 := by linarith
  have hn' := hn.trans (projection_dimension_cost d hp)
  have hexponent : ((n * r : ℕ) : ℝ) * (p + 1) + p ≤ (p + 2) ^ (d + 4) := by
    have hfirst : ((n * r : ℕ) : ℝ) * (p + 1) ≤ (p + 2) ^ (d + 3) := by
      calc
        _ ≤ (p + 2) ^ (d + 1) * (p + 2) * (p + 2) := by
          rw [Nat.cast_mul]
          apply mul_le_mul
          · exact mul_le_mul hn' (hr.trans (by linarith)) (Nat.cast_nonneg _) (by positivity)
          · linarith
          · linarith
          · positivity
        _ = _ := by simp only [pow_succ]
    have hpterm : p ≤ (p + 2) ^ (d + 3) :=
      (by linarith : p ≤ p + 2).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ ht (show 1 ≤ d + 3 by omega))
    calc
      _ ≤ 2 * (p + 2) ^ (d + 3) := by linarith
      _ ≤ (p + 2) * (p + 2) ^ (d + 3) := by gcongr; linarith
      _ = _ := by rw [show d + 4 = (d + 3) + 1 by omega, pow_succ]; ring
  calc
    _ ≤ (Real.exp (p + 1)) ^ (n * r) * Real.exp p := by
      simp only [Nat.cast_mul, Nat.cast_pow]
      exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) hm
        (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (((n * r : ℕ) : ℝ) * (p + 1) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

variable {σ : Type u} {ι : Type v} [Fintype σ] [Fintype ι]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

include hw in
theorem weightedTranslationProjectionGrid_le_exp {p : ℝ} (hp : 0 ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp p) :
    ((⌈Real.exp p⌉₊ ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m : ℕ) : ℝ)
      ≤ Real.exp ((p + 2) ^ (d + 4)) := by
  apply projection_grid_power_le_exp d _ _ _ _ hp _ hι (ceil_exp_le_exp_add_one hp) hm
  have hcard := weightedBasisIndex_card_le w d hw
  have hcast : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤
      (Fintype.card σ : ℝ) + ((Fintype.card σ : ℝ) + 1) ^ d := by exact_mod_cast hcard
  exact hcast.trans (add_le_add hσ (pow_le_pow_left₀ (by positivity) (by linarith) d))

include hw in
theorem weightedTranslationProjectionGrid_fixed_degree {p : ℝ} (hp : 0 ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp p) :
    ((⌈Real.exp p⌉₊ ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m : ℕ) : ℝ)
      ≤ Real.exp ((p + (d + 4 : ℕ)) ^ (d + 4)) := by
  apply (weightedTranslationProjectionGrid_le_exp w d hw hp hσ hι m hm).trans
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (by linarith) (by push_cast; linarith) _

include hw in

theorem weightedBasisIndex_card_le_pair_basis
    {L : Type u} [LieRing L] [LieAlgebra ℚ L]
    (b : Module.Basis ι ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L)) :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card ι := by
  let : Module.Finite ℚ
      (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) :=
    b.finiteDimensional_of_finite
  have hproj := LinearMap.finrank_le_finrank_of_surjective
    (LinearMap.proj_surjective (R := ℚ) (φ := BoolLieFamily (weightedSubalgebra w d) L) true)
  change Module.finrank ℚ (weightedSubalgebra w d) ≤
    Module.finrank ℚ (RationalFilteredNilmanifold.PairAlgebra (weightedSubalgebra w d) L) at hproj
  rw [Module.finrank_eq_card_basis (weightedBasis w d hw),
    Module.finrank_eq_card_basis b] at hproj
  exact hproj

end Erdos3.PolynomialTranslationLie

end

end OAI
