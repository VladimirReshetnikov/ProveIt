import OAI.Combinatorics.Progressions.Estimates.FixedObservableCorrelation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_niltest_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : D.filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → D.Niltest w,
            (∀ i, (A i).orbit = g) ∧
            (∀ i, (A i).UnitIntervalValued) ∧
            (∀ i, (A i).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ i, ((A i).observable z).re = 1) ∧
            (letI := D.metricSpace
             ∀ i x y, 0 < ((A i).observable x).re → 0 < ((A i).observable y).re → dist x y ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_positive_partition s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w p ρ hp hD hρ hρinv g
  obtain ⟨n, hn, hnb, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ := hpartition D hp hD hρ hρinv
  have hcost : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hB0 : 0 ≤ (p + B) ^ B := pow_nonneg (by positivity) _
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp ((p + B) ^ B) := Real.one_le_exp hB0
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hle : 3 + (K : ℝ) ≤ Real.exp ((p + B) ^ B + 2) := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg ((p + B) ^ B))]
    exact hle.trans (Real.exp_le_exp.mpr (by linarith))
  let A : Fin n → D.Niltest w := fun i =>
    D.sectionNiltest g (fun z (_ : Unit) => ψ i z) (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hBC), A, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    exact D.sectionNiltest_unit_interval g _ _ K _ (some ())
  · intro i
    exact D.sectionNiltest_complexityLE g _ _ K _ (some ()) (hD.mono D hpC) hlog
  · intro z
    change ∑ i, ψ i z = 1
    exact hsum z
  · let := D.metricSpace
    intro i x y hx hy
    exact hdiam i x y hx hy

end Erdos3.RationalFilteredNilmanifold

end

end OAI
