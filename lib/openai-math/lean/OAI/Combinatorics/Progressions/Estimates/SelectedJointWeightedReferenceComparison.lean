import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedJointFiniteLaw_weighted_reference_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
          (f a z * (D a z : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * f a z‖ ≤ ε) :
    ‖(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).complexMean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).complexMean
        (fun z => f z.1.val z.2.val)‖ ≤ η + ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T V hV hZ
  let test (z : A × rectangularWeightIndices 0 V 1) := f z.1.val z.2.val
  let density (z : A × rectangularWeightIndices 0 V 1) := D z.1.val z.2.val
  have hraw := p.norm_complexMean_sub_le
    (fun a => q.complexMean (fun z => (D a.val z.val : ℂ) * f a.val z.val))
    (fun a => q.complexMean (fun z => f a.val z.val)) (fun _ => ε) (by
      intro a _
      change ‖(selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => (D a.val z.val : ℂ) * f a.val z.val) -
        (selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => f a.val z.val)‖ ≤ ε
      rw [selectedResidueFiniteLaw_complexMean modulus T V hV hZ
          (fun z => (D a.val z : ℂ) * f a.val z),
        selectedResidueFiniteLaw_complexMean modulus T V hV hZ (f a.val)]
      simpa only [mul_comm (D a.val _ : ℂ)] using htest a.val)
  rw [p.mean_const] at hraw
  have hraw' : ‖(p.prod q).complexMean (fun z => (density z : ℂ) * test z) -
      (p.prod q).complexMean test‖ ≤ ε := by
    simpa only [FiniteProbabilityWeights.complexMean_prod, density, test] using hraw
  have hglobal : 0 < (selectedJointReference A hA modulus T V hV hZ).mean density := by
    rw [selectedJointReference_densityMass]
    exact hD
  have hnorm := (selectedJointReference A hA modulus T V hV hZ).normalizedDensityTest_remove_normalization
    density (fun z => hD0 z.1.val z.2.val) hglobal test (fun z => hf z.1.val z.2.val)
  rw [selectedJointReference_densityMass] at hnorm
  have hnorm' := hnorm.trans (selectedJointDensityMass_close A hA modulus T V D hmass)
  rw [selectedJointFiniteLaw_complexMean]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnorm' hraw')

theorem selectedJointFiniteLaw_weighted_reference_real_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * (f a z * D a z)) -
        ∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * f a z| ≤ ε) :
    |(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).mean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).mean
        (fun z => f z.1.val z.2.val)| ≤ η + ε := by
  have h := selectedJointFiniteLaw_weighted_reference_comparison A hA modulus T V hV hZ
    D hD0 hD (fun a z => (f a z : ℂ))
    (fun a z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf a z)
    hmass (fun a => by
      simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using htest a)
  simpa only [FiniteProbabilityWeights.complexMean_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

end Erdos3

end

end OAI
