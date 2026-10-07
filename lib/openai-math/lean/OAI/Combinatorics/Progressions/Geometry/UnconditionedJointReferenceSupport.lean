import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

variable {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]

theorem selectedJointReference_trimmed_site_mem
    (root : K → ℤ) (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (W : Option K × I → ℝ)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (z : trimmedIntegerBox N margin × rectangularWeightIndices 0 W 1) :
    jointIntegerPhysicalSite root (z.1.val, z.2.val) ∈ integerBox N :=
  jointIntegerPhysicalSite_mem_box root N margin (fun i => (hmargin i).le) W hwidth z

theorem selectedJointReference_trimmed_domination
    (root : K → ℤ) (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1 / 2)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, 0 ≤ f x) :
    (selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) modulus T W hW hZ).mean
      (fun z => f (jointIntegerPhysicalSite root (z.1.val, z.2.val))) ≤
        2 * (𝔼 x ∈ integerBox N, f x) := by
  rw [selectedJointReference, FiniteProbabilityWeights.mean_prod]
  simp only [jointIntegerPhysicalSite]
  have he (a : I → ℤ) := selectedResidueFiniteLaw_mean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simp_rw [he]
  rw [FiniteProbabilityWeights.uniformFinset_mean (trimmedIntegerBox N margin)
    (trimmedIntegerBox_nonempty N margin hmargin)
    (fun a => ∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal *
      f (a + integerPhysicalSite root z))]
  exact selectedResidue_trimmed_reference_le root N margin hmargin hloss
    modulus T W hW hZ hwidth f hf

end Erdos3.BooleanCubeKernel

end

end OAI
