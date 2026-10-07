import OAI.Combinatorics.Progressions.Polynomial.FiniteMarginalLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CylinderRemovalChain.uniform_section_bounds {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P : ℝ} {j r q b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hK : 1 ≤ K) (hτ : 0 < τ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hq : 2 ≤ q) (heven : Even q)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max (j + r * (q + 1)) (2 * b + j)))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
          (8 * (1 + K) * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤ 3 * τ⁻¹ := by
  have hlo := hchain.low_degree_bounds hμ hK hτ hη0 hq heven hrP hlog hPq hqP hsmall
    (ProductMarginalsClose.mono μ hclose (le_max_left _ _)) hw
  intro cf hcf
  refine ⟨hlo cf hcf, ?_⟩
  obtain ⟨hsize, hmass⟩ := hchain.removed_size_mass cf hcf
  have hweight : ∀ z, 0 ≤ cf.2 z ∧ cf.2 z ≤ 1 :=
    removedCylinderWeights_bounds F w cs (fun z => (hw z).1) (fun z => (hw z).2)
      (List.of_mem_zip hcf).2
  have hz : (FiniteProbabilityWeights.pi μ).weight (cf.1.assignment base) ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (cf.1.assignment base i))).ne'
  have hinv : (cf.1.mass μ base (observedProductDensity μ p F cf.2))⁻¹ ≤ τ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hτ hmass.le
  exact observedProductDensity_scaled_section_norm μ p F cf.2 hweight (hτ.trans hmass) hinv
    cf.1.1 cf.1.1 le_rfl (cf.1.assignment base) hz hη0 hη1 _
    (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS)
    (ProductMarginalsClose.mono μ hclose (by omega)) herr

end Erdos3

end

end OAI
