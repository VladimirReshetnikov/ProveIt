import OAI.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem polynomialDensity_principalTuple_riemann {D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [Fintype J] [Fintype N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (p : I → N → MvPolynomial (JointBlockParameter B h α) ℝ)
    {degree : ℕ} (hdegree : ∀ i n, (p i n).totalDegree ≤ degree)
    (C R H K S : ℝ≥0) (hc : ∀ i n, realPolynomialMass (p i n) ≤ C)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith K f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (v : I → ℝ) :
    let ρ := fun x => pivotOutputDensity A (splitFreeColumns F (polynomialColumns p x)) (splitFreeProfile f g) v
    let Lip := pivotKernelLip J A R K *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree C) * S
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => ρ (fun s => (z ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) -
      ∫ x, ρ x ∂jointBooleanSource h| ≤
      (2 * (pivotKernelCap J A R H : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + Lip) *
        ∑ j, (M j : ℝ)/L j := by
  dsimp only
  apply principalTuple_residue_riemann_on_box B h L M hL m r hm hmM hsize hsmall
    (fun x => pivotOutputDensity A (splitFreeColumns F (polynomialColumns p x)) (splitFreeProfile f g) v)
  · exact splitPivotDensity_parameter_lipschitzOn A F (polynomialColumns p) (Metric.closedBall 0 1)
      _ R K S (polynomialColumns_lipschitzOn_box p hdegree C hc) hf hg hfs hgs hg0 hgmass v
  · exact (pivotKernelCap J A R H).coe_nonneg
  · intro x _
    exact splitPivotDensity_norm_le_cap A F (polynomialColumns p x) R H S hf.continuous hg hfs hgs hfb hg0 hgmass v

end Erdos3

end

end OAI
