import OAI.Combinatorics.Progressions.Sampling.AllocatedTranslatedCutoffSampling

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
variable (r : ℝ≥0) (hr : 0 < r) (hR₀ : ∀ j, 0 < R₀ j) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

variable (rowSets : Fin m → Finset (Finset (Fin dim)))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

variable (hbudgetRows : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (r : ℝ) * R₀ j)))) ≤ 1 / 4)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (κ : ℝ≥0) (hκ : ∀ j, (R₀ j)⁻¹ ≤ κ)

local notation "kernelLip" => (ampN * (Fintype.card (Finset (Fin dim)) *
  (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
    (κ * ∑ j, D j * Fintype.card (J j))) * ∑ j, (Finset.card (rowSets j) : ℝ≥0))))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets r *
  (2 * ((2 : ℝ) ^ dim * (2 * (r : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

include hR₀ hσ1 hC hchart hbudgetRows hb bW hD hκ in
theorem allocatedNormalizedCutoff_reference_envelope {K : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim K rowTypes rows)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P : ℝ} (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d] (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P) (hρ : 0 < ρ) (hε : 0 < ε)
    (hρP : 1 / ρ ≤ Real.exp P) (hεP : 1 / ε ≤ Real.exp P)
    (hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ (N x : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) R (U j) (p j))
    (hR : Real.exp ((P + K) ^ K) ≤ R)
    {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hamb : (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ L)
    (hηL : η⁻¹ ≤ Real.exp L) (hLip : (kernelLip : ℝ) ≤ Real.exp L)
    (hfreqP : Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P)
    (hcoeffP : Real.exp (2 * L * (2 * L + 2) ^ 4) * amp ≤ Real.exp P)
    (base : X → ℤ) (cell : ColumnResiduePattern (Option (Fin dim)) X stride) :
    let V := referenceJetEnvelopeWidths (q := dim) stride (trimmedSpatialRootScale ρ N stride)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {cell} V z,
      selectedResidueDensityMass stride {cell} V
        (fun z => amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
          (physicalCubeRowSample U d rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤
        massCap + 2 * η + ε := by
  intro V
  have hN (t : X) : (0 : ℝ) < N t := (Real.exp_pos _).trans_le (hsize t)
  have hV (z : Option (Fin dim) × X) : 0 < V z := by
    change 0 < referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    exact mul_pos (mul_pos (by norm_num) hρ) (hN z.2)
  have hwidth (z : Option (Fin dim) × X) : ρ * (N z.2 : ℝ) ≤ V z := by
    change _ ≤ referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    nlinarith only [mul_pos hρ (hN z.2)]
  exact allocatedNormalizedCutoff_sampled_translate (X := X) (J := J) B U b o S r hr hR₀ hσ1 C hC hchart
    rowSets hbudgetRows hb bW D hD κ hκ hSampling hP hn hdim μ ν p hp hm
    d stride hs hS hSP hρ hε hρP hεP hstride (fun t => (N t : ℝ)) hsize hrank hR
    {cell} (Finset.singleton_nonempty cell) V hV hwidth hη hL hamb hηL hLip hfreqP hcoeffP base

end Erdos3.BooleanCubeKernel

end

end OAI
