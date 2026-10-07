import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalPointMixture
import OAI.Combinatorics.Progressions.Probability.AllocatedPlateauPointMixture
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridFamilyAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)

noncomputable def allocatedBudgetedPlateauApproximation (P ε : ℝ)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ) : ℂ :=
  allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z
    (positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε))

theorem allocatedBudgetedPlateauApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (ε : ℝ) (z : rows → ℤ) :
    ‖allocatedBudgetedPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize
      P ε M rows z‖ ≤ allocatedGridPointCap B P ⟨j, i⟩ rows := by
  exact allocatedConstantPlateauApproximation_norm_le B U basis hR hσ S q r j i hactive hq hsize
    hgrid hgamma L hL P hcP hsP hM rows hrows hB z _

theorem allocatedBudgetedPlateauApproximation_error
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((scale : ℝ) ^ rows.card *
        (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ) -
      allocatedBudgetedPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize
        P ε M rows z‖ ≤ ε := by
  exact allocatedConstantPlateauApproximation_error B U basis hR hσ S q r hcell j i hactive hq hsize
    hgrid hgamma hM L hL P hcP hsP rows hrows hB hε hε1 x z

end Erdos3.VectorPolynomial

end

end OAI
