import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedPointBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

noncomputable def allocatedSupportedPhysicalGridPMF
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) : PMF (rows → ℤ) :=
  (conditioned).toPMF.bind (fun y =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
      (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
noncomputable def allocatedSupportedPhysicalPointApproximation
    (P ε : ℝ) (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ) : ℂ :=
  ∑' c : ℤ, (((constantLaw) c).toReal : ℂ) *
    allocatedSupportedPointApproximation B U basis hR S q r j i hactive hq hsize P ε M rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z

theorem allocatedSupportedPhysicalPointApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ) -
      allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r j i hactive hq hsize
        P ε M rows z‖ ≤ ε := by
  unfold allocatedSupportedPhysicalGridPMF allocatedSupportedPhysicalPointApproximation
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_point_error (constantLaw)
    (fun c => allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t))
    (fun c => allocatedSupportedPointApproximation B U basis hR S q r j i hactive hq hsize P ε M rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z)
    (pow_nonneg (Nat.cast_nonneg _) _) z
  intro c
  exact allocatedSupportedPointApproximation_error B U basis hR hσ S q r hcell j i hactive hq hsize
    hgrid A hA P hcP hsP hM rows hrows hB hε hε1 _ z

end Erdos3.VectorPolynomial

end

end OAI
