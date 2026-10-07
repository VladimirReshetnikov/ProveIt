import OAI.Combinatorics.Progressions.Lattices.AllocatedActiveResiduePointMass

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

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
noncomputable def allocatedSupportedPointApproximation
    (P ε : ℝ) (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ) : ℂ :=
  allocatedActiveResiduePointApproximation B U basis hR S q r j i hactive hq hsize M rows shift z
    (positiveModerateSpectrumCover rows M j.val P ((torus : ℝ) / (2 * gamma)) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P ((torus : ℝ) / (2 * gamma)) ((torus : ℝ) ^ rows.card) ε))

theorem allocatedSupportedPointApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (shift z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedSupportedPointApproximation B U basis hR S q r j i hactive hq hsize
        P ε M rows shift z‖ ≤ ε := by
  have hMK : (M : ℝ) ≤ (torus : ℝ) * basisAxisScale (basis j) i := by
    simp only [hM, Nat.cast_mul, le_refl]
  unfold allocatedSupportedPointApproximation
  apply allocatedActiveResiduePointMass_error_of_tail B U basis hR hσ S q r hcell j i hactive hq hsize
    hM rows hrows shift z _ hε.le
  exact allocatedSupportedResidueSpectrum_tail B U basis hR S j i hactive q hq r hsize
    hgrid A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMK rows hrows hB hε hε1

end Erdos3.VectorPolynomial

end

end OAI
