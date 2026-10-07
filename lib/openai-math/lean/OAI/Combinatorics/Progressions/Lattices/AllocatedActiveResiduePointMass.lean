import OAI.Combinatorics.Progressions.Fourier.AllocatedSupportedResidueSpectrum

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
noncomputable def allocatedActiveResiduePointApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) : ℂ :=
  if ∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩))
        (4 * gamma) * basisAxisScale (basis j) i then
    weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
      (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F
  else 0

theorem allocatedActiveResiduePointMass_error_of_tail
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedActiveResiduePointApproximation B U basis hR S q r j i hactive hq hsize
        M rows shift z F‖ ≤ ε := by
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  exact weightedModeratePointMass_error_cutoff (fun _ : B ⟨j, Sum.inr i⟩ => csource)
    sources (fun _ => 0) (by positivity) (basisAxisScale_pos (basis j) i)
    (allocatedActiveResidueSources_volume B U basis S j i hactive q hq r hsize hR)
    hM rows hrows shift z
    (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift)
    (allocatedSupportedResidueJetPMF_source B U basis hR hσ S q r hcell j i hactive hq hsize rows shift)
    F hε (by
      simp only [Int.cast_zero]
      exact htail)

theorem allocatedActiveResiduePointMass_error_of_grid
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ζ ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P ((torus : ℝ) / (2 * gamma)) *
        2 ^ positiveModerateSpectrumExponent j.val rows.card +
      (torus : ℝ) ^ rows.card *
        (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^
          ((layerTailDegree m + 1) * rows.card)) * ζ ≤ ε)
    (shift z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedActiveResiduePointApproximation B U basis hR S q r j i hactive hq hsize
        M rows shift z
          (positiveModerateSpectrumCover rows M j.val P ((torus : ℝ) / (2 * gamma)) S.value ζ)‖ ≤ ε := by
  have hMK : (M : ℝ) ≤ (torus : ℝ) * basisAxisScale (basis j) i := by
    simp only [hM, Nat.cast_mul, le_refl]
  apply allocatedActiveResiduePointMass_error_of_tail B U basis hR hσ S q r hcell j i hactive hq hsize
    hM rows hrows shift z _ hε
  exact allocatedActiveResidueSpectrum_tail B U basis S j i hactive q hq r hsize hR
    A hA P hcP hsP (Nat.cast_nonneg torus) (pow_nonneg (Nat.cast_nonneg torus) _)
    hζ hζ1 hε (Nat.pos_of_ne_zero (NeZero.ne M)) hMK rows hrows hB
    (allocatedGrid_modulus_cardinality B U basis S j i hgrid (Nat.cast_nonneg torus) hMK rows.card)
    haccuracy

end Erdos3.VectorPolynomial

end

end OAI
