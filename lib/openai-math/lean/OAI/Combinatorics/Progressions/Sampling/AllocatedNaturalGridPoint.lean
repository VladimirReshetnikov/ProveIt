import OAI.Combinatorics.Progressions.Fourier.AllocatedSupportedResidueSpectrum

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

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

theorem allocatedActiveResidueSources_natural_volume (b : B ⟨j, Sum.inr i⟩) :
    (|((0 : ℤ) : ℝ)| + ((csource).length : ℝ)) *
      (∏ v : Fin (j.val + 1), (((sources) b v).length : ℝ)) ≤ 4 * (scale : ℝ) := by
  calc
    _ ≤ 4 * gamma * (basisAxisScale (basis j) i : ℝ) :=
      allocatedActiveResidueSources_volume B U basis S j i hactive q hq r hsize hR b
    _ ≤ 4 * (scale : ℝ) := by
      have hl := (allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).1
      linarith

noncomputable def allocatedNaturalGridPointApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) : ℂ :=
  if ∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4 * scale then
    weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
      scale M rows (fun _ => 0) shift z F
  else 0

theorem allocatedNaturalGridPoint_error_of_tail
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(((scale : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedNaturalGridPointApproximation B U basis hR S q r j i hactive hq hsize
        M rows shift z F‖ ≤ ε := by
  exact weightedModeratePointMass_error_cutoff (fun _ : B ⟨j, Sum.inr i⟩ => csource)
    sources (fun _ => 0) (by norm_num) (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
    (allocatedActiveResidueSources_natural_volume B U basis hR S q r j i hactive hq hsize)
    hM rows hrows shift z
    (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift)
    (allocatedSupportedResidueJetPMF_source B U basis hR hσ S q r hcell j i hactive hq hsize rows shift)
    F hε (by simpa only [Int.cast_zero] using htail)

theorem allocatedNaturalGridPointApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) :
    ‖allocatedNaturalGridPointApproximation B U basis hR S q r j i hactive hq hsize
      M rows shift z F‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) 1 + 1 := by
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
  have hcap := allocatedNaturalGridSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid hgamma A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMN rows hrows hB
  have hnorm := weightedModerateGridApproximation_norm_le_cap
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources scale M rows
    (fun _ => 0) shift z F hscale (by simpa only [Int.cast_zero] using hcap)
  unfold allocatedNaturalGridPointApproximation
  split_ifs
  · exact hnorm
  · simpa only [norm_zero] using (norm_nonneg _).trans hnorm

noncomputable def allocatedNaturalGridBudgetApproximation (P ε : ℝ)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ) : ℂ :=
  allocatedNaturalGridPointApproximation B U basis hR S q r j i hactive hq hsize M rows shift z
    (positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε))

theorem allocatedNaturalGridBudgetApproximation_error
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (shift z : rows → ℤ) :
    ‖(((scale : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedNaturalGridBudgetApproximation B U basis hR S q r j i hactive hq hsize
        P ε M rows shift z‖ ≤ ε := by
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  exact allocatedNaturalGridPoint_error_of_tail B U basis hR hσ S q r j i hactive hq hsize hcell
    hM rows hrows shift z _ hε.le
    (allocatedNaturalGridSpectrum_tail B U basis hR S j i hactive q hq r hsize
      hgrid hgamma A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
      hMN rows hrows hB hε hε1)

end Erdos3.VectorPolynomial

end

end OAI
