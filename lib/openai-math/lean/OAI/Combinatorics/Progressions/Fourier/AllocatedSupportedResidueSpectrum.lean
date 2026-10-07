import OAI.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
import OAI.Combinatorics.Progressions.Sampling.CeilGridScaleRatio

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize

variable (hR : ∀ j, 0 < R j)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedActiveResidueSources_volume
    (b : B ⟨j, Sum.inr i⟩) :
    (|((0 : ℤ) : ℝ)| + ((csource).length : ℝ)) *
      (∏ v : Fin (j.val + 1), (((sources) b v).length : ℝ)) ≤
        4 * gamma * (basisAxisScale (basis j) i : ℝ) := by
  simpa only [Int.cast_zero, abs_zero, zero_add,
    allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).2

theorem allocatedActiveResidueSpectrum_tail
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C W ζ ε : ℝ} {t M : ℕ} (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (C / (2 * gamma)) *
        2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε) :
    spectrumTail
      (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value ζ)
      (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
        weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε := by
  have hc : ScalarCubePrimitiveBudget csource A P :=
    (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      ScalarCubePrimitiveBudget ((sources) b v) A P :=
    (allocatedActiveResidueSources_primitive B U basis S j i hactive q hq r hsize b v A).mono hsP
  have hlength (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      (S.value : ℝ) ≤ ((sources) b v).length := by
    rw [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize b v]
  have hproduct (b : B ⟨j, Sum.inr i⟩) :
      (∏ v : Fin (j.val + 1), (((sources) b v).length : ℝ)) =
        (S.value : ℝ) ^ (j.val + 1) := by
    simp only [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hscale (b : B ⟨j, Sum.inr i⟩) :
      (M : ℝ) / (((csource).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤
        C / (2 * gamma) := by
    rw [hproduct b]
    exact allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  exact weightedPositiveModerate_uniform_spectrum_tail
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources A hA hc.one_le (fun _ => hc) hs
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    (div_nonneg hC (by positivity)) hW (Nat.cast_nonneg S.value) hζ hζ1 hε hlength hM hscale
    rows hrows hB hcard haccuracy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

theorem allocatedNaturalGridSpectrum_tail
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {H ε : ℝ} {M : ℕ} (hH : 0 ≤ H) (hM : 0 < M)
    (hMN : (M : ℝ) ≤ H * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    spectrumTail (positiveModerateSpectrumCover rows M j.val P H S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P H ((2 * H) ^ rows.card) ε))
      (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
        weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε := by
  have hc : ScalarCubePrimitiveBudget csource A P :=
    (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      ScalarCubePrimitiveBudget ((sources) b v) A P :=
    (allocatedActiveResidueSources_primitive B U basis S j i hactive q hq r hsize b v A).mono hsP
  have hlength (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      (S.value : ℝ) ≤ ((sources) b v).length := by
    rw [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize b v]
  have hscale (b : B ⟨j, Sum.inr i⟩) :
      (M : ℝ) / (((csource).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ H := by
    simp only [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact allocatedPrincipalGridScale_ratio B U basis hR S j i hactive hH hMN
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec j.val rows.card
    ((layerTailDegree m + 2) * rows.card) (V := H) hc.one_le
    (by positivity : (0 : ℝ) ≤ (2 * H) ^ rows.card) hε hε1
  exact weightedPositiveModerate_uniform_spectrum_tail
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources A hA hc.one_le (fun _ => hc) hs
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hH (by positivity : (0 : ℝ) ≤ (2 * H) ^ rows.card) (Nat.cast_nonneg S.value)
    hζ hζ1 hε.le hlength hM hscale rows hrows hB
    (allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive hgrid hgamma hH hMN rows.card)
    hacc

theorem allocatedNaturalGridSpectrum_absolute_cap
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {H : ℝ} {M : ℕ} (hH : 0 ≤ H) (hM : 0 < M)
    (hMN : (M : ℝ) ≤ H * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    (∑ k, ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤
        positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
          P H ((2 * H) ^ rows.card) 1 + 1 := by
  have hP := ((allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP).one_le
  have ht := allocatedNaturalGridSpectrum_tail B U basis hR S j i hactive q hq r hsize
    hgrid hgamma A hA P hcP hsP hH hM hMN rows hrows hB zero_lt_one le_rfl
  exact weightedPositiveModerateSpectrum_absolute_cap
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources M ((layerTailDegree m + 2) * rows.card) rows
    hP hH (by positivity : (0 : ℝ) ≤ (2 * H) ^ rows.card) (Nat.cast_nonneg S.value)
    (allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive hgrid hgamma hH hMN rows.card) ht

omit [Fintype α] in
include hR hactive in
theorem allocatedNaturalGridSpectrum_cover_card
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) {P H ε : ℝ} {M : ℕ}
    (hP : 1 ≤ P) (hH : 0 ≤ H) (hMN : (M : ℝ) ≤ H * scale)
    (rows : Finset (Finset α)) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((positiveModerateSpectrumCover rows M j.val P H S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P H ((2 * H) ^ rows.card) ε)).card : ℝ) ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P H ((2 * H) ^ rows.card) ε := by
  have hc := positiveModerateSpectrumCover_card_budget rows M j.val
    ((layerTailDegree m + 2) * rows.card) hP hH
    (by positivity : (0 : ℝ) ≤ (2 * H) ^ rows.card) (Nat.cast_nonneg S.value) hε hε1
    (by simpa only [Fintype.card_coe] using
      allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive hgrid hgamma hH hMN rows.card)
  simpa only [Fintype.card_coe] using hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSupportedResidueSpectrum_tail
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C ε : ℝ} {M : ℕ} (hC : 0 ≤ C) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    spectrumTail (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P (C / (2 * gamma)) (C ^ rows.card) ε))
      (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
        weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε := by
  have hP := ((allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP).one_le
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec j.val rows.card
    ((layerTailDegree m + 1) * rows.card) (V := C / (2 * gamma))
    hP (pow_nonneg hC _) hε hε1
  exact allocatedActiveResidueSpectrum_tail B U basis S j i hactive q hq r hsize hR
    A hA P hcP hsP hC (pow_nonneg hC _) hζ hζ1 hε.le hM hMK rows hrows hB
    (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card) hacc

theorem allocatedSupportedResidueSpectrum_absolute_cap
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C : ℝ} {M : ℕ} (hC : 0 ≤ C) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    (∑ k, ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤
        positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 1) * rows.card)
          P (C / (2 * gamma)) (C ^ rows.card) 1 + 1 := by
  have hP := ((allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP).one_le
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have ht := allocatedSupportedResidueSpectrum_tail B U basis hR S j i hactive q hq r hsize
    hgrid A hA P hcP hsP hC hM hMK rows hrows hB zero_lt_one le_rfl
  exact weightedPositiveModerateSpectrum_absolute_cap
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources M ((layerTailDegree m + 1) * rows.card) rows
    hP (div_nonneg hC (by positivity)) (pow_nonneg hC _) (Nat.cast_nonneg S.value)
    (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card) ht

end Erdos3.VectorPolynomial

end

end OAI
