import OAI.Combinatorics.Progressions.Lattices.AllocatedActiveResiduePointMass
import OAI.Combinatorics.Progressions.Sampling.AllocatedNaturalGridPoint

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

noncomputable def allocatedConstantPointApproximation (M : ℕ) [NeZero M]
    (rows : Finset (Finset α)) (z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  ∫ c, allocatedActiveResiduePointApproximation B U basis hR S q r j i hactive hq hsize M rows
    (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F ∂(constantLaw).toMeasure

theorem allocatedConstantPointMixture_error_of_tail
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((conditioned).toPMF.bind (fun y => integerMatrixImagePMF
          (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
            (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))) z).toReal : ℝ) : ℂ) -
      allocatedConstantPointApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F‖ ≤ ε := by
  unfold allocatedConstantPointApproximation
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro c
  exact allocatedActiveResiduePointMass_error_of_tail B U basis hR hσ S q r hcell j i hactive hq hsize
    hM rows hrows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F hε htail

theorem allocatedConstantPointMixture_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((conditioned).toPMF.bind (fun y => integerMatrixImagePMF
          (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
            (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))) z).toReal : ℝ) : ℂ) -
      allocatedConstantPointApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z
        (positiveModerateSpectrumCover rows M j.val P ((torus : ℝ) / (2 * gamma)) S.value
          (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 1) * rows.card)
            P ((torus : ℝ) / (2 * gamma)) ((torus : ℝ) ^ rows.card) ε))‖ ≤ ε := by
  apply allocatedConstantPointMixture_error_of_tail B U basis hR hσ S q r hcell j i hactive hq hsize
    hgrid hM rows hrows x z _ hε.le
  have hMK : (M : ℝ) ≤ (torus : ℝ) * basisAxisScale (basis j) i := by
    simp only [hM, Nat.cast_mul, le_refl]
  exact allocatedSupportedResidueSpectrum_tail B U basis hR S j i hactive q hq r hsize
    hgrid A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMK rows hrows hB hε hε1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4
local notation "radius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
noncomputable def allocatedResiduePlateauApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) : ℂ :=
  weightedModeratePlateauApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
    (fun _ => 0) scale radius rows shift z F

theorem allocatedResiduePlateauApproximation_error_of_tail
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(((scale : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
      allocatedResiduePlateauApproximation B U basis hR S q r j i hactive hq hsize
        M rows shift z F‖ ≤ ε := by
  exact weightedModeratePointMass_error_plateau (fun _ : B ⟨j, Sum.inr i⟩ => csource)
    sources (fun _ => 0) (by norm_num) (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
    (allocatedActiveResidueSources_natural_volume B U basis hR S q r j i hactive hq hsize)
    hM rows hrows shift z
    (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift)
    (allocatedSupportedResidueJetPMF_source B U basis hR hσ S q r hcell j i hactive hq hsize rows shift)
    F hε (by simpa only [Int.cast_zero] using htail)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResiduePlateauApproximation_norm_le
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
    ‖allocatedResiduePlateauApproximation B U basis hR S q r j i hactive hq hsize M rows shift z F‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) 1 + 1 := by
  have hMK : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
  have hcap := allocatedNaturalGridSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid hgamma A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M)) hMK rows hrows hB
  exact weightedModeratePlateauApproximation_norm_le_cap
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (fun _ => 0) radius rows shift z F hscale
    (by simpa only [Int.cast_zero] using hcap)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
noncomputable def allocatedConstantPlateauApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) : ℂ :=
  ∫ c, allocatedResiduePlateauApproximation B U basis hR S q r j i hactive hq hsize M rows
    (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F ∂(constantLaw).toMeasure

theorem allocatedConstantPlateauApproximation_error_of_tail
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(((scale : ℝ) ^ rows.card *
        (((conditioned).toPMF.bind (fun y => integerMatrixImagePMF
          (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
            (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))) z).toReal : ℝ) : ℂ) -
      allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F‖ ≤ ε := by
  unfold allocatedConstantPlateauApproximation
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro c
  exact allocatedResiduePlateauApproximation_error_of_tail B U basis hR hσ S q r hcell j i
    hactive hq hsize hM rows hrows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F hε htail

theorem allocatedConstantPlateauApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((scale : ℝ) ^ rows.card *
        (((conditioned).toPMF.bind (fun y => integerMatrixImagePMF
          (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
            (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))) z).toReal : ℝ) : ℂ) -
      allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z
        (positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value
          (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
            P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε))‖ ≤ ε := by
  apply allocatedConstantPlateauApproximation_error_of_tail B U basis hR hσ S q r hcell j i
    hactive hq hsize hgrid hM rows hrows x z _ hε.le
  have hMK : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  exact allocatedNaturalGridSpectrum_tail B U basis hR S j i hactive q hq r hsize
    hgrid hgamma A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMK rows hrows hB hε hε1

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedConstantPlateauApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (z : rows → ℤ) (F : Finset (rows → Fin M)) :
    ‖allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) 1 + 1 := by
  unfold allocatedConstantPlateauApproximation
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (ae_of_all (constantLaw).toMeasure (fun c =>
      allocatedResiduePlateauApproximation_norm_le B U basis hR S q r j i hactive hq hsize
        hgrid hgamma A hA P hcP hsP hM rows hrows hB _ z F))

end Erdos3.VectorPolynomial

end

end OAI
