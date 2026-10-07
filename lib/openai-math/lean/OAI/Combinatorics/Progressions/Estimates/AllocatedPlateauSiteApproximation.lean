import OAI.Combinatorics.Progressions.Dynamics.AllocatedBudgetedPlateau
import OAI.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
import OAI.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4
local notation "radius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hR hactive in
theorem allocatedNaturalGridSpectrum_character
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) {M : ℕ} (hM : M = torus * scale)
    (rows : Finset (Finset α)) (P ζ : ℝ) (k : rows → Fin M)
    (hk : k ∈ positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ positiveRetainedDenominatorBound j.val rows.card
        ((layerTailDegree m + 2) * rows.card) P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ζ ∧
      ∃ (a : rows → ℤ) (ω : rows → ℝ),
        (∀ t, |ω t| ≤ positiveRetainedFrequencyBound j.val rows.card P (torus : ℝ) ζ) ∧
        ∀ t, ((k t).val : ℝ) / M = (a t : ℝ) / D + ω t / scale := by
  have hNM : scale ≤ M := by
    rw [hM]
    calc
      scale = 1 * scale := (one_mul _).symm
      _ ≤ torus * scale := Nat.mul_le_mul_right _ (blockTorusFactor_pos _ _ _ _)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hcard := allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive
    hgrid hgamma (Nat.cast_nonneg torus) hMN rows.card
  simpa only [Fintype.card_coe] using positiveModerateSpectrumCover_character
    (allocatedPrincipalGridScale_pos B U basis hR S j i hactive) hNM j.val
    ((layerTailDegree m + 2) * rows.card) (Nat.cast_nonneg S.value)
    (by positivity : (0 : ℝ) ≤ (2 * (torus : ℝ)) ^ rows.card)
    (by simpa only [Fintype.card_coe] using hcard) k hk

theorem allocatedConstantPlateauApproximation_expansion
    (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / scale) :
    allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F =
      ((scale : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b : B ⟨j, Sum.inr i⟩,
          weightedModerateGridCoefficient csource
            (allocatedActiveResidueSources B U basis S j i hactive q hq r hsize b) 0 M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture constantLaw radius (D k) scale (a k) (ω k)
              (fun c t => booleanCoefficient (fun _ : Finset α => c) t)
              (fun t => (z t : ℝ) / scale)) := by
  unfold allocatedConstantPlateauApproximation allocatedResiduePlateauApproximation
  simpa only [Int.cast_zero] using weightedModeratePlateauMixture_expansion
    (K := scale) (M := M)
    (fun _ : B ⟨j, Sum.inr i⟩ => csource)
    (allocatedActiveResidueSources B U basis S j i hactive q hq r hsize) (fun _ => 0)
    constantLaw (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
    radius rows (fun c t => booleanCoefficient (fun _ : Finset α => c) t) z F D a ω hfreq

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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "radius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hR hactive in
theorem allocatedNaturalGridSpectrum_modes
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) {M : ℕ} (hM : M = torus * scale)
    (rows : Finset (Finset α)) (P ζ : ℝ) :
    ∃ (D : (rows → Fin M) → ℕ) (a : (rows → Fin M) → rows → ℤ)
      (ω : (rows → Fin M) → rows → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value ζ,
        (D k : ℝ) ≤ positiveRetainedDenominatorBound j.val rows.card
          ((layerTailDegree m + 2) * rows.card) P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ζ ∧
        (∀ t, |ω k t| ≤ positiveRetainedFrequencyBound j.val rows.card P (torus : ℝ) ζ) ∧
        ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / scale := by
  have hNM : scale ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  have hcard := allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive
    hgrid hgamma (Nat.cast_nonneg torus) hMN rows.card
  simpa only [Fintype.card_coe] using positiveModerateSpectrumCover_modes (J := rows)
    (allocatedPrincipalGridScale_pos B U basis hR S j i hactive) hNM j.val
    ((layerTailDegree m + 2) * rows.card) (U := P) (V := (torus : ℝ)) (ζ := ζ)
    (Nat.cast_nonneg S.value) (by positivity : (0 : ℝ) ≤ (2 * (torus : ℝ)) ^ rows.card)
    (by simpa only [Fintype.card_coe] using hcard)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize

noncomputable def allocatedPlateauModeModel (M : ℕ) [NeZero M] (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) : ℂ :=
  weightedPlateauModeModel (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (fun _ => 0)
    constantLaw radius scale rows F D a ω
    (fun c t => booleanCoefficient (fun _ : Finset α => c) t) residue x

theorem allocatedPlateauModeModel_grid_value (M : ℕ) [NeZero M] (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / scale)
    (z : rows → ℤ) :
    allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F =
      allocatedPlateauModeModel B U basis hR hσ S j i hactive q r hq hsize M rows F D a ω
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / scale) := by
  unfold allocatedConstantPlateauApproximation allocatedResiduePlateauApproximation allocatedPlateauModeModel
  exact weightedPlateauModeModel_grid_value
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (fun _ => 0) constantLaw
    (allocatedPrincipalGridScale_pos B U basis hR S j i hactive) radius rows F D a ω hfreq
    (fun c t => booleanCoefficient (fun _ : Finset α => c) t) z

theorem allocatedPlateauModeModel_norm
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale) (rows : Finset (Finset α))
    (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) :
    ‖allocatedPlateauModeModel B U basis hR hσ S j i hactive q r hq hsize M rows F D a ω residue x‖ ≤
      allocatedGridPointCap B P ⟨j, i⟩ rows := by
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  have hcap := allocatedNaturalGridSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid hgamma L hL P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMN rows hrows hB
  unfold allocatedPlateauModeModel
  apply weightedPlateauModeModel_norm _ _ _ _ _ _ _ _ _ _ _ hscale _ residue x
  simpa only [Int.cast_zero, allocatedGridPointCap] using hcap

theorem allocatedPlateauModeModel_lipschitz
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * scale) (rows : Finset (Finset α))
    (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W) (residue : ∀ k : F, rows → ZMod (D k)) :
    LipschitzWith (Real.toNNReal (allocatedGridPointCap B P ⟨j, i⟩ rows) *
      (CircleFourier.characterLipConstant * (rows.card * W) + 4))
      (allocatedPlateauModeModel B U basis hR hσ S j i hactive q r hq hsize M rows F D a ω residue) := by
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  have hcap := allocatedNaturalGridSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid hgamma L hL P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMN rows hrows hB
  unfold allocatedPlateauModeModel
  apply weightedPlateauModeModel_lipschitz _ _ _ _ _ _ _ _ _ _ _ hscale _ W _ hW residue
  apply le_trans (b := allocatedGridPointCap B P ⟨j, i⟩ rows) _ (Real.le_coe_toNNReal _)
  simpa only [Int.cast_zero, allocatedGridPointCap] using hcap

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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable {M : ℕ} [NeZero M] (rows : Finset (Finset α)) (P ε : ℝ)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "radius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "bias" => positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
  P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε
local notation "spectrum" => positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value bias
local notation "cap" => allocatedGridPointCap B P (Sigma.mk j i) rows
local notation "freq" => Real.toNNReal (positiveRetainedFrequencyBound j.val rows.card P (torus : ℝ) bias)
local notation "chartRatio" => allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i

include hactive hq hsize in
theorem exists_allocated_physical_site_approximation
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : M = torus * scale) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {H δ Q : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : H ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ D : (rows → Fin M) → ℕ, (∀ k, 0 < D k) ∧
      (∀ k ∈ spectrum, (D k : ℝ) ≤ positiveRetainedDenominatorBound j.val rows.card
        ((layerTailDegree m + 2) * rows.card) P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) bias) ∧
      ∃ N : spectrum → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * Q + 8)) ∧
        (Fintype.card (PlateauSiteIndex α spectrum N) : ℝ) ≤
          (Finset.card spectrum) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)) ∧
        ∃ (β : PlateauSiteIndex α spectrum N → ℂ)
          (f : (k : PlateauSiteIndex α spectrum N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
          (∑ k, ‖β k‖) ≤ cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q) ∧
          (∀ k u v x, ‖f k u v x‖ ≤ 1) ∧
          (∀ k u v, LipschitzWith ⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ (f k u v)) ∧
          ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
            (∀ u, |(y u : ℝ) / scale| ≤ H) →
            (‖(((scale : ℝ) ^ rows.card *
                (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
                  (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
              ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale)‖ ≤ ε + δ) ∧
            ‖(basisAxisScale (basis j) i : ℂ) ^ rows.card *
                ((allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
                  (fun t => booleanCoefficient y t)).toReal : ℂ) -
              ∑ k, ((chartRatio : ℂ) ^ rows.card * β k) * ∏ u,
                f k u (y u : ZMod (D k.1)) (chartRatio * ((y u : ℝ) / basisAxisScale (basis j) i))‖ ≤
              chartRatio ^ rows.card * (ε + δ) := by
  obtain ⟨D, a, ω, hD, hmodes⟩ := allocatedNaturalGridSpectrum_modes
    B U basis hR S j i hactive hgrid hgamma hM rows P bias
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by simp only [hM, Nat.cast_mul, le_refl]
  have hcap := allocatedNaturalGridSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid hgamma L hL P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMN rows hrows hB
  have hcap' : (∑ k, ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource (sources b) ((0 : ℤ) : ℝ) M rows k‖) ≤ cap := by
    simpa only [Int.cast_zero, allocatedGridPointCap] using hcap
  obtain ⟨N, hN, hcard, β, f, hβ, hf, hLf, he⟩ := exists_weighted_plateau_site_approximation
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (fun _ => 0) constantLaw
    (allocatedPrincipalGridScale_pos B U basis hR S j i hactive) radius rows spectrum D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun c t => booleanCoefficient (fun _ : Finset α => c) t) hscale hcap' freq
    (fun k hk t => ((hmodes k hk).2.1 t).trans (Real.le_coe_toNNReal _))
    hH hδ hQ hHQ hδQ hLQ
  refine ⟨D, hD, (fun k hk => (hmodes k hk).1), N, hN, hcard, β, f, hβ, hf, hLf, ?_⟩
  intro x y hy
  have hpoint := allocatedBudgetedPlateauApproximation_error B U basis hR hσ S q r j i hactive hq hsize
    hcell hgrid hgamma L hL P hcP hsP hM rows hrows hB hε hε1 x
    (fun t => booleanCoefficient y t)
  have hsite : ‖allocatedBudgetedPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize
      P ε M rows (fun t => booleanCoefficient y t) -
      ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale)‖ ≤ δ := by
    simpa only [allocatedBudgetedPlateauApproximation, allocatedConstantPlateauApproximation,
      allocatedResiduePlateauApproximation] using he y hy
  have hn := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hpoint hsite)
  refine ⟨hn, ?_⟩
  have ht := grid_site_normalization_error
    (K := (basisAxisScale (basis j) i : ℝ)) (N := (scale : ℝ))
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)) rows.card
    ((allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
      (fun t => booleanCoefficient y t)).toReal : ℂ)
    β (fun k u z => f k u (y u : ZMod (D k.1)) z) (fun u => (y u : ℝ))
    (by simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using hn)
  simpa only [Complex.ofReal_natCast, allocatedPrincipalChartRatio] using ht

end Erdos3.VectorPolynomial

end

end OAI
