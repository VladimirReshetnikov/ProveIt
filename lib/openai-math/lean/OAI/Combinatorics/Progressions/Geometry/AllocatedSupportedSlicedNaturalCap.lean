import OAI.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite

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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hactive hsize in
theorem allocatedSupportedSlicedPhysicalGridPMF_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hKM : height ≤ M) (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1 := by
  intro V t W
  have hcap := allocatedSupportedSlicedGridDensity_absolute_cap B U basis hR S q hq r H step c hH
    j i hactive hsize hgrid hδ hlength hstep A hA P hcP hsP hstride hC hMK rows hrows hB
  have hcap0 : 0 ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1 :=
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))).mpr
      (Nat.cast_le.mpr hKM))
  have hpoint (shift : rows → ℤ) :
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
        positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1 := by
    have hp := integerPointDensity_norm_le_fourier_sum (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) height M z
    rw [allocatedSupportedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
      j i hactive hsize rows shift] at hp
    have heq (k : rows → Fin M) := weightedAffineModerateIntegerJetSum_coefficient
      coeff sources lower strides M rows (fun _ => 0) shift k
    simp_rw [heq, norm_mul, rectangularGridCharacter_norm, one_mul] at hp
    simp only [Fintype.card_coe, Int.cast_zero] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hcap (by positivity)).trans
      (mul_le_of_le_one_left hcap0 hscale))
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell
    j i hgrid rows x]
  exact pmf_bind_point_norm_le _ _ _ _ z (fun zeta => hpoint (fun t => booleanCoefficient (fun _ : Finset α => zeta) t))

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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in
theorem allocatedSupportedSlicedInactivePhysicalGridPMF_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C) (hMK : (M : ℝ) ≤ C * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hKM : height ≤ M) (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    let V := C * cost / δ ^ degree
    let t := degree * rows.card
    let W := (C * cost) ^ rows.card / δ ^ t
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val rows.card t P V W := by
  intro V t W
  obtain ⟨_,hcap,_⟩ := allocatedSupportedSlicedInactiveGridDensity_approximation B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride hC hMK rows hrows hB
    zero_lt_one le_rfl
  have hcap0 : 0 ≤ uniformSpectrumAbsoluteCap j.val rows.card t P V W :=
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))).mpr
      (Nat.cast_le.mpr hKM))
  have hpoint (shift : rows → ℤ) :
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W := by
    have hp := integerPointDensity_norm_le_fourier_sum (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z
    rw [allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
      j i hsmall hlarge hsize rows shift] at hp
    have heq (k : rows → Fin M) := affineWeightedCubeIntegerSum_coefficient
      sources lower strides M rows shift k
    simp_rw [heq, norm_mul, rectangularGridCharacter_norm, one_mul] at hp
    simp only [Fintype.card_coe] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hcap (by positivity)).trans
      (mul_le_of_le_one_left hcap0 hscale))
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell
    j i hgrid rows x]
  exact pmf_bind_point_norm_le _ _ _ _ z (fun zeta => hpoint (fun t => booleanCoefficient (fun _ : Finset α => zeta) t))

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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

noncomputable def allocatedSlicedGridPointCap (δ P : ℝ) (T d : ℕ) : ℝ :=
  max 1 (max ((allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ^ d)
    (max
      (positiveModerateSpectrumCardBudget j.val d ((layerTailDegree m + 1) * d) P
        (((torusA : ℝ) / (2 * gamma)) / δ ^ degree) ((torusA : ℝ) ^ d / δ ^ ((layerTailDegree m + 1) * d)) 1 + 1)
      (uniformSpectrumAbsoluteCap j.val d (degree * d) P
        ((torusI : ℝ) * cost / δ ^ degree) (((torusI : ℝ) * cost) ^ d / δ ^ (degree * d)))))

include hq in
theorem allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T rows.card := by
  rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
      ((Fintype.card α + 1) * q) T hQT with hsmall | ⟨hsize, hcases⟩
  · have hprob : (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal ≤ 1 :=
      (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := (mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg _) _) hprob).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hsmall) rows.card)
    exact hb.trans ((le_max_left _ _).trans (le_max_right _ _))
  · rcases hcases with ⟨ha, hlength⟩ | ⟨hi, hl, hlength⟩
    · let M := torusA * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      have hMK : (M : ℝ) ≤ (torusA : ℝ) * height := by simp only [M, Nat.cast_mul, le_refl]
      have hp := allocatedSupportedSlicedPhysicalGridPMF_norm_le B U basis hR hσ S q hq r H step c hH hsubset hcell
        j i ha hsize hgrid hδ hlength hstep A hA P hcP hsP hstride (Nat.cast_nonneg torusA) hMK rows hrows hBa
        (Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)) x z
      exact hp.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · let M := torusI * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      have hMK : (M : ℝ) ≤ (torusI : ℝ) * height := by simp only [M, Nat.cast_mul, le_refl]
      have hp := allocatedSupportedSlicedInactivePhysicalGridPMF_norm_le B U basis hR hσ S q hq r H step c hH hsubset hcell
        j i hsize hgrid hi hl hδ hlength hstep A hA P hP hsP hstride (Nat.cast_nonneg torusI) hMK rows hrows hBi
        (Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)) x z
      exact hp.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem allocatedSupportedSlicedPhysicalGridPMF_natural_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      (gamma + 1) ^ rows.card * allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T rows.card := by
  have h := allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hgrid hδ hdense T hQT hstep
    A hA P hP hcP hsP hstride rows hrows hBa hBi x z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h ⊢
  exact ceilGridScale_mass_bound height rows.card (basisAxisScale_pos (basis j) i)
    (principalProfileSize_pos (hR j) _) ENNReal.toReal_nonneg
    (le_trans zero_le_one (le_max_left _ _)) h

end Erdos3.VectorPolynomial

end

end OAI
