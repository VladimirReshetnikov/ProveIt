import OAI.Combinatorics.Progressions.Fourier.AllocatedSupportedSlicedInactiveSpectrum
import OAI.Combinatorics.Progressions.Lattices.IntegerGridPointCap

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

include hsubset in
theorem allocatedSupportedSlicedInactiveSource_support
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree) (shift : rows → ℤ)
    (x : ∀ b v, IntegerScalarCubeBox α ((sources) b v).length)
    (hx : (weightedCubeIntegerSource sources).weight x ≠ 0) (t : rows) :
    |(affineWeightedCubeIntegerSum sources lower strides rows shift x t : ℝ) - shift t| ≤ radius * height := by
  let _ : ∀ index, DecidableEq (I index) := inferInstance
  have hcoord (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) (a : Option α) :
      |affineIntegerCubeCoordinates (lower b v) (strides b v) (fun a => (x b v a : ℤ)) a| ≤ side := by
    have hb : (FiniteProbabilityWeights.pi (fun v => ((sources) b v).source)).weight (x b) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
    have hprod : (∏ v, ((sources) b v).source.weight (x b v)) ≠ 0 := hb
    have hv := (Finset.prod_ne_zero_iff.mp hprod) v (Finset.mem_univ v)
    have he : allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
      rw [layerIntegerPrincipalSlots_card]
      change integerAxisSideLength degree height S.value
        (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
      simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]
    have hbnd := containedProgressionCoordinate_bound (c ⟨⟨j,Sum.inr i⟩,b,v⟩)
      (hsubset ⟨⟨j,Sum.inr i⟩,b,v⟩) (x b v) (((sources) b v).source_cube _ hv) a
    rw [he] at hbnd
    exact hbnd
  have hvol : (side : ℝ) ^ degree ≤ 1 * (height : ℝ) := by
    rw [one_mul]
    exact_mod_cast (inactiveSideLength_power (Nat.zero_lt_succ _) hlarge).trans (Nat.div_le_self _ _)
  exact affineWeightedCubeIntegerSum_box_bound sources lower strides side rows hrows
    zero_le_one (Nat.cast_nonneg _) hvol shift x hcoord t

theorem allocatedSupportedSlicedInactivePointApproximation_error
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ shift z : rows → ℤ,
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ) -
        (normalizedSupportPlateau radius (fun t => ((z t : ℝ) - shift t) / height) : ℂ) *
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ε := by
  intro V t W ζ F
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  obtain ⟨hF, hcap, he⟩ := allocatedSupportedSlicedInactiveGridDensity_approximation B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride
    (Nat.cast_nonneg torus) hMK rows hrows hB hε hε1
  refine ⟨hF, hcap, fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsmall hlarge hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedCubeIntegerSource sources)
    (affineWeightedCubeIntegerSum sources lower strides rows shift) _ hlaw height M z
  have hd' : integerGridDensity (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z =
      allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have he' := (he shift z).trans (mul_le_of_le_one_left hε.le hscale)
  rw [← hd'] at he'
  have hp := integerGridDensity_plateau_transfer (weightedCubeIntegerSource sources)
    (affineWeightedCubeIntegerSum sources lower strides rows shift) shift z
    (blockJetScaleBound_nonneg _ _ _ zero_le_one) (basisAxisScale_pos (basis j) i) hM
    (fun x hx t => allocatedSupportedSlicedInactiveSource_support B U basis S q hq r H step c hH hsubset
      j i hsize hsmall hlarge rows hrows shift x hx t) _ hε.le he'
  simpa only [hlaw, Fintype.card_coe] using hp

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

include hq hsize in

theorem allocatedSupportedSlicedInactiveResidueJetPMF_norm_le
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val rows.card t P V W := by
  intro V t W
  let M := torus * height
  have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  let _ : NeZero M := ⟨hM.ne'⟩
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [M, Nat.cast_mul, le_refl]
  have hKM : height ≤ M := Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨_,hcap,_⟩ := allocatedSupportedSlicedInactiveGridDensity_approximation B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride
    (Nat.cast_nonneg torus) hMK rows hrows hB zero_lt_one le_rfl
  have hcap0 : 0 ≤ uniformSpectrumAbsoluteCap j.val rows.card t P V W :=
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr hKM))
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

end Erdos3.VectorPolynomial

end

end OAI
