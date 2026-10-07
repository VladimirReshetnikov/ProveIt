import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveSource
import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueGrid

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

theorem allocatedSupportedSlicedInactiveGridDensity_approximation
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C) (hMK : (M : ℝ) ≤ C * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := C * cost / δ ^ degree
    let t := degree * rows.card
    let W := (C * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ shift z : rows → ℤ,
      ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ((height : ℝ) / M) ^ rows.card * ε := by
  intro V t W ζ F
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ (C * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hC)
  have hratio : (M : ℝ) / (1 * (side : ℝ) ^ degree) ≤ C * cost := by
    rw [one_mul]
    exact (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hside) _)).mpr hbound
  have hscale (b : B ⟨j,Sum.inr i⟩) : (M : ℝ) / ∏ v, (((sources) b v).length : ℝ) ≤ V := by
    change (M : ℝ) / ∏ v : Fin degree, (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ) ≤ C * cost / δ ^ degree
    simpa only [one_mul, layerSamplerDegree] using dense_slice_product_ratio (n := j.val + 1)
      (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ (Nat.cast_pos.mpr hside)
      zero_lt_one (Nat.cast_nonneg M) (hlength b) hratio
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card rows M j.val t
      hP hV hW hL hε hε1 (by simpa only [Fintype.card_coe] using hcard)
  · exact (affine_weightedCube_uniform_spectrum sources (fun b v a => (lower b v a : ℝ)) strides
      A hA hP hV hW hL hε hs hlength (fun b v _ => hstep b v) (fun b v _ => hstride b v)
      M t (Nat.pos_of_ne_zero (NeZero.ne M)) rows hrows hB hcard hscale).2
  · intro shift z
    have he := affine_weightedCube_grid_density sources lower strides A hA hP hV hW hL hε hs hlength
      (fun b v _ => hstep b v) (fun b v _ => hstride b v) height M t rows hrows hB hcard hscale shift z
    have hlaw := allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c
      hH hsubset hcell j i hsmall hlarge hsize rows shift
    have hd := integerGridDensity_eq_of_pmf_image (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) _ hlaw height M z
    have hd' : integerGridDensity (weightedCubeIntegerSource sources)
        (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
      simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
    rw [← hd']
    exact he

end Erdos3.VectorPolynomial

end

end OAI
