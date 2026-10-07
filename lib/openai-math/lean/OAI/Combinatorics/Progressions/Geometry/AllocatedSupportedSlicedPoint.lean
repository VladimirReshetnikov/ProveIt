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

omit [∀ layer, DecidableEq (I layer)] in
include hsubset in
theorem allocatedSupportedSlicedSource_support
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (shift : rows → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (coeff b).length ×
      (∀ v, IntegerScalarCubeBox α ((sources) b v).length))
    (hx : (weightedModerateIntegerProductSource coeff sources).weight x ≠ 0) (t : rows) :
    |(weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      radius * height := by
  have hcoord (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) :
      |affineIntegerCubeCoordinates (lower b v) (strides b v) (fun a => ((x b).2 v a : ℤ)) a| ≤ S.value := by
    have hb : (weightedModerateIntegerSource (coeff b) (sources b)).weight (x b) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
    have hprod : (∏ v, ((sources) b v).source.weight ((x b).2 v)) ≠ 0 :=
      (mul_ne_zero_iff.mp hb).2
    have hv : ((sources) b v).source.weight ((x b).2 v) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) v (Finset.mem_univ v)
    have he := allocatedPrincipalSides_active B U basis S j i hactive b v
    have hbound := containedProgressionCoordinate_bound (c ⟨⟨j,Sum.inr i⟩,b,v⟩)
      (hsubset ⟨⟨j,Sum.inr i⟩,b,v⟩) ((x b).2 v) (((sources) b v).source_cube _ hv) a
    rw [he] at hbound
    exact hbound
  have hgamma := principalProfileSize_pos (hR j)
    (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  exact weightedAffineModerateIntegerJetSum_box_bound coeff sources lower strides S.value rows hrows
    (by positivity) (Nat.cast_nonneg _) (fun _ =>
      (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).2) shift x hcoord t

theorem allocatedSupportedSlicedPointApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := ((torus : ℝ) / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := (torus : ℝ) ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ) -
          (normalizedSupportPlateau radius (fun t => ((z t : ℝ) - shift t) / height) : ℂ) *
            weightedAffineModerateGridApproximation coeff sources lower strides height M rows
              (fun _ => 0) shift z F‖ ≤ ε := by
  intro V t W F
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  obtain ⟨hF, he⟩ := allocatedSupportedSlicedGridDensity_approximation_on_cover
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hactive hsize
    hgrid hδ hlength hstep A hA P hcP hsP hstride (Nat.cast_nonneg torus) hMK rows hrows hB hε hε1
  refine ⟨hF, fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw height M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) height M z =
      allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have he' := (he shift z).trans (mul_le_of_le_one_left hε.le hscale)
  rw [← hd'] at he'
  have hgamma := principalProfileSize_pos (hR j)
    (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  have hp := integerGridDensity_plateau_transfer (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    shift z (blockJetScaleBound_nonneg _ _ _ (by positivity)) (basisAxisScale_pos (basis j) i) hM
    (fun x hx t => allocatedSupportedSlicedSource_support B U basis hR S q hq r H step c hH hsubset
      j i hactive hsize rows hrows shift x hx t) _ hε.le he'
  simpa only [hlaw, Fintype.card_coe] using hp

end Erdos3.VectorPolynomial

end

end OAI
