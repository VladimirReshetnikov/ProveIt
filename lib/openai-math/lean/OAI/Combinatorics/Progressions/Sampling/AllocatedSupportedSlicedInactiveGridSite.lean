import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveFixedCap
import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedPoint
import OAI.Combinatorics.Progressions.Lattices.AffineCubePlateauSite
import OAI.Combinatorics.Progressions.Lattices.AffineModeratePlateauSite
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

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

noncomputable def allocatedSupportedSlicedPhysicalGridPMF
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) : PMF (rows → ℤ) :=
  (conditioned).toPMF.bind (fun y =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
      (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))

noncomputable def allocatedSupportedSlicedPhysicalGridApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (F : Finset (rows → Fin M)) (z : rows → ℤ) : ℂ :=
  ∫ zeta, weightedAffineModeratePlateauApproximation coeff sources lower strides (fun _ => 0)
    height radius rows (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z F
    ∂(constantLaw).toMeasure

theorem allocatedSupportedSlicedPhysicalGridApproximation_error
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
    ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ) -
        allocatedSupportedSlicedPhysicalGridApproximation B U basis hR hσ S q hq r H step c hH j i
          hactive hsize M rows F z‖ ≤ ε := by
  intro V t W F
  obtain ⟨hF, he⟩ := allocatedSupportedSlicedPointApproximation_error B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hactive hsize hgrid hδ hlength hstep A hA P hcP hsP hstride hM rows hrows hB hε hε1
  refine ⟨hF, fun x z => ?_⟩
  unfold allocatedSupportedSlicedPhysicalGridPMF allocatedSupportedSlicedPhysicalGridApproximation
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c
    hH hsubset hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro zeta
  exact he (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z

theorem allocatedSupportedSlicedPhysicalGridPMF_scaled_support
    (hσ1 : σ j ≤ 1) (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (z : rows → ℤ)
    (hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z ≠ 0)
    (t : rows) : |(z t : ℝ) / height| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  by_contra hbad
  apply hmass
  unfold allocatedSupportedSlicedPhysicalGridPMF
  apply pmf_bind_zero_of_support
  intro y _
  by_contra hmass'
  have hreal := (ENNReal.toReal_pos hmass' (PMF.apply_ne_top _ _)).ne'
  have hT : ∀ k, 0 < layerSamplerBox B U basis S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U basis S k)
  have hroot (k) : |(allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y k : ℝ) /
      layerSamplerBox B U basis S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U basis S x y (fun _ => 0) k
  apply hbad
  exact integerMatrixImagePMF_scaled_support_bound _ _
    (fun e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) =>
      monomialScale (layerSamplerBox B U basis S) e.val)
    (fun e => monomialScale_pos _ hT e.val) (by positivity)
    (boundedCoefficientJetMatrix_scaled_entry_bound _ _ _ hT hroot
      (allocatedPhysicalCube_directions_normalized B U basis S x y) _ (fun t : rows => (t : Finset α)))
    (fun e z hz => allocatedLayerIntegerCoefficient_scaled_bound B U basis hR hσ S j hσ1 i e z hz)
    z hreal t

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
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
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

theorem allocatedSupportedSlicedPhysicalGridPMF_base_independent
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x x' : G → IntegerScalarCubeBox α S.value) :
    allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x =
      allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x' := by
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x,
    allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x']

theorem exists_allocatedSupportedSliced_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : height ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  let p := allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x₀
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / height| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 rows x₀
      (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  obtain ⟨e, he, herr⟩ := exists_bounded_grid_site_expansion rows p
    (basisAxisScale_pos (basis j) i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP
  refine ⟨e, he, ?_⟩
  intro x y hy
  rw [allocatedSupportedSlicedPhysicalGridPMF_base_independent B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x x₀]
  exact herr y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
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
theorem exists_allocatedSupportedSliced_grid_site_expansion
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
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := ((torus : ℝ) / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := (torus : ℝ) ^ rows.card / δ ^ t
    let ζ := positiveModerateRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (positiveRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (positiveModerateSpectrumCardBudget j.val rows.card t P V W ε *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (positiveRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  intro V t W ζ freq cap R0 η Q hη hQ hRQ hηQ hLQ
  let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value) ζ
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have hL : 0 ≤ δ * S.value := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid (Nat.cast_nonneg torus) hMK rows.card)
  have hKM : height ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨D, a, ω, hD, hmodes⟩ := positiveModerateSpectrumCover_modes (J := rows)
    (basisAxisScale_pos (basis j) i) hKM j.val t hL hW
    (by simpa only [Fintype.card_coe] using hcard) (U := P) (V := V) (ζ := ζ)
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  have hcap := allocatedSupportedSlicedGridDensity_absolute_cap B U basis hR S q hq r H step c hH
    j i hactive hsize hgrid hδ hlength hstep A hA P hcP hsP hstride (Nat.cast_nonneg torus) hMK rows hrows hB
  have hRj : 0 ≤ R j := (hR j).le
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  obtain ⟨N, hN, hcount, β, f, hβ, hf, hLf, he⟩ := exists_weighted_affine_plateau_site_approximation
    coeff sources lower strides (fun _ => 0) constantLaw (basisAxisScale_pos (basis j) i) radius rows F D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun zeta t => booleanCoefficient (fun _ : Finset α => zeta) t) hscale
    (by simpa only [Int.cast_zero] using hcap) freq
    (fun k hk t => (by simpa only [Fintype.card_coe] using (hmodes k hk).2.1 t :
      |ω k t| ≤ positiveRetainedFrequencyBound j.val rows.card P V ζ).trans (Real.le_coe_toNNReal _))
    (R := R0 + 1 / 4) (by positivity) hη hQ hRQ hηQ hLQ
  obtain ⟨hF, hpoint⟩ := allocatedSupportedSlicedPhysicalGridApproximation_error B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hactive hsize hgrid hδ hlength hstep A hA P hcP hsP hstride hM rows hrows hB hε hε1
  let g (k : PlateauSiteIndex α F N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau R0 z * f k u v z
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := g }
  refine ⟨e, ⟨?_, (fun k => hD k.1), ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hcount.trans (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
  · intro k
    simpa only [Fintype.card_coe] using (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau R0 z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz R0 (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau R0 z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    have hkeep :
        (((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) ≠ 0 →
        ∀ u, scalarSupportPlateau R0 ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      apply scalarSupportPlateau_one hR0
      apply integer_boolean_sites_bound y rows hy (by positivity) (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      intro t ht
      have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support B U basis hR hσ S q r H step c hH hsubset hcell
        j i hσ1 rows x (fun t => booleanCoefficient y t) hmass ⟨t, ht⟩
      have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
      rw [abs_div, abs_of_pos hk] at hb
      exact (div_le_iff₀ hk).mp hb
    exact finite_site_cutoff_error _ β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau R0 ((y u : ℝ) / height))
      (by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
      (fun hcut => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (hpoint x (fun t => booleanCoefficient y t))
          (he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le))))

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

noncomputable def allocatedSupportedSlicedInactivePhysicalGridApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (F : Finset (rows → Fin M)) (z : rows → ℤ) : ℂ :=
  ∫ zeta, affineCubePlateauApproximation sources lower strides height radius rows
    (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z F ∂(constantLaw).toMeasure

theorem allocatedSupportedSlicedInactivePhysicalGridApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
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
    ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ) -
        allocatedSupportedSlicedInactivePhysicalGridApproximation B U basis hR hσ S q hq r H step c hH j i hsize
          M rows F z‖ ≤ ε := by
  intro V t W ζ F
  obtain ⟨hF, hcap, he⟩ := allocatedSupportedSlicedInactivePointApproximation_error B U basis hR hσ S q hq r H step c
    hH hsubset hcell j i hsize hsmall hlarge hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  refine ⟨hF, hcap, fun x z => ?_⟩
  unfold allocatedSupportedSlicedPhysicalGridPMF allocatedSupportedSlicedInactivePhysicalGridApproximation
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c
    hH hsubset hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error _ _ z _ (pow_nonneg (Nat.cast_nonneg _) _)
  intro zeta
  exact he (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
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
theorem exists_allocatedSupportedSliced_inactive_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
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
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val rows.card t P V W
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((uniformSpectrumSizeConstant j.val rows.card t P V W /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (uniformScaledRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  intro V t W ζ freq cap R0 η Q hη hQ hRQ hηQ hLQ
  let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ ((torus : ℝ) * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg torus))
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hKM : height ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨D, a, ω, hD, hmodes⟩ := uniformBlockSpectrumCover_modes (J := rows)
    (basisAxisScale_pos (basis j) i) hKM j.val t hL hW
    (by simpa only [Fintype.card_coe] using hcard) (U := P) (V := V) (ζ := ζ)
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  obtain ⟨hF, hcap, hpoint⟩ := allocatedSupportedSlicedInactivePhysicalGridApproximation_error
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  have hRj : 0 ≤ R j := (hR j).le
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  obtain ⟨N, hN, hcount, β, f, hβ, hf, hLf, he⟩ := exists_affineCube_plateau_site_approximation
    sources lower strides constantLaw (basisAxisScale_pos (basis j) i) radius rows F D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun zeta t => booleanCoefficient (fun _ : Finset α => zeta) t) hscale
    hcap freq
    (fun k hk t => (by simpa only [Fintype.card_coe] using (hmodes k hk).2.1 t :
      |ω k t| ≤ uniformScaledRetainedFrequencyBound j.val rows.card P V ζ).trans (Real.le_coe_toNNReal _))
    (R := R0 + 1 / 4) (by positivity) hη hQ hRQ hηQ hLQ
  let g (k : PlateauSiteIndex α F N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau R0 z * f k u v z
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := g }
  refine ⟨e, ⟨?_, (fun k => hD k.1), ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hcount.trans (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
  · intro k
    simpa only [Fintype.card_coe] using (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau R0 z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz R0 (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau R0 z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    have hkeep :
        (((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) ≠ 0 →
        ∀ u, scalarSupportPlateau R0 ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      apply scalarSupportPlateau_one hR0
      apply integer_boolean_sites_bound y rows hy (by positivity) (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      intro t ht
      have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support B U basis hR hσ S q r H step c hH hsubset hcell
        j i hσ1 rows x (fun t => booleanCoefficient y t) hmass ⟨t, ht⟩
      have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
      rw [abs_div, abs_of_pos hk] at hb
      exact (div_le_iff₀ hk).mp hb
    exact finite_site_cutoff_error _ β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau R0 ((y u : ℝ) / height))
      (by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
      (fun hcut => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (hpoint x (fun t => booleanCoefficient y t))
          (he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le))))

end Erdos3.VectorPolynomial

end

end OAI
