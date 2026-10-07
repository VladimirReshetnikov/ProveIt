import OAI.Combinatorics.Progressions.Geometry.AllocatedChartIdealAmbientLift
import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedAmbientGrid

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in
theorem exists_allocated_supported_affine_ambient_surrogate
    (period : ℕ) [NeZero period] (hdiv : period ∣ d)
    (rad : ℝ≥0) (hrad : 0 < rad)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (rad : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Kmodel : Type*} [Fintype Kmodel] (a : Kmodel → ℂ)
    (f : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hfb : ∀ k s z, ‖f k s z‖ ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f y‖ ≤ η) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * rad)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u v₀) q (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          allocatedFullGridNaturalVolume B U b S rowSets * η := by
  intro Lcoord Lcut Lsite Lrows mass Lgrid N
  have hb0 (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)) ≤ 1 / 4 := by
    have hp0 : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)) :=
      mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset α))
    have hfac : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) (rowSets j).card; linarith) hcard
    exact (le_mul_of_one_le_left hp0 hfac).trans (by simpa only [mul_assoc] using hbudget j)
  let model := allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f
  obtain ⟨F, hF, hFb, hFv⟩ := exists_allocated_chart_ideal_ambient_lift B U b S rowSets x y₀ q d period
    rad hrad hb o bW hdiv hR C hC hchart hb0 Cforward hforward K hK a f hf hfb
  change ∀ y, model y = F (coveredJetAmbientTorus U 1 y) at hFv
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_supported_sliced_ambient_grid B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x v₀ Q d hb o bW Cforward hforward
  have hzero (y) (hy : y ∉ chart '' region) : model y = 0 :=
    allocatedProductChartIdealApproximation_zero_outside B U b S rowSets x y₀ q d period rad hrad hb o bW
      hR C hC hchart hbudget a f y hy
  obtain ⟨G₀, hG₀, hG₀b, hG₀v⟩ := exists_allocated_grid_times_ambient_lift B U b S o hb bW d
    gridDensity g hg hgb hgv model F hF hFb hFv hzero
  change LipschitzWith (mass * (Lgrid * d) +
    mass * (Fintype.card (Finset α) * (Lsite * Lrows))) G₀ at hG₀
  let Fout := fun z => (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ z
  have hFN : LipschitzWith (N * (mass * (Lgrid * d) +
      mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) Fout := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm]
    change ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ z -
      (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ w‖ ≤ _
    rw [← mul_sub, norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hG₀.dist_le_mul z w)
      (norm_nonneg (allocatedFullGridNaturalVolume B U b S rowSets : ℂ))
    simpa only [N, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, mul_assoc] using hh
  refine ⟨Fout, hFN, ?_, ?_⟩
  · intro z
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hG₀b z) (norm_nonneg _))
  · intro y
    have hh := allocatedSupportedSlicedProfile_ambient_surrogate_error B U b hR hσ S rowSets
      H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW
      (allocatedRowSlicedIdeal B U b S rowSets ρ center width) rad hrad g hgb hgv
      model F hFv hzero hη happrox y
    have hfix := allocatedAffineRowIdeal_cutoff_fixes_mean B U b S rowSets o hb bW d rad hrad hR hσ
      T hT hsource hradius C hC hchart hb0 hσ1 hTideal ρ hρ hρ1 center width hw x gridLaw
      (fun u => principalAxisJoin grid u v₀) q y
    rw [hfix] at hh
    have heq : G₀ (coveredJetAmbientTorus U 1 y) =
        F (coveredJetAmbientTorus U 1 y) * (g (coveredJetAmbientTorus U d y) : ℂ) := by
      rw [← hG₀v]
      by_cases hy : y ∈ chart '' region
      · obtain ⟨z, hz, rfl⟩ := hy
        rw [allocatedChartGridMultiplier_apply B U b S rowTypes hb o bW d gridDensity z hz, hgv z hz, hFv]
      · rw [← hFv, hzero y hy, zero_mul, zero_mul]
    simpa only [Fout, heq, mul_assoc] using hh

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in

theorem exists_allocated_supported_affine_ambient_approximation
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp p) :
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    let mass := Real.toNNReal ((2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A))
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ +
      Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * allocatedRowSlicedSiteRadius rowSets)
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lsite := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord * d +
      max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          allocatedFullGridNaturalVolume B U b S rowSets * (‖inverseNormalizer‖ * maskCap * ε) := by
  intro Q A maskCap mass L Lcoord Lsite Lrows Lgrid N
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hfn, hfm, hmeas, herr⟩ :=
    exists_allocated_global_masked_affine_ideal_approximation B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget center width ρ hρ hρ1 hw hε hp hbox hεp hρp
  let Mactual := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖₊
  have hmass : Mactual ≤ mass := by
    apply NNReal.coe_le_coe.mp
    apply le_trans _ (Real.le_coe_toNNReal _)
    change (Mactual : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A)
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have he : (Mactual : ℝ) = (2 : ℝ) ^ Fintype.card (Finset α) *
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) := by
      simp only [Mactual, NNReal.coe_sum, coe_nnnorm, norm_mul, norm_pow, h2, Finset.mul_sum]
    rw [he]
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring)
  have hη : 0 ≤ ‖inverseNormalizer‖ * maskCap * ε :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg
      (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period))) hε.le
  have hjoin := principalAxisJoin_restrict grid y₀
  have herr' : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀))
      ideal y - allocatedProductChartIdealApproximation B U b S rowSets x
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀))
      q d period r hr hb o bW a f y‖ ≤ ‖inverseNormalizer‖ * maskCap * ε := by
    simpa only [hjoin] using herr
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_ambient_surrogate B U b hR hσ S rowSets
    H step c hH hsubset q label hcell x (principalAxisRestrict grid y₀) hu₀
    (principalAxisRestrict (fun a => ¬grid a) y₀) E d hmodulus hb o bW
    period hdiv r hr C hC hchart hbudget Cforward hforward K hK T hT hTideal hsource hradius hσ1
    ρ hρ hρ1 center width hw a f hLf hf hη herr'
  simp only [hjoin] at hF hFb
  change LipschitzWith (N * (Mactual * (Lgrid * d) +
    Mactual * (Fintype.card (Finset α) * (Lsite * Lrows)))) F at hF
  change ∀ z, ‖F z‖ ≤ (N * Mactual : ℝ≥0) at hFb
  refine ⟨F, hF.weaken ?_, ?_, hFe⟩
  · gcongr
  · intro z
    exact (hFb z).trans (by exact_mod_cast mul_le_mul_of_nonneg_left hmass (show 0 ≤ N from zero_le))

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in

theorem exists_allocated_supported_affine_accurate_ambient
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    let mass := Real.toNNReal ((2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A))
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ +
      Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * allocatedRowSlicedSiteRadius rowSets)
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lsite := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord * d +
      max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          Real.exp (-target) := by
  intro p Q A maskCap mass L Lcoord Lsite Lrows Lgrid N
  let e := Vlog + Nlog + Mlog + target
  let ε := Real.exp (-e)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hep : e ≤ p := by dsimp [e, p]; linarith
  have hεp : ε⁻¹ ≤ Real.exp p := by
    rw [show ε = Real.exp (-e) from rfl, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hep
  have hbox' : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p :=
    hbox.trans (Real.exp_le_exp.mpr (by dsimp [p]; linarith))
  have hρp' : (ρ : ℝ)⁻¹ ≤ Real.exp p :=
    hρp.trans (Real.exp_le_exp.mpr (by dsimp [p]; linarith))
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_ambient_approximation
    B U b S rowSets x y₀ q d period r hr hb o bW hperiod hM hm hR C hC hchart hbudget
    ρ center width hσ H step c hH hsubset label hcell hu₀ hmodulus hdiv
    Cforward hforward K hK T hT hTideal hsource hradius hσ1 hρ hρ1 hw
    (Real.exp_pos (-e)) hp hbox' hεp hρp'
  refine ⟨F, hF, hFb, ?_⟩
  intro y
  apply (hFe y).trans
  have hmask0 : 0 ≤ maskCap := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _)
    (coefficientDeckPeriodCap_nonneg rowTypes E period)
  calc
    _ ≤ Real.exp Vlog * (Real.exp Nlog * Real.exp Mlog * ε) :=
      mul_le_mul hvolume (mul_le_mul_of_nonneg_right
        (mul_le_mul hnormalizer hmask hmask0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [ε, e]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_ge_one : 1 ≤ allocatedRowSlicedSiteRadius rowSets := by
  apply NNReal.coe_le_coe.mp
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (partitionedIdealRadius_nonneg α m) zero_le_one)))

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in
theorem exists_allocated_supported_affine_bounded_ambient
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog)
    {base : ℝ} (hbase : 0 ≤ base)
    (hvbase : Vlog ≤ base) (hnbase : Nlog ≤ base) (hmbase : Mlog ≤ base)
    (hsites : (Fintype.card (Finset α) : ℝ) ≤ base)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ base)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ≤ Real.exp base)
    (hKbase : (K : ℝ) ≤ Real.exp base)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp base)
    (hrone : 1 ≤ r) (hdbase : (d : ℝ) ≤ Real.exp base) (hpbase : (period : ℝ) ≤ Real.exp base)
    (hrows : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ base)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp base) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let budget := affineAmbientPrimitiveBudget base Q
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith ⟨Real.exp budget, Real.exp_nonneg _⟩ F ∧
      (∀ z, ‖F z‖ ≤ Real.exp budget) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤ Real.exp (-target) := by
  intro p Q budget
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_accurate_ambient
    B U b S rowSets x y₀ q d period r hr hb o bW hperiod hM hm hR C hC hchart hbudget
    ρ center width hσ H step c hH hsubset label hcell hu₀ hmodulus hdiv
    Cforward hforward K hK T hT hTideal hsource hradius hσ1 hρ hρ1 hw
    hPbox hPrho hVlog hNlog hMlog htarget hbox hρp hvolume hnormalizer hmask
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds _ _ hp).1
  have hN : (‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊ : ℝ) ≤ Real.exp base := by
    rw [coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le]
    exact hvolume.trans (Real.exp_le_exp.mpr hvbase)
  have hradone : 1 ≤ allocatedRowSlicedSiteRadius rowSets :=
    allocatedRowSlicedSiteRadius_ge_one rowSets
  have hmask0 : 0 ≤ M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
  have hprim := affineAmbientPrimitive_bounds (d := d) (period := period)
    (gridaxes := Fintype.card gridAxes)
    (N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊)
    (K := K) (coords := ∑ j, Cforward j * Fintype.card (J j))
    (cutoff := normalizedSiteCutoffBound) (r := r) (radius := allocatedRowSlicedSiteRadius rowSets)
    (Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0))
    (height := (S.value : ℝ≥0) ^ (layerTailDegree m + 1))
    hbase hQ hsites haxes hlabels (norm_nonneg _) (hnormalizer.trans (Real.exp_le_exp.mpr hnbase))
    hmask0 (hmask.trans (Real.exp_le_exp.mpr hmbase)) hN hKbase hcoords hcutoff hrone hradone
    hdbase hpbase hrows ((Nat.cast_le.mpr (Fintype.card_subtype_le (allocatedGridAxis (I := I) U b S.value))).trans haxes)
    houtputs hheight
  refine ⟨F, hF.weaken ?_, fun z => (hFb z).trans hprim.1, hFe⟩
  exact NNReal.coe_le_coe.mp hprim.2

end Erdos3.VectorPolynomial

end

end OAI
