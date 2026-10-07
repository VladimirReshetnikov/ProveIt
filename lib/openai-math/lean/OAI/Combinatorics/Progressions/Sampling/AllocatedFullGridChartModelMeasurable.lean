/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.AllocatedProductSiteSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

noncomputable def allocatedProductFullGridPrefactor (y : EuclideanJetLayers U rowTypes) : ℂ :=
  cutoff y * (1 / (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y : ℂ))

theorem allocatedProductFullGridPrefactor_zero (y : EuclideanJetLayers U rowTypes)
    (hy : y ∉ chart '' region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y = 0 := by
  have hp : allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y = 0 := by
    unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
    exact restrictedChartDensity_zero _ _ _ _ hy
  rw [allocatedProductFullGridPrefactor, hp, Complex.ofReal_zero, mul_zero, mul_zero]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

noncomputable def allocatedProductFullGridProfile
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U rowTypes) : ℂ :=
  cutoff y * allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e y

theorem allocatedProductFullGridProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e (chart z) =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedProductFullGridProfile,
    allocatedFullGridSiteProfile_mixed B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz]
  unfold allocatedProductFullGridPrefactor allocatedFullGridSiteChartPrefactor
  exact (mul_assoc _ _ _).symm

theorem allocatedProductFullGridProfile_zero
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y = 0 := by
  rw [allocatedProductFullGridProfile, allocatedFullGridSiteProfile,
    allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, zero_mul, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

noncomputable def allocatedFullGridChartModel
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) : EuclideanJetLayers U rowTypes → ℂ :=
  allocatedComplexGridMultiplier B U b S rowTypes hb o bW d
    (allocatedFullGridSiteApproximation B U b S rowSets e)

theorem allocatedFullGridChartModel_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedFullGridChartModel B U b S rowSets d hb o bW e (chart z) =
      allocatedFullGridSiteApproximation B U b S rowSets e
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) :=
  allocatedComplexGridMultiplier_apply B U b S rowTypes hb o bW d _ z hz

theorem allocatedFullGridChartModel_norm_le
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ ∏ a, Cc a := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz,
      allocatedFullGridSiteApproximation, siteFamilyEval_eq, norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun axis _ => (e axis).eval_norm_le (he axis) _ _)
  · rw [allocatedFullGridChartModel, allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, norm_zero]
    exact Finset.prod_nonneg (fun a _ => (Finset.sum_nonneg (fun k _ => norm_nonneg _)).trans (he a).coefficient_le)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedProductFullGridProfile_eq_model
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedProductFullGridProfile_mixed B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e z hz,
      allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz]
  · rw [allocatedProductFullGridProfile_zero B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ f y hy, zero_mul]

theorem allocatedProductFullGridProfile_prefactor_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (herr : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ η * ∏ a, Cc a := by
  rw [allocatedProductFullGridProfile_eq_model B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y,
    ← sub_mul, norm_mul]
  exact mul_le_mul (herr y) (allocatedFullGridChartModel_norm_le B U b S rowSets d hb o bW e he y)
    (norm_nonneg _) hη

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_product_full_grid_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (r : ℝ≥0) (hr : 0 < r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
      (Fintype.card (Finset (Fin dim)) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
          {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
        {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_cover_site_expansion (G := G)
    (A := gridAxes) (S := Finset (Fin dim)) B U b e ig hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, ?_⟩
  intro x f X p hp hm v
  by_cases hy : physicalCubeRowSample U d rows p hm v ∈ chart '' region
  · obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, allocatedProductFullGridProfile_mixed B U b S rowSets d r hr x hb o bW q y₀ f
      hR hσ hcell e z hz]
    by_cases hzero : allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) = 0
    · rw [hzero, zero_mul, zero_mul]
    · have hcut : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) ≠ 0 :=
        (mul_ne_zero_iff.mp hzero).1
      have hs := allocatedProductSiteCutoff_sites_quarter B U b S rowSets o hb bW d r hr hR
        C hC hchart hbudget z hz hcut
      have hmatch := physicalRowChart_base_matching U o b hb bW d p hp hm v z hzy
      have hval := hv
        (fun s => physicalEuclideanSitePoint U p hm (fun z => (physicalCubeVertexValue v s z : ℝ)))
        (fun s j => mixedArrayRegroup (I j) (Fin (n j)) Unit
          ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) hmatch
        (fun s j i => (hs s j (Set.mem_univ j) () (Set.mem_univ ())).1 i)
      apply congrArg (fun a : ℂ =>
        allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) * a)
      rw [allocatedFullGridSiteApproximation_mixed B U b S rowSets d e z]
      simpa only [allocatedGridNaturalScale, physicalEuclideanSitePoint_apply,
        mixedArrayRegroup_apply] using hval.symm
  · rw [allocatedProductFullGridProfile_zero B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e _ hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ f _ hy, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

theorem allocatedFullGridChartModel_measurable
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) :
    Measurable (allocatedFullGridChartModel B U b S rowSets d hb o bW e) := by
  let : ∀ a : gridAxes, Countable (CoefficientJetAxisRow rowTypes a.val) := by
    intro a
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change Countable (rowTypes j → ℤ)
      infer_instance
  let : ∀ a : gridAxes, MeasurableSingletonClass (CoefficientJetAxisRow rowTypes a.val) := by
    intro a
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change MeasurableSingletonClass (rowTypes j → ℤ)
      infer_instance
  exact allocatedComplexGridMultiplier_measurable B U b S rowTypes hb o bW d _
    (measurable_of_countable _)

end Erdos3.VectorPolynomial

end

end OAI
