import OAI.Combinatorics.Progressions.Estimates.PhysicalCubeWindowReindex
import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

noncomputable def allocatedAmbientSpatialWeight (u : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  ∑ t : terms, (coeff (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)) *
    ∏ s, twist r.val a.val t s (physicalCubeVertexValue u s)

noncomputable def allocatedAmbientGridIdealValue
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  ∑ kg : ∀ i, ((coverWitness r).expansion i).Term,
    ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
      ∑ k : K,
        (coverSiteCoefficient (coverWitness r).expansion kg *
          allocatedProductMaskedIdealCoefficient B U b S rowSets x
            (coverWitness r).representative refined d period cI label k) *
          ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
            (g r kg s (fun j => (((eval (fun z => (physicalCubeVertexValue u s z : ℝ)) (p j.1) j.2) /
                commonSitePeriod (coverWitness r).expansion kg : ℝ) : UnitAddCircle)) *
              allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period
                (label s) (fI k s) (physicalSingleSiteValue U d p hm
                  (fun z => (physicalCubeVertexValue u s z : ℝ))))

local notation "weight" => allocatedAmbientSpatialWeight (τ := τ) B U b S X modulus q wholeReference
  x hM selection hx N hW mesh base cells r a
local notation "gridIdeal" => allocatedAmbientGridIdealValue B U b S X modulus q coverWitness
  hb o bW d g x p hm r period cI fI
local notation "ambient" => allocatedAmbientMaskedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI

theorem allocatedAmbientMaskedSpatialApproximation_factor
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ) :
    ambient test u = weight u * gridIdeal test u := by
  unfold allocatedAmbientMaskedSpatialApproximation allocatedAmbientSpatialWeight allocatedAmbientGridIdealValue
  dsimp only
  rw [Finset.sum_mul]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro kg _
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem allocatedAmbientSpatialWeight_reconstruction (hq : ∀ z, 0 < q z)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    weight (point v) =
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh
        (principalResidueLabel modulus (wholeReference r.val)) v / ((volume : ℝ) : ℂ) := by
  have h := allocatedRecenteredResidueWeight_expansion (τ := τ) B U b S X modulus q
    wholeReference x N mesh base hM selection hx hW cells hq r.val a v (fun _ _ => 1)
  simpa only [allocatedAmbientSpatialWeight, allocatedRecenteredResidueWeight,
    physicalCubeSiteTest, Finset.prod_const_one, mul_one, one_mul] using h.symm

theorem allocatedAmbientSpatialWeight_zero_off_image (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hu : u ∉ Set.range point) : weight u = 0 := by
  unfold allocatedAmbientSpatialWeight
  apply Finset.sum_eq_zero
  intro t _
  have hz : (∏ s, twist r.val a.val t s (physicalCubeVertexValue u s)) = 0 := by
    by_contra hn
    apply hu
    exact physicalResidueSpatialSiteFactor_prod_nonzero_mem_range
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r.val))
      (allocatedPhysicalCubeDirections B U b S x (wholeReference r.val)) base
      (boundedColumnResidueRepresentative q a.val) q 4 mesh (trimmedSpatialRootScale τ N q) t u hn
  rw [hz, mul_zero]

theorem allocatedAmbientSpatialWeight_zero_outside_window
    (hq : ∀ z, 0 < q z) (hH : ∀ z, 0 < trimmedSpatialRootScale τ N q z)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < (mesh : ℝ)) (hmargin : 3 + 2 * (mesh : ℝ) ≤ 4)
    (v : X → (Unit ⊕ Fin dim) → ℤ)
    (hv : v ∉ spatialWindow (trimmedSpatialRootScale τ N q) 4) :
    weight (point v) = 0 := by
  rw [allocatedAmbientSpatialWeight_reconstruction B U b S X modulus q wholeReference x hM
    selection hx N hW mesh base cells r a hq]
  have hv' : v ∉ spatialWindow (trimmedSpatialRootScale τ N q) (3 + 2 * (mesh : ℝ)) :=
    fun h => hv (spatialWindow_radius_mono _ (fun z => (hH z).le) hmargin h)
  rw [allocatedResidueSpatialKernel_zero_outside B U b S x X hM selection hx modulus
    (trimmedSpatialRootScale τ N q) hW mesh hbudget hH hmesh
    (principalResidueLabel modulus (wholeReference r.val)) v hv', zero_div]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

theorem finiteNestedCubeMixtureMean
    {T L K Ω : Type*} [Fintype T] [Fintype L] [Fintype K] [Fintype Ω]
    {D : T → Type*} [∀ t, Fintype (D t)] (a : ℂ) (c : T → L → K → ℂ)
    (value : ∀ t, L → K → D t → Ω → ℂ) :
    a * (𝔼 ω, ∑ t, ∑ l, ∑ k, ∑ d, c t l k * value t l k d ω) =
      ∑ t, ∑ l, ∑ k, ∑ d, (a * c t l k) * (𝔼 ω, value t l k d ω) := by
  simp only [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_expect, mul_assoc]

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "ambient" => allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI
local notation "recentered" => allocatedRecenteredNormalizedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI

theorem allocatedAmbientNormalizedSpatialApproximation_mixture [DecidableEq X]
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    (integerBoxCubeCount N dim : ℂ) *
      (𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
        ambient test ((physicalCubeParametersEquiv X dim).symm cube.val)) =
      ∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
        ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
          ∑ k : K,
            ∑ gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
              ((integerBoxCubeCount N dim : ℂ) *
                ((coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
                  coverSiteCoefficient (coverWitness r).expansion t.2 *
                  allocatedProductMaskedIdealCoefficient B U b S rowSets x
                    (coverWitness r).representative refined d period cI label k)) *
                𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                  let u : X → (Unit ⊕ Fin dim) → ℤ := (physicalCubeParametersEquiv X dim).symm cube.val
                  ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
                    allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
                      hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
                      (gridLabel s) (physicalCubeVertexValue u s) := by
  let coefficient (t : terms × (∀ i, ((coverWitness r).expansion i).Term))
      (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))
      (k : K) : ℂ :=
    (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2 *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x
        (coverWitness r).representative refined d period cI label k
  let value (t : terms × (∀ i, ((coverWitness r).expansion i).Term))
      (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))
      (k : K)
      (gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)))
      (cube : SupportedCube dim (integerBox N : Set (X → ℤ))) : ℂ :=
    let u : X → (Unit ⊕ Fin dim) → ℤ := (physicalCubeParametersEquiv X dim).symm cube.val
    ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
      allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
        hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
        (gridLabel s) (physicalCubeVertexValue u s)
  have h := finiteNestedCubeMixtureMean (integerBoxCubeCount N dim : ℂ) coefficient value
  dsimp only [coefficient, value] at h
  unfold allocatedAmbientNormalizedSpatialApproximation
  dsimp only
  convert h using 1
  apply congrArg (fun z : ℂ => (integerBoxCubeCount N dim : ℂ) * z)
  refine Finset.expect_congr (by ext z; simp only [Finset.mem_univ]) ?_
  intro cube _
  refine Finset.sum_congr (by ext z; simp only [Finset.mem_univ]) ?_
  intro t _
  refine Finset.sum_congr (by ext z; simp only [Finset.mem_univ]) ?_
  intro label _
  refine Finset.sum_congr (by ext z; simp only [Finset.mem_univ]) ?_
  intro k _
  refine Finset.sum_congr (by ext z; simp only [Finset.mem_univ]) ?_
  intro gridLabel _
  rfl

variable
    (hsite : ∀ (kg : ∀ i, ((coverWitness r).expansion i).Term)
      (s : Finset (Fin dim)) (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g r kg s (fun v => ((((u₀ v.1).val v.2) / commonSitePeriod (coverWitness r).expansion kg : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) (coverWitness r).expansion (allocatedGridIntegerAxis B U b S) kg s
          (fun i => ((w₀ (allocatedGridIntegerAxis B U b S i).1).2 (allocatedGridIntegerAxis B U b S i).2 : ZMod (((coverWitness r).expansion i).period (kg i))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1)) C j)
    (hN : ∀ z, 0 < N z)

include hR hsite hC hchart hsmall hN

theorem allocatedAmbientNormalizedSpatialApproximation_zero_off_image
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hu : u ∉ Set.range point) : ambient test u = 0 := by
  rw [← allocatedAmbientMaskedSpatialApproximation_normalized (τ := τ) B U b hR S X modulus q
    wholeReference coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period
    cI fI hsite C hC hchart hsmall hN test u]
  rw [allocatedAmbientMaskedSpatialApproximation_factor,
    allocatedAmbientSpatialWeight_zero_off_image B U b S X modulus q wholeReference x hM
      selection hx N hW mesh base cells r a u hu, zero_mul]

theorem allocatedAmbientNormalizedSpatialApproximation_zero_outside_window
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < (mesh : ℝ)) (hmargin : 3 + 2 * (mesh : ℝ) ≤ 4)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (hv : v ∉ spatialWindow (trimmedSpatialRootScale τ N q) 4) : ambient test (point v) = 0 := by
  rw [← allocatedAmbientMaskedSpatialApproximation_normalized (τ := τ) B U b hR S X modulus q
    wholeReference coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period
    cI fI hsite C hC hchart hsmall hN test (point v)]
  rw [allocatedAmbientMaskedSpatialApproximation_factor,
    allocatedAmbientSpatialWeight_zero_outside_window B U b S X modulus q wholeReference x hM
      selection hx N hW mesh base cells r a hq
      (fun z => (trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)).1)
      hbudget hmesh hmargin v hv, zero_mul]

variable [DecidableEq X]

theorem allocatedNormalizedSpatial_sum_eq_genuine_cube_mean
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < (mesh : ℝ)) (hmargin : 3 + 2 * (mesh : ℝ) ≤ 4)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
      recentered (fun s => integerBoxTestExtension N (test s)) v) =
      (integerBoxCubeCount N dim : ℂ) *
        𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
          ambient test ((physicalCubeParametersEquiv X dim).symm cube.val) := by
  have hbox : ∀ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
      ambient (fun s => integerBoxTestExtension N (test s)) (point v) ≠ 0 →
        ∀ s, physicalCubeVertexValue (point v) s ∈ integerBox N := by
    intro v _ hv
    apply (mem_physicalIntegerBoxCubes N dim (point v)).mp
    exact allocatedAmbientNormalizedSpatialApproximation_testExtension_nonzero_mem_box
      B U b S X modulus q wholeReference coverWitness hb o bW d x hM selection hx N hW mesh
      base cells p hm r a period cI fI test (point v) hv
  have hwindow : ∀ v, v ∉ spatialWindow (trimmedSpatialRootScale τ N q) 4 →
      ambient (fun s => integerBoxTestExtension N (test s)) (point v) = 0 := by
    intro v hv
    exact allocatedAmbientNormalizedSpatialApproximation_zero_outside_window
      B U b hR S X modulus q wholeReference coverWitness hb o bW d g x hM selection hx N hW mesh
      base cells p hm r a period cI fI hsite C hC hchart hsmall hN hq hτ hbudget hmesh hmargin
      (fun s => integerBoxTestExtension N (test s)) v hv
  have hresidue : ∀ u, ambient (fun s => integerBoxTestExtension N (test s)) u ≠ 0 →
      u ∈ Set.range point := by
    intro u hu
    by_contra hn
    apply hu
    exact allocatedAmbientNormalizedSpatialApproximation_zero_off_image
      B U b hR S X modulus q wholeReference coverWitness hb o bW d g x hM selection hx N hW mesh
      base cells p hm r a period cI fI hsite C hC hchart hsmall hN
      (fun s => integerBoxTestExtension N (test s)) u hn
  have hsum := physicalResidueWindow_sum_eq_count_mul_mean
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r.val))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r.val)) base
    (boundedColumnResidueRepresentative q a.val) q N hq
    (spatialWindow (trimmedSpatialRootScale τ N q) 4)
    (ambient (fun s => integerBoxTestExtension N (test s))) hbox hwindow hresidue
  calc
    _ = ∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        ambient (fun s => integerBoxTestExtension N (test s)) (point v) := by
      simp only [allocatedAmbientNormalizedSpatialApproximation_reconstruction]
    _ = (integerBoxCubeCount N dim : ℂ) *
        𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
          ambient (fun s => integerBoxTestExtension N (test s))
            ((physicalCubeParametersEquiv X dim).symm cube.val) := hsum
    _ = _ := by
      apply congrArg (fun z : ℂ => (integerBoxCubeCount N dim : ℂ) * z)
      apply Finset.expect_congr rfl
      intro cube _
      apply allocatedAmbientNormalizedSpatialApproximation_testExtension_eq
      exact Finset.mem_image.mpr ⟨cube, Finset.mem_univ _, rfl⟩

theorem allocatedNormalizedSpatial_sum_eq_genuine_cube_mixture
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < (mesh : ℝ)) (hmargin : 3 + 2 * (mesh : ℝ) ≤ 4)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
      recentered (fun s => integerBoxTestExtension N (test s)) v) =
      ∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
        ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
          ∑ k : K,
            ∑ gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
              ((integerBoxCubeCount N dim : ℂ) *
                ((coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
                  coverSiteCoefficient (coverWitness r).expansion t.2 *
                  allocatedProductMaskedIdealCoefficient B U b S rowSets x
                    (coverWitness r).representative refined d period cI label k)) *
                𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                  let u : X → (Unit ⊕ Fin dim) → ℤ := (physicalCubeParametersEquiv X dim).symm cube.val
                  ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
                    allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
                      hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
                      (gridLabel s) (physicalCubeVertexValue u s) := by
  exact (allocatedNormalizedSpatial_sum_eq_genuine_cube_mean B U b hR S X modulus q wholeReference
    coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI
    hsite C hC hchart hsmall hN hq hτ hbudget hmesh hmargin test).trans
      (allocatedAmbientNormalizedSpatialApproximation_mixture B U b S X modulus q wholeReference
        coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test)

end Erdos3.VectorPolynomial

end

end OAI
