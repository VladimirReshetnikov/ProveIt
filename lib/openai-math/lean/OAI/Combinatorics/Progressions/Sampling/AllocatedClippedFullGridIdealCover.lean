import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
import OAI.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} (d : ℕ) (T : Fin m → ℝ)

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedClippedFullGrid_coordinate_bounds
    (z : MixedCoveredJetSource I O E n d)
    (hw : allocatedPhysicalGridCondition B U b S O T ((split z.1).1))
    (hl : ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |allocatedLongJetRealCoordinates B U b S ((split z.1).2) ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (j : Fin m) (t : O j) :
    (∀ i, |(z.1 j).1 i t| ≤ T j * R j) ∧
      (∀ i, |((z.1 j).2 i t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j) := by
  constructor
  · intro i
    exact hl ⟨⟨j, Sum.inl i⟩, by change ¬False; exact not_false⟩ t
  · intro i
    by_cases hg : grid ⟨j, Sum.inr i⟩
    · exact hw j i hg t
    · exact hl ⟨⟨j, Sum.inr i⟩, hg⟩ t

variable [∀ j, Fintype (E j)] [NeZero d]
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] in
include hR in
theorem allocatedClippedFullGridPrefactor_sites_quarter
    (hT : ∀ j, 0 ≤ T j)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, (rowSets j).card * (C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j))) ≤ 1 / 4)
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)))
    (hne : allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z ≠ 0)
    (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  obtain ⟨hw, hl⟩ := allocatedClippedFullGridPrefactor_support B U b S rowSets d T x hb o bW q y₀ f z hz hne
  apply mixedCoveredRowsSiteValue_mem_quarter rowSets U o b d z
    (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)))
    (fun j => mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (hT j) (hR j).le)))
    _ hbudget s
  intro j t
  obtain ⟨hr, hz⟩ := allocatedClippedFullGrid_coordinate_bounds B U b S rowSets d T z hw (hf _ hl) j t
  exact mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg (hT j) (hR j).le) (hchart j) _ _ hr hz

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

@[instance_reducible]
noncomputable def fullGridCoverAxisDecidableEq :
    DecidableEq {a // allocatedGridAxis (I := I) U b S.value a} := Classical.decEq _

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_clipped_full_grid_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j) (T j)) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
          {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ),
        (∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
          |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1) →
        ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedClippedFullGridSiteProfile B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_cover_site_expansion (G := G)
    (A := gridAxes) (S := Finset (Fin dim)) B U b e ig hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, ?_⟩
  intro x f hf X p hp hm v
  by_cases hy : physicalCubeRowSample U d rows p hm v ∈ chart '' region
  · obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, allocatedClippedFullGridGlobalPrefactor_apply B U b S rowSets d T x hb o bW q y₀ f z,
      allocatedClippedFullGridSiteProfile_mixed B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e z hz]
    by_cases hzero : allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z = 0
    · rw [hzero, zero_mul, zero_mul]
    · have hs := allocatedClippedFullGridPrefactor_sites_quarter B U b S rowSets d T hR x hb o bW q y₀ f
        hT hf C hC hchart
        (fun j => finiteRowChartRadius_budget _ _ (hC j) (hT j) (hR j).le (hsmall j)) z hz hzero
      have hmatch := physicalRowChart_base_matching U o b hb bW d p hp hm v z hzy
      have hval := hv
        (fun s => physicalEuclideanSitePoint U p hm (fun z => (physicalCubeVertexValue v s z : ℝ)))
        (fun s j => mixedArrayRegroup (I j) (Fin (n j)) Unit
          ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) hmatch
        (fun s j i => (hs s j (Set.mem_univ j) () (Set.mem_univ ())).1 i)
      apply congrArg (fun a : ℂ =>
        allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z * a)
      rw [allocatedFullGridSiteApproximation_mixed B U b S rowSets d e z]
      simpa only [allocatedGridNaturalScale, physicalEuclideanSitePoint_apply,
        mixedArrayRegroup_apply] using hval.symm
  · rw [allocatedClippedFullGridSiteProfile_zero B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e _ hy,
      allocatedClippedFullGridGlobalPrefactor_zero B U b S rowSets d T x hb o bW q y₀ f _ hy,
      zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

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

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_clipped_full_grid_ideal_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedClippedFullGridSiteProfile B U b S rowSets d (allocatedIdealCoverSupport (G := G) B rowSets)
                hR hσ x hb o bW q y₀ hcell
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ) e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedClippedFullGridGlobalPrefactor B U b S rowSets d (allocatedIdealCoverSupport (G := G) B rowSets)
                x hb o bW q y₀
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_clipped_full_grid_cover B U b hR hσ S
    d q y₀ hcell hb o bW e he Q hQ Cforward hforward K hK
    (allocatedIdealCoverSupport (G := G) B rowSets) (allocatedIdealCoverSupport_nonneg (G := G) B rowSets)
    C hC hchart hsmall
  refine ⟨g, hg, hc, ?_⟩
  intro δ hδ hδ1 x X p hp hm v
  exact hv x (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    (allocatedPhysicalLongIdeal_cover_support B U b hR S rowSets δ hδ hδ1) p hp hm v

end Erdos3.VectorPolynomial

end

end OAI
