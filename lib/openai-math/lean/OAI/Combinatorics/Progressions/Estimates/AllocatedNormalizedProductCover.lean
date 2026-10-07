import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable

namespace OAI

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

theorem exists_allocated_normalized_product_full_grid_cover
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
      (∀ k s (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g k s (fun a => ((((u a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) e ig k s
            (fun a => ((w (ig a).1).2 (ig a).2 : ZMod ((e a).period (k a))))
            (allocatedFullMixedSiteValue (R := R) U b w) / 2) ∧
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
  obtain ⟨g, hg, hc, hsite, hv⟩ := exists_allocated_normalized_cover_site_expansion (G := G)
    (A := gridAxes) (S := Finset (Fin dim)) B U b e ig hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, hsite, ?_⟩
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

end OAI
