import OAI.Combinatorics.Progressions.Lattices.AllocatedCommonResidueMask

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {A α : Type*} [Fintype A] [Fintype α] (e : A → ScalarSiteExpansion (Finset α))
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (r : ℝ≥0) (hr : 0 < r) (k : ∀ a, (e a).Term) (s : Finset α)
variable (f : (LayerSamplerAxis I n → ℝ) → ℂ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j a, coefficients (p j) a ∈ U j)

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "base" => (fun w : MixedCoveredJetSource I single E n d =>
  fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit ((Prod.fst w) j) ())

variable {Ksp : Type*} [Fintype Ksp]
variable (root : Ksp → ℤ) (spatialD : Matrix α Ksp ℤ) (spatialBase : X → ℤ)
variable [Fintype X] (spatialResidue : Option Ksp × X → ℤ) (q : X → ℕ)
variable (box : ℝ) (mesh : ℝ≥0) (H N : X → ℝ) {spatialModulus : ℕ}
variable (t : X → SpatialSiteLabel α spatialModulus box mesh)
variable [∀ a, NeZero ((e a).period (k a))]

variable {M period : ℕ}
variable (hs : ∀ x, q x * spatialModulus ∣ M)
variable (hgM : ∀ a, (e a).period (k a) ∣ M) (hi : period ∣ M)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))

noncomputable def allocatedNormalizedCommonSiteFactor
    (gridLabel : ∀ a, ZMod ((e a).period (k a))) (u : X → ℤ)
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d) : ℂ :=
  allocatedCommonResidueMask e k selected root spatialD spatialBase spatialResidue q box mesh
    hs hgM hi t s label gridLabel (fun x => (u x : ZMod M)) (mixedCoveredSiteResidue d M w) *
    normalizedSiteTwistProduct
      (physicalResidueSpatialSmooth root spatialD spatialBase spatialResidue q box mesh H N t s)
      (allocatedNormalizedGridIdealFactor B U b S e selected r hr k s gridLabel f)
      ((fun x => (u x : ℝ) / N x), allocatedFullMixedSiteValue (R := R) U b (base w))

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedPhysicalSiteTwist_common_smallBox
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hg : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun a => ((((u₀ a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => ((w₀ (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (u : X → ℤ) (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j)))
    (hphysical : chart w = physicalSingleSiteValue U d p hm (fun x => (u x : ℝ)))
    (hN : ∀ x, N x ≠ 0) :
    (physicalResidueSpatialSiteFactor root spatialD spatialBase spatialResidue q box mesh H t s u *
      g (fun a => (((eval (fun x => (u x : ℝ)) (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (physicalSingleSiteValue U d p hm (fun x => (u x : ℝ))) =
      ∑ gridLabel : ∀ a, ZMod ((e a).period (k a)),
        allocatedNormalizedCommonSiteFactor B U b S e selected r hr k s f d
          root spatialD spatialBase spatialResidue q box mesh H N t hs hgM hi label gridLabel u w := by
  simp only [allocatedNormalizedCommonSiteFactor, allocatedCommonResidueMask_eval, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  conv_rhs =>
    arg 2
    arg 2
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
  rw [allocatedNormalizedGridIdealFactor_smallBox B U b S e selected r hr k s f
    o hb bW d p hm (fun x => (u x : ℝ)) hR C hC hchart hbudget g hg period label w hw hphysical]
  rw [physicalResidueSpatialSiteFactor_normalized root spatialD spatialBase spatialResidue q
    box mesh H N t s hN u]
  dsimp only [normalizedSiteTwistProduct, mixedArrayRegroup_apply]
  ring_nf

include hR hC hchart hbudget in
theorem allocatedPhysicalSiteTwist_common_global
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hg : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun a => ((((u₀ a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => ((w₀ (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (hN : ∀ x, N x ≠ 0) (u : X → ℤ) :
    (physicalResidueSpatialSiteFactor root spatialD spatialBase spatialResidue q box mesh H t s u *
      g (fun a => (((eval (fun x => (u x : ℝ)) (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (physicalSingleSiteValue U d p hm (fun x => (u x : ℝ))) =
      ∑ gridLabel : ∀ a, ZMod ((e a).period (k a)),
        restrictedComplexChartDensity chart
          (mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j))) 1
          (allocatedNormalizedCommonSiteFactor B U b S e selected r hr k s f d
            root spatialD spatialBase spatialResidue q box mesh H N t hs hgM hi label gridLabel u)
          (physicalSingleSiteValue U d p hm (fun x => (u x : ℝ))) := by
  let region := mixedCoveredJetRegion (I := I) (E := E) U o b d
    (fun j (_ : Unit) => standardLatticeSmallBox (J j))
  let y := physicalSingleSiteValue U d p hm (fun x => (u x : ℝ))
  by_cases hmem : y ∈ chart '' region
  · obtain ⟨w, hw, hy⟩ := hmem
    dsimp only [y] at hy
    have heq := allocatedPhysicalSiteTwist_common_smallBox B U b S e selected r hr k s f
      o hb bW d p hm root spatialD spatialBase spatialResidue q box mesh H N t hs hgM hi label
      hR C hC hchart hbudget g hg u w hw hy hN
    apply heq.trans
    apply Finset.sum_congr rfl
    intro gridLabel _
    symm
    rw [← hy]
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Set.Subset.rfl)) hw]
    simp only [Complex.ofReal_one, one_mul]
  · have hquarter : y ∉ chart '' mixedCoveredJetRegion U o b d
        (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
      intro h
      apply hmem
      exact Set.image_mono (mixedCoveredJetRegion_mono U o b d
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) h
    have hz : allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y = 0 :=
      restrictedComplexChartDensity_zero _ _ _ _ hquarter
    change (_ * _) * allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y = _
    rw [hz, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro gridLabel _
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

omit [∀ j, Fintype (E j)] [NeZero d] [∀ a, NeZero ((e a).period (k a))] in
include hR in
theorem allocatedNormalizedCommonSiteFactor_norm
    {T Vg Cg Hg : A → ℝ} {L LI Lsp : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (Vg a) (Cg a) L (Hg a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (hf : ∀ y, ‖f y‖ ≤ 1)
    (hI : LipschitzWith LI (bufferedCoordinateProjection
      (allocatedGridAxis (I := I) U b S.value) r hr f))
    (hmesh : 0 < mesh) (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ Lsp)
    (gridLabel : ∀ a, ZMod ((e a).period (k a))) (u : X → ℤ)
    (w : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d) :
    ‖allocatedNormalizedCommonSiteFactor B U b S e selected r hr k s f d
      root spatialD spatialBase spatialResidue q box mesh H N t hs hgM hi label gridLabel u w‖ ≤ 1 := by
  have hsp := physicalResidueSpatialSmooth_bounds root spatialD spatialBase spatialResidue q
    box mesh H N t s hmesh hscale
  have hgrid := allocatedNormalizedGridIdealFactor_bounds B U b S e selected r hr k s gridLabel f
    hR he Q hQ hf hI
  have hprod := normalizedSiteTwistProduct_bounds _ _ hsp.2 hgrid.2 hsp.1 hgrid.1
  rw [allocatedNormalizedCommonSiteFactor, norm_mul]
  exact (mul_le_mul
    (allocatedCommonResidueMask_norm e k selected root spatialD spatialBase spatialResidue q
      box mesh hs hgM hi t s label gridLabel _ _) (hprod.1 _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Erdos3.VectorPolynomial

end

end OAI
