/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.SupportMaskComplexMean
import OAI.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridIdealCover

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical Matrix

variable {α : Type*} [DecidableEq α]

theorem rowRestrictedSiteMatrix_real_bound (rows : Finset (Finset α))
    (v : rows → ℝ) {T : ℝ} (hT : 0 ≤ T) (hv : ∀ t, |v t| ≤ T) (s : Finset α) :
    |∑ t : rows, (rowRestrictedSiteMatrix rows s t : ℝ) * v t| ≤ rows.card * T := by
  calc
    _ ≤ ∑ t : rows, |(rowRestrictedSiteMatrix rows s t : ℝ) * v t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : rows, T := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t.val ⊆ s
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix, ite_eq_left ht,
          Int.cast_one, one_mul] using hv t
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix, ite_eq_right ht,
          Int.cast_zero, zero_mul, abs_zero] using hT
    _ = _ := by simp

namespace VectorPolynomial

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

omit [∀ j, Fintype (I j)] in
include hR in
theorem mixedCoveredRowsSiteValue_full_coordinate_bound
    (z : MixedCoveredJetSource I rowTypes E n d) (T : Fin m → ℝ)
    (hT : ∀ j, 0 ≤ T j)
    (hreal : ∀ j t i, |(z.1 j).1 i t| ≤ T j * R j)
    (hint : ∀ j t i, |((z.1 j).2 i t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j)
    (s : Finset α) (a : LayerSamplerAxis I n) :
    |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤
      (rowSets a.1).card * T a.1 := by
  rcases a with ⟨j, i | i⟩
  · change |(∑ t : rowTypes j, (rowRestrictedSiteMatrix (rowSets j) s t : ℝ) * (z.1 j).1 i t) / R j| ≤ _
    simp only [Finset.sum_div, mul_div_assoc]
    apply rowRestrictedSiteMatrix_real_bound (rowSets j) (fun t => (z.1 j).1 i t / R j) (hT j)
      (fun t => ?_) s
    rw [abs_div, abs_of_pos (hR j)]
    exact (div_le_iff₀ (hR j)).mpr (hreal j t i)
  · change |((∑ t : rowTypes j, rowRestrictedSiteMatrix (rowSets j) s t * (z.1 j).2 i t : ℤ) : ℝ) /
        basisAxisScale (b j) i / R j| ≤ _
    simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div, mul_div_assoc]
    apply rowRestrictedSiteMatrix_real_bound (rowSets j)
      (fun t => ((z.1 j).2 i t : ℝ) / basisAxisScale (b j) i / R j) (hT j) (fun t => ?_) s
    rw [abs_div, abs_of_pos (hR j)]
    exact (div_le_iff₀ (hR j)).mpr (hint j t i)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

noncomputable def allocatedProductSiteCutoff (y : EuclideanJetLayers U rowTypes) : ℂ :=
  ∏ s : Finset α, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)

theorem allocatedProductSiteCutoff_norm (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y‖ ≤ 1 := by
  rw [allocatedProductSiteCutoff, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro s _
  exact allocatedBufferedSiteChartFactor_norm_le B U b S o hb bW d r hr (fun _ => 1)
    (fun _ => by simp) _

theorem allocatedProductSiteCutoff_eq_one (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤ (r : ℝ)) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) = 1 := by
  unfold allocatedProductSiteCutoff
  apply Finset.prod_eq_one
  intro s _
  have hval : allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) = 1 := by
    rw [allocatedBufferedMixedSiteFactor_eq B U b S r hr (fun _ => 1) _ (hbox s)]
  have hs := allocatedBufferedMixedSiteFactor_nonzero_mem_quarter B U b S r hr (fun _ => 1)
    hR o d (mixedCoveredRowsSiteValue rowSets d z s) (by rw [hval]; exact one_ne_zero) C hC hchart hbudget
  rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
    allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d
        (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hs,
    Complex.ofReal_one, one_mul, hval]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hT hsource hradius hC hchart hbudget in
theorem allocatedProductSiteCutoff_fixes_source (hσ1 : ∀ j, σ j ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ)
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : rowTypes a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
        (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    by_cases hzero : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f (chart z) = 0
    · rw [hzero, Complex.ofReal_zero, mul_zero]
    have hmul : allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y₀)
        (principalAxisRestrict (fun a => ¬grid a) y₀) rows ((split z.1).1) *
        allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) ≠ 0 := by
      intro he
      apply hzero
      rw [allocatedWholeMaskedCoveredProfile_grid_multiplier]
      dsimp only
      rw [allocatedChartGridMultiplier_apply B U b S rowTypes hb o bW d _ z hz]
      exact he
    have hg := (mul_ne_zero_iff.mp hmul).1
    have hfne : f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) ≠ 0 := by
      intro he
      apply (mul_ne_zero_iff.mp hmul).2
      unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
      rw [restrictedChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d
          (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz]
      simp only [allocatedLongProfileDensity, he, mul_zero, zero_div]
    have hw : allocatedPhysicalGridCondition B U b S rowTypes T ((split z.1).1) := by
      intro j i hga t
      exact (allocatedGridJetDensity_scaled_support_bound B U b hR hσ S x
        (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
        rows z.1 hg j (hσ1 j) i hga t).trans
        (mul_le_mul_of_nonneg_right (hsource j) (hR j).le)
    have hcoords := allocatedClippedFullGrid_coordinate_bounds B U b S rowSets d T z hw (hf _ hfne)
    have hbox (s : Finset α) (a : LayerSamplerAxis I n) :
        |allocatedFullMixedSiteValue (R := R) U b
          (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤ (r : ℝ) :=
      (mixedCoveredRowsSiteValue_full_coordinate_bound rowSets U b hR d z T hT
        (fun j t => (hcoords j t).1) (fun j t => (hcoords j t).2) s a).trans (hradius a.1)
    rw [allocatedProductSiteCutoff_eq_one B U b S rowSets o hb bW d r hr hR C hC hchart hbudget z hbox,
      one_mul]
  · have hzero : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y = 0 := by
      unfold allocatedWholeMaskedCoveredProfile allocatedCoveredProfileDensity
      exact restrictedChartDensity_zero _ _ _ _ hy
    rw [hzero, Complex.ofReal_zero, mul_zero]

include hT hsource hradius hC hchart hbudget in
theorem allocatedProductSiteCutoff_weighted_error (hσ1 : ∀ j, σ j ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value) (q : ℕ) [NeZero q]
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : rowTypes a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (weight target : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (y : EuclideanJetLayers U rowTypes) :
    let law := principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let original := law.complexMean (fun y₀ => weight (principalResidueLabel q y₀) *
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ))
    let raw := original - (law.fiberLaw (principalResidueLabel q)).complexMean (fun a => weight a * target a)
    let clipped := original - (law.fiberLaw (principalResidueLabel q)).complexMean
      (fun a => weight a * (allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y * target a))
    clipped = allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y * raw ∧ ‖clipped‖ ≤ ‖raw‖ := by
  intro law original raw clipped
  have he : clipped = allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y * raw := by
    exact supportMask_weighted_complexMean_difference law (law.fiberLaw (principalResidueLabel q))
      (principalResidueLabel q) weight
      (fun y₀ => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ))
      target (allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y)
      (fun y₀ => allocatedProductSiteCutoff_fixes_source B U b S rowSets o hb bW d r hr hR hσ T hT
        hsource hradius C hC hchart hbudget hσ1 x y₀ q f hf y)
  refine ⟨he, ?_⟩
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_right (allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d r hr y)
    (norm_nonneg raw)).trans_eq (one_mul _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductIdealSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j,
    add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))⟩

theorem allocatedProductIdealSiteRadius_one_le : 1 ≤ allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))

theorem allocatedProductIdealSiteRadius_pos : 0 < allocatedProductIdealSiteRadius (G := G) B rowSets :=
  zero_lt_one.trans_le (allocatedProductIdealSiteRadius_one_le B rowSets)

theorem allocatedProductIdealSiteRadius_dominates (j : Fin m) :
    (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
      allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
    1 + ∑ k : Fin m, (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k
  exact (Finset.single_le_sum
    (f := fun k : Fin m => (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets k))
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

variable [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets

theorem allocatedProductSiteCutoff_fixes_physical_ideal
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ finiteRowChartRadius 1 (Fintype.card (I j)) (C j) (2 * (radius : ℝ)))
    (x : G → IntegerScalarCubeBox α S.value)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d radius
        (allocatedProductIdealSiteRadius_pos B rowSets) y *
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y : ℂ) := by
  have hbudget (j : Fin m) :
      C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j)) ≤ 1 / 4 := by
    simpa only [Nat.cast_one, one_mul] using
      finiteRowChartRadius_budget 1 (Fintype.card (I j)) (hC j)
        (mul_nonneg (by norm_num) (radius).coe_nonneg) (hR j).le (hsmall j)
  exact allocatedProductSiteCutoff_fixes_source B U b S rowSets o hb bW d radius
    (allocatedProductIdealSiteRadius_pos B rowSets) hR hσ
    (allocatedIdealCoverSupport (G := G) B rowSets)
    (allocatedIdealCoverSupport_nonneg B rowSets) (allocatedIdealCoverSupport_inactive B rowSets)
    (allocatedProductIdealSiteRadius_dominates B rowSets) C hC hchart hbudget hσ1 x y₀ q
    (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
    (allocatedPhysicalLongIdeal_cover_support B U b hR S rowSets δ hδ hδ1) y

end Erdos3.VectorPolynomial

end

end OAI
