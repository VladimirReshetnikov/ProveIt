/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.AllocatedNormalizedConditionalHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (T : Fin m → ℝ)

noncomputable def allocatedPhysicalGridCondition
    (z : AllocatedFrozenJetRows B U b S O) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hg : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (t : O j), |(z ⟨⟨j, Sum.inr i⟩, hg⟩ t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

noncomputable def allocatedPhysicalGridMask (y : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (fun z => if allocatedPhysicalGridCondition B U b S O T z then 1 else 0) y

omit [∀ j, Fintype (O j)] in
theorem allocatedPhysicalGridMask_apply (z : MixedCoveredJetSource I O Q n d) (hz : z ∈ region) :
    allocatedPhysicalGridMask B U b S O T hb o bW d (chart z) =
      if allocatedPhysicalGridCondition B U b S O T ((split z.1).1) then 1 else 0 :=
  allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz

omit [∀ j, Fintype (O j)] in
theorem allocatedPhysicalGridMask_zero (y : EuclideanJetLayers U O) (hy : y ∉ chart '' region) :
    allocatedPhysicalGridMask B U b S O T hb o bW d y = 0 :=
  allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy

omit [∀ j, Fintype (O j)] in
theorem allocatedPhysicalGridMask_norm (y : EuclideanJetLayers U O) :
    ‖allocatedPhysicalGridMask B U b S O T hb o bW d y‖ ≤ 1 := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedPhysicalGridMask_apply B U b S O T hb o bW d z hz]
    split_ifs <;> norm_num
  · rw [allocatedPhysicalGridMask_zero B U b S O T hb o bW d y hy]
    norm_num

theorem allocatedPhysicalGridMask_measurable :
    Measurable (allocatedPhysicalGridMask B U b S O T hb o bW d) := by
  apply allocatedComplexGridMultiplier_measurable
  exact measurable_of_countable _

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [∀ j, DecidableEq (O j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (hT : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
include hT in
theorem allocatedPhysicalGridMask_fixes_source (hσ1 : ∀ j, σ j ≤ 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ)
    (y : EuclideanJetLayers U O) :
    allocatedPhysicalGridMask B U b S O T hb o bW d y *
        (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) := by
  rw [allocatedWholeMaskedCoveredProfile_grid_multiplier B U b hR hσ S x rows hb o bW d y₀ q f]
  dsimp only
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedPhysicalGridMask_apply B U b S O T hb o bW d z hz,
      allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz]
    by_cases hc : allocatedPhysicalGridCondition B U b S O T ((split z.1).1)
    · rw [ite_eq_left hc, one_mul]
    · have hzero : allocatedGridJetDensity B U b hR hσ S x
          (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀) rows
          ((split z.1).1) = 0 := by
        by_contra hne
        apply hc
        intro j i hg t
        exact (allocatedGridJetDensity_scaled_support_bound B U b hR hσ S x
          (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
          rows z.1 hne j (hσ1 j) i hg t).trans
          (mul_le_mul_of_nonneg_right (hT j) (hR j).le)
      rw [hzero, zero_mul, Complex.ofReal_zero, mul_zero]
  · rw [allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy,
      zero_mul, Complex.ofReal_zero, mul_zero]

end Erdos3.VectorPolynomial

end

end OAI
