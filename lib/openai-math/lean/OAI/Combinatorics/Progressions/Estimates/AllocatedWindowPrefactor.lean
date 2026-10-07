/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedActiveSiteChartValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "split" => coefficientJetAxisSplit O I n grid

noncomputable def allocatedActiveWindowCondition (z : MixedCoveredJetSource I O E n d) : Prop :=
  ∀ a : activeAxes, allocatedActiveRowsOfMixed B U b S rowSets z.1 a ∈
    allocatedGridSiteWindow B rowSets U b S a.val

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "prefactor" => allocatedActiveSiteChartPrefactor (G := G) (I := I) (n := n)
  (J := J) (R := R) (σ := σ) (α := α) (E := E) B U b S rowSets d hR hσ x hb o bW q y₀ hcell f
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell

include B U b S hR hσ x hb o bW q y₀ hcell f in
noncomputable def allocatedActiveWindowPrefactor (z : MixedCoveredJetSource I O E n d) : ℂ :=
  @ite ℂ (allocatedActiveWindowCondition B U b S rowSets d z) (Classical.propDecidable _)
    (allocatedActiveSiteChartPrefactor (G := G) (I := I) (n := n) (J := J)
      (R := R) (σ := σ) (α := α) (E := E) B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z) 0

theorem allocatedActiveSiteProfile_window
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (he : ∀ a i s r v, allocatedNaturalSiteRadius (G := G) B (ig a.val).1 (ig a.val).2
      (rowSets (ig a.val).1) + 1 / 4 ≤ |v| → (e a).factor i s r v = 0)
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))) :
    allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
      allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z *
        allocatedActiveSiteApproximation B U b S rowSets e
          (allocatedActiveRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedActiveSiteProfile_mixed B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz]
  unfold allocatedActiveWindowPrefactor
  split_ifs with hw
  · rfl
  · have hout : ∃ a : activeAxes, allocatedActiveRowsOfMixed B U b S rowSets z.1 a ∉
        allocatedGridSiteWindow B rowSets U b S a.val := by
      simpa only [allocatedActiveWindowCondition, not_forall] using hw
    rw [allocatedActiveSiteApproximation_zero B U b hR S rowSets e hrows he _ hout]
    simp only [mul_zero]

theorem allocatedActiveWindowPrefactor_support
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)))
    (hne : allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z ≠ 0) :
    allocatedActiveWindowCondition B U b S rowSets d z ∧
      (∏ a : {a : {a // grid a} // ¬active a}, (laws a.val ((split z.1).1 a.val)).toReal) ≠ 0 ∧
      f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) ≠ 0 := by
  have hw : allocatedActiveWindowCondition B U b S rowSets d z := by
    by_contra hw
    exact hne (by simp only [allocatedActiveWindowPrefactor, ite_eq_right hw])
  have hbase : prefactor z ≠ 0 := by
    simpa only [allocatedActiveWindowPrefactor, ite_eq_left hw] using hne
  refine ⟨hw, ?_, ?_⟩
  · intro hp
    apply hbase
    simp only [allocatedActiveSiteChartPrefactor, hp, Complex.ofReal_zero, zero_div, zero_mul]
  · intro hf
    have hprofile : allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) = 0 := by
      have hinj := mixedCoveredJetChart_injOn U o b hb bW d
        (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
      unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
      rw [restrictedChartDensity_apply _ _ _ _ hinj hz]
      simp only [allocatedLongProfileDensity, hf, mul_zero, zero_div]
    apply hbase
    simp only [allocatedActiveSiteChartPrefactor, hprofile, Complex.ofReal_zero, mul_zero]

end Erdos3.VectorPolynomial

end

end OAI
