/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (d : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

theorem mixedCoveredBooleanSiteValue_point_norm
    (z : MixedCoveredJetSource I jets Q n d) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hz : ∀ j r, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j r).1‖ ≤ c j)
    (s : Finset α) (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1‖ ≤
      (Fintype.card (jets j) : ℝ) * c j := by
  calc
    _ = ‖∑ r : jets j, boundedBooleanReconstructionMatrix α (j.val + 1) s r •
        normalizedLatticePoint (euclideanSubspace (U j)) (b j) (mixedCoveredJetCoordinates U o d z j r).1‖ :=
      congrArg norm (mixedCoveredJetIntegerImage_point U o b d
        (fun j (_ : Unit) => boundedBooleanReconstructionMatrix α (j.val + 1) s) z j ())
    _ ≤ ∑ r : jets j, ‖boundedBooleanReconstructionMatrix α (j.val + 1) s r •
      normalizedLatticePoint (euclideanSubspace (U j)) (b j) (mixedCoveredJetCoordinates U o d z j r).1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : jets j, c j := by
      apply Finset.sum_le_sum
      intro r _
      by_cases h : r.val ⊆ s
      · simpa only [boundedBooleanReconstructionMatrix, ite_eq_left h, one_zsmul] using hz j r
      · simpa only [boundedBooleanReconstructionMatrix, ite_eq_right h, zero_zsmul, norm_zero] using hc j
    _ = _ := by simp

theorem mixedCoveredBooleanSiteValue_mem_quarter
    (z : MixedCoveredJetSource I jets Q n d) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hz : ∀ j r, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j r).1‖ ≤ c j)
    (hbudget : ∀ j, (Fintype.card (jets j) : ℝ) * c j ≤ 1 / 4) (s : Finset α) :
    mixedCoveredBooleanSiteValue d z s ∈ mixedCoveredJetRegion (E := Q) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  cases t
  have h := (mixedCoveredBooleanSiteValue_point_norm U o b d z c hc hz s j).trans (hbudget j)
  have hi : |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1 i| ≤
      ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1) i
  exact hi.trans h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ) (d : ℕ)

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

omit [Fintype α] in
theorem mixedCoveredRowsSiteValue_point_norm
    (z : MixedCoveredJetSource I O E n d) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hz : ∀ j t, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j t).1‖ ≤ c j)
    (s : Finset α) (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1‖ ≤
      (rowSets j).card * c j := by
  calc
    _ = ‖∑ t : O j, rowRestrictedSiteMatrix (rowSets j) s t •
        normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (mixedCoveredJetCoordinates U o d z j t).1‖ :=
      congrArg norm (mixedCoveredJetIntegerImage_point U o b d
        (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z j ())
    _ ≤ ∑ t : O j, ‖rowRestrictedSiteMatrix (rowSets j) s t •
        normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (mixedCoveredJetCoordinates U o d z j t).1‖ := norm_sum_le _ _
    _ ≤ ∑ _t : O j, c j := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t.val ⊆ s
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix,
          ite_eq_left ht, one_zsmul] using hz j t
      · simpa only [rowRestrictedSiteMatrix, booleanReconstructionMatrix,
          ite_eq_right ht, zero_zsmul, norm_zero] using hc j
    _ = _ := by simp

omit [Fintype α] in
theorem mixedCoveredRowsSiteValue_mem_quarter
    (z : MixedCoveredJetSource I O E n d) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hz : ∀ j t, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j t).1‖ ≤ c j)
    (hbudget : ∀ j, (rowSets j).card * c j ≤ 1 / 4) (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion (E := E) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  cases t
  have hn := (mixedCoveredRowsSiteValue_point_norm rowSets U o b d z c hc hz s j).trans (hbudget j)
  have hi : |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1 i| ≤
      ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1‖ := by
    simpa only [Real.norm_eq_abs] using
    PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1) i
  exact hi.trans hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule Set
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable (rowSets : Fin m → Finset (Finset α)) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)

noncomputable def mixedCoveredSiteArray
    (w : Finset α → MixedCoveredJetSource I single E n d) :
    MixedCoveredJetSource I (fun _ => Finset α) E n d :=
  (fun j => (fun i s => ((w s).1 j).1 i (), fun i s => ((w s).1 j).2 i ()),
    fun j s i => (w s).2 j () i)

noncomputable def mixedCoveredRowsOfSites
    (w : Finset α → MixedCoveredJetSource I single E n d) :
    MixedCoveredJetSource I rowTypes E n d :=
  mixedCoveredJetIntegerImage d (fun j => booleanJetExtractionMatrix (Subtype.val : rowTypes j → Finset α))
    (mixedCoveredSiteArray d w)

variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem mixedCoveredRowsOfSites_chart
    (z : MixedCoveredJetSource I rowTypes E n d)
    (w : Finset α → MixedCoveredJetSource I single E n d)
    (hw : ∀ s, chart (w s) = coveredRowsSiteValue rowSets U (chart z) s) :
    chart (mixedCoveredRowsOfSites rowSets d w) = chart z := by
  funext j t
  rw [mixedCoveredRowsOfSites, mixedCoveredJetIntegerImage_chart]
  change (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val t s • chart (w s) j ()) = _
  simp only [hw, coveredRowsSiteValue]
  exact rowRestrictedReconstruction_zsmul_inverse (rowSets j) (chart z j) t

omit [∀ j, Fintype (E j)] [NeZero d] in
theorem mixedCoveredRowsOfSites_point_bound
    (w : Finset α → MixedCoveredJetSource I single E n d) (c : Fin m → ℝ)
    (_hc : ∀ j, 0 ≤ c j)
    (hw : ∀ s j, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (w s) j ()).1‖ ≤ c j)
    (j : Fin m) (t : rowTypes j) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsOfSites rowSets d w) j t).1‖ ≤
      Fintype.card (Finset α) * c j := by
  rw [mixedCoveredRowsOfSites, mixedCoveredJetIntegerImage_point]
  calc
    _ ≤ ∑ s : Finset α, ‖booleanJetExtractionMatrix Subtype.val t s •
        normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (mixedCoveredJetCoordinates U o d (w s) j ()).1‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Finset α, c j := by
      apply Finset.sum_le_sum
      intro s _
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (booleanJetExtractionMatrix_abs_le_one Subtype.val t s)
        (hw s j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp

include hb bW in
theorem mixedCoveredRowsOfSites_recover
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (w : Finset α → MixedCoveredJetSource I single E n d)
    (hw : ∀ s, chart (w s) = coveredRowsSiteValue rowSets U (chart z) s)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hpoint : ∀ s j, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (w s) j ()).1‖ ≤ c j)
    (hbudget : ∀ j, Fintype.card (Finset α) * c j ≤ 1 / 4) :
    mixedCoveredRowsOfSites rowSets d w = z := by
  have hregion : mixedCoveredRowsOfSites rowSets d w ∈ region := by
    intro j _ t _
    refine ⟨?_, Set.mem_univ _⟩
    intro i
    have hn := (mixedCoveredRowsOfSites_point_bound rowSets d U o b w c hc hpoint j t).trans (hbudget j)
    exact (PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (mixedCoveredRowsOfSites rowSets d w) j t).1) i).trans hn
  exact (mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hregion hz
      (mixedCoveredRowsOfSites_chart rowSets d U o b hb bW z w hw)

theorem mixedCoveredRowsOfSites_reconstructed_quarter
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (w : Finset α → MixedCoveredJetSource I single E n d)
    (hw : ∀ s, chart (w s) = coveredRowsSiteValue rowSets U (chart z) s)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hpoint : ∀ s j, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d (w s) j ()).1‖ ≤ c j)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) * c j) ≤ 1 / 4)
    (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion (E := E) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  have hnonneg (j : Fin m) : 0 ≤ (Fintype.card (Finset α) : ℝ) * c j :=
    mul_nonneg (Nat.cast_nonneg _) (hc j)
  have hrow (j : Fin m) : (Fintype.card (Finset α) : ℝ) * c j ≤ 1 / 4 := by
    have h := hbudget j
    have hn := hnonneg j
    nlinarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]
  have he := mixedCoveredRowsOfSites_recover rowSets d U o b hb bW z hz w hw c hc hpoint hrow
  apply mixedCoveredRowsSiteValue_mem_quarter rowSets U o b d z
    (fun j => Fintype.card (Finset α) * c j) hnonneg
  · intro j t
    rw [← he]
    exact mixedCoveredRowsOfSites_point_bound rowSets d U o b w c hc hpoint j t
  · intro j
    have h := hbudget j
    have hn := hnonneg j
    nlinarith

end Erdos3.VectorPolynomial

end

end OAI
