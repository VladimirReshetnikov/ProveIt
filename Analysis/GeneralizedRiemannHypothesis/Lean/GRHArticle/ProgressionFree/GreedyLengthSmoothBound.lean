import GRHArticle.ProgressionFree.IntegerSmoothNaturalBound
import GRHArticle.ProgressionFree.IntegerPrimeBlockPartitions

/-!
# Smooth-template bound at arbitrary progression length

Within each rough-part fiber, multiplication by that rough part
preserves every positive rational ratio. The reciprocal bound for
smooth fibers therefore applies at any fixed length.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- Reciprocal weights of all admissible smooth templates at the cutoff. -/
def integerLengthSmoothTemplateWeights (k Y : ℕ) : Set ℝ :=
  {w | ∃ A : Set ℕ, A ⊆ Nat.smoothNumbers (Y+1) ∧ KTermGPFree k A ∧
    w = ∑' s : A, (s.val:ℝ)⁻¹}

/-- The maximum density obtainable from a common smooth template when
rough factors carry no other constraints. -/
noncomputable def integerLengthSmoothOptimization (k Y : ℕ) : ℝ :=
  integerSmoothDensityFactor Y * sSup (integerLengthSmoothTemplateWeights k Y)

private theorem kTermGPFree_empty {k : ℕ} (hk : 0 < k) : KTermGPFree k (∅ : Set ℕ) := by
  intro a _ _ _ _ h
  exact (h ⟨0,hk⟩).elim

theorem integerLengthSmoothTemplateWeights_nonempty {k : ℕ} (hk : 0 < k) (Y : ℕ) :
    (integerLengthSmoothTemplateWeights k Y).Nonempty :=
  ⟨_,∅,Set.empty_subset _,kTermGPFree_empty hk,rfl⟩

theorem integerLengthSmoothTemplateWeights_bddAbove (k Y : ℕ) :
    BddAbove (integerLengthSmoothTemplateWeights k Y) :=
  ⟨(integerSmoothDensityFactor Y)⁻¹, by
    rintro w ⟨A,hA,_,rfl⟩
    exact smoothSubset_reciprocal_le hA⟩

theorem integerLengthSmoothOptimization_le_one {k : ℕ} (hk : 0 < k) (Y : ℕ) :
    integerLengthSmoothOptimization k Y ≤ 1 := by
  have h := csSup_le (integerLengthSmoothTemplateWeights_nonempty hk Y)
    (show ∀ w ∈ integerLengthSmoothTemplateWeights k Y, w ≤ (integerSmoothDensityFactor Y)⁻¹ by
      rintro w ⟨A,hA,_,rfl⟩
      exact smoothSubset_reciprocal_le hA)
  exact (mul_le_mul_of_nonneg_left h (integerSmoothDensityFactor_pos Y).le).trans_eq
    (mul_inv_cancel₀ (integerSmoothDensityFactor_pos Y).ne')

private theorem kTermGPFree_smoothFiber {k Y r : ℕ} {A : Set ℕ}
    (hA : KTermGPFree k A) (hr : 0 < r) :
    KTermGPFree k (integerSmoothFiber A Y r) := by
  intro a u q hu hq hmem hR
  refine hA (fun i ↦ r*a i) ((r:ℚ)*u) q
    (mul_pos (by exact_mod_cast hr) hu) hq (fun i ↦ (hmem i).2) (fun i ↦ ?_)
  push_cast
  rw [hR i,mul_assoc]

/-- Every set with a true natural density is bounded by the reciprocal
optimization of smooth templates at the cutoff. -/
theorem naturalDensity_le_integerLengthSmoothOptimization {k : ℕ} (Y : ℕ)
    {A : Set ℕ} (hA : KTermGPFree k A) {d : ℝ} (hd : HasNaturalDensity A d) :
    d ≤ integerLengthSmoothOptimization k Y := by
  let M := sSup (integerLengthSmoothTemplateWeights k Y)
  have hM (r : ℕ) (hr : 0 < r) :
      (∑' s : integerSmoothFiber A Y r, (s.val:ℝ)⁻¹) ≤ M :=
    le_csSup (integerLengthSmoothTemplateWeights_bddAbove k Y)
      ⟨integerSmoothFiber A Y r,fun _ h ↦ h.1,kTermGPFree_smoothFiber hA hr,rfl⟩
  have h := naturalDensity_le_of_reciprocalMass_le hd (hasNaturalDensity_integerRoughNumbers Y)
    (reciprocalMassUpTo_le_of_smoothFiber_weight_bound A Y M hM)
  simpa only [integerLengthSmoothOptimization,M,mul_comm] using h

theorem integerLengthNaturalDensitySupremum_le_smoothOptimization {k : ℕ} (hk : 0 < k) (Y : ℕ) :
    integerLengthNaturalDensitySupremum k ≤ integerLengthSmoothOptimization k Y := by
  let S : Set ℝ := {a | ∃ A : Set ℕ, 0 ∉ A ∧ KTermGPFree k A ∧ HasNaturalDensity A a}
  have hS : S.Nonempty := ⟨0,∅,by simp,kTermGPFree_empty hk,hasNaturalDensity_empty⟩
  change sSup S ≤ _
  apply csSup_le hS
  rintro d ⟨A,_,hA,hd⟩
  exact naturalDensity_le_integerLengthSmoothOptimization Y hA hd

end GRHArticle.ProgressionFree
