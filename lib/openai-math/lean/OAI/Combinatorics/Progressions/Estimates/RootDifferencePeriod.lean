import OAI.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
import OAI.Combinatorics.Progressions.Linear.RootDifferenceMatrix

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (a : ℤ)
    (hperiod : integerScalarLattice I a ≤ D.mulVecLin.range) :
    integerScalarLattice (Unit ⊕ I) a ≤ (rootDifferenceMatrix root D).mulVecLin.range := by
  rintro y ⟨z, rfl⟩
  have hz : a • (fun i => z (Sum.inr i)) ∈ integerScalarLattice I a :=
    ⟨fun i => z (Sum.inr i), rfl⟩
  obtain ⟨v, hv⟩ := hperiod hz
  refine ⟨Sum.elim (fun _ : Unit => a * z (Sum.inl ()) - ∑ j, root j * v j) v, ?_⟩
  change rootDifferenceMatrix root D *ᵥ _ = a • z
  rw [rootDifferenceMatrix_mulVec]
  funext i
  cases i with
  | inl i => cases i; simp
  | inr i => exact congrFun hv i

theorem rootDifferenceMatrix_bounded_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) {B : ℕ}
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod (rootDifferenceMatrix root D).mulVecLin.range B := by
  obtain ⟨a, ha, haB, hp⟩ := hperiod
  exact ⟨a, ha, haB, rootDifferenceMatrix_period root D (a : ℤ) hp⟩

theorem rootDifferenceMatrix_index_le {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) {B : ℕ}
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (rootDifferenceMatrix root D).mulVecLin.range.toAddSubgroup.index ≤ B^(Fintype.card I + 1) := by
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_comm] using
    hasBoundedScalarPeriod_index_le _ B (rootDifferenceMatrix_bounded_period root D hperiod)

end Erdos3

end

end OAI
