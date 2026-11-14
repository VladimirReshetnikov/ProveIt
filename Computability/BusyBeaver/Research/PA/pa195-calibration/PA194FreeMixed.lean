import PA194MixedTransition
import PA194FreeBlockBasis
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace PA194FreeMixed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MixedVector PA194MixedTransition
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem free_block_exact (p k : V) (hp : IsUFormula ℒₒᵣ p) :
    free ℒₒᵣ (qqAlls p k) = qqAlls (subst ℒₒᵣ (mixedVec k 1) (shift ℒₒᵣ p)) k := by
  obtain ⟨w,hw,hb,hf,he⟩ := PA194FreeBlockBasis.free_block_basis p k hp
  obtain ⟨hm,hmb,hmf⟩ := mixed_shape k (1 : V)
  have heq : w = mixedVec k 1 := by
    apply nth_ext' (k+1) hw.lh
    · simpa using hm.lh
    · intro i hi
      by_cases hlt : i < k
      · rw [hb i hlt,hmb i hlt]
      · have h : i = k := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hlt)
        subst i
        simpa using hf.trans (hmf 0 (by simp)).symm
  simpa [heq] using he

theorem free_mixed_transition (p k m : V) (hp : IsSemiformula ℒₒᵣ (k+1+m) p)
    (hshift : shift ℒₒᵣ p = p) :
    free ℒₒᵣ (qqAlls (subst ℒₒᵣ (mixedVec (k+1) m) p) k) =
      qqAlls (subst ℒₒᵣ (mixedVec k (m+1)) p) k := by
  have hv := (mixed_shape (k+1) m).1
  have hw := (mixed_shape k (1 : V)).1
  rw [free_block_exact _ _ (hp.subst hv).isUFormula]
  rw [shift_substs hp hv,hshift,substs_substs hp hw hv.termShiftVec,mixed_transition]
#print axioms free_block_exact
#print axioms free_mixed_transition
end PA194FreeMixed
