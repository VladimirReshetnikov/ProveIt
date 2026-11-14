import PA194QVecBasis
import PA194QVecDistribution
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace PA194FreeBlockBasis
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem free_block_basis (p k : V) (hp : IsUFormula ℒₒᵣ p) :
    ∃ w, IsSemitermVec ℒₒᵣ (k+1) k w ∧ (∀ j < k, w.[j] = ^#j) ∧ w.[k] = ^&0 ∧
      free ℒₒᵣ (qqAlls p k) = qqAlls (subst ℒₒᵣ w (shift ℒₒᵣ p)) k := by
  obtain ⟨s,hseq,hlen,hzero,hrec⟩ := PA194QVecHistory.opening_history (V := V) ?[^&0] k
  have hb := PA194QVecBasis.qvec_basis s k hzero hrec k (le_refl k)
  refine ⟨znth s k,hb.1,hb.2.1,hb.2.2,?_⟩
  unfold free substs1
  rw [PA194QVecDistribution.shift_all_iter p k hp]
  have hd := PA194QVecDistribution.distribution (shift ℒₒᵣ p) s k hp.shift hrec k (le_refl k) 0 zero_le (by simp)
  simpa [hzero] using hd
#print axioms free_block_basis
end PA194FreeBlockBasis
