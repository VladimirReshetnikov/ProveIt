import PA194BindAllDecode
import PA194OpeningEndpoint
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194FullInternalInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem internal_induction_body (K : V) (hK : IsSemiformula ℒₒᵣ 1 K) :
    Provable (𝗣𝗔 : ArithmeticTheory) (indBodyVal K) := by
  let kt : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨K,by simpa using hK⟩
  have hform : IsFormula ℒₒᵣ (indBodyVal K) := by
    change IsFormula ℒₒᵣ (indBodyVal kt.val)
    rw [indBodyVal_eq]
    exact (indBody kt).isSemiformula
  let body := PA194BindAllFormula.bindAll 0 (indBodyVal K)
  let n := bv ℒₒᵣ body
  have hwf : IsUFormula ℒₒᵣ body ∧ shift ℒₒᵣ body = body := PA194BindAllFormula.bindAll_wf_fixed 0 _ hform
  have hsemi : IsSemiformula ℒₒᵣ n body := hwf.1.isSemiformula
  have hdecode : subst ℒₒᵣ (fvarVec n) body = indBodyVal K := PA194BindAllDecode.bindAll_root_inverse _ hform
  exact PA194OpeningEndpoint.induction_body_of_closure body K n hsemi hwf.2 rfl hK hdecode
#print axioms internal_induction_body
end PA194FullInternalInduction
