import PA194PAeqMulCommProof
import PA194PAeqDistributivityProof
import PA194PAeqMulCongrAtTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulLawsAt
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne
variable {Γ : List Fm}
noncomputable def commAt (x y : Tm) (hΓ : ∀ p ∈ MulComm.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (mul x y) (mul y x)) := by
  have h : ND.Proof Γ (.all MulComm.prop) := ND.weaken MulComm.proof hΓ
  have h1 := ND.allElim _ x h
  have h2 := ND.allElim _ y h1
  simpa [MulComm.prop,eq,mul,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h2
noncomputable def distrAt (x y z : Tm) (hΓ : ∀ p ∈ Distributivity.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (mul x (add y z)) (add (mul x y) (mul x z))) := by
  have h : ND.Proof Γ (.all Distributivity.prop) := ND.weaken Distributivity.proof hΓ
  have h1 := ND.allElim _ x h
  have h2 := ND.allElim _ y h1
  have h3 := ND.allElim _ z h2
  simpa [Distributivity.prop,eq,add,mul,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using h3
#print axioms commAt
#print axioms distrAt
end PA194PAeq.MulLawsAt
