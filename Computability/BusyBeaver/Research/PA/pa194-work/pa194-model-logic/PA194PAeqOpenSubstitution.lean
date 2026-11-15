import PA194PAeqBooleanCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.OpenSubstitution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem open_subst (p : Semiformula V language 2) (t : Term V language) :
    (p.subst (SemitermVec.q ![t])).free = p.free1.subst ![t.shift] := by
  simp [Bootstrapping.Semiformula.free1,Bootstrapping.Semiformula.free,SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs, ← Semiterm.bShift_shift_comm]
#print axioms open_subst
end PA194PAeq.OpenSubstitution
