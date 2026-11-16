import PA194DomainSuccElimination
import PA194SuccValueIntro
import PA194EqualComponentsShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194SuccExtensionInputs PA194InverseEqual
variable {Γ : List Form}

def succCongruenceValue (a b : Nat) (I : Inputs Γ) (he : ND.Proof Γ (equalAt a b)) :
    ND.Proof Γ (succEqualAt a b) := by
  apply equalEliminate a b (succEqualAt a b) he
  intro Δ hincl hv
  let J := I.shift.shift.weaken hincl
  rw [succEqualAt_shift,succEqualAt_shift]
  apply domainSuccessorEliminate 1 (succEqualAt (a+1+1) (b+1+1))
    (J.successorExists 1 (ND.andLeft hv.left))
  intro Ψ hincl' hdom1 hsucc1
  let K := J.shift.weaken hincl'
  let hv' := hv.shift.weaken hincl'
  rw [succEqualAt_shift]
  apply domainSuccessorEliminate 1 (succEqualAt (a+1+1+1) (b+1+1+1))
    (K.successorExists 1 (ND.andLeft hv'.right))
  intro Ω hincl'' hdom2 hsucc2
  let L := K.shift.weaken hincl''
  let hv'' := hv'.shift.weaken hincl''
  have hd1 : ND.Proof Ω (Ordinal.domain (.fvar 1)) := by
    exact ND.weaken (Ordinal.domainShift 0 hdom1) hincl''
  have hs1 : ND.Proof Ω (Ordinal.successor (.fvar 3) (.fvar 1)) := by
    exact ND.weaken (Ordinal.successorShift 2 0 hsucc1) hincl''
  have hiso := L.extend 3 2 1 0 (ND.andLeft hv''.left) (ND.andLeft hv''.right) hs1 hsucc2 hv''.iso
  have hv1 := succValueIntro (a+1+1+1+1) 3 1 hv''.left hd1 hs1
  have hv2 := succValueIntro (b+1+1+1+1) 2 0 hv''.right hdom2 hsucc2
  rw [succEqualAt_shift]
  exact succEqualFromWitnesses (a+1+1+1+1) (b+1+1+1+1) 1 0 hv1 hv2 hiso
#print axioms succCongruenceValue
end PA194SuccInjective
