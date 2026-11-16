import PA194SuccComponentsShift
import PA194EqualElimination
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194CancelInputs PA194InverseEqual
variable {Γ : List Form}

def succInjectiveValue (x y : Nat) (I : Inputs Γ) (h : ND.Proof Γ (succEqualAt x y)) :
    ND.Proof Γ (equalAt x y) := by
  apply succEqualEliminate x y (equalAt x y) h
  intro Δ hincl hs
  let J := I.shift.shift.weaken hincl
  rw [equalAt_shift,equalAt_shift]
  apply succValueEliminate (x+1+1) 1 (equalAt (x+1+1) (y+1+1)) hs.left
  intro Ψ hincl' hp
  let K := J.shift.weaken hincl'
  let hs' := hs.shift.weaken hincl'
  rw [equalAt_shift]
  apply succValueEliminate (y+1+1+1) 1 (equalAt (x+1+1+1) (y+1+1+1)) hs'.right
  intro Ω hincl'' hq
  let L := K.shift.weaken hincl''
  let hp' := hp.shift.weaken hincl''
  let hs'' := hs'.shift.weaken hincl''
  have hi := L.cancel (1+1+1) (0+1+1) 1 0 hq.outputDomain hp'.successor hq.successor hs''.iso
  rw [equalAt_shift]
  exact equalFromWitnesses (x+1+1+1+1) (y+1+1+1+1) 1 0 hp'.predValue hq.predValue hi
#print axioms succInjectiveValue
end PA194SuccInjective
