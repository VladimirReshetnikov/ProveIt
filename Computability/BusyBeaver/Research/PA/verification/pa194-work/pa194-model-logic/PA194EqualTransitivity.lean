import PA194EqualComponentsShift
import PA194CompositionInputs
import PA194CompositionAlign
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194InverseEqual
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194CompositionInputs PA194CompositionAlign
variable {Γ : List Form}

def equalTransitivity (a b c : Nat) (I : Inputs Γ)
    (hab : ND.Proof Γ (equalAt a b)) (hbc : ND.Proof Γ (equalAt b c)) :
    ND.Proof Γ (equalAt a c) := by
  apply equalEliminate a b (equalAt a c) hab
  intro Δ hinc hxy
  let J := I.shift.shift.weaken hinc
  have hbc' : ND.Proof Δ (equalAt (b+1+1) (c+1+1)) := by
    have h := ND.weaken (ND.shiftProof (ND.shiftProof hbc)) hinc
    simpa only [equalAt_shift] using h
  rw [equalAt_shift,equalAt_shift]
  apply equalEliminate (b+1+1) (c+1+1) (equalAt (a+1+1) (c+1+1)) hbc'
  intro Ω hinc' hyz
  let K := J.shift.shift.weaken hinc'
  let hxy' := hxy.shift.shift.weaken hinc'
  have hmid : ND.Proof Ω (orderIso (.fvar (0+1+1)) (.fvar 0)) :=
    alignMiddle K.equality (1+1+1) (0+1+1) 1 0 (b+1+1+1+1)
      (ND.andRight hxy'.right) (ND.andRight hyz.left) hyz.iso
  have hiso := K.compose (1+1+1) (0+1+1) 0 (ND.andLeft hxy'.left) hxy'.iso hmid
  rw [equalAt_shift,equalAt_shift]
  exact equalFromWitnesses (a+1+1+1+1) (c+1+1+1+1) (1+1+1) 0 hxy'.left hyz.right hiso
#print axioms equalTransitivity
end PA194InverseEqual
