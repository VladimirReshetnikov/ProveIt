import ZFCinPA.ModelCodedBindOneSwap

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.swapVec_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.swapVec_isSemitermVec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.swapVec_spec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.termBindOneAt_swap
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.termBindOneVecAt_swap
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOneSwap.bindOneAt_swap
example (d : V) : IsSemitermVec L (d+2) (d+2) (swapVec L d) := swapVec_isSemitermVec d
example (d i : V) (hi : i < d) : (swapVec L d).[i] = ^#i := (swapVec_spec d).1 i hi
example (d : V) : (swapVec L d).[d] = ^#(d+1) := (swapVec_spec d).2.1
example (d : V) : (swapVec L d).[d+1] = ^#d := (swapVec_spec d).2.2
example (d t a b : V) (ht : IsSemiterm L d t) (hab : a ≠ b) :
    termSubst L (swapVec L d) (termBindOneAt L a (d+1) (termBindOneAt L b d t)) =
      termBindOneAt L b (d+1) (termBindOneAt L a d t) := termBindOneAt_swap ht a b hab
example (d n v a b : V) (hv : IsSemitermVec L n d v) (hab : a ≠ b) :
    termSubstVec L n (swapVec L d)
      (termBindOneVecAt L a (d+1) n (termBindOneVecAt L b d n v)) =
      termBindOneVecAt L b (d+1) n (termBindOneVecAt L a d n v) := termBindOneVecAt_swap hv a b hab
example (d p a b : V) (hp : IsSemiformula L d p) (hab : a ≠ b) :
    subst L (swapVec L d) (bindOneAt L a (d+1) (bindOneAt L b d p)) =
      bindOneAt L b (d+1) (bindOneAt L a d p) := bindOneAt_swap hp a b hab
example (p : V) (hp : IsFormula L p) :
    subst L (swapVec L (0 : V)) (bindOneAt L 0 1 (bindOneAt L 1 0 p)) =
      bindOneAt L 1 1 (bindOneAt L 0 0 p) := by
  simpa only [zero_add] using bindOneAt_swap hp (0 : V) 1 (by simp)
