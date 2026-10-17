import ZFCinPA.ModelCodedBindTwoSlots

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBindTwoSlots
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_zero
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_succ
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_isSemitermVec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_spec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.termBindTwo_reindex
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.termBindTwoVec_reindex
#print axioms LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.bindTwo_reindex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

example : 𝚺₁-Function₃[V] (twoSlotVec L) via twoSlotVecDef L := inferInstance
example (i j : V) : twoSlotVec L 0 i j = ^#i ∷ ^#j ∷ 0 := twoSlotVec_zero i j
example (d i j : V) : twoSlotVec L (d+1) i j = qVec L (twoSlotVec L d i j) :=
  twoSlotVec_succ d i j
example (d i j : V) :
    IsSemitermVec L (d+2) (d+(i+j+1)) (twoSlotVec L d i j) :=
  twoSlotVec_isSemitermVec d i j
example (d i j : V) :
    (∀ z < d, (twoSlotVec L d i j).[z] = ^#z) ∧
    (twoSlotVec L d i j).[d] = ^#(d+i) ∧
    (twoSlotVec L d i j).[d+1] = ^#(d+j) := twoSlotVec_spec i j d
example {d t : V} (h : IsSemiterm L d t) (a b i j : V) (hab : a ≠ b) :
    termSubst L (twoSlotVec L d i j) (termBindOneAt L b (d+1) (termBindOneAt L a d t)) =
      termBindOneAt L b (d+j) (termBindOneAt L a (d+i) t) :=
  termBindTwo_reindex h a b i j hab
example {d n v : V} (h : IsSemitermVec L n d v) (a b i j : V) (hab : a ≠ b) :
    termSubstVec L n (twoSlotVec L d i j)
      (termBindOneVecAt L b (d+1) n (termBindOneVecAt L a d n v)) =
      termBindOneVecAt L b (d+j) n (termBindOneVecAt L a (d+i) n v) :=
  termBindTwoVec_reindex h a b i j hab
example {d p : V} (hp : IsSemiformula L d p) (a b i j : V) (hab : a ≠ b) :
    subst L (twoSlotVec L d i j) (bindOneAt L b (d+1) (bindOneAt L a d p)) =
      bindOneAt L b (d+j) (bindOneAt L a (d+i) p) :=
  bindTwo_reindex hp a b i j hab
example {p : V} (hp : IsFormula L p) (a b : V) (hab : a ≠ b) :
    subst L (^#1 ∷ ^#0 ∷ 0) (bindOneAt L b 1 (bindOneAt L a 0 p)) =
      bindOneAt L b 0 (bindOneAt L a 1 p) := by
  simpa only [twoSlotVec_zero,zero_add] using bindTwo_reindex hp a b 1 0 hab
example {p : V} (hp : IsFormula L p) (a b : V) (hab : a ≠ b) :
    subst L (^#2 ∷ ^#0 ∷ 0) (bindOneAt L b 1 (bindOneAt L a 0 p)) =
      bindOneAt L b 0 (bindOneAt L a 2 p) := by
  simpa only [twoSlotVec_zero,zero_add] using bindTwo_reindex hp a b 2 0 hab
example {p : V} (hp : IsFormula L p) (a b : V) (hab : a ≠ b) :
    subst L (^#0 ∷ ^#1 ∷ 0) (bindOneAt L b 1 (bindOneAt L a 0 p)) =
      bindOneAt L b 1 (bindOneAt L a 0 p) := by
  simpa only [twoSlotVec_zero,zero_add] using bindTwo_reindex hp a b 0 1 hab
example {d p : V} (hp : IsSemiformula L d p) (a b i : V) (hab : a ≠ b) :
    subst L (twoSlotVec L d i i) (bindOneAt L b (d+1) (bindOneAt L a d p)) =
      bindOneAt L b (d+i) (bindOneAt L a (d+i) p) :=
  bindTwo_reindex hp a b i i hab
