import ZFCinPA.ModelCodedBindFree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindFree
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeVecAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.bindFreeAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeAt_isUTerm
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeVecAt_isUTerm
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeAt_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeVecAt_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.bindFreeAt_isUFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.bindFreeAt_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.Opening.qVec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.termBindFreeVecAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.bindFreeAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.fvarVec_isTermVec
#print axioms LeanProofs.ZFCinPA.ModelCodedBindFree.bindFreeAt_closing

example (out d p : V) : (bindFreeAtDef L).val.Evalb ![out,d,p] ↔ out = bindFreeAt L d p := by simp
example (d x : V) : termBindFreeAt L d (^&x) = ^#(d+x) := termBindFreeAt_fvar d x
example (d z : V) : termBindFreeAt L d (^#z) = ^#z := termBindFreeAt_bvar d z
example (d x : V) : termShift L (termBindFreeAt L d (^&x)) = termBindFreeAt L d (^&x) := by simp
example (d : V) : termBindFreeAt L d (^&17) = ^#(d+17) := by simp
example : termBindFreeAt L (1 : V) (^#0) = ^#0 := by simp
example : termBindFreeAt L (1 : V) (^&0) = ^#1 := by simp
example (d p : V) (hp : IsUFormula L p) : bindFreeAt L d (^∀ p) = ^∀ (bindFreeAt L (d+1) p) := bindFreeAt_all d hp
example (d p : V) (hp : IsUFormula L p) : bindFreeAt L d (^∃ p) = ^∃ (bindFreeAt L (d+1) p) := bindFreeAt_exs d hp
example (d m w : V) (hw : IsSemitermVec L m d w) (ho : Opening d m w) : Opening (d+1) (m+1) (qVec L w) := ho.qVec hw
example (d p m w : V) (hp : IsSemiformula L d p) (hw : IsSemitermVec L m d w)
    (hb : IsSemiformula L m (bindFreeAt L d p)) (ho : Opening d m w) :
    subst L w (bindFreeAt L d p) = p := bindFreeAt_inverse hp m w hw hb ho
example (p : V) (hp : IsFormula L p) : IsUFormula L (bindFreeAt L 0 p) := (bindFreeAt_closing hp).1
example (p : V) (hp : IsFormula L p) : shift L (bindFreeAt L 0 p) = bindFreeAt L 0 p := (bindFreeAt_closing hp).2.1
example (p : V) (hp : IsFormula L p) : subst L (fvarVec (bv L (bindFreeAt L 0 p))) (bindFreeAt L 0 p) = p := (bindFreeAt_closing hp).2.2
example (p : V) (hp : IsFormula L p) : ∃ b : V, IsUFormula L b ∧ shift L b = b ∧ subst L (fvarVec (bv L b)) b = p := ⟨bindFreeAt L 0 p,bindFreeAt_closing hp⟩
