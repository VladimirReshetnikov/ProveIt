import ZFCinPA.ModelCodedBindOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneVecAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.bindOneAt_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_bvar
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_chosen
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_other
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_isSemiterm
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneVecAt_isSemiterm
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.bindOneAt_isSemiformula
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.termBindOneVecAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.bindOneAt_inverse
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.namedAll_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.namedAll_isFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedBindOne.bindOneAt_open

example : 𝚺₁-Function₃[V] (termBindOneAt L) via termBindOneAtDef L := inferInstance
example : 𝚺₁-Function₄[V] (termBindOneVecAt L) via termBindOneVecAtDef L := inferInstance
example (out a d p : V) : (bindOneAtDef L).val.Evalb ![out,a,d,p] ↔
    out = bindOneAt L a d p := by simp
example (a d z : V) : termBindOneAt L a d (^#z) = ^#z := termBindOneAt_bvar a d z
example (a d : V) : termBindOneAt L a d (^&a) = ^#d := termBindOneAt_chosen a d
example (a d x : V) (h : x ≠ a) : termBindOneAt L a d (^&x) = ^&x := termBindOneAt_other a d x h
example (a d : V) : termBindOneAt L a d (^&(a+1)) = ^&(a+1) := termBindOneAt_other a d (a+1) (by simp)
example (a d t : V) (h : IsSemiterm L d t) :
    IsSemiterm L (d+1) (termBindOneAt L a d t) := termBindOneAt_isSemiterm h a
example (a d k v : V) (h : IsSemitermVec L k d v) :
    IsSemitermVec L k (d+1) (termBindOneVecAt L a d k v) := termBindOneVecAt_isSemiterm h a
example (a d p : V) (h : IsSemiformula L d p) :
    IsSemiformula L (d+1) (bindOneAt L a d p) := bindOneAt_isSemiformula h a
example (a d t : V) (h : IsSemiterm L d t) :
    termSubst L (qVecIter L d (^&a ∷ 0)) (termBindOneAt L a d t) = t := termBindOneAt_inverse h a
example (a d k v : V) (h : IsSemitermVec L k d v) :
    termSubstVec L k (qVecIter L d (^&a ∷ 0)) (termBindOneVecAt L a d k v) = v := termBindOneVecAt_inverse h a
example (a d p : V) (h : IsSemiformula L d p) :
    subst L (qVecIter L d (^&a ∷ 0)) (bindOneAt L a d p) = p := bindOneAt_inverse h a
example (a d p : V) (h : IsUFormula L p) :
    bindOneAt L a d (^∀ p) = ^∀ (bindOneAt L a (d+1) p) := bindOneAt_all a d h
example (a d p : V) (h : IsUFormula L p) :
    bindOneAt L a d (^∃ p) = ^∃ (bindOneAt L a (d+1) p) := bindOneAt_exs a d h
example (a d : V) : bindOneAt L a d (^∀ (^∃ ^⊤)) = ^∀ (^∃ ^⊤) := by
  rw [bindOneAt_all a d (by simp),bindOneAt_exs a (d+1) (by simp),bindOneAt_verum]
example (a p : V) (hp : IsFormula L p) : IsFormula L (namedAll L a p) := namedAll_isFormula hp a
example (a p : V) (hp : IsFormula L p) :
    substs1 L (^&a) (bindOneAt L a 0 p) = p := bindOneAt_open hp a
example (a p : V) (hp : IsFormula L p) :
    ∃ b : V, IsSemiformula L 1 b ∧ substs1 L (^&a) b = p :=
  ⟨bindOneAt L a 0 p,by simpa using bindOneAt_isSemiformula hp a,bindOneAt_open hp a⟩
