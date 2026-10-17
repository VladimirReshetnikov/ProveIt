import ZFCinPA.ModelCodedBinderAbsorption
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.termBindOneAt_absorb
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.termBindOneVecAt_absorb
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.bindOneAt_absorb
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.bindOneAt_namedAll
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.subst_unused_free
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.substs1_formula
#print axioms LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.free_formula
example (d t a : V) (h : IsSemiterm L d t) :
    termBindOneAt L a (d+1) (termBindOneAt L a d t) = termBindOneAt L a d t :=
  termBindOneAt_absorb h a
example (d k ts a : V) (h : IsSemitermVec L k d ts) :
    termBindOneVecAt L a (d+1) k (termBindOneVecAt L a d k ts) =
      termBindOneVecAt L a d k ts := termBindOneVecAt_absorb h a
example (d p a : V) (h : IsSemiformula L d p) :
    bindOneAt L a (d+1) (bindOneAt L a d p) = bindOneAt L a d p := bindOneAt_absorb h a
example (p a : V) (h : IsFormula L p) :
    bindOneAt L a 0 (namedAll L a p) = namedAll L a p := bindOneAt_namedAll h a
example (d p : V) (h : IsSemiformula L d p) :
    bindOneAt L 0 (d+1) (bindOneAt L 0 d p) = bindOneAt L 0 d p := bindOneAt_absorb h 0
example (a : V) : bindOneAt L a 0 (namedAll L a (^⊤ : V)) = namedAll L a (^⊤ : V) :=
  bindOneAt_namedAll (by simp) a
example (d p x : V) (h : IsSemiformula L d p) :
    subst L (qVecIter L d (^&x ∷ 0)) p = p := subst_unused_free h x
example (p x : V) (h : IsFormula L p) : substs1 L (^&x) p = p := substs1_formula h x
example (p : V) (h : IsFormula L p) : free L p = shift L p := free_formula h
