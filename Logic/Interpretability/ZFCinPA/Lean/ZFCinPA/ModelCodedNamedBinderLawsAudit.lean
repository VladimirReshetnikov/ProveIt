import ZFCinPA.ModelCodedNamedBinderLaws

set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws.bindOneAt_neg
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws.bindOneAt_imp
example (d p a : V) (hp : IsSemiformula L d p) :
    bindOneAt L a d (neg L p) = neg L (bindOneAt L a d p) := bindOneAt_neg hp a
example (d p q a : V) (hp : IsSemiformula L d p) (hq : IsSemiformula L d q) :
    bindOneAt L a d (imp L p q) =
      imp L (bindOneAt L a d p) (bindOneAt L a d q) := bindOneAt_imp hp hq a
example (p : V) (hp : IsFormula L p) :
    bindOneAt L 0 0 (neg L p) = neg L (bindOneAt L 0 0 p) := bindOneAt_neg hp 0
example (d p a : V) (hp : IsSemiformula L (d+1) p) :
    bindOneAt L a d (neg L (^∀ p)) = neg L (bindOneAt L a d (^∀ p)) :=
  bindOneAt_neg (IsSemiformula.all.mpr hp) a
example (d a : V) : bindOneAt L a d (neg L (^⊤ : V)) =
    neg L (bindOneAt L a d (^⊤ : V)) := bindOneAt_neg IsSemiformula.verum a
