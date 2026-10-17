import ZFCinPA.ModelCodedRenamingBindOne

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedRenamingBindOne
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingBindOne.bindOneAt_free
#print axioms LeanProofs.ZFCinPA.ModelCodedRenamingBindOne.free_bindOneAt

example (a d p : V) (hp : IsSemiformula L d p) :
    subst L (LeanProofs.ZFCinPA.ModelCodedSpecialization.qVecIter L d (^&0 ∷ 0))
      (shift L (bindOneAt L a d p)) = rename L a 0 0 p := bindOneAt_free hp a
example (a p : V) (hp : IsFormula L p) :
    free L (bindOneAt L a 0 p) = rename L a 0 0 p := free_bindOneAt hp a
-- Literal truth may contain free zero; these laws have no freshness premise.
example (a p : V) (hp : IsFormula L p) :
    IsFormula L (namedAll L a p) := namedAll_isFormula hp a
