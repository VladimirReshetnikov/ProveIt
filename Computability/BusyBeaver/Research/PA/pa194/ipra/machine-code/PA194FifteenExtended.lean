import PA194FifteenReturn
import PA194ZeroScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194FifteenExtended
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194UnaryRuns PA194ZeroRuns PA194FifteenReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelExtendedReturn (n m l r : M) :
    F PA194Stepper.stepper ![(((((n+1)+(m+1))+1)+1)+m)+n,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 15,
      F pairCode ![l,F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]+F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]]] := by
  change F PA194Stepper.stepper ![F addCode ![((((n+1)+(m+1))+1)+1)+m,n],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelReturn,PA194ZeroScanInvariant.modelFullScan]
#print axioms modelExtendedReturn
end models
end PA194FifteenExtended
