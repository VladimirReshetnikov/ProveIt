import PA194TwelveExitComposition
import PA194ThirteenScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194TwelveThirteenCompose
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194TwelveExitComposition PA194ThirteenScanInvariant PA194UnaryRuns PA194ZeroRuns

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelTwoScans (n m l r : M) :
    F PA194Stepper.stepper ![(n+1)+m,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m,r]+F ones ![m,r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 13,
      F pairCode ![F zeros ![m,F zeros ![n,l]+F zeros ![n,l]],r]] := by
  change F PA194Stepper.stepper ![F addCode ![n+1,m],_] = _
  rw [PA194StepperCompose.modelStepperCompose, PA194TwelveExitComposition.modelScanExit,
    PA194ThirteenScanInvariant.modelFullScan]
#print axioms modelTwoScans
end models
end PA194TwelveThirteenCompose
