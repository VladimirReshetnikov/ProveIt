import PA194SourceSite38ZeroPhysical
import PA194Site38ZeroPath
import PA194SourceSite41Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite38ZeroThen41
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem twoSteps (k tail : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    F step ![F step ![sourceState 38 args tail]] = sourceState 34 args tail ∧
    F PA194Stepper.stepper ![modelNumeral M 34,
      F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site38ZeroRollback.cost args,k+1],modelNumeral M 5],((modelNumeral M 3+1)+(k+1))+1],((1 : M)+((k+1)+1))+modelNumeral M 3],modelNumeral M 25],
        PA194Site38Branch.runTo4 k args]] = physicalFrame 34 ((((((k+1)+1)+1)+1)+1)+1) args := by
  have h38 := PA194SourceSite38ZeroPhysical.zeroBranch k tail args hz
  have h41 := PA194SourceSite41Physical.sourcePhysical ((((k+1)+1)+1)+1) tail args
  refine ⟨?_,?_⟩
  · rw [h38.1,h41.1]
  · rw [h38.2,h41.2]
#print axioms twoSteps
end models
end PA194SourceSite38ZeroThen41
