import PA194Site3664ZeroPath
import PA194SourceSite3664Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite3664ZeroPhysical
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

theorem zeroBranch (k tail : M) (args : Fin 11 → M) (hz : args 5 = (0 : M)) :
    F step ![sourceState 3664 args tail] = sourceState 3668 args tail ∧
    F PA194Stepper.stepper ![F addCode ![PA194Site3664ZeroTo16.clock k args,modelNumeral M 22],
      PA194Site3664Branch.runTo4 k args] = physicalFrame 3668 ((k+1)+1) args := by
  exact ⟨PA194SourceSite3664Controller.zeroBranch args tail hz,PA194Site3664ZeroPath.zeroPath k args hz⟩
#print axioms zeroBranch
end models
end PA194SourceSite3664ZeroPhysical
