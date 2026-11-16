import PA194Site42ZeroPath
import PA194SourceSite42Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite42ZeroPhysical
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

theorem zeroBranch (k tail : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    F step ![sourceState 42 args tail] = sourceState 45 args tail ∧
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site42ZeroRollback.cost args,k+1],modelNumeral M 5],((modelNumeral M 3+1)+(k+1))+1],((1 : M)+((k+1)+1))+modelNumeral M 3],modelNumeral M 21],
      PA194Site42Branch.runTo4 k args] = physicalFrame 45 (((k+1)+1)+1) args := by
  exact ⟨PA194SourceSite42Controller.zeroBranch args tail hz,PA194Site42ZeroPath.zeroPath k args hz⟩
#print axioms zeroBranch
end models
end PA194SourceSite42ZeroPhysical
