import PA194Site33JumpPath
import PA194SourceSite33Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite33Physical
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

theorem sourcePhysical (k tail : M) (args : Fin 11 → M) :
    F step ![sourceState 33 args tail] = sourceState 31 args tail ∧
      F PA194Stepper.stepper ![modelNumeral M 34,physicalFrame 33 ((k+1)+1) args] =
        physicalFrame 31 (((k+1)+1)+1) args := by
  exact ⟨PA194SourceSite33Controller.controllerStep args tail,PA194Site33JumpPath.jumpPath k args⟩
#print axioms sourcePhysical
end models
end PA194SourceSite33Physical
