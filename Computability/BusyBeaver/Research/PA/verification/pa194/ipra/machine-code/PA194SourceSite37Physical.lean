import PA194Site37JumpPath
import PA194SourceSite37Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite37Physical
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
    F step ![sourceState 37 args tail] = sourceState 41 args tail ∧
      F PA194Stepper.stepper ![modelNumeral M 38,physicalFrame 37 k args] =
        physicalFrame 41 ((k+1)+1) args := by
  exact ⟨PA194SourceSite37Controller.controllerStep args tail,PA194Site37JumpPath.jumpPath k args⟩
#print axioms sourcePhysical
end models
end PA194SourceSite37Physical
