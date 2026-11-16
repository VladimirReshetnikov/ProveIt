import PA194Site40JumpPath
import PA194SourceSite40Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite40Physical
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
    F step ![sourceState 40 args tail] = sourceState 38 args tail ∧
      F PA194Stepper.stepper ![modelNumeral M 40,physicalFrame 40 k args] =
        physicalFrame 38 (k+1) args := by
  exact ⟨PA194SourceSite40Controller.controllerStep args tail,PA194Site40JumpPath.jumpPath k args⟩
#print axioms sourcePhysical
end models
end PA194SourceSite40Physical
