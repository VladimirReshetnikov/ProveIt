import PA194DecrementPositiveCell
import PA194RightRows
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27BranchRows
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194UnaryRuns PA194RightRows PA194DecrementPositiveCell PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem zeroRow (z t : M) :
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 4,
      F pairCode ![z+z,F ones ![(0 : M),t+t]]]] =
    F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  rw [modelOnesZero]
  have h := rightZero 4 1 5 (by decide) (by decide +kernel) (z+z) t
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,h]

theorem positiveRow (z m tail : M) :
    let r := F ones ![m,tail]
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 4,
      F pairCode ![z+z,F ones ![m+1,tail]]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![z,(r+r+1)+(r+r+1)]] := by
  dsimp only
  have h : F ones ![m+1,tail] = F ones ![m,tail]+F ones ![m,tail]+1 := by
    change F ones ![F addCode ![m,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  rw [h]
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,packedFourOdd]
#print axioms zeroRow
#print axioms positiveRow
end models
end PA194Site27BranchRows
