import PA194ZeroSelectedRollback
import PA194SelectedZeroTo12
import PA194HeaderController
import PA194NineOdd
import PA194DecrementZeroCell
import PA194LeftRows
import PA194RightRows
import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroSelectedScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroSelectedRollback PA194SelectedZeroTo12 PA194HeaderController PA194ZeroRuns PA194StateOne PA194FiniteControls PA194NineOdd PA194DecrementZeroCell PA194LeftRows PA194RightRows PackedIterationModel ConfigurationStep
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- Roll back the selected-zero result and reach the state-12 scanner. -/
theorem rollbackTo12 (m h file : M) :
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let left := F ones ![m,(a3+a3)+(a3+a3)]
    let p := F ones ![m,file]
    F PA194Stepper.stepper ![m+modelNumeral M 8,
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => left),
        F parityCode (fun _ => left)+file+file]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![xx+xx+1,
      F zeros ![modelNumeral M 6,p+p+1]]] := by
  dsimp only
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let p := F ones ![m,file]
  change F PA194Stepper.stepper ![F addCode ![m,modelNumeral M 8],_] = _
  rw [PA194StepperCompose.modelStepperCompose,rollbackSelectedZero,←zerosSix]
  exact boundaryTo12 h p
#print axioms rollbackTo12
end models
end PA194ZeroSelectedScan
