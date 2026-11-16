import PA194HeaderController
import PA194ControllerReturn
import PA194ZeroScanInvariant
import PA194FifteenExitComposition
import PA194MarkerReturnCell
import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SelectedZeroSeventeenTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FiniteControls PA194StateOne PA194HeaderController PA194ControllerReturn PA194BinaryDouble PA194ZeroScanInvariant PA194FifteenExitComposition PA194MarkerReturnCell PA194StateOne PA194ZeroRuns
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
/-- The selected-zero state-17 header returns to dense 24. -/
theorem seventeenTo24 (u b : M) :
    let s := F zeros ![modelNumeral M 1,F zeros ![modelNumeral M 6,u]]
    let v := 1+(b+b)+(b+b)
    let w := F ones ![modelNumeral M 2,v]
    let t := F ones ![modelNumeral M 1,v]
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let ct := ((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1
    F PA194Stepper.stepper ![(1 : M)+ct,
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => s),
        F parityCode (fun _ => s)+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![g+g+1,t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a := F zeros ![modelNumeral M 6,u]
  let d := F zeros ![modelNumeral M 5,u]
  let v := 1+(b+b)+(b+b)
  let t := F ones ![modelNumeral M 1,v]
  let w := F ones ![modelNumeral M 2,v]
  have hs : F zeros ![modelNumeral M 1,a] = a+a := by
    rw [show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelZerosSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelZerosZero]
  have ha : a=d+d := by
    dsimp [a]
    rw [show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,modelZerosSucc]
  have hd : d = (((u+u)+(u+u))+((u+u)+(u+u)))+(((u+u)+(u+u))+((u+u)+(u+u)))+
      ((((u+u)+(u+u))+((u+u)+(u+u)))+(((u+u)+(u+u))+((u+u)+(u+u)))) := by
    dsimp [d]
    rw [show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,modelZerosSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelZerosSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelZerosSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelZerosSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelZerosSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelZerosZero]
  have hw : w=t+t+1 := by
    dsimp [w]
    rw [show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc]
  have h1 := modelPackedSeventeenEven a (w+w)
  have hhalf : F halfCode (fun _ => a) = d := by rw [ha,(modelDouble d).2]
  have hpar : F parityCode (fun _ => a) = (0 : M) := by rw [ha,(modelDouble d).1]
  rw [hhalf,hpar,zero_add,hd] at h1
  have h2 := headerHandoff (modelNumeral M 2) u t
  dsimp only at h2
  rw [zerosTwo] at h2
  rw [←hw] at h2
  have step (x : M) : F PA194Stepper.stepper ![x+1,
      F pairCode ![modelNumeral M 17,F pairCode ![a,(w+w)+(w+w)]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![x,
        F pairCode ![modelNumeral M 17,F pairCode ![a,(w+w)+(w+w)]]]) := by
    change F PA194Stepper.stepper ![F addCode ![x,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  rw [hs,(modelDouble a).1,(modelDouble a).2,zero_add]
  change F PA194Stepper.stepper ![F addCode ![(1 : M),_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have step1 (x : M) : F PA194Stepper.stepper ![(1 : M),x] = F PackedClock.encodedStep (fun _ => x) := by
    rw [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => (0 : M)),x] = _
    rw [PA194Stepper.modelStepperSucc]
    change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,x]) = _
    rw [PA194Stepper.modelStepperZero]
  rw [step1,h1]
  simpa only [add_assoc,t,v] using h2
#print axioms seventeenTo24
end models
end PA194SelectedZeroSeventeenTo24
