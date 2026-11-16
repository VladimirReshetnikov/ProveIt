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
namespace PA194SelectedZeroFifteenReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroScanInvariant PA194FifteenExitComposition PA194MarkerReturnCell PA194StateOne PA194ZeroRuns
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
/-- Scan the actual state-15 zero run and reach the next state-17 header. -/
theorem fifteenTo17 (m s r : M) :
    let g := s+s
    let h := g+g+1
    let xx := h+h+1
    let l := xx+xx+1
    let t := (1 : M)+(r+r)+(r+r)
    let b := F zeros ![modelNumeral M 5,F zeros ![m,t]]
    let w := F ones ![modelNumeral M 2,1+(b+b)+(b+b)]
    F PA194Stepper.stepper ![((m+modelNumeral M 5)+1)+((modelNumeral M 2+1)+1),
      F pairCode ![modelNumeral M 15,F pairCode ![F zeros ![m,F zeros ![modelNumeral M 5,l]],t+t]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => s),
      F parityCode (fun _ => s)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := s+s
  let h := g+g+1
  let xx := h+h+1
  let l := xx+xx+1
  let t := (1 : M)+(r+r)+(r+r)
  let b := F zeros ![modelNumeral M 5,F zeros ![m,t]]
  let w := F ones ![modelNumeral M 2,1+(b+b)+(b+b)]
  have h1 := PA194ZeroScanInvariant.modelFullScan m (F zeros ![modelNumeral M 5,l]) t
  have h2 := PA194ZeroScanInvariant.modelFullScan (modelNumeral M 5) l (F zeros ![m,t])
  have h3 := modelPackedBoundary15 xx b
  have hl : F ones ![modelNumeral M 2,s+s] = xx := by
    rw [show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h4 := modelMarkerReturnCell ⟨0,by decide⟩ (modelNumeral M 2) s (b+b)
  dsimp only at h4
  rw [hl] at h4
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,F oneCode Fin.elim0],_]] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PA194Stepper.stepper ![_,F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![_,_],_])] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2,h3]
  exact h4
#print axioms fifteenTo17
end models
end PA194SelectedZeroFifteenReturn
