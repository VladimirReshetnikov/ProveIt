import PA194MarkDelimiter
import PA194MarkerReturnCell
import PA194RegisterFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194RewindFirst
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194BinaryDouble PA194MarkDelimiter PA194MarkerReturnCell
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
/-- The state-14 exit consumes the last traversed block and enters the
marker-return controller, with an exact model-valued clock. -/
theorem firstTo17 (v l t : M) :
    let z := (t+t)+(t+t)
    let a := F ones ![v,(1 : M)+z+z]
    F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
      F pairCode ![modelNumeral M 14,F pairCode ![F block ![v,l+l],t+t+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := F ones ![v,l+l]
  let z := (t+t)+(t+t)
  have hs : F ones ![v+1,l+l] = x+x+1 := by
    change F ones ![F addCode ![v,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h2 : F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 14,
      F pairCode ![F block ![v,l+l],t+t+1]]] =
      F pairCode ![modelNumeral M 15,F pairCode ![x,z+z+1]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,modelBlock,hs,modelPackedWrite,(modelDouble _).1,(modelDouble _).2,zero_add,
      modelPackedReturn,(modelOdd x).1,(modelOdd x).2]
    dsimp [z]
    simp only [add_assoc,add_comm,add_left_comm]
  have hm := modelMarkerReturnCell ⟨0,by decide⟩ v l z
  dsimp only at hm
  rw [show returnControl (⟨0,by decide⟩ : Fin 2) = 15 from rfl] at hm
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,(v+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h2,hm]
#print axioms firstTo17
end models
end PA194RewindFirst
