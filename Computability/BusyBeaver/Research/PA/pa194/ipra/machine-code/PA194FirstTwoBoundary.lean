import PA194PositiveThreshold
import PA194PositiveMarkerRoute
import PA194RightRows
import PA194ThresholdRows
import PA194MarkDelimiter
/-! All-model state-35 one-run classification and the five-one marker-return branch. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194FirstTwoBoundary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194RightRows
open PA194PositiveThreshold PA194ThresholdRows PA194MarkDelimiter PA194PositiveMarkerRoute PA194IncrementDispatch PA194MarkToHeader PA194OnesCommute PA194ReturnFile
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194MarkerScan PRAModelIOpenPairing TableDispatch PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem twoTo86 (l t : M) :
    let w := (t+t)+(t+t)
    let a0 := l+l+1
    let a1 := a0+a0+1
    F PA194Stepper.stepper ![modelNumeral M 2+1,
      F pairCode ![modelNumeral M 35,F pairCode ![l,F ones ![modelNumeral M 2,w]]]] =
    F pairCode ![modelNumeral M 86,F pairCode ![a1+a1,t+t]] := by
  dsimp only
  let w := (t+t)+(t+t)
  let a0 := l+l+1
  let a1 := a0+a0+1
  have ht : F ones ![modelNumeral M 2,w] = (w+w+1)+(w+w+1)+1 := by
    rw [show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h1 := shortTraverse2 l w
  dsimp only at h1
  rw [←ht] at h1
  have h2 := shortBoundary (⟨2,by decide⟩ : Fin 5) a1 (t+t)
  have h2' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![a1,w]]) =
      F pairCode ![modelNumeral M 86,F pairCode ![a1+a1,t+t]] := by
    simpa [shortControl,shortExit,w] using h2
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h1,h2']
#print axioms twoTo86
end models
end PA194FirstTwoBoundary
