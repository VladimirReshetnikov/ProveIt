import PA194PositiveThreshold
import PA194PositiveMarkerRoute
import PA194RightRows
import PA194ThresholdRows
import PA194MarkDelimiter
/-! All-model state-35 one-run classification and the five-one marker-return branch. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194FirstOneBoundary
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

theorem oneTo36 (l t : M) :
    let w := (t+t)+(t+t)
    let a0 := l+l+1
    F PA194Stepper.stepper ![modelNumeral M 1+1,
      F pairCode ![modelNumeral M 35,F pairCode ![l,F ones ![modelNumeral M 1,w]]]] =
    F pairCode ![modelNumeral M 36,F pairCode ![a0+a0,t+t]] := by
  dsimp only
  let w := (t+t)+(t+t)
  let a0 := l+l+1
  have ht : F ones ![modelNumeral M 1,w] = w+w+1 := by
    rw [show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h1 := shortTraverse1 l w
  dsimp only at h1
  rw [←ht] at h1
  have h2 := shortBoundary (⟨1,by decide⟩ : Fin 5) a0 (t+t)
  have h2' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 47,F pairCode ![a0,w]]) =
      F pairCode ![modelNumeral M 36,F pairCode ![a0+a0,t+t]] := by
    simpa [shortControl,shortExit,w] using h2
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h1,h2']
#print axioms oneTo36
end models
end PA194FirstOneBoundary
