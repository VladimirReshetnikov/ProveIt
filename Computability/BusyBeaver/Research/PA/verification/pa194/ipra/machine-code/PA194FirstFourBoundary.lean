import PA194PositiveThreshold
import PA194PositiveMarkerRoute
import PA194RightRows
import PA194ThresholdRows
import PA194MarkDelimiter
/-! All-model state-35 one-run classification and the five-one marker-return branch. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194FirstFourBoundary
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

/-- Four first-block ones lead to the dense-61 branch. -/
theorem fourTo61 (l t : M) :
    let w := (t+t)+(t+t)
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    F PA194Stepper.stepper ![modelNumeral M 4+1,
      F pairCode ![modelNumeral M 35,F pairCode ![l,F ones ![modelNumeral M 4,w]]]] =
    F pairCode ![modelNumeral M 61,F pairCode ![a3+a3,t+t]] := by
  dsimp only
  let w := (t+t)+(t+t)
  let a0 := l+l+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  have h1 := shortTraverse4 l w
  dsimp only at h1
  have h4 : F ones ![modelNumeral M 4,w] = F ones ![modelNumeral M 3,w]+F ones ![modelNumeral M 3,w]+1 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc]
  rw [h4,onesThree]
  have h2 := shortBoundary (⟨4,by decide⟩ : Fin 5) a3 (t+t)
  have h2' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 43,F pairCode ![a3,w]]) =
      F pairCode ![modelNumeral M 61,F pairCode ![a3+a3,t+t]] := by
    simpa [shortControl,shortExit,w] using h2
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 4,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h1,h2']
#print axioms fourTo61
end models
end PA194FirstFourBoundary
