import PA194PositiveThreshold
import PA194PositiveMarkerRoute
import PA194RightRows
import PA194ThresholdRows
import PA194MarkDelimiter
/-! All-model state-35 one-run classification and the five-one marker-return branch. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194FirstZeroBoundary
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

theorem zeroTo46 (l t : M) :
    let w := (t+t)+(t+t)
    F PA194Stepper.stepper ![(0 : M)+1,
      F pairCode ![modelNumeral M 35,F pairCode ![l,F ones ![(0 : M),w]]]] =
    F pairCode ![modelNumeral M 46,F pairCode ![l+l,t+t]] := by
  dsimp only
  rw [modelOnesZero]
  change F PA194Stepper.stepper ![F addCode ![(0 : M),F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have hz := PA194Stepper.modelStepperZero (F pairCode ![modelNumeral M 35,F pairCode ![l,(t+t)+(t+t)]])
  change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
  rw [hz]
  have h := shortBoundary (⟨0,by decide⟩ : Fin 5) l (t+t)
  simpa [shortControl,shortExit] using h
#print axioms zeroTo46
end models
end PA194FirstZeroBoundary
