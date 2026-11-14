import PA194ContinueTwoHeader
import PA194SeventeenToRootControl
import PA194ZeroFirstHeader
import PA194ZeroFirstReturn
import PA194MarkerReturnCell
import PA194MarkDelimiter
import PA194FourteenComposition
import PA194HeaderController
import PA194SevenReturnController
import PA194FifteenExitComposition
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroFirstContinue
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FiniteControls PA194ContinueTwoHeader PA194SeventeenToRootControl PA194ZeroFirstHeader PA194ZeroFirstReturn PA194MarkerReturnCell PA194BinaryDouble PA194MarkDelimiter PA194FourteenComposition PA194HeaderController PA194StateOne
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ZeroRuns PA194SevenReturnController
open PA194FifteenExitComposition PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The zero first block reaches dense 24 and takes the continue-two path. -/
theorem zeroToContinueTarget (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let b := F block ![(0 : M),r+r]
    let t := (1 : M)+(r+r)+(r+r)
    let z := t+t
    let rr := z+z
    let tt := (rr+rr)+(rr+rr)
    let out := F ones ![modelNumeral M 3,1+tt+tt]
    let c := (modelNumeral M 2+(((modelNumeral M 2+1)+(0 : M))+1+1))+modelNumeral M 2
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((c+((modelNumeral M 5+1)+1))+ct)+modelNumeral M 32,
      F pairCode ![modelNumeral M 7,F pairCode ![a3+a3,b+b]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(out+out)+(out+out)]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let t := (1 : M)+(r+r)+(r+r)
  let z := t+t
  let q := z+z
  let w := F ones ![modelNumeral M 5,1+q+q]
  have h1 := zeroTo17 (M := M) h r
  have h2 := returnToControl24 u w
  have h3 := continueHeader u z
  dsimp only at h1 h2 h3
  have hfive : modelNumeral M 4+1 = modelNumeral M 5 := by
    rw [←modelNumeralOne,←modelNumeralAdd]
  rw [hfive] at h3
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  exact h3
#print axioms zeroToContinueTarget
end models
end PA194ZeroFirstContinue
