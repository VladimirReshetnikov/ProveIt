import PA194IncrementHeaderReturn
import PA194SevenToSixteen
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SevenIncrementHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194IncrementHeaderReturn PA194SevenToSixteen PA194RegisterFile PA194ZeroRuns
open BinaryTapeCodes PA194UnaryRuns PA194SixteenScanExit PA194BinaryDouble
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
/-- Positive first block: continue the increment return to the next header. -/
theorem sevenToHeader (h k r : M) :
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let b := F block ![k+1,r+r]
    let n := modelNumeral M 2
    let z := F zeros ![n,F zeros ![k,1+(r+r)+(r+r)]]
    let c := (((((((n+1)+(k+1))+1)+1)+k)+n)+1)+1
    let w := F ones ![modelNumeral M 4+1,1+(z+z)+(z+z)]
    F PA194Stepper.stepper ![(modelNumeral M 2+c)+((modelNumeral M 4+1)+1),
      F pairCode ![modelNumeral M 7,F pairCode ![a3+a3,b+b]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,1+(w+w)+(w+w)]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,positiveFirstToSixteen]
  exact incrementToHeader _ _
#print axioms sevenToHeader
end models
end PA194SevenIncrementHeader
