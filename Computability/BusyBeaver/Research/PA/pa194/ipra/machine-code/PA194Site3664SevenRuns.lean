import PA194Site35SixteenSixRuns
import PA194Site35MarkerReturnNext
import PA194SixteenTwoRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site3664SevenRuns
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Site35MarkerReturnNext PA194SixteenTwoRuns
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkerScan PA194BinaryDouble
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

theorem modelSevenRuns (n0 n1 n2 n3 n4 n5 n6 l r : M) :
    let x1 := F ones ![n0+1,l+l]
    let x2 := F ones ![n1+1,x1+x1]
    let x3 := F ones ![n2+1,x2+x2]
    let x4 := F ones ![n3+1,x3+x3]
    let x5 := F ones ![n4+1,x4+x4]
    let x6 := F ones ![n5+1,x5+x5]
    let s := F ones ![n6,x6+x6]
    let w1 := F ones ![n6,(1 : M)+r+r]
    let w2 := F ones ![n5,(1 : M)+(w1+w1)+(w1+w1)]
    let w3 := F ones ![n4,(1 : M)+(w2+w2)+(w2+w2)]
    let w4 := F ones ![n3,(1 : M)+(w3+w3)+(w3+w3)]
    let w5 := F ones ![n2,(1 : M)+(w4+w4)+(w4+w4)]
    let w6 := F ones ![n1,(1 : M)+(w5+w5)+(w5+w5)]
    let w7 := F ones ![n0,(1 : M)+(w6+w6)+(w6+w6)]
    F PA194Stepper.stepper ![((((((n6+1)+((n5+1)+1))+((n4+1)+1))+((n3+1)+1))+((n2+1)+1))+((n1+1)+1))+((n0+1)+1),
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => s),
        F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w7+w7)+(w7+w7)]] := by
  dsimp only
  let x1 := F ones ![n0+1,l+l]
  let w1 := F ones ![n6,(1 : M)+r+r]
  let w2 := F ones ![n5,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![n4,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![n3,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![n2,(1 : M)+(w4+w4)+(w4+w4)]
  let w6 := F ones ![n1,(1 : M)+(w5+w5)+(w5+w5)]
  have h6 := PA194Site35SixteenSixRuns.modelSixteenSixRuns n1 n2 n3 n4 n5 n6 x1 r
  dsimp only at h6
  have h7 := PA194Site35MarkerReturnNext.modelMarkerReturnNext n0 l w6
  dsimp only at h7
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h6,h7]
#print axioms modelSevenRuns
end models
end PA194Site3664SevenRuns
