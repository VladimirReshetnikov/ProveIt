import PA194Site35MarkerReturnNext
import PA194SixteenTwoRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site35SixteenSixRuns
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

theorem modelSixteenSixRuns (n0 n1 n2 n3 n4 n5 l r : M) :
    let x1 := F ones ![n0+1,l+l]
    let x2 := F ones ![n1+1,x1+x1]
    let x3 := F ones ![n2+1,x2+x2]
    let x4 := F ones ![n3+1,x3+x3]
    let x5 := F ones ![n4+1,x4+x4]
    let s := F ones ![n5,x5+x5]
    let w1 := F ones ![n5,(1 : M)+r+r]
    let w2 := F ones ![n4,(1 : M)+(w1+w1)+(w1+w1)]
    let w3 := F ones ![n3,(1 : M)+(w2+w2)+(w2+w2)]
    let w4 := F ones ![n2,(1 : M)+(w3+w3)+(w3+w3)]
    let w5 := F ones ![n1,(1 : M)+(w4+w4)+(w4+w4)]
    let w6 := F ones ![n0,(1 : M)+(w5+w5)+(w5+w5)]
    F PA194Stepper.stepper ![(((((n5+1)+((n4+1)+1))+((n3+1)+1))+((n2+1)+1))+((n1+1)+1))+((n0+1)+1),
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => s),
        F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w6+w6)+(w6+w6)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x1 := F ones ![n0+1,l+l]
  let x2 := F ones ![n1+1,x1+x1]
  let x3 := F ones ![n2+1,x2+x2]
  let x4 := F ones ![n3+1,x3+x3]
  let x5 := F ones ![n4+1,x4+x4]
  let w1 := F ones ![n5,(1 : M)+r+r]
  let w2 := F ones ![n4,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![n3,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![n2,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![n1,(1 : M)+(w4+w4)+(w4+w4)]
  let w6 := F ones ![n0,(1 : M)+(w5+w5)+(w5+w5)]
  have h1 := modelSixteenTwoRuns n5 n4 x4 r
  dsimp only at h1
  have h3 := modelMarkerReturnNext n3 x3 w2
  dsimp only at h3
  have h4 := modelMarkerReturnNext n2 x2 w3
  dsimp only at h4
  have h5 := modelMarkerReturnNext n1 x1 w4
  dsimp only at h5
  have h6 := modelMarkerReturnNext n0 l w5
  dsimp only at h6
  let start := F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => F ones ![n5,x5+x5]),
    F parityCode (fun _ => F ones ![n5,x5+x5])+(1+1)+(r+r)+(r+r)]]
  let t1 := (n5+1)+((n4+1)+1)
  let t3 := (n3+1)+1
  let t4 := (n2+1)+1
  let t5 := (n1+1)+1
  let t6 := (n0+1)+1
  have chain3 : F PA194Stepper.stepper ![t1+t3,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x3),
        F parityCode (fun _ => x3)+(w3+w3)+(w3+w3)]] := by
    change F PA194Stepper.stepper ![F addCode ![t1,t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1]
    exact h3
  have chain4 : F PA194Stepper.stepper ![(t1+t3)+t4,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),
        F parityCode (fun _ => x2)+(w4+w4)+(w4+w4)]] := by
    change F PA194Stepper.stepper ![F addCode ![(t1+t3),t4],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain3]
    exact h4
  have chain5 : F PA194Stepper.stepper ![((t1+t3)+t4)+t5,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),
        F parityCode (fun _ => x1)+(w5+w5)+(w5+w5)]] := by
    change F PA194Stepper.stepper ![F addCode ![((t1+t3)+t4),t5],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain4]
    exact h5
  have chain6 : F PA194Stepper.stepper ![(((t1+t3)+t4)+t5)+t6,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
        F parityCode (fun _ => l)+(w6+w6)+(w6+w6)]] := by
    change F PA194Stepper.stepper ![F addCode ![(((t1+t3)+t4)+t5),t6],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain5]
    exact h6
  exact chain6
#print axioms modelSixteenSixRuns
end models
end PA194Site35SixteenSixRuns
