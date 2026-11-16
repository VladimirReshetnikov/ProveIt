import PA194SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SixteenFourRuns
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkerReturnNext PA194SixteenTwoRuns PA194SixteenReturnRun PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem modelSixteenFourRuns (n0 n1 n2 n3 l r : M) :
    let x1 := F ones ![n0+1,l+l]
    let x2 := F ones ![n1+1,x1+x1]
    let x3 := F ones ![n2+1,x2+x2]
    let s := F ones ![n3,x3+x3]
    let w1 := F ones ![n3,(1 : M)+r+r]
    let w2 := F ones ![n2,(1 : M)+(w1+w1)+(w1+w1)]
    let w3 := F ones ![n1,(1 : M)+(w2+w2)+(w2+w2)]
    let w4 := F ones ![n0,(1 : M)+(w3+w3)+(w3+w3)]
    F PA194Stepper.stepper ![(((n3+1)+((n2+1)+1))+((n1+1)+1))+((n0+1)+1),
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => s),
        F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w4+w4)+(w4+w4)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x1 := F ones ![n0+1,l+l]
  let x2 := F ones ![n1+1,x1+x1]
  let x3 := F ones ![n2+1,x2+x2]
  let w1 := F ones ![n3,(1 : M)+r+r]
  let w2 := F ones ![n2,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![n1,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![n0,(1 : M)+(w3+w3)+(w3+w3)]
  have h1 := modelSixteenTwoRuns n3 n2 x2 r
  dsimp only at h1
  have h3 := modelMarkerReturnNext n1 x1 w2
  dsimp only at h3
  have h4 := modelMarkerReturnNext n0 l w3
  dsimp only at h4
  let start := F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => F ones ![n3,x3+x3]),
    F parityCode (fun _ => F ones ![n3,x3+x3])+(1+1)+(r+r)+(r+r)]]
  let t1 := (n3+1)+((n2+1)+1)
  let t3 := (n1+1)+1
  let t4 := (n0+1)+1
  have chain3 : F PA194Stepper.stepper ![t1+t3,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),
        F parityCode (fun _ => x1)+(w3+w3)+(w3+w3)]] := by
    change F PA194Stepper.stepper ![F addCode ![t1,t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1]
    exact h3
  have chain4 : F PA194Stepper.stepper ![(t1+t3)+t4,start] =
      F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
        F parityCode (fun _ => l)+(w4+w4)+(w4+w4)]] := by
    change F PA194Stepper.stepper ![F addCode ![(t1+t3),t4],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain3]
    exact h4
  exact chain4
#print axioms modelSixteenFourRuns
end models
end PA194SixteenFourRuns
