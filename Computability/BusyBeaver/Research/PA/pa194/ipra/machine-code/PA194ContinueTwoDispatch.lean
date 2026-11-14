import PA194PositiveThreshold
import PA194SeventeenToRootControl
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ContinueTwoDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FiniteControls PA194PositiveMarkerRoute PA194PositiveThreshold PA194MarkerReturnCell PA194HeaderController PA194StateOne PA194SeventeenToRootControl PA194ZeroRuns
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
/-- First nine pinned transitions for the path bits `10111111`. -/
theorem nineToFifteen (h r : M) :
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let b := t4+t4+1
    let a := b+b
    let l1 := h+h+1
    let l2 := l1+l1
    let l3 := l2+l2+1
    let a0 := l3+l3+1
    let a1 := a0+a0+1
    F PA194Stepper.stepper ![modelNumeral M 3+modelNumeral M 6,
      F pairCode ![modelNumeral M 24,F pairCode ![h,a+a+1]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a1,((r+r)+(r+r))+((r+r)+(r+r))+1]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,threeTo35]
  exact fiveThreshold (M := M) _ _
/-- The three-one return following the dispatch. -/
theorem fifteenToSeventeen (h r : M) :
    let l := h+h+1
    let t := (r+r)+(r+r)
    let v := F ones ![modelNumeral M 3,(1 : M)+t+t]
    F PA194Stepper.stepper ![(modelNumeral M 3+1)+1,
      F pairCode ![modelNumeral M 15,F pairCode ![F ones ![modelNumeral M 3,l+l],t+t+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,1+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hm := modelMarkerReturnCell ⟨0,by decide⟩ (modelNumeral M 3) (h+h+1) ((r+r)+(r+r))
  dsimp only at hm
  rw [(modelOdd h).1,(modelOdd h).2] at hm
  exact hm
/-- Dispatch and return to dense control 24, preserving the high tape. -/
theorem continueTwo (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let b := t4+t4+1
    let a := b+b
    let t := (r+r)+(r+r)
    let v := F ones ![modelNumeral M 3,(1 : M)+t+t]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((modelNumeral M 3+modelNumeral M 6)+((modelNumeral M 3+1)+1))+ct,
      F pairCode ![modelNumeral M 24,F pairCode ![h,a+a+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let t := (r+r)+(r+r)
  let v := F ones ![modelNumeral M 3,(1 : M)+t+t]
  have htape : F ones ![modelNumeral M 3,(h+h+1)+(h+h+1)] =
      (((h+h+1)+(h+h+1)+(h+h+1+(h+h+1))+1)+
        ((h+h+1)+(h+h+1)+(h+h+1+(h+h+1))+1)+1)+
       (((h+h+1)+(h+h+1)+(h+h+1+(h+h+1))+1)+
        ((h+h+1)+(h+h+1)+(h+h+1+(h+h+1))+1)+1)+1 := by
    rw [show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h1 := nineToFifteen (M := M) h r
  dsimp only at h1
  have h2 := fifteenToSeventeen (M := M) h r
  dsimp only at h2
  rw [htape] at h2
  have h3 := returnToControl24 u v
  dsimp only at h3
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  exact h3
/-- The same transition with the exact numeral 32 clock. -/
theorem continueTwo32 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let b := t4+t4+1
    let a := b+b
    let t := (r+r)+(r+r)
    let v := F ones ![modelNumeral M 3,(1 : M)+t+t]
    F PA194Stepper.stepper ![modelNumeral M 32,
      F pairCode ![modelNumeral M 24,F pairCode ![h,a+a+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hm := continueTwo (M := M) u r
  dsimp only at hm ⊢
  have hc : ((modelNumeral M 3+modelNumeral M 6)+((modelNumeral M 3+1)+1))+
      ((((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)) = modelNumeral M 32 := by
    simp only [←modelNumeralOne,←modelNumeralAdd]
  rw [hc] at hm
  exact hm
#print axioms continueTwo32
#print axioms continueTwo
#print axioms fifteenToSeventeen
#print axioms nineToFifteen
end models
end PA194ContinueTwoDispatch
