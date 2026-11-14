import PA194SeventeenToRootControl
import PA194ZeroScanInvariant
import PA194FifteenExitComposition
import PA194MarkerReturnCell
import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFiveFifteenTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeventeenToRootControl PA194BinaryDouble PA194ZeroScanInvariant PA194FifteenExitComposition PA194MarkerReturnCell PA194StateOne PA194ZeroRuns
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
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
/-- Normalize the state-15 scanner return to dense 24 for any model-valued
number of remaining ones in its left tape. -/
theorem fifteenTo24 (n u q : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let t := (1 : M)+q+q
    let w := F ones ![n,1+t+t]
    let w2 := F ones ![modelNumeral M 3,1+(w+w)+(w+w)]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((n+1)+1)+((modelNumeral M 3+1)+1))+ct,
      F pairCode ![modelNumeral M 15,F pairCode ![F ones ![n,a3],t+t+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w2+w2)+(w2+w2)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let t := (1 : M)+q+q
  let w := F ones ![n,1+t+t]
  let w2 := F ones ![modelNumeral M 3,1+(w+w)+(w+w)]
  have h1 := modelMarkerReturnCell ⟨0,by decide⟩ n a2 t
  dsimp only at h1
  rw [show returnControl (⟨0,by decide⟩ : Fin 2) = 15 from rfl] at h1
  rw [(modelOdd a1).1,(modelOdd a1).2] at h1
  have ha : F ones ![modelNumeral M 3,xx+xx] = a1 := by
    rw [show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h2 := modelMarkerReturnCell ⟨1,by decide⟩ (modelNumeral M 3) xx (w+w)
  dsimp only at h2
  rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] at h2
  rw [ha,(modelOdd h).1,(modelOdd h).2] at h2
  have ht : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [←ht] at h2
  have h3 := returnToControl24 u w2
  dsimp only at h3
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  exact h3
/-- Apply the return to the exact output of a positive-length dense-84 scan. -/
theorem scanExitTo24 (n u q : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let a := F ones ![n+1,a3]
    let t := (1 : M)+q+q
    let w := F ones ![n,1+t+t]
    let w2 := F ones ![modelNumeral M 3,1+(w+w)+(w+w)]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((n+1)+1)+((modelNumeral M 3+1)+1))+ct,
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(q+q)+(q+q)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w2+w2)+(w2+w2)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let z := F ones ![n,a3]
  have ha : F ones ![n+1,a3] = z+z+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ha,(modelOdd z).1,(modelOdd z).2]
  have hr : (1 : M)+(1+1)+(q+q)+(q+q) = ((1+q+q)+(1+q+q))+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hr]
  exact fifteenTo24 n u q
/-- Extend any run ending in the stated state-15 scan-exit layout. -/
theorem extendScanExit (n u q time start : M)
    (hrun :
      let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
      let h := g+g+1
      let xx := h+h+1
      let ll := (xx+xx)+(xx+xx)+1
      let a0 := ll+ll+1
      let a1 := a0+a0+1
      let a2 := a1+a1+1
      let a3 := a2+a2
      let a := F ones ![n+1,a3]
      F PA194Stepper.stepper ![time,start] =
        F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
          F parityCode (fun _ => a)+(1+1)+(q+q)+(q+q)]]) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    ∃ finalClock right : M, F PA194Stepper.stepper ![finalClock,start] =
      F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  dsimp only at hrun ⊢
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let t := (1 : M)+q+q
  let w := F ones ![n,1+t+t]
  let w2 := F ones ![modelNumeral M 3,1+(w+w)+(w+w)]
  refine ⟨time+((((n+1)+1)+((modelNumeral M 3+1)+1))+ct),1+(w2+w2)+(w2+w2),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun]
  exact scanExitTo24 n u q
#print axioms extendScanExit
#print axioms scanExitTo24
#print axioms fifteenTo24
end models
end PA194FirstFiveFifteenTo24
