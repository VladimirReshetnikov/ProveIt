import PA194FirstFourFifteenTo17
import PA194SeventeenToRootControl
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourFifteenTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkerReturnCell PA194BinaryDouble PA194ZeroRuns
open PA194FirstFourFifteenTo17 PA194SeventeenToRootControl
open PRAModelIOpenPairing TableDispatch PA194MarkerScan
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fifteenTo24 (u q : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let a4 := a3+a3
    let a := F ones ![modelNumeral M 2,a4]
    let t := (1 : M)+q+q
    let w := F ones ![(1 : M),1+t+t]
    let w2 := F ones ![modelNumeral M 4,1+(w+w)+(w+w)]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((((1 : M)+1)+1)+((modelNumeral M 4+1)+1))+ct,
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
  let a3 := a2+a2+1
  let t := (1 : M)+q+q
  let w := F ones ![(1 : M),1+t+t]
  let w2 := F ones ![modelNumeral M 4,1+(w+w)+(w+w)]
  have h1 := PA194FirstFourFifteenTo17.fifteenTo17 a3 q
  dsimp only at h1
  rw [(modelOdd a2).1,(modelOdd a2).2] at h1
  have ha : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h2 := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) (modelNumeral M 4) xx (w+w)
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
/-- Continue the genuine first-four zero-selected marker path to dense 24. -/
theorem markerFirstFourZeroTo24 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let q := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
    let t := (1 : M)+q+q
    let w := F ones ![(1 : M),1+t+t]
    let w2 := F ones ![modelNumeral M 4,1+(w+w)+(w+w)]
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w2+w2)+(w2+w2)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let q := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
  obtain ⟨time,hrun⟩ := PA194FirstFourZeroTo15.markerFirstFourZeroTo15 n e rest u ht hfirst
  have hnext := fifteenTo24 u q
  dsimp only at hnext
  refine ⟨time+((((1 : M)+1)+1)+((modelNumeral M 4+1)+1))+
    ((((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)),?_⟩
  rw [add_assoc]
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun]
  exact hnext
#print axioms markerFirstFourZeroTo24
#print axioms fifteenTo24
end models
end PA194FirstFourFifteenTo24
