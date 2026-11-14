import PA194OddEntryReturn
import PA194LeftRows
import PA194FirstFourPositiveExact
import PA194SixteenScanExit
import PA194MarkerReturnCell
import PA194SeventeenToRootControl
import PA194FirstThreeBlankTailTo16
import PA194ZerosDouble
import PA194FourteenComposition
import PA194ZerosEven
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstZeroHeaderTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194OddEntryReturn PA194LeftRows PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem oddHeaderTo24 (q : Nat) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+1) (0,0,194) = (1,0,16)) (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let w := F ones ![modelNumeral M 0,(1 : M)+r+r]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((1 : M)+(modelNumeral M 0+1))+ct,
      F pairCode ![modelNumeral M q,F pairCode ![xx+xx,r+r+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let w := F ones ![modelNumeral M 0,(1 : M)+r+r]
  have ha : F ones ![modelNumeral M 0,xx+xx] = xx+xx := by
    change F ones ![(0 : M),xx+xx] = _
    rw [modelOnesZero]
  have h1 := modelOddEntryReturn q hq hrow (modelNumeral M 0) xx r
  dsimp only at h1
  rw [ha,(modelOdd h).1,(modelOdd h).2] at h1
  have h2 := returnToControl24 u w
  dsimp only at h2
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1]
  exact h2
theorem evenHeaderTo24 (u w : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 17,
      F pairCode ![ll+ll,(w+w)+(w+w)]]] = F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let r1 := w+w
  let r2 := r1+r1
  let r3 := r2+r2
  have hstart : F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 17,
      F pairCode ![ll+ll,r1+r1]]] = F pairCode ![modelNumeral M 19,F pairCode ![xx+xx,r3+r3+1]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    have h1 := leftZero 17 18 (by decide) (by decide +kernel) (ll+ll) r1
    have h2 := leftZero 18 19 (by decide) (by decide +kernel) ll r2
    rw [h1,(modelDouble ll).1,(modelDouble ll).2,zero_add,h2,(modelOdd (xx+xx)).1,(modelOdd (xx+xx)).2]
    simp only [r3,add_assoc,add_comm,add_left_comm]
  let endw := F ones ![modelNumeral M 0,(1 : M)+r3+r3]
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  refine ⟨modelNumeral M 2+(((1 : M)+(modelNumeral M 0+1))+ct),1+(endw+endw)+(endw+endw),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact oddHeaderTo24 19 (by decide) (by decide +kernel) u r3
theorem fourHeaderTo24 (u w : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 17,
      F pairCode ![(ll+ll)+(ll+ll),(w+w)+(w+w)]]] = F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let r1 := w+w
  let r2 := r1+r1
  let r3 := r2+r2
  let r4 := r3+r3
  have hstart : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 17,
      F pairCode ![(ll+ll)+(ll+ll),r1+r1]]] = F pairCode ![modelNumeral M 20,F pairCode ![xx+xx,r4+r4+1]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    have h1 := leftZero 17 18 (by decide) (by decide +kernel) ((ll+ll)+(ll+ll)) r1
    have h2 := leftZero 18 19 (by decide) (by decide +kernel) (ll+ll) r2
    have h3 := leftZero 19 20 (by decide) (by decide +kernel) ll r3
    rw [h1,(modelDouble (ll+ll)).1,(modelDouble (ll+ll)).2,zero_add,
      h2,(modelDouble ll).1,(modelDouble ll).2,zero_add,h3,(modelOdd (xx+xx)).1,(modelOdd (xx+xx)).2]
    simp only [r4,add_assoc,add_comm,add_left_comm]
  let endw := F ones ![modelNumeral M 0,(1 : M)+r4+r4]
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  refine ⟨modelNumeral M 3+(((1 : M)+(modelNumeral M 0+1))+ct),1+(endw+endw)+(endw+endw),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact oddHeaderTo24 20 (by decide) (by decide +kernel) u r4
theorem selectedReturnTo24 (u k v : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let d := (ll+ll)+(ll+ll)
    let scanned := F ones ![k,d+d]
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+(v+v)+(v+v)]]] =
      F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let d := (ll+ll)+(ll+ll)
  have he := PRAExhaustion.modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at he
  rcases he with hk | hk
  · subst k
    rw [modelOnesZero,(modelDouble d).1,(modelDouble d).2,zero_add]
    exact fourHeaderTo24 u v
  · let j := F predCode (fun _ => k)
    have hk' : k=j+1 := by
      have hs : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans hs
    rw [hk']
    let x := F ones ![j,d+d]
    have hs : F ones ![j+1,d+d] = x+x+1 := by
      change F ones ![F addCode ![j,F oneCode Fin.elim0],d+d] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hs,(modelOdd x).1,(modelOdd x).2]
    let w := F ones ![j,(1 : M)+(v+v)+(v+v)]
    have hcell := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) j d (v+v)
    dsimp only at hcell
    rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl,
      (modelDouble (ll+ll)).1,(modelDouble (ll+ll)).2,zero_add] at hcell
    have hv : (1 : M)+(v+v)+(v+v) = (v+v)+(v+v)+1 := by
      simp only [add_assoc,add_comm,add_left_comm]
    rw [←hv] at hcell
    obtain ⟨time,right,hnext⟩ := evenHeaderTo24 u w
    refine ⟨((j+1)+1)+time,right,?_⟩
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hcell]
    exact hnext
#print axioms selectedReturnTo24
#print axioms fourHeaderTo24
#print axioms evenHeaderTo24
#print axioms oddHeaderTo24
end models
end PA194FirstZeroHeaderTo24
