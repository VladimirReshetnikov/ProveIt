import PA194FirstTwoHeaderTo24
import PA194FirstFourPositiveExact
import PA194SevenReturnController
import PA194OnesCommute
import PA194SixteenScanExit
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
namespace PA194FirstTwoZeroFinish
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveExact PA194SevenReturnController PA194OnesCommute PA194FirstTwoHeaderTo24 PA194SixteenScanExit PA194OddEntryReturn PA194LeftRows PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem sixteenZeroHeaderTo24 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 16,
      F pairCode ![a1,(1+1)+(r+r)+(r+r)]]] = F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let s := (1 : M)+r+r
  let r2 := s+s
  have he : (1+1)+(r+r)+(r+r) = s+s := by simp only [s,add_assoc,add_comm,add_left_comm]
  have ho : (1 : M)+(s+s)+(s+s) = r2+r2+1 := by simp only [r2,add_assoc,add_comm,add_left_comm]
  have hstart : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,
      F pairCode ![a1,(1+1)+(r+r)+(r+r)]]] = F pairCode ![modelNumeral M 17,F pairCode ![a0,r2+r2+1]] := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,PA194StateOne.modelNumeralOne,he,modelPackedExit16,
      (modelOdd a0).1,(modelOdd a0).2,ho]
  let endw := F ones ![modelNumeral M 2,(1 : M)+r2+r2]
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  refine ⟨(1 : M)+(((1 : M)+(modelNumeral M 2+1))+ct),1+(endw+endw)+(endw+endw),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact oddHeaderTo24 17 (by decide) (by decide +kernel) u r2
theorem state7ZeroTo24 (u n p : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let d := (a1+a1)+(a1+a1)
    let l := (d+d)+(d+d)
    let ret := p+p
    let scanned := F ones ![n,l]
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![scanned,ret+ret+1]]] = F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let d := (a1+a1)+(a1+a1)
  let ret := p+p
  let w := F ones ![n,(1 : M)+ret+ret]
  let z := F zeros ![n,1+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  have hcell := PA194ReturnCell.modelReturnCell n (d+d) ret
  dsimp only at hcell
  rw [(modelDouble d).1,(modelDouble d).2,zero_add] at hcell
  have hs : F ones ![n+1,ret] = F ones ![n,ret]+F ones ![n,ret]+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],ret] = _
    rw [modelAddOne,modelOnesSucc]
  have ht : (1 : M)+ret+ret = ret+ret+1 := by simp only [add_assoc,add_comm,add_left_comm]
  have hb : F block ![n,ret] = w+w := by
    rw [modelBlock,hs]
    simp only [w,ht,modelOnesCommute]
  have h13 := sevenThroughFirst n (a1+a1) ret
  dsimp only at h13
  rw [hb] at h13
  have h16 := thirteenToSixteen n (a1+a1) p
  dsimp only at h16
  rw [(modelDouble a1).1,(modelDouble a1).2,zero_add] at h16
  obtain ⟨time,right,hfinish⟩ := sixteenZeroHeaderTo24 u r
  let t1 := (n+1)+1
  let t2 := modelNumeral M 3+(((1 : M)+1)+n)
  let t3 := (1 : M)+(((1 : M)+n)+modelNumeral M 3)
  refine ⟨((t1+t2)+t3)+time,right,?_⟩
  change F PA194Stepper.stepper ![F addCode ![(t1+t2)+t3,time],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![time,F PA194Stepper.stepper ![F addCode ![t1+t2,t3],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![time,F PA194Stepper.stepper ![t3,F PA194Stepper.stepper ![F addCode ![t1,t2],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,hcell,h13,h16]
  exact hfinish
#print axioms state7ZeroTo24
#print axioms sixteenZeroHeaderTo24
end models
end PA194FirstTwoZeroFinish
