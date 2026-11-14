import PA194FirstTwoZeroFinish
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
namespace PA194FirstOneZeroFinish
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstTwoZeroFinish PA194FirstFourPositiveExact PA194SevenReturnController PA194OnesCommute PA194FirstTwoHeaderTo24 PA194SixteenScanExit PA194OddEntryReturn PA194LeftRows PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem sixteenFirstOneZeroHeaderTo24 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 16,
      F pairCode ![a0,(1+1)+(r+r)+(r+r)]]] = F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let z := (1 : M)+r+r
  let w := F ones ![(1 : M),(1 : M)+(z+z)+(z+z)]
  have he : (1+1)+(r+r)+(r+r) = z+z := by simp only [z,add_assoc,add_comm,add_left_comm]
  have h1 : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,
      F pairCode ![a0,(1+1)+(r+r)+(r+r)]]] = F pairCode ![modelNumeral M 17,
      F pairCode ![ll,1+(z+z)+(z+z)]] := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,PA194StateOne.modelNumeralOne,he,modelPackedExit16,
      (modelOdd ll).1,(modelOdd ll).2]
  have hs : F ones ![(1 : M),xx+xx] = ll := by
    rw [←PA194StateOne.modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h2 := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) (1 : M) xx (z+z)
  dsimp only at h2
  rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl,hs,(modelOdd h).1,(modelOdd h).2] at h2
  have hz : (1 : M)+(z+z)+(z+z) = (z+z)+(z+z)+1 := by simp only [add_comm,add_left_comm]
  rw [←hz] at h2
  have h3 := returnToControl24 u w
  dsimp only at h3
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  refine ⟨((1 : M)+(((1 : M)+1)+1))+ct,1+(w+w)+(w+w),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  exact h3
theorem state7FirstOneZeroTo24 (u n p : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let d := (a0+a0)+(a0+a0)
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
  let d := (a0+a0)+(a0+a0)
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
  have h13 := sevenThroughFirst n (a0+a0) ret
  dsimp only at h13
  rw [hb] at h13
  have h16 := thirteenToSixteen n (a0+a0) p
  dsimp only at h16
  rw [(modelDouble a0).1,(modelDouble a0).2,zero_add] at h16
  obtain ⟨time,right,hfinish⟩ := sixteenFirstOneZeroHeaderTo24 u r
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
#print axioms state7FirstOneZeroTo24
#print axioms sixteenFirstOneZeroHeaderTo24
end models
end PA194FirstOneZeroFinish
