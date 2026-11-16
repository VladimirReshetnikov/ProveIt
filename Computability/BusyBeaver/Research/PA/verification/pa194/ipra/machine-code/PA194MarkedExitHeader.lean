import PA194ControllerReturn
import PA194EighteenOdd
import PA194SixteenScanExit
import PA194UnaryRuns
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkedExitHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194ControllerReturn PA194EighteenOdd
open PA194SixteenScanExit PackedIterationModel ConfigurationStep PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem packed18Odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(1+1)+(r+r)+(r+r)]] := by
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 18,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 18,l,r+r+1],F nextL ![modelNumeral M 18,l,r+r+1],
    F nextR ![modelNumeral M 18,l,r+r+1]) = stepSem (modelNumeral M 18) l (r+r+1) at hm
  rw [←hm,modelEighteenOdd]

theorem markedToHeader (u k f : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let l := F ones ![k,(a3+a3)+(a3+a3)]
    let a := F ones ![k+1,(1 : M)+f+f]
    let w := F ones ![modelNumeral M 3+1,(1 : M)+((a+a)+(a+a))+((a+a)+(a+a))]
    let c := ((((k+1)+1)+1)+1)+1+((modelNumeral M 3+1)+1)
    F PA194Stepper.stepper ![c,F pairCode ![modelNumeral M 17,F pairCode ![l+l+1,(1 : M)+f+f]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,(1 : M)+(w+w)+(w+w)]] := by
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
  let l := F ones ![k,(a3+a3)+(a3+a3)]
  let a := F ones ![k+1,(1 : M)+f+f]
  let t := (a+a)+(a+a)
  have hl : F ones ![k+1,(a3+a3)+(a3+a3)] = l+l+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hh : F ones ![modelNumeral M 3,xx+xx] = a1 := by
    rw [show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have hc := modelReturnToControl18 ⟨1,by decide⟩ (k+1) a3 f
  dsimp only at hc
  rw [show PA194MarkerReturnCell.returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl,
    hl,(modelOdd a2).1,(modelOdd a2).2] at hc
  have hr : (1 : M)+f+f = f+f+1 := by simp only [add_assoc,add_comm]
  rw [←hr] at hc
  have h18 := packed18Odd a2 t
  rw [(modelOdd a1).1,(modelOdd a1).2] at h18
  have hright : (1 : M)+(1+1)+(t+t)+(t+t) = (1+(t+t))+(1+(t+t))+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at h18
  have hscan := modelScanExit (modelNumeral M 3) xx (1+(t+t))
  rw [(modelOdd h).1,(modelOdd h).2,hh] at hscan
  have hr2 : (1 : M)+((a+a)+(a+a))+((a+a)+(a+a)) = t+t+1 := by
    dsimp [t]
    simp only [add_assoc,add_comm,add_left_comm]
  change F PA194Stepper.stepper ![F addCode ![((((k+1)+1)+1)+1)+1,(modelNumeral M 3+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  let c := (((k+1)+1)+1)+1
  have hmid : F PA194Stepper.stepper ![c+1,F pairCode ![modelNumeral M 17,F pairCode ![l+l+1,(1 : M)+f+f]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a1,(1+(t+t))+(1+(t+t))+1]] := by
    change F PA194Stepper.stepper ![F addCode ![c,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc,hc]
    rw [hr2,h18]
  rw [hmid,hscan]
  dsimp only [t,a,h,g]
  simp only [add_assoc]
#print axioms markedToHeader
end models
end PA194MarkedExitHeader
