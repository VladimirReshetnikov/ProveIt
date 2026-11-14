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
namespace PA194FirstFourPositiveTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem succSixteenTo24 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let R := (1 : M)+r+r
    let w := F ones ![modelNumeral M 4+1,R]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((modelNumeral M 4+1)+1)+ct,
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a3),
        F parityCode (fun _ => a3)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let R := (1 : M)+r+r
  let w := F ones ![modelNumeral M 4+1,R]
  have ha : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have hr : (1 : M)+(1+1)+(r+r)+(r+r) = R+R+1 := by
    dsimp [R]
    simp only [add_assoc,add_comm,add_left_comm]
  have hs := PA194SixteenScanExit.modelScanExit (modelNumeral M 4) xx R
  rw [ha,(modelOdd h).1,(modelOdd h).2] at hs
  have hroot := returnToControl24 u w
  dsimp only at hroot
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,(modelOdd a2).1,(modelOdd a2).2,hr,hs]
  exact hroot
theorem zeroSixteenTo24 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let R := (1 : M)+r+r
    let w := F ones ![modelNumeral M 4,1+(R+R)+(R+R)]
    let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((1 : M)+((modelNumeral M 4+1)+1))+ct,
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a3+a3),
        F parityCode (fun _ => a3+a3)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]] := by
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
  let R := (1 : M)+r+r
  let w := F ones ![modelNumeral M 4,1+(R+R)+(R+R)]
  have ha : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have hr : ((1 : M)+1)+(r+r)+(r+r) = R+R := by
    dsimp [R]
    simp only [add_assoc,add_comm,add_left_comm]
  have hs : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,
      F pairCode ![F halfCode (fun _ => a3+a3),F parityCode (fun _ => a3+a3)+(1+1)+(r+r)+(r+r)]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![a2,1+(R+R)+(R+R)]] := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,PA194StateOne.modelNumeralOne,(modelDouble a3).1,(modelDouble a3).2,zero_add,hr,
      PA194SixteenScanExit.modelPackedExit16,(modelOdd a2).1,(modelOdd a2).2]
  have hm := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) (modelNumeral M 4) xx (R+R)
  dsimp only at hm
  rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] at hm
  rw [ha,(modelOdd h).1,(modelOdd h).2] at hm
  have ht : (1 : M)+(R+R)+(R+R) = (R+R)+(R+R)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [←ht] at hm
  have hroot := returnToControl24 u w
  dsimp only at hroot
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hs,hm]
  exact hroot
theorem selectedTo24 (u k m q : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let l := ((a3+a3)+(a3+a3))+((a3+a3)+(a3+a3))
    let scanned := F ones ![k,l]
    let ret := F block ![m,q+q]
    ∃ time right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
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
  let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have he := PRAExhaustion.modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at he
  rcases he with hk | hk
  · subst k
    let z := F zeros ![m,1+(q+q)+(q+q)]
    let r := (z+z)+(z+z)
    let R := (1 : M)+r+r
    let w := F ones ![modelNumeral M 4,1+(R+R)+(R+R)]
    let t1 := modelNumeral M 3+(((1 : M)+1)+m)
    let t2 := (1 : M)+(((1 : M)+m)+modelNumeral M 3)
    let t3 := ((1 : M)+((modelNumeral M 4+1)+1))+ct
    refine ⟨(t1+t2)+t3,1+(w+w)+(w+w),?_⟩
    change F PA194Stepper.stepper ![F addCode ![t1+t2,t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    change F PA194Stepper.stepper ![t3,F PA194Stepper.stepper ![F addCode ![t1,t2],_]] = _
    rw [PA194StepperCompose.modelStepperCompose,selectedZeroExact,thirteenToSixteen]
    exact zeroSixteenTo24 u r
  · let j := F predCode (fun _ => k)
    have hk' : k=j+1 := by
      have hs : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans hs
    rw [hk']
    let b := F ones ![m+1,q+q]
    have hb : F block ![m,q+q] = b+b := modelBlock m (q+q)
    let z := F zeros ![j,1+(b+b)+(b+b)]
    let r := (z+z)+(z+z)
    let R := (1 : M)+r+r
    let w := F ones ![modelNumeral M 4+1,R]
    let t1 := ((j+1)+1)+(modelNumeral M 3+(((1 : M)+1)+j))
    let t2 := (1 : M)+(((1 : M)+j)+modelNumeral M 3)
    let t3 := ((modelNumeral M 4+1)+1)+ct
    refine ⟨(t1+t2)+t3,1+(w+w)+(w+w),?_⟩
    change F PA194Stepper.stepper ![F addCode ![t1+t2,t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    change F PA194Stepper.stepper ![t3,F PA194Stepper.stepper ![F addCode ![t1,t2],_]] = _
    rw [PA194StepperCompose.modelStepperCompose,selectedSuccExact,hb,thirteenToSixteen]
    exact succSixteenTo24 u r
theorem markerFirstFourPositiveBlankTo24 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    ∃ time right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
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
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let w := F ones ![(1 : M),six+six+1]
  let ret := F (PA194ReturnFile.returnCode (n+1)) (Fin.cases (w+w) rest)
  obtain ⟨time,hreturn⟩ := markerFirstFourPositiveBlankReturn n e rest u k ht hfirst hblank
  obtain ⟨m,q,hblock⟩ := returnBlockEven (M := M) n (Fin.cases (w+w) rest) w rfl
  obtain ⟨more,right,hselected⟩ := selectedTo24 u k m q
  rw [←hblock] at hselected
  refine ⟨time+more,right,?_⟩
  change F PA194Stepper.stepper ![F addCode ![time,more],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hreturn]
  exact hselected
#print axioms markerFirstFourPositiveBlankTo24
#print axioms selectedTo24
#print axioms zeroSixteenTo24
#print axioms succSixteenTo24
end models
end PA194FirstFourPositiveTo24
