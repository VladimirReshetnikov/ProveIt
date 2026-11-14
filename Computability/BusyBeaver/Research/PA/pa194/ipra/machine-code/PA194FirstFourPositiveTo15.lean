import PA194FirstFourPositiveTo14
import PA194FourteenComposition
import PA194ZerosEven
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveTo15
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem selectedZeroEven (a m p : M) :
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let ret := F block ![m,p]
    let scanned := F ones ![(0 : M),l]
    ∃ time left : M, F parityCode (fun _ => left) = (0 : M) ∧ F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![left,p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelOnesZero,(modelDouble ((a+a)+(a+a))).1,(modelDouble ((a+a)+(a+a))).2]
  simp only [zero_add]
  let ll := (((a+a)+(a+a))+1)+(((a+a)+(a+a))+1)
  refine ⟨modelNumeral M 3+(((1 : M)+1)+m),F zeros ![m,(ll+ll)+(ll+ll)],modelZerosEven m (ll+ll),?_⟩
  exact sevenThroughFirst m (a+a) p

theorem selectedSuccEven (k a ret : M) :
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let scanned := F ones ![k+1,l]
    ∃ time left : M, F parityCode (fun _ => left) = (0 : M) ∧ F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![left,ret]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let l := ((a+a)+(a+a))+((a+a)+(a+a))
  let x := F ones ![k,l]
  let w := F ones ![k,(1 : M)+ret+ret]
  have hone : F ones ![k+1,l] = x+x+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],l] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hone,(modelOdd x).1,(modelOdd x).2]
  have hret := PA194ReturnCell.modelReturnCell k ((a+a)+(a+a)) ret
  dsimp only at hret
  rw [(modelDouble (a+a)).1,(modelDouble (a+a)).2] at hret
  simp only [zero_add] at hret
  have ht : (1 : M)+ret+ret = ret+ret+1 := by simp only [add_assoc,add_comm,add_left_comm]
  have hb : F block ![k,ret] = w+w := by
    have hs : F ones ![k+1,ret] = F ones ![k,ret]+F ones ![k,ret]+1 := by
      change F ones ![F addCode ![k,F oneCode Fin.elim0],ret] = _
      rw [modelAddOne,modelOnesSucc]
    rw [modelBlock,hs]
    simp only [w,ht,modelOnesCommute]
  let ll := ((a+a)+1)+((a+a)+1)
  refine ⟨((k+1)+1)+(modelNumeral M 3+(((1 : M)+1)+k)),F zeros ![k,(ll+ll)+(ll+ll)],modelZerosEven k (ll+ll),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,ht,hret]
  have hh := sevenThroughFirst k a ret
  rw [hb] at hh
  exact hh
theorem selectedBothEven (k a m q : M) :
    let ret := F block ![m,q+q]
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let scanned := F ones ![k,l]
    ∃ time left right : M, F parityCode (fun _ => left) = (0 : M) ∧ F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![left,right+right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have he := PRAExhaustion.modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at he
  rcases he with hk | hk
  · subst k
    obtain ⟨time,left,heven,h⟩ := selectedZeroEven a m (q+q)
    exact ⟨time,left,q,heven,h⟩
  · let j := F predCode (fun _ => k)
    have hk' : k=j+1 := by
      have hs : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans hs
    rw [hk']
    obtain ⟨time,left,heven,h⟩ := selectedSuccEven j a (F block ![m,q+q])
    refine ⟨time,left,F ones ![m+1,q+q],heven,?_⟩
    simpa only [modelBlock] using h

theorem markerFirstFourPositiveBlankTo15 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![left,right]] := by
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
  obtain ⟨more,left,right,heven,hselected⟩ := selectedBothEven k a3 m q
  rw [←hblock] at hselected
  let outRight := right+right
  refine ⟨((time+more)+1)+1,F halfCode (fun _ => F halfCode (fun _ => left)),
    F parityCode (fun _ => F halfCode (fun _ => left))+(1+1)+(outRight+outRight)+(outRight+outRight),?_⟩
  change F PA194Stepper.stepper ![F addCode ![(time+more)+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![time+more,F oneCode Fin.elim0],_]) = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![time,more],_])) = _
  rw [PA194StepperCompose.modelStepperCompose,hreturn,hselected,
    PA194ThirteenExitComposition.modelPackedThirteenExit,heven,zero_add]
  exact PA194FourteenComposition.modelPackedFourteen _ outRight
#print axioms markerFirstFourPositiveBlankTo15
#print axioms selectedBothEven
end models
end PA194FirstFourPositiveTo15
