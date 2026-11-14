import PA194FirstFourPositiveTo15
import PA194FirstThreeBlankTailTo16
import PA194ZerosDouble
import PA194FourteenComposition
import PA194ZerosEven
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveExact
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem selectedZeroExact (a m p : M) :
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let ret := F block ![m,p]
    let scanned := F ones ![(0 : M),l]
    let ll := (((a+a)+(a+a))+1)+(((a+a)+(a+a))+1)
    F PA194Stepper.stepper ![modelNumeral M 3+(((1 : M)+1)+m),F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![F zeros ![m,(ll+ll)+(ll+ll)],p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelOnesZero,(modelDouble ((a+a)+(a+a))).1,(modelDouble ((a+a)+(a+a))).2]
  simp only [zero_add]
  exact sevenThroughFirst m (a+a) p

theorem selectedSuccExact (k a ret : M) :
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let scanned := F ones ![k+1,l]
    let ll := ((a+a)+1)+((a+a)+1)
    F PA194Stepper.stepper ![((k+1)+1)+(modelNumeral M 3+(((1 : M)+1)+k)),F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![F zeros ![k,(ll+ll)+(ll+ll)],ret]] := by
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
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,ht,hret]
  have hh := sevenThroughFirst k a ret
  rw [hb] at hh
  exact hh
theorem thirteenToSixteen (k a p : M) :
    let x := (a+a+1)+(a+a+1)
    let y := F zeros ![k,x]
    let z := F zeros ![k,1+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![(1 : M)+(((1 : M)+k)+modelNumeral M 3),
      F pairCode ![modelNumeral M 13,F pairCode ![F zeros ![k,(x+x)+(x+x)],p+p]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := (a+a+1)+(a+a+1)
  let y := F zeros ![k,x]
  have hz : F zeros ![k,(x+x)+(x+x)] = (y+y)+(y+y) := by
    dsimp only [y]
    rw [PA194ZerosDouble.modelZerosDouble,PA194ZerosDouble.modelZerosDouble]
  have hs : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 13,
      F pairCode ![F zeros ![k,(x+x)+(x+x)],p+p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![y+y,(p+p)+(p+p)]] := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,PA194ThirteenExitComposition.modelPackedThirteenExit,
      hz,(modelDouble (y+y)).1,(modelDouble (y+y)).2]
    simp only [zero_add]
  change F PA194Stepper.stepper ![F addCode ![(1 : M),_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hs]
  exact PA194FirstThreeBlankTailTo16.header14To16 k a p
theorem thirteenReach16 (k a p : M) :
    let x := (a+a+1)+(a+a+1)
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M 13,F pairCode ![F zeros ![k,(x+x)+(x+x)],p+p]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![left,right]] := by
  let z := F zeros ![k,1+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  exact ⟨(1 : M)+(((1 : M)+k)+modelNumeral M 3),F halfCode (fun _ => a),
    F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r),thirteenToSixteen k a p⟩

theorem selectedTo16 (k a m q : M) :
    let ret := F block ![m,q+q]
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let scanned := F ones ![k,l]
    ∃ time left right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![left,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have he := PRAExhaustion.modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at he
  rcases he with hk | hk
  · subst k
    obtain ⟨t,left,right,h⟩ := thirteenReach16 m (a+a) q
    refine ⟨(modelNumeral M 3+(((1 : M)+1)+m))+t,left,right,?_⟩
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,selectedZeroExact]
    exact h
  · let j := F predCode (fun _ => k)
    have hk' : k=j+1 := by
      have hs : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans hs
    rw [hk']
    let b := F ones ![m+1,q+q]
    have hb : F block ![m,q+q] = b+b := modelBlock m (q+q)
    obtain ⟨t,left,right,h⟩ := thirteenReach16 j a b
    refine ⟨(((j+1)+1)+(modelNumeral M 3+(((1 : M)+1)+j)))+t,left,right,?_⟩
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,selectedSuccExact,hb]
    exact h
theorem markerFirstFourPositiveBlankTo16 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    F pairCode ![modelNumeral M 16,F pairCode ![left,right]] := by
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
  obtain ⟨more,left,right,hselected⟩ := selectedTo16 k a3 m q
  rw [←hblock] at hselected
  refine ⟨time+more,left,right,?_⟩
  change F PA194Stepper.stepper ![F addCode ![time,more],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hreturn]
  exact hselected
#print axioms markerFirstFourPositiveBlankTo16
#print axioms selectedTo16
#print axioms thirteenReach16
#print axioms thirteenToSixteen
#print axioms selectedZeroExact
#print axioms selectedSuccExact
end models
end PA194FirstFourPositiveExact
