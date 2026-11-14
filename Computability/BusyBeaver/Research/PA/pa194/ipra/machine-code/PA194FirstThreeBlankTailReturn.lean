import PA194CarryThreeLeftCode
import PA194ReturnFile
import PA194FirstThreeBlankTailExactTo7
import PA194ThreeBlankTail
import PA194FirstThreePositiveTo1
import PA194FirstThreePositiveScan
import PA194FirstThreePositiveTo3
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreeBlankTailReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstThreePositiveTo1 PA194FirstThreePositiveScan PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
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

/-- The positive-selected first-three path returns across its finite file when the final file tail is blank. -/
theorem markerFirstThreeBlankTailReturn (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let l := ((a2+a2)+(a2+a2))+((a2+a2)+(a2+a2))
    let a := F ones ![k,l]
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let ret := F (returnCode (n+1)) (Fin.cases six rest)
    ∃ time : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 7,F pairCode ![a,ret+ret+1]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let l := ((a2+a2)+(a2+a2))+((a2+a2)+(a2+a2))
  let a := F ones ![k,l]
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let ret := F (returnCode (n+1)) (Fin.cases six rest)
  obtain ⟨t,hm⟩ := PA194FirstThreeBlankTailExactTo7.markerFirstThreeBlankTailExactTo7 n e rest u k ht hfirst hblank
  rw [PA194CarryThreeLeftCode.carried_eq_leftCode] at hm
  have hid : Fin.cases (rest 0) (fun i => rest i.succ) = rest := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  rw [hid] at hm
  refine ⟨t+F (costCode (n+1)) rest,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact PA194ReturnFile.modelReturnFile (n+1) rest a six
/-- The positive-selected first-three path returns across its finite file when the final file tail is blank. -/
theorem markerFirstThreeBlankTailHeader (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let ret := F (returnCode (n+1)) (Fin.cases six rest)
    let w := F ones ![k,(1 : M)+ret+ret]
    ∃ time : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 7,F pairCode ![a2+a2,(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let ret := F (returnCode (n+1)) (Fin.cases six rest)
  obtain ⟨t,hm⟩ := markerFirstThreeBlankTailReturn n e rest u k ht hfirst hblank
  have hc := PA194ReturnCell.modelReturnCell k ((a2+a2)+(a2+a2)) ret
  dsimp only at hc
  rw [(modelDouble (a2+a2)).1,(modelDouble (a2+a2)).2] at hc
  simp only [zero_add] at hc
  refine ⟨t+((k+1)+1),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hc
#print axioms markerFirstThreeBlankTailHeader
#print axioms markerFirstThreeBlankTailReturn
end models
end PA194FirstThreeBlankTailReturn
