import PA194FirstThreeBlankTailReturn
import PA194SevenReturnController
import PA194TwelveExitComposition
import PA194OnesCommute
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
namespace PA194FirstThreeBlankTailTo13
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

theorem headerTo13 (a ret k : M) :
    let w := F ones ![k,(1 : M)+ret+ret]
    let q := F ones ![k,ret]
    let x := (a+a+1)+(a+a+1)
    F PA194Stepper.stepper ![modelNumeral M 3+((1 : M)+1),
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,(w+w)+(w+w)]]] =
      F pairCode ![modelNumeral M 13,F pairCode ![((x+x)+(x+x)),q]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let q := F ones ![k,ret]
  let w := F ones ![k,(1 : M)+ret+ret]
  let x := (a+a+1)+(a+a+1)
  have hw : w = q+q+1 := by
    dsimp only [w,q]
    have ht : (1 : M)+ret+ret = ret+ret+1 := by simp only [add_assoc,add_comm]
    rw [ht,PA194OnesCommute.modelOnesCommute]
  have hz (y : M) : F zeros ![(1 : M),y] = y+y := by
    have h1 : F Code.succ (fun _ => (0 : M)) = (1 : M) := by
      rw [←PA194StateOne.modelNumeralOne]
      rfl
    rw [←h1,modelZerosSucc,modelZerosZero]
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194SevenReturnController.sevenToBlock]
  have hs := PA194TwelveExitComposition.modelScanExit (1 : M) x q
  rw [hz,hz] at hs
  change F PA194Stepper.stepper ![(1 : M)+1,F pairCode ![modelNumeral M 12,F pairCode ![x,w+w]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![(x+x)+(x+x),q]]
  rw [hw]
  exact hs
/-- The positive-selected first-three path returns across its finite file when the final file tail is blank. -/
theorem markerFirstThreeBlankTailTo13 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    let q := F ones ![k,ret]
    let x := (a2+a2+1)+(a2+a2+1)
    ∃ time : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 13,F pairCode ![(x+x)+(x+x),q]] := by
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
  obtain ⟨t,hm⟩ := PA194FirstThreeBlankTailReturn.markerFirstThreeBlankTailHeader n e rest u k ht hfirst hblank
  refine ⟨t+(modelNumeral M 3+((1 : M)+1)),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact headerTo13 a2 ret k
#print axioms markerFirstThreeBlankTailTo13
#print axioms headerTo13
end models
end PA194FirstThreeBlankTailTo13
