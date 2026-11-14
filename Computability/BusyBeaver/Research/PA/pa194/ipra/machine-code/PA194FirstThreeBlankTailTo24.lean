import PA194FirstThreeBlankTailTo16
import PA194SixteenHeaderReturn
import PA194SeventeenToRootControl
import PA194FirstThreeBlankTailTo14
import PA194ZerosDouble
import PA194FourteenComposition
import PA194FifteenExitComposition
import PA194FirstThreeBlankTailTo13
import PA194ThirteenExitComposition
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
namespace PA194FirstThreeBlankTailTo24
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
theorem markerFirstThreeBlankTailTo24 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let tail := F (returnCode n) (Fin.cases six (fun i => rest i.succ))
    let p := F ones ![rest 0,tail+tail+1]
    let r0 := F zeros ![k,1+(p+p)+(p+p)]
    let w := F ones ![modelNumeral M 3+1,1+((r0+r0)+(r0+r0))+((r0+r0)+(r0+r0))]
    ∃ time : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let tail := F (returnCode n) (Fin.cases six (fun i => rest i.succ))
  let p := F ones ![rest 0,tail+tail+1]
  let r0 := F zeros ![k,1+(p+p)+(p+p)]
  let w := F ones ![modelNumeral M 3+1,1+((r0+r0)+(r0+r0))+((r0+r0)+(r0+r0))]
  let ct16 := (modelNumeral M 3+1)+1
  let ct17 := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  obtain ⟨t,hm⟩ := PA194FirstThreeBlankTailTo16.markerFirstThreeBlankTailTo16 n e rest u k ht hfirst hblank
  refine ⟨(t+ct16)+ct17,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![ct17,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  have hs := PA194SixteenHeaderReturn.backToHeader h (r0+r0)
  dsimp only at hs
  rw [PA194StepperCompose.modelStepperCompose,hm,hs]
  exact PA194SeventeenToRootControl.returnToControl24 u w
#print axioms markerFirstThreeBlankTailTo24
end models
end PA194FirstThreeBlankTailTo24
