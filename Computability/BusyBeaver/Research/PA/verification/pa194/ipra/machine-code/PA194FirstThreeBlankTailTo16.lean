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
namespace PA194FirstThreeBlankTailTo16
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

/-- Continue the physical header return through dense 14 and 15. -/
theorem header14To16 (k a p : M) :
    let x := (a+a+1)+(a+a+1)
    let y := F zeros ![k,x]
    let z := F zeros ![k,1+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
      F pairCode ![modelNumeral M 14,F pairCode ![y+y,(p+p)+(p+p)]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := (a+a+1)+(a+a+1)
  let y := F zeros ![k,x]
  let b := 1+(p+p)+(p+p)
  let z := F zeros ![k,b]
  let r := (z+z)+(z+z)
  have h3 : F PA194Stepper.stepper ![modelNumeral M 3,
      F pairCode ![modelNumeral M 15,F pairCode ![x,z+z]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
    dsimp only [x,r]
    rw [PA194ZeroRuns.modelPackedZeroTransition,
      PA194FifteenExitComposition.modelPackedBoundary15,
      PA194FifteenExitComposition.modelPackedExit15]
  have h1 : F PA194Stepper.stepper ![(1 : M),
      F pairCode ![modelNumeral M 14,F pairCode ![y+y,(p+p)+(p+p)]]] =
      F pairCode ![modelNumeral M 15,F pairCode ![y,b+b]] := by
    let c := F pairCode ![modelNumeral M 14,F pairCode ![y+y,(p+p)+(p+p)]]
    have hs (t : M) : F PA194Stepper.stepper ![t+1,c] = F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![t,c]) := by
      change F PA194Stepper.stepper ![F addCode ![t,F oneCode Fin.elim0],c] = _
      rw [modelAddOne,PA194Stepper.modelStepperSucc]
    have hz : F PA194Stepper.stepper ![(0 : M),c] = c := PA194Stepper.modelStepperZero c
    have ht := hs (0 : M)
    rw [hz] at ht
    dsimp only [c] at ht
    rw [PA194FourteenComposition.modelPackedFourteen,(modelDouble y).1,(modelDouble y).2] at ht
    simp only [zero_add] at ht
    have ht' : ((1 : M)+1)+((p+p)+(p+p))+((p+p)+(p+p)) = b+b := by
      dsimp only [b]
      simp only [add_assoc,add_comm,add_left_comm]
    rw [ht'] at ht
    simpa only [zero_add] using ht
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,PA194ZeroScanInvariant.modelFullScan]
  exact h3
/-- The positive-selected first-three path returns across its finite file when the final file tail is blank. -/
theorem markerFirstThreeBlankTailTo16 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    let tail := F (returnCode n) (Fin.cases six (fun i => rest i.succ))
    let p := F ones ![rest 0,tail+tail+1]
    let r0 := F zeros ![k,1+(p+p)+(p+p)]
    let r := (r0+r0)+(r0+r0)
    ∃ time : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a2),
      F parityCode (fun _ => a2)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let x := (a2+a2+1)+(a2+a2+1)
  let y := F zeros ![k,x]
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let tail := F (returnCode n) (Fin.cases six (fun i => rest i.succ))
  let p := F ones ![rest 0,tail+tail+1]
  obtain ⟨t,hm⟩ := PA194FirstThreeBlankTailTo14.markerFirstThreeBlankTailTo14 n e rest u k ht hfirst hblank
  have hz : F zeros ![k,(x+x)+(x+x)] = (y+y)+(y+y) := by
    dsimp only [y]
    rw [PA194ZerosDouble.modelZerosDouble,PA194ZerosDouble.modelZerosDouble]
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l64 := z4+z4
  let startx := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
  let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![startx+startx+1,F (fileCode 1) e]]
  change F PA194Stepper.stepper ![t,start] =
    F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => F zeros ![k,(x+x)+(x+x)]),
      F parityCode (fun _ => F zeros ![k,(x+x)+(x+x)])+(p+p)+(p+p)]] at hm
  rw [hz,(modelDouble (y+y)).1,(modelDouble (y+y)).2] at hm
  simp only [zero_add] at hm
  refine ⟨t+(((1 : M)+k)+modelNumeral M 3),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact header14To16 k a2 p
#print axioms markerFirstThreeBlankTailTo16
#print axioms header14To16
end models
end PA194FirstThreeBlankTailTo16
