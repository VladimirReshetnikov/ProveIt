import PA194FirstZeroZeroTo1
import PA194FirstTwoPositiveTo71
import PA194FirstThreePositiveScan
import PA194RightRows
import PA194PositiveMarkerRoute
import PA194FirstFiveFirstCore
import PA194FirstFiveTo84
import PA194EightyFourScan
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstZeroZeroTo3
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstZeroZeroTo1 PA194FirstTwoPositiveTo71 PA194FirstThreePositiveScan PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstZeroZeroBlankTo3 (e : Fin 2 → M) (rest : Fin 9 → M) (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode 8) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = (0 : M))
    (hblank : rest (Fin.last 8) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let d := (ll+ll)+(ll+ll)
    let l := (d+d)+(d+d)
    let left := F ones ![rest 0,l]
    ∃ time p : M, F (fileCode 7) (fun i => rest i.succ) = p+p ∧
      F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),
        F pairCode ![x+x+1,F (fileCode 1) e]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![left+left+1,p]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let d := (ll+ll)+(ll+ll)
  let l := (d+d)+(d+d)
  let y := F ones ![rest 0,l]
  let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let t := ((((markClock+headerClock)+modelNumeral M 3)+((0 : M)+1))+modelNumeral M 3)+modelNumeral M 2
  obtain ⟨p,hp⟩ := evenRemainingFile 7 rest hblank
  have hm := markerFirstZeroZeroTo1 7 e rest u ht hfirst
  dsimp only at hm
  rw [hp] at hm
  refine ⟨t+(rest 0+1),p,hp,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact scanTo3 (rest 0) l p
#print axioms markerFirstZeroZeroBlankTo3
end models
end PA194FirstZeroZeroTo3
