import PA194FirstZeroZeroTo7
import PA194CarryThreeLeftCode
import PA194ReturnFile
import PA194CarryThreeExactFile
import PA194ThreeBlankTail
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
namespace PA194FirstZeroZeroReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstZeroZeroTo7 PA194FirstZeroZeroTo3 PA194FirstZeroZeroTo1 PA194FirstTwoPositiveTo71 PA194FirstThreePositiveScan PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstZeroZeroBlankReturn (e : Fin 2 → M) (rest : Fin 9 → M) (u : M)
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
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let tail : Fin 8 → M := fun i => rest i.succ
    let ret := F (returnCode 7) (Fin.cases six tail)
    ∃ time : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),
      F pairCode ![x+x+1,F (fileCode 1) e]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![left,ret+ret+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let d := (ll+ll)+(ll+ll)
  let l := (d+d)+(d+d)
  let y := F ones ![rest 0,l]
  let tail : Fin 8 → M := fun i => rest i.succ
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  obtain ⟨time,hm⟩ := markerFirstZeroZeroBlankTo7 e rest u ht hfirst hblank
  rw [PA194CarryThreeLeftCode.carried_eq_leftCode] at hm
  have hid : Fin.cases (rest ⟨1,by decide⟩) (fun i => rest i.succ.succ) = tail := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hid] at hm
  refine ⟨time+F (costCode 7) tail,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact PA194ReturnFile.modelReturnFile 7 tail y six
#print axioms markerFirstZeroZeroBlankReturn
end models
end PA194FirstZeroZeroReturn
