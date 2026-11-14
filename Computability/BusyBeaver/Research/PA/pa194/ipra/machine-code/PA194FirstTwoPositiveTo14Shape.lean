import PA194FirstTwoPositiveTo14
import PA194HalfFileSixShape
import PA194GenericRightScan
import PA194State106Scan
import PA194GenericRightScan
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
namespace PA194FirstTwoPositiveTo14Shape
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileSixShape PA194HalfFileSix PA194HalfFileScan PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstTwoPositiveBlankTo14Shape (e : Fin 2 → M) (rest : Fin 9 → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode 8) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 2)
    (hblank : rest (Fin.last 8) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    ∃ time a right : M, F (fileCode 1) (fun i => rest ⟨i.val+7,by omega⟩) = right+right ∧ F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),right]] := by
  dsimp only
  let tail : Fin 8 → M := fun i => rest i.succ
  have hb : tail (Fin.last 7) = (0 : M) := by simpa only [tail,Fin.succ_last] using hblank
  obtain ⟨time,l,p,hfile,hm⟩ := markerFirstTwoPositiveBlankTo71WithFile 7 e rest u k ht hfirst hblank
  obtain ⟨more,a,right,hremain,hscan⟩ := scanSixShape tail l p hb hfile
  have he : (fun i : Fin 2 => tail ⟨i.val+6,by omega⟩) =
      (fun i : Fin 2 => rest ⟨i.val+7,by omega⟩) := by
    funext i
    congr 1
  rw [he] at hremain
  refine ⟨time+more,a,right,hremain,?_⟩
  change F PA194Stepper.stepper ![F addCode ![time,more],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hscan
#print axioms markerFirstTwoPositiveBlankTo14Shape
end models
end PA194FirstTwoPositiveTo14Shape
