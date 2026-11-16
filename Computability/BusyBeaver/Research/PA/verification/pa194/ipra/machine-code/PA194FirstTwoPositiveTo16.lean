import PA194FirstTwoPositiveTo14Shape
import PA194FourteenOddTo16
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
namespace PA194FirstTwoPositiveTo16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FourteenOddTo16 PA194FirstTwoPositiveTo14Shape PA194HalfFileSixShape PA194HalfFileSix PA194HalfFileScan PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstTwoPositiveBlankTo16 (e : Fin 2 → M) (rest : Fin 9 → M)
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
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![left,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  obtain ⟨time,a,right,hfile,hm⟩ := markerFirstTwoPositiveBlankTo14Shape e rest u k ht hfirst hblank
  let last : Fin 2 → M := fun i => rest ⟨i.val+7,by omega⟩
  let b := F ones ![last 0,last 1]
  have hsucc : F ones ![last 0+1,last 1] = b+b+1 := by
    change F ones ![F addCode ![last 0,F oneCode Fin.elim0],last 1] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode 1) last = (b+b+1)+(b+b+1) := by
    rw [modelFileSucc,modelBlock,fileCode,modelProjection]
    change F ones ![last 0+1,last 1] + F ones ![last 0+1,last 1] = _
    rw [hsucc]
  change F (fileCode 1) last = right+right at hfile
  have hh := congrArg (fun z : M => F halfCode (fun _ => z)) (hf.symm.trans hfile)
  rw [(modelDouble (b+b+1)).2,(modelDouble right).2] at hh
  have hr : right=b+b+1 := hh.symm
  rw [hr] at hm
  let c := (b+b)+(b+b)
  refine ⟨time+modelNumeral M 3,F halfCode (fun _ => a),
    F parityCode (fun _ => a)+(1+1)+(c+c)+(c+c),?_⟩
  change F PA194Stepper.stepper ![F addCode ![time,modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact fourteenOddTo16 a b
#print axioms markerFirstTwoPositiveBlankTo16
end models
end PA194FirstTwoPositiveTo16
