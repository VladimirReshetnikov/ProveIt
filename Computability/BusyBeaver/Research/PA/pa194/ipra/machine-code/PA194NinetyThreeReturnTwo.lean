import PA194HalfFileTwo
import PA194SixteenTwoRuns
import PA194SixteenSixRuns
import PA194FirstTwoPositiveTo14Exact
import PA194SixteenReturnRun
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
namespace PA194NinetyThreeReturnTwo
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileTwo PA194SixteenTwoRuns PA194SixteenSixRuns PA194FirstTwoPositiveTo14Exact PA194SixteenReturnRun PA194FourteenOddTo16 PA194FirstTwoPositiveTo14Shape PA194HalfFileSixShape PA194HalfFileSix PA194HalfFileScan PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem ninetyThreeReturnTwo (e : Fin 9 → M) (l p : M)
    (hblank : e (Fin.last 8) = (0 : M)) (hp : F (fileCode 8) e = p+p) :
    ∃ time w : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 93,F pairCode ![l+l,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let x := F ones ![e ⟨0,by decide⟩+1,l+l]
  let a := F ones ![e ⟨1,by decide⟩,x+x]
  let last : Fin 7 → M := fun i => e ⟨i.val+2,by omega⟩
  let suffix := F (fileCode 5) (fun i => last i.succ)
  let b := F ones ![last 0,suffix]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e ⟨1,by decide⟩,(1 : M)+c+c]
  let w2 := F ones ![e ⟨0,by decide⟩,(1 : M)+(w1+w1)+(w1+w1)]
  let back := (e ⟨1,by decide⟩+1)+((e ⟨0,by decide⟩+1)+1)
  obtain ⟨t,right,hfile,hscan⟩ := scanTwo e (l+l) p hblank hp
  have hsucc : F ones ![last 0+1,suffix] = b+b+1 := by
    change F ones ![F addCode ![last 0,F oneCode Fin.elim0],suffix] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode 6) last = (b+b+1)+(b+b+1) := by
    rw [modelFileSucc,modelBlock,hsucc]
  change F (fileCode 6) last = right+right at hfile
  have hh := congrArg (fun z : M => F halfCode (fun _ => z)) (hf.symm.trans hfile)
  rw [(modelDouble (b+b+1)).2,(modelDouble right).2] at hh
  have hright : right=b+b+1 := hh.symm
  rw [hright] at hscan
  have h16 := fourteenOddTo16 a b
  have h17 := modelSixteenTwoRuns (e ⟨1,by decide⟩) (e ⟨0,by decide⟩) l c
  dsimp only at hscan h16 h17
  refine ⟨(t+modelNumeral M 3)+back,w2,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t+modelNumeral M 3,back],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![back,F PA194Stepper.stepper ![F addCode ![t,modelNumeral M 3],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan,h16]
  exact h17
#print axioms ninetyThreeReturnTwo
end models
end PA194NinetyThreeReturnTwo
