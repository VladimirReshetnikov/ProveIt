import PA194HalfFileSixFull
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
namespace PA194SeventyOneReturnSix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileSixFull PA194SixteenSixRuns PA194FirstTwoPositiveTo14Exact PA194SixteenReturnRun PA194FourteenOddTo16 PA194FirstTwoPositiveTo14Shape PA194HalfFileSixShape PA194HalfFileSix PA194HalfFileScan PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem seventyOneReturnSix (e : Fin 8 → M) (l p : M)
    (hblank : e (Fin.last 7) = (0 : M)) (hp : F (fileCode 7) e = p+p) :
    ∃ time w : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 71,F pairCode ![l+l,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let x1 := F ones ![e ⟨0,by decide⟩+1,l+l]
  let x2 := F ones ![e ⟨1,by decide⟩+1,x1+x1]
  let x3 := F ones ![e ⟨2,by decide⟩+1,x2+x2]
  let x4 := F ones ![e ⟨3,by decide⟩+1,x3+x3]
  let x5 := F ones ![e ⟨4,by decide⟩+1,x4+x4]
  let a := F ones ![e ⟨5,by decide⟩,x5+x5]
  let last : Fin 2 → M := fun i => e ⟨i.val+6,by omega⟩
  let b := F ones ![last 0,last 1]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e ⟨5,by decide⟩,(1 : M)+c+c]
  let w2 := F ones ![e ⟨4,by decide⟩,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e ⟨3,by decide⟩,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e ⟨2,by decide⟩,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e ⟨1,by decide⟩,(1 : M)+(w4+w4)+(w4+w4)]
  let w6 := F ones ![e ⟨0,by decide⟩,(1 : M)+(w5+w5)+(w5+w5)]
  let back := (((((e ⟨5,by decide⟩+1)+((e ⟨4,by decide⟩+1)+1))+((e ⟨3,by decide⟩+1)+1))+
    ((e ⟨2,by decide⟩+1)+1))+((e ⟨1,by decide⟩+1)+1))+((e ⟨0,by decide⟩+1)+1)
  obtain ⟨t,right,hfile,hscan⟩ := scanSixFull e (l+l) p hblank hp
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
  have hright : right=b+b+1 := hh.symm
  rw [hright] at hscan
  have h16 := fourteenOddTo16 a b
  have h17 := modelSixteenSixRuns (e ⟨0,by decide⟩) (e ⟨1,by decide⟩) (e ⟨2,by decide⟩)
    (e ⟨3,by decide⟩) (e ⟨4,by decide⟩) (e ⟨5,by decide⟩) l c
  dsimp only at hscan h16 h17
  refine ⟨(t+modelNumeral M 3)+back,w6,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t+modelNumeral M 3,back],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![back,F PA194Stepper.stepper ![F addCode ![t,modelNumeral M 3],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan,h16]
  exact h17
#print axioms seventyOneReturnSix
end models
end PA194SeventyOneReturnSix
