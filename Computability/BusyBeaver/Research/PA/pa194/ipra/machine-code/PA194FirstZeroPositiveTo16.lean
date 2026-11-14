import PA194FirstZeroPositiveTo114
import PA194HalfFileFour
import PA194FourteenOddTo16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstZeroPositiveTo16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstZeroPositiveTo114 PA194HalfFileFour PA194FourteenOddTo16
open PA194FirstZeroPositiveTo95 PA194FirstZeroFirstTo110 PA194FirstZeroFirstTo46 PA194RightRows PA194FirstZeroBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem scanFourTo16 (e : Fin 9 → M) (l p : M)
    (hblank : e (Fin.last 8) = (0 : M)) (hp : F (fileCode 8) e = p+p) :
    let x1 := F ones ![e ⟨0,by decide⟩+1,l]
    let x2 := F ones ![e ⟨1,by decide⟩+1,x1+x1]
    let x3 := F ones ![e ⟨2,by decide⟩+1,x2+x2]
    let a := F ones ![e ⟨3,by decide⟩,x3+x3]
    let last : Fin 5 → M := fun i => e ⟨i.val+4,by omega⟩
    let b := F ones ![last 0,F (fileCode 3) (fun i => last i.succ)]
    let c := (b+b)+(b+b)
    ∃ time : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 114,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(c+c)+(c+c)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x1 := F ones ![e ⟨0,by decide⟩+1,l]
  let x2 := F ones ![e ⟨1,by decide⟩+1,x1+x1]
  let x3 := F ones ![e ⟨2,by decide⟩+1,x2+x2]
  let a := F ones ![e ⟨3,by decide⟩,x3+x3]
  let last : Fin 5 → M := fun i => e ⟨i.val+4,by omega⟩
  let tail := F (fileCode 3) (fun i => last i.succ)
  let b := F ones ![last 0,tail]
  let c := (b+b)+(b+b)
  obtain ⟨t,right,hfile,hscan⟩ := scanFour e l p hblank hp
  have hsucc : F ones ![last 0+1,tail] = b+b+1 := by
    change F ones ![F addCode ![last 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode 4) last = (b+b+1)+(b+b+1) := by
    rw [modelFileSucc,modelBlock]
    change F ones ![last 0+1,tail] + F ones ![last 0+1,tail] = _
    rw [hsucc]
  change F (fileCode 4) last = right+right at hfile
  have hh := congrArg (fun z : M => F halfCode (fun _ => z)) (hf.symm.trans hfile)
  rw [(modelDouble (b+b+1)).2,(modelDouble right).2] at hh
  have hr : right=b+b+1 := hh.symm
  rw [hr] at hscan
  refine ⟨t+modelNumeral M 3,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t,modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan]
  exact fourteenOddTo16 a b
#print axioms scanFourTo16

end models
end PA194FirstZeroPositiveTo16
