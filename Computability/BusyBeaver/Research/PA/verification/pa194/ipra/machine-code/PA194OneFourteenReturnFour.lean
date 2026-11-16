import PA194FirstZeroPositiveTo16
import PA194SixteenFourRuns
import PA194FirstZeroPositiveTo114
import PA194HalfFileFour
import PA194FourteenOddTo16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194OneFourteenReturnFour
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstZeroPositiveTo16 PA194SixteenFourRuns PA194FirstZeroPositiveTo114 PA194HalfFileFour PA194FourteenOddTo16
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

theorem oneFourteenReturnFour (e : Fin 9 → M) (l p : M)
    (hblank : e (Fin.last 8) = (0 : M)) (hp : F (fileCode 8) e = p+p) :
    ∃ time w : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 114,F pairCode ![l+l,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let last : Fin 5 → M := fun i => e ⟨i.val+4,by omega⟩
  let b := F ones ![last 0,F (fileCode 3) (fun i => last i.succ)]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e ⟨3,by decide⟩,(1 : M)+c+c]
  let w2 := F ones ![e ⟨2,by decide⟩,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e ⟨1,by decide⟩,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e ⟨0,by decide⟩,(1 : M)+(w3+w3)+(w3+w3)]
  let back := (((e ⟨3,by decide⟩+1)+((e ⟨2,by decide⟩+1)+1))+((e ⟨1,by decide⟩+1)+1))+((e ⟨0,by decide⟩+1)+1)
  obtain ⟨t,h16⟩ := scanFourTo16 e (l+l) p hblank hp
  have h17 := modelSixteenFourRuns (e ⟨0,by decide⟩) (e ⟨1,by decide⟩) (e ⟨2,by decide⟩) (e ⟨3,by decide⟩) l c
  dsimp only at h16 h17
  refine ⟨t+back,w4,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t,back],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h16]
  exact h17
#print axioms oneFourteenReturnFour
end models
end PA194OneFourteenReturnFour
