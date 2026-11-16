import PA194HalfFileScan
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
namespace PA194HalfFileTwo
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileScan PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem scanTwo (e : Fin 9 → M) (l p : M)
    (hblank : e (Fin.last 8) = (0 : M)) (hp : F (fileCode 8) e = p+p) :
    let x := F ones ![e ⟨0,by decide⟩+1,l]
    let a := F ones ![e ⟨1,by decide⟩,x+x]
    ∃ time right : M, F (fileCode 6) (fun i => e ⟨i.val+2,by omega⟩) = right+right ∧
      F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 93,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have loop93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 93 1 93 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x,y]] := by
    have hh := rightZero 93 0 113 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have hh := rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  let e1 : Fin 8 → M := fun i => e i.succ
  let e2 : Fin 7 → M := fun i => e1 i.succ
  have hb : e1 (Fin.last 7) = (0 : M) := by simpa only [e1,Fin.succ_last] using hblank
  obtain ⟨r1,hr1,h1⟩ := scanHalfBlock 7 93 113 e l p hblank hp loop93 exit93
  let x := F ones ![e 0+1,l]
  let l1 := x+x
  obtain ⟨r2,hr2,h2⟩ := scanHalfBlock 6 113 14 e1 l1 r1 hb hr1 loop113 exit113
  let a := F ones ![e1 0,l1]
  have ha : F ones ![e1 0+1,l1] = a+a+1 := by
    change F ones ![F addCode ![e1 0,F oneCode Fin.elim0],l1] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ha] at h2
  have he : e2 = (fun i : Fin 7 => e ⟨i.val+2,by omega⟩) := by
    funext i
    congr 1
  change F (fileCode 6) e2 = r2+r2 at hr2
  rw [he] at hr2
  refine ⟨((e 0+1)+1)+((e1 0+1)+1),r2,hr2,?_⟩
  change F PA194Stepper.stepper ![F addCode ![(e 0+1)+1,(e1 0+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  dsimp only [a,l1,x,e1]
  congr 1
#print axioms scanTwo
end models
end PA194HalfFileTwo
