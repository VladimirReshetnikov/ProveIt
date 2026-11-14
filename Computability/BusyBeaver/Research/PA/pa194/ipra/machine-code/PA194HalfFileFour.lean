import PA194HalfFileScan
import PA194GenericRightScan
import PA194State106Scan
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
namespace PA194HalfFileFour
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

theorem scanFour (e : Fin 9 → M) (l p : M)
    (hblank : e (Fin.last 8) = (0 : M)) (hp : F (fileCode 8) e = p+p) :
    let x1 := F ones ![e ⟨0,by decide⟩+1,l]
    let x2 := F ones ![e ⟨1,by decide⟩+1,x1+x1]
    let x3 := F ones ![e ⟨2,by decide⟩+1,x2+x2]
    let a := F ones ![e ⟨3,by decide⟩,x3+x3]
    ∃ time right : M, F (fileCode 4) (fun i => e ⟨i.val+4,by omega⟩) = right+right ∧
      F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 114,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have loop114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 114,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 114 1 114 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 68,F pairCode ![x+x,y]] := by
    have hh := rightZero 114 0 68 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 68,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 68 1 68 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![x+x,y]] := by
    have hh := rightZero 68 0 93 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
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
  let e0 := e
  let e1 : Fin 8 → M := fun j => e0 j.succ
  let e2 : Fin 7 → M := fun j => e1 j.succ
  let e3 : Fin 6 → M := fun j => e2 j.succ
  let e4 : Fin 5 → M := fun j => e3 j.succ
  have hb1 : e1 (Fin.last 7) = (0 : M) := by simpa only [e1,Fin.succ_last] using hblank
  have hb2 : e2 (Fin.last 6) = (0 : M) := by simpa only [e2,Fin.succ_last] using hb1
  have hb3 : e3 (Fin.last 5) = (0 : M) := by simpa only [e3,Fin.succ_last] using hb2
  obtain ⟨r1,hr1,h1⟩ := scanHalfBlock 7 114 68 e0 l p hblank hp loop114 exit114
  let x1 := F ones ![e0 0+1,l]
  let l1 := x1+x1
  let t1 := (e0 0+1)+1
  obtain ⟨r2,hr2,h2⟩ := scanHalfBlock 6 68 93 e1 l1 r1 hb1 hr1 loop68 exit68
  let x2 := F ones ![e1 0+1,l1]
  let l2 := x2+x2
  let t2 := (e1 0+1)+1
  obtain ⟨r3,hr3,h3⟩ := scanHalfBlock 5 93 113 e2 l2 r2 hb2 hr2 loop93 exit93
  let x3 := F ones ![e2 0+1,l2]
  let l3 := x3+x3
  let t3 := (e2 0+1)+1
  obtain ⟨r4,hr4,h4⟩ := scanHalfBlock 4 113 14 e3 l3 r3 hb3 hr3 loop113 exit113
  let x4 := F ones ![e3 0+1,l3]
  let l4 := x4+x4
  let t4 := (e3 0+1)+1
  have he : e4 = (fun i : Fin 5 => e ⟨i.val+4,by omega⟩) := by
    funext i
    congr 1
  change F (fileCode 4) e4 = r4+r4 at hr4
  rw [he] at hr4
  have chain2 : F PA194Stepper.stepper ![t1+t2,F pairCode ![modelNumeral M 114,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 93,F pairCode ![l2,r2]] := by
    change F PA194Stepper.stepper ![F addCode ![t1,t2],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  have chain3 : F PA194Stepper.stepper ![(t1+t2)+t3,F pairCode ![modelNumeral M 114,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 113,F pairCode ![l3,r3]] := by
    change F PA194Stepper.stepper ![F addCode ![(t1+t2),t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain2,h3]
  have chain4 : F PA194Stepper.stepper ![((t1+t2)+t3)+t4,F pairCode ![modelNumeral M 114,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![l4,r4]] := by
    change F PA194Stepper.stepper ![F addCode ![((t1+t2)+t3),t4],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain3,h4]
  let a := F ones ![e3 0,x3+x3]
  have hx : x4 = a+a+1 := by
    change F ones ![F addCode ![e3 0,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hl : l4 = (a+a+1)+(a+a+1) := by dsimp only [l4]; rw [hx]
  rw [hl] at chain4
  refine ⟨(((t1+t2)+t3)+t4),r4,hr4,?_⟩
  convert chain4 using 1 <;> congr 1
#print axioms scanFour
end models
end PA194HalfFileFour
