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
namespace PA194HalfFileSixExact
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

theorem scanSixExact (e : Fin 8 → M) (l p : M)
    (hblank : e (Fin.last 7) = (0 : M))
    (hp : F (fileCode 7) e = p+p) :
    ∃ time a right tail : M, a = F ones ![e ⟨5,by decide⟩,tail+tail] ∧ F (fileCode 1) (fun i => e ⟨i.val+6,by omega⟩) = right+right ∧
      F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have loop71 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 71,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 71 1 71 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit71 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 95,F pairCode ![x+x,y]] := by
    have hh := rightZero 71 0 95 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 95,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 95 1 95 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 114,F pairCode ![x+x,y]] := by
    have hh := rightZero 95 0 114 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
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
  let e1 : Fin 7 → M := fun j => e0 j.succ
  let e2 : Fin 6 → M := fun j => e1 j.succ
  let e3 : Fin 5 → M := fun j => e2 j.succ
  let e4 : Fin 4 → M := fun j => e3 j.succ
  let e5 : Fin 3 → M := fun j => e4 j.succ
  let e6 : Fin 2 → M := fun j => e5 j.succ
  have hb1 : e1 (Fin.last 6) = (0 : M) := by simpa only [e1,Fin.succ_last] using hblank
  have hb2 : e2 (Fin.last 5) = (0 : M) := by simpa only [e2,Fin.succ_last] using hb1
  have hb3 : e3 (Fin.last 4) = (0 : M) := by simpa only [e3,Fin.succ_last] using hb2
  have hb4 : e4 (Fin.last 3) = (0 : M) := by simpa only [e4,Fin.succ_last] using hb3
  have hb5 : e5 (Fin.last 2) = (0 : M) := by simpa only [e5,Fin.succ_last] using hb4
  obtain ⟨r1,hr1,h1⟩ := scanHalfBlock 6 71 95 e0 l p hblank hp loop71 exit71
  let x1 := F ones ![e0 0+1,l]
  let l1 := x1+x1
  let t1 := (e0 0+1)+1
  obtain ⟨r2,hr2,h2⟩ := scanHalfBlock 5 95 114 e1 l1 r1 hb1 hr1 loop95 exit95
  let x2 := F ones ![e1 0+1,l1]
  let l2 := x2+x2
  let t2 := (e1 0+1)+1
  obtain ⟨r3,hr3,h3⟩ := scanHalfBlock 4 114 68 e2 l2 r2 hb2 hr2 loop114 exit114
  let x3 := F ones ![e2 0+1,l2]
  let l3 := x3+x3
  let t3 := (e2 0+1)+1
  obtain ⟨r4,hr4,h4⟩ := scanHalfBlock 3 68 93 e3 l3 r3 hb3 hr3 loop68 exit68
  let x4 := F ones ![e3 0+1,l3]
  let l4 := x4+x4
  let t4 := (e3 0+1)+1
  obtain ⟨r5,hr5,h5⟩ := scanHalfBlock 2 93 113 e4 l4 r4 hb4 hr4 loop93 exit93
  let x5 := F ones ![e4 0+1,l4]
  let l5 := x5+x5
  let t5 := (e4 0+1)+1
  obtain ⟨r6,hr6,h6⟩ := scanHalfBlock 1 113 14 e5 l5 r5 hb5 hr5 loop113 exit113
  let x6 := F ones ![e5 0+1,l5]
  let l6 := x6+x6
  let t6 := (e5 0+1)+1
  have he : e6 = (fun i : Fin 2 => e ⟨i.val+6,by omega⟩) := by
    funext i
    congr 1
  change F (fileCode 1) e6 = r6+r6 at hr6
  rw [he] at hr6
  have chain2 : F PA194Stepper.stepper ![(t1+t2),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 114,F pairCode ![l2,r2]] := by
    change F PA194Stepper.stepper ![F addCode ![t1,t2],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  have chain3 : F PA194Stepper.stepper ![((t1+t2)+t3),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 68,F pairCode ![l3,r3]] := by
    change F PA194Stepper.stepper ![F addCode ![(t1+t2),t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain2,h3]
  have chain4 : F PA194Stepper.stepper ![(((t1+t2)+t3)+t4),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 93,F pairCode ![l4,r4]] := by
    change F PA194Stepper.stepper ![F addCode ![((t1+t2)+t3),t4],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain3,h4]
  have chain5 : F PA194Stepper.stepper ![((((t1+t2)+t3)+t4)+t5),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 113,F pairCode ![l5,r5]] := by
    change F PA194Stepper.stepper ![F addCode ![(((t1+t2)+t3)+t4),t5],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain4,h5]
  have chain6 : F PA194Stepper.stepper ![(((((t1+t2)+t3)+t4)+t5)+t6),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![l6,r6]] := by
    change F PA194Stepper.stepper ![F addCode ![((((t1+t2)+t3)+t4)+t5),t6],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain5,h6]
  let a := F ones ![e5 0,l5]
  have hx : x6 = a+a+1 := by
    change F ones ![F addCode ![e5 0,F oneCode Fin.elim0],l5] = _
    rw [modelAddOne,modelOnesSucc]
  have hl : l6 = (a+a+1)+(a+a+1) := by dsimp only [l6]; rw [hx]
  rw [hl] at chain6
  exact ⟨(((((t1+t2)+t3)+t4)+t5)+t6),a,r6,x5,rfl,hr6,chain6⟩
#print axioms scanSixExact
end models
end PA194HalfFileSixExact
