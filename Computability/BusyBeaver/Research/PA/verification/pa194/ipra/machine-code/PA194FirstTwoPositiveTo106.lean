import PA194FirstTwoPositiveTo85
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
namespace PA194FirstTwoPositiveTo106
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstTwoPositiveTo106 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 2) :
    let t := F ones ![k+1,F (fileCode (n+1)) rest]
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
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let d := (a1+a1)+(a1+a1)
    let scanned := F ones ![k,d+d]
    let r := F ones ![rest 0+1,F (fileCode n) (fun i => rest i.succ)]
    F PA194Stepper.stepper ![(((((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 2+1))+1)+1+k)+1,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 106,F pairCode ![scanned+scanned,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let d := (a1+a1)+(a1+a1)
  let tail := F (fileCode n) (fun i => rest i.succ)
  let r := F ones ![rest 0+1,tail]
  have hf : F (fileCode (n+1)) rest = r+r := by
    rw [modelFileSucc,modelBlock]
  have hloop (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 85,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 85 1 85 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have hscan := PA194GenericRightScan.modelFullScan 85 hloop k (d+d) (F (fileCode (n+1)) rest)
  have hnext := rightZero 85 0 106 (by decide) (by decide +kernel) (F ones ![k,d+d]) r
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at hnext
  change F PA194Stepper.stepper ![F addCode ![_,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![_,k],_]) = _
  rw [PA194StepperCompose.modelStepperCompose,PA194FirstTwoPositiveTo85.markerFirstTwoPositiveTo85 n e rest u k ht hfirst,hscan,hf,hnext]
#print axioms markerFirstTwoPositiveTo106
end models
end PA194FirstTwoPositiveTo106
