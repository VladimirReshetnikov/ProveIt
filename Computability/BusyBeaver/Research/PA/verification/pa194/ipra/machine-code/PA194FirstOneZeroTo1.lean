import PA194FirstOneFirstTo48
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
namespace PA194FirstOneZeroTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstOneFirstTo48 PA194FirstOneFirstTo36 PA194RightRows PA194FirstOneBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem markerFirstOneZeroTo1 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 1) :
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
    let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 1+1))+1)+modelNumeral M 2,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![((a0+a0)+(a0+a0))+((a0+a0)+(a0+a0))+
        (((a0+a0)+(a0+a0))+((a0+a0)+(a0+a0))),F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let d := (a0+a0)+(a0+a0)
  let tail := F (fileCode n) (fun i => rest i.succ)
  let x := F ones ![rest 0,tail]
  have hs : F ones ![rest 0+1,tail] = x+x+1 := by
    change F ones ![F addCode ![rest 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode (n+1)) rest = (x+x+1)+(x+x+1) := by
    rw [modelFileSucc,modelBlock,hs]
  have hm := PA194FirstOneFirstTo48.markerFirstOneTo48 n e rest u (0 : M) ht hfirst
  dsimp only at hm
  rw [modelOnesZero,hf] at hm
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  change F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 48,
    F pairCode ![d,(x+x+1)+(x+x+1)]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(d+d)+(d+d),x]]
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  have h1 := rightZero 48 0 59 (by decide) (by decide +kernel) d (x+x+1)
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h1
  have h2 := rightOne 59 0 1 (by decide) (by decide +kernel) (d+d) x
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h2
  rw [h1,h2]
  rfl
#print axioms markerFirstOneZeroTo1
end models
end PA194FirstOneZeroTo1
