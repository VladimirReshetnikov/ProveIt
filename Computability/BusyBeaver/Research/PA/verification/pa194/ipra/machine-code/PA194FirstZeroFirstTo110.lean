import PA194FirstZeroFirstTo46
import PA194LeftRows
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
namespace PA194FirstZeroFirstTo110
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstZeroFirstTo46 PA194LeftRows PA194RightRows PA194FirstZeroBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem fortySixTo110 (l t : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 46,F pairCode ![l+l,t+t]]] =
    F pairCode ![modelNumeral M 110,F pairCode ![(l+l)+(l+l),t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
    PA194Stepper.modelStepperSucc,show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  have h1 := leftZero 46 65 (by decide) (by decide +kernel) (l+l) t
  have h2 := rightZero 65 0 91 (by decide) (by decide +kernel) l (t+t)
  have h3 := rightZero 91 0 110 (by decide) (by decide +kernel) (l+l) t
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h2 h3
  rw [h1,(modelDouble l).1,(modelDouble l).2,zero_add,h2,h3]
#print axioms fortySixTo110
theorem markerFirstZeroTo110 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u v : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = (0 : M)) :
    let t := F ones ![v,F (fileCode (n+1)) rest]
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
    let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((markClock+headerClock)+modelNumeral M 3)+((0 : M)+1))+modelNumeral M 3,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 110,F pairCode ![(ll+ll)+(ll+ll),t]] := by
  dsimp only
  have hm := markerFirstZeroTo46 n e rest u v ht hfirst
  dsimp only at hm
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact fortySixTo110 _ _
#print axioms markerFirstZeroTo110
end models
end PA194FirstZeroFirstTo110
