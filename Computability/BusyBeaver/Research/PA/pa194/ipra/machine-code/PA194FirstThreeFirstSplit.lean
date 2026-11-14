import PA194FirstThreeFileCases
import PA194FirstThreeFirstTo42
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreeFirstSplit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstThreeFileCases PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

/-- The first non-first marker with first physical value three reaches
the state-42 file-dependent boundary. -/
theorem markerFirstThreeSplit (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u v : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3) :
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
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let time := (((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 3+1))+modelNumeral M 2
    let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]
    (v=(0 : M) ∧ ∃ q : M, t=(q+q+1)+(q+q+1) ∧ F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 84,F pairCode ![a2+a2,t+t]]) ∨
    (∃ k q : M, v=k+1 ∧ t=q+q+1 ∧ F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 1,F pairCode ![((a2+a2)+(a2+a2))+((a2+a2)+(a2+a2)),q]]) := by
  dsimp only
  let t := F ones ![v,F (fileCode (n+1)) rest]
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  have hm := markerFirstThreeTo42 n e rest u v ht hfirst
  have hc := selectedFileCases n rest v
  dsimp only at hm hc
  rcases hc with ⟨hv,q,hq⟩ | ⟨k,q,hv,hq⟩
  · left
    refine ⟨hv,q,hq,?_⟩
    have hs := twoZero (a2+a2) (q+q+1)
    rw [←hq] at hs
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hm]
    exact hs
  · right
    refine ⟨k,q,hv,hq,?_⟩
    have hs := twoPositive (a2+a2) q
    rw [←hq] at hs
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hm]
    exact hs
#print axioms markerFirstThreeSplit
end models
end PA194FirstThreeFirstSplit
