import PA194FirstFiveTo84
import PA194FirstFiveSuccCore
import PA194EightyFourScan
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFiveSuccTo15
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFiveTo84 PA194FirstFiveSuccCore PA194EightyFourScan PA194HeaderController PA194State42Boundary PA194PositiveMarkCycle
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

/-- With first physical value five, the genuine marker cycle takes the
zero-residual state-42 branch to dense 84, for every selected value. -/
theorem markerFirstFiveSuccTo15 (idx : Nat) (bound : (idx+1)+1 < 9) (e : Fin ((idx+1)+2) → M)
    (u t : M) (ht : e (Fin.last ((idx+1)+1)) = (t+t+1)+(t+t+1))
    (hfirst : e 0 = ((((0 : M)+1)+1)+1)+1+1) :
    let j : Fin ((idx+1)+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode (idx+1)) (Fin.cases (j 0) (fun i => j i.succ.succ))
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
    let a3 := a2+a2
    let markClock := (F (costCode ((idx+1)+1)) e+modelNumeral M 3)+F (costCode ((idx+1)+1)) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
    let cycleClock := (((c1+headerClock)+modelNumeral M 3)+modelNumeral M 3)+1
    ∃ q : M, w = (q+q+1)+(q+q+1) ∧
      let a := F ones ![modelNumeral M 2,a3]
      F PA194Stepper.stepper ![((((markClock+headerClock)+modelNumeral M 3)+cycleClock)+modelNumeral M 2)+(modelNumeral M 2+1),
        F pairCode ![modelNumeral M (markerControl ⟨(idx+1)+1,bound⟩),F pairCode ![x+x+1,F (fileCode ((idx+1)+1)) e]]] =
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(q+q)+(q+q)]] := by
  dsimp only
  have hm := markerFirstFiveTo84 (idx+1) bound e u t ht hfirst
  dsimp only at hm
  obtain ⟨q,hq⟩ := returnedOddHalf idx e t
  refine ⟨q,hq,?_⟩
  rw [hq] at hm
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  have hs := scanExit (modelNumeral M 2) a3 q
  dsimp only at hs
  rw [zerosTwo] at hs
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hs
#print axioms markerFirstFiveSuccTo15
end models
end PA194FirstFiveSuccTo15
