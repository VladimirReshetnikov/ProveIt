import PA194CarryThreeFile
import PA194FirstThreePositiveTo1
import PA194FirstThreePositiveScan
import PA194FirstThreePositiveTo3
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreePositiveCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstThreePositiveTo1 PA194FirstThreePositiveScan PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

/-- Traverse the remaining finite file after the genuine first-three,
positive-selected marker path, assuming the final file tail is even. -/
theorem markerFirstThreePositiveCarry (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k p : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3)
    (heven : rest (Fin.last (n+1)) = p+p) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]
    ∃ time out : M, F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 3,F pairCode ![out,p]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let l := ((a2+a2)+(a2+a2))+((a2+a2)+(a2+a2))
  let a := F ones ![k,l]
  let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let time := (((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 3+1))+modelNumeral M 2
  have hm := PA194FirstThreePositiveTo3.markerFirstThreePositiveTo3 n e rest u k ht hfirst
  dsimp only at hm
  have he : (fun i : Fin (n+1) => rest i.succ) (Fin.last n) = p+p := heven
  obtain ⟨t,out,hr⟩ := PA194CarryThreeFile.carryThreeAcross n (fun i => rest i.succ) (rest 0) (a+a+1) p he
  refine ⟨(time+(k+1))+t,out,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hr
#print axioms markerFirstThreePositiveCarry
end models
end PA194FirstThreePositiveCarry
