import PA194FirstFiveFifteenTo24
import PA194FirstThreeFirstTo42
import PA194State42Boundary
import PA194EightyFourScan
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreeZeroTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFiveFifteenTo24 PA194State42Boundary PA194EightyFourScan PA194HeaderController PA194FiniteControls PA194StateOne PA194FirstThreeFirstTo42 PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

/-- The first non-first marker, with first physical value three and zero
selected value, reaches dense state 24 under the stated file layout. -/
theorem markerFirstThreeZeroTo24 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    ∃ time right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F (fileCode (n+1)) rest
  let q := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l64 := z4+z4
  let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
  let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]
  let clock := (((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 3+1))+modelNumeral M 2
  have htail : tail=(q+q+1)+(q+q+1) := by
    dsimp [tail]
    rw [modelFileSucc,modelBlock]
    have hs : F ones ![rest 0+1,F (fileCode n) (fun i => rest i.succ)] = q+q+1 := by
      change F ones ![F addCode ![rest 0,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hs]
  have hm := markerFirstThreeTo42 n e rest u (0 : M) ht hfirst
  dsimp only at hm
  have hq : F ones ![(0 : M),tail] = (q+q+1)+(q+q+1) := (modelOnesZero tail).trans htail
  rw [hq] at hm
  have h84 : F PA194Stepper.stepper ![clock,start] =
      F pairCode ![modelNumeral M 84,F pairCode ![a3,((q+q+1)+(q+q+1))+((q+q+1)+(q+q+1))]] := by
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,hm]
    exact twoZero a3 (q+q+1)
  have hs := scanExit (modelNumeral M 2) a3 q
  dsimp only at hs
  rw [zerosTwo] at hs
  have h15 : F PA194Stepper.stepper ![clock+(modelNumeral M 2+1),start] =
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => F ones ![modelNumeral M 2,a3]),
        F parityCode (fun _ => F ones ![modelNumeral M 2,a3])+(1+1)+(q+q)+(q+q)]] := by
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h84]
    exact hs
  have hn1 : modelNumeral M 1+1 = modelNumeral M 2 := by rw [←modelNumeralOne,←modelNumeralAdd]
  apply extendScanExit (modelNumeral M 1) u q _ _
  rw [hn1]
  exact h15
#print axioms markerFirstThreeZeroTo24
end models
end PA194FirstThreeZeroTo24
