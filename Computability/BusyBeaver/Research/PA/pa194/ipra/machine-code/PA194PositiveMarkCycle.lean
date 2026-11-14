import PA194ThresholdCycle
/-! Actual non-first marking followed by the k=1 and at-least-five controller cycle. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PositiveMarkCycle
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
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

/-- A genuine non-first marking output with k=1 and first prefix value n+5
returns through the next controller cycle to state 42, preserving the exact
nonstandard residual one-run in its right tape half. -/
theorem positiveMarkFiveTo42 (idx : Nat) (bound : idx+1 < 9) (e : Fin (idx+2) → M)
    (n u t : M) (ht : e (Fin.last (idx+1)) = (t+t+1)+(t+t+1))
    (hfirst : e 0 = ((((n+1)+1)+1)+1)+1) :
    let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
    let r := F ones ![n,w]
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
    let markClock := (F (costCode (idx+1)) e+modelNumeral M 3)+F (costCode (idx+1)) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
    let c2 := headerClock
    let cycleClock := (((c1+c2)+modelNumeral M 3)+modelNumeral M 3)+1
    F PA194Stepper.stepper ![((markClock+headerClock)+modelNumeral M 3)+cycleClock,
      F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
    F pairCode ![modelNumeral M 42,F pairCode ![a3,r+r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
  let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
  let r := F ones ![n,w]
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let markClock := (F (costCode (idx+1)) e+modelNumeral M 3)+F (costCode (idx+1)) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
  let c2 := headerClock
  let cycleClock := (((c1+c2)+modelNumeral M 3)+modelNumeral M 3)+1
  have hm := positiveMarkTo35 idx bound e u t ht
  dsimp only at hm
  change _ = F pairCode ![modelNumeral M 35,F pairCode ![ll,F ones ![j 1,w]]] at hm
  have hindex : j 1 = e 0 := rfl
  rw [hindex,hfirst] at hm
  have hs (q : M) : F ones ![q+1,w] = F ones ![q,w]+F ones ![q,w]+1 := by
    change F ones ![F addCode ![q,F oneCode Fin.elim0],w] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hs,hs,hs,hs,hs] at hm
  have hc := thresholdCycleTo42 u r
  dsimp only at hc
  change F PA194Stepper.stepper ![F addCode ![(markClock+headerClock)+modelNumeral M 3,cycleClock],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hc]
#print axioms positiveMarkFiveTo42
end models
end PA194PositiveMarkCycle
