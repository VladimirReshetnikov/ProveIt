import PA194MarkToHeader
import PA194IncrementDispatch
/-! Actual k=1 non-first marker path through dense state 35 in every candidate PRA model. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194PositiveMarkerRoute
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194RightRows
open PA194IncrementDispatch PA194MarkToHeader PA194OnesCommute PA194ReturnFile
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194MarkerScan PRAModelIOpenPairing TableDispatch PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row29one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 35,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 29 1 35 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem threeTo35 (l r : M) :
    let b := r+r+1
    let a := b+b
    let l1 := l+l+1
    let l2 := l1+l1
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 24,F pairCode ![l,a+a+1]]] =
    F pairCode ![modelNumeral M 35,F pairCode ![l2+l2+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [row24,row26,row29one]
theorem returnShape (n : Nat) (e : Fin (n+3) → M) :
    let w := F (returnCode n) (Fin.cases (e 0) (fun j => e j.succ.succ))
    let p := F ones ![e 1,w]
    F (returnCode (n+1)) e = (p+p+1)+(p+p+1) := by
  dsimp only
  rw [modelReturnCodeSucc]
  rw [modelOnesCommute]

/-- Under the existing marking input shape and a one-bit controller run,
the actual non-first marking output follows 24→26→29→35. -/
theorem positiveMarkTo35 (n : Nat) (bound : n+1 < 9) (e : Fin (n+2) → M) (u t : M)
    (ht : e (Fin.last (n+1)) = (t+t+1)+(t+t+1)) :
    let j : Fin (n+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode n) (Fin.cases (j 0) (fun i => j i.succ.succ))
    let p := F ones ![j 1,w]
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := ((l+l)+(l+l))+((l+l)+(l+l))+1
    let y := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := y+y+1
    let h1 := h+h+1
    let h2 := h1+h1
    let markClock := (F (costCode (n+1)) e+modelNumeral M 3)+F (costCode (n+1)) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(markClock+headerClock)+modelNumeral M 3,
      F pairCode ![modelNumeral M (markerControl ⟨n+1,bound⟩),F pairCode ![x+x+1,F (fileCode (n+1)) e]]] =
    F pairCode ![modelNumeral M 35,F pairCode ![h2+h2+1,p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let j : Fin (n+3) → M := Fin.cases ((t+t)+(t+t)) e
  let w := F (returnCode n) (Fin.cases (j 0) (fun i => j i.succ.succ))
  let p := F ones ![j 1,w]
  let y := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := y+y+1
  let markClock := (F (costCode (n+1)) e+modelNumeral M 3)+F (costCode (n+1)) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have hm := positiveMarkTo24 n bound e (modelNumeral M 1) u t ht
  dsimp only at hm
  simp only [onesOne] at hm
  have ha := returnShape n j
  dsimp only at ha
  rw [ha] at hm
  have hs := threeTo35 h p
  dsimp only at hs
  change F PA194Stepper.stepper ![F addCode ![markClock+headerClock,modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hs]
#print axioms positiveMarkTo35
#print axioms returnShape
#print axioms threeTo35
end models
end PA194PositiveMarkerRoute
