import PA194MarkAll
import PA194MarkDelimiter
import PA194HeaderController
/-! Conditional physical marking-entry to dense state 24, for all nine register positions and all candidate-PRA model values. -/
set_option autoImplicit false
namespace PA194MarkToHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194MarkAll PA194MarkDelimiter
open PA194RegisterFile PA194CarryFile PA194ReturnFile PA194MarkerScan PA194MarkerReturnCell
open PA194HeaderController PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Mark a non-first physical register and continue through the padded header. -/
theorem positiveMarkTo24 (n : Nat) (bound : n+1 < 9) (e : Fin (n+2) → M) (k u t : M)
    (ht : e (Fin.last (n+1)) = (t+t+1)+(t+t+1)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := F ones ![k,(l+l)+(l+l)]
    let a := F (returnCode (n+1)) (Fin.cases ((t+t)+(t+t)) e)
    let y := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let markClock := (F (costCode (n+1)) e+modelNumeral M 3)+F (costCode (n+1)) e
    let headerClock := (((k+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![markClock+headerClock,
      F pairCode ![modelNumeral M (markerControl ⟨n+1,bound⟩),F pairCode ![x+x+1,F (fileCode (n+1)) e]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![y+y+1,F ones ![k,a]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l := z4+z4
  let x := F ones ![k,(l+l)+(l+l)]
  let a := F (returnCode (n+1)) (Fin.cases ((t+t)+(t+t)) e)
  have hm := modelMarkAllPositive n bound e (x+x+1) t ht
  dsimp only at hm
  rw [(modelOdd x).1,(modelOdd x).2] at hm
  have hcomm : (1 : M)+a+a = a+a+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hcomm] at hm
  have hh := markerTo24 ⟨1,by decide⟩ k u a
  dsimp only at hh
  change F PA194Stepper.stepper ![F addCode ![(F (costCode (n+1)) e+modelNumeral M 3)+F (costCode (n+1)) e,(((k+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hh
/-- The first physical register, whose marker starts at dense state 113. -/
theorem firstMarkTo24 (k u t : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := F ones ![k,(l+l)+(l+l)]
    let a := (t+t)+(t+t)
    let y := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let headerClock := (((k+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 3+headerClock,
      F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,(t+t+1)+(t+t+1)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![y+y+1,F ones ![k,a]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l := z4+z4
  let x := F ones ![k,(l+l)+(l+l)]
  let a := (t+t)+(t+t)
  have hm := modelMarkDelimiter (x+x+1) t
  rw [(modelOdd x).1,(modelOdd x).2] at hm
  have hcomm : (1 : M)+a+a = a+a+1 := by simp only [add_assoc,add_comm,add_left_comm]
  change F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,(t+t+1)+(t+t+1)]]] = F pairCode ![modelNumeral M 15,F pairCode ![x,1+a+a]] at hm
  rw [hcomm] at hm
  have hh := markerTo24 ⟨0,by decide⟩ k u a
  dsimp only at hh
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,(((k+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hh
#print axioms firstMarkTo24
#print axioms positiveMarkTo24
end models
end PA194MarkToHeader
