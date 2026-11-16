import PA194MarkToHeader
import PA194ControllerHalt
/-! An all-model terminal path from a specified first-register marking entry. -/
set_option autoImplicit false
namespace PA194MarkHalt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194MarkToHeader PA194ControllerHalt PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- Under the displayed intermediate tape shape, the first physical-register
marking entry reaches the terminal state. This theorem does not assert that a
blank-tape run reaches the displayed configuration. -/
theorem firstMarkTerminal (u r : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := (l+l)+(l+l)
    let t := r+r+1
    let a := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let b := a+a+1
    let headerClock := ((((0 : M)+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(modelNumeral M 3+headerClock)+modelNumeral M 3,
      F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,(t+t+1)+(t+t+1)]]] =
    F pairCode ![modelNumeral M 194,F pairCode ![(b+b+b+b)+(b+b+b+b)+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let t := r+r+1
  let a := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let b := a+a+1
  have hm := firstMarkTo24 (0 : M) u t
  dsimp only at hm
  rw [modelOnesZero,modelOnesZero] at hm
  have hh := threeSteps b r
  dsimp only at hh
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3+(((((0 : M)+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)),modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hh]
#print axioms firstMarkTerminal
end models
end PA194MarkHalt
