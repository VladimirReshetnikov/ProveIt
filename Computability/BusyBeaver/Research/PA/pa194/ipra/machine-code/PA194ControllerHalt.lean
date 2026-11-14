import PA194HaltRows
import PA194ControllerReturn
import PA194HeaderController
/-! All-model terminal branch for a specified intermediate PA194 tape shape. -/
set_option autoImplicit false
namespace PA194ControllerHalt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194MarkerReturnCell PA194ZeroRuns PA194BinaryDouble PA194HaltRows
open PackedIterationModel ConfigurationStep PRAModelIOpenPairing PA194ControllerReturn PA194HeaderController PA194OnesCommute
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem packed24 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 25,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 24,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 24,l,r+r],F nextL ![TableDispatch.modelNumeral M 24,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 24,l,r+r]) = stepSem (TableDispatch.modelNumeral M 24) l (r+r) at hm
  rw [←hm,modelState24Even]

theorem packed25 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 25,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 27,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 25,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 25,l,r+r],F nextL ![TableDispatch.modelNumeral M 25,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 25,l,r+r]) = stepSem (TableDispatch.modelNumeral M 25) l (r+r) at hm
  rw [←hm,modelState25Even]

theorem packed27 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 27,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 194,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 27,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 27,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 27,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 27,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 27) l (r+r+1) at hm
  rw [←hm,modelState27Odd]

theorem threeSteps (l r : M) :
    let x := r+r+1
    let y := x+x
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 3,
      F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![l,y+y]]] =
    F pairCode ![TableDispatch.modelNumeral M 194,F pairCode ![(l+l+l+l)+(l+l+l+l)+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => TableDispatch.modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 2 = F Code.succ (fun _ => TableDispatch.modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 1 = F Code.succ (fun _ => TableDispatch.modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [packed24,packed25,packed27]
  simp only [add_assoc]
/-- If a marker-exit configuration has the displayed padded header and a
`001` terminal prefix, it reaches the pinned terminal control in the displayed
finite model clock. This is an all-model physical-tape statement only. -/
theorem markerTerminal (i : Fin 2) (u r : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := r+r+1
    let y := x+x
    let v := y+y
    let a := F zeros ![TableDispatch.modelNumeral M 2,F zeros ![TableDispatch.modelNumeral M 6,u]]
    let b := a+a+1
    let clock := ((((0 : M)+1)+1)+1)+(((TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+TableDispatch.modelNumeral M 2)+1)
    F PA194Stepper.stepper ![clock+TableDispatch.modelNumeral M 3,
      F pairCode ![TableDispatch.modelNumeral M (returnControl i), F pairCode ![(l+l)+(l+l),v+v+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 194,F pairCode ![(b+b+b+b)+(b+b+b+b)+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := r+r+1
  let y := x+x
  let v := y+y
  let a := F zeros ![TableDispatch.modelNumeral M 2,F zeros ![TableDispatch.modelNumeral M 6,u]]
  let b := a+a+1
  have hm := markerTo24 i (0 : M) u v
  dsimp only at hm
  rw [modelOnesZero,modelOnesZero] at hm
  have hh := threeSteps b r
  dsimp only at hh
  change F PA194Stepper.stepper ![F addCode ![((((0 : M)+1)+1)+1)+(((TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+TableDispatch.modelNumeral M 2)+1),TableDispatch.modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hh]
#print axioms markerTerminal
#print axioms threeSteps
end models
end PA194ControllerHalt
