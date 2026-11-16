import PA194Site28SecondReturn
import PA194Site29HeaderReturn
import PA194SeedHeaderReturn19
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29HeaderBackTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194LeftOneWriteOne PA194SeedHeaderTo21 PA194Site28HeaderReturnPrefix PA194ZeroReturnFrom16 PA194Site28SecondReturn PA194Site29HeaderReturn PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem eighteenOneOddLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 18 16 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem eightTo19 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6+1
    let r0 := (w+w)+(w+w)
    let r1 := r0+r0+1
    let r2 := r1+r1+1
    let r3 := r2+r2
    let r4 := r3+r3+1
    let r5 := r4+r4
    let r6 := r5+r5
    let r7 := r6+r6
    let r8 := r7+r7+1
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 17,F pairCode ![a7,r0]]] =
    F pairCode ![modelNumeral M 19,F pairCode ![(1 : M),r8]] := by
  dsimp only
  have heven16 := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  have heven17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 7),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 7 = F Code.succ (fun _ => modelNumeral M 6) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,
      seventeenZeroOddLeft,eighteenOneOddLeft,row16oneEven,sixteenZeroOddLeft,seventeenOneEvenLeft,heven16,heven17,row18Odd]

theorem returnTo24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6+1
    let r0 := (w+w)+(w+w)
    let r1 := r0+r0+1
    let r2 := r1+r1+1
    let r3 := r2+r2
    let r4 := r3+r3+1
    let r5 := r4+r4
    let r6 := r5+r5
    let r7 := r6+r6
    let r8 := r7+r7+1
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 8+rc,F pairCode ![modelNumeral M 17,F pairCode ![a7,r0]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),r8]] := by
  dsimp only
  let r0 := (w+w)+(w+w)
  let r1 := r0+r0+1
  let r2 := r1+r1+1
  let r3 := r2+r2
  let r4 := r3+r3+1
  let r5 := r4+r4
  let r6 := r5+r5
  let r7 := r6+r6
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h := eightTo19 w
  dsimp only at h
  have hr := PA194SeedHeaderReturn19.returnTo24 r7
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h,hr]
#print axioms eightTo19
#print axioms returnTo24
end models
end PA194Site29HeaderBackTo24
