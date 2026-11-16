import PA194Site29ReturnHeader
import PA194Site27ZeroTo24
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveReturnFrom16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site29ReturnHeader PA194Site27ZeroTo24 PA194ZeroReturnFrom16 PA194BinaryDouble PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnTo24 (r : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let r1 := (1 : M)+r+r
    let r2 := r1+r1+1
    let r3 := r2+r2+1
    let t := (1 : M)+r3+r3
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,modelNumeral M 3+rc],
      F pairCode ![modelNumeral M 16,F pairCode ![a5,(1 : M)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let r1 := (1 : M)+r+r
  let r2 := r1+r1+1
  let r3 := r2+r2+1
  have h1 := oneFrom16Odd (M := M) a4 r1
  have h2 := oneFrom16Odd (M := M) a3 r2
  have h3 := oneFrom16 (M := M) a2 r3
  have heq : (1 : M)+(1+1)+(r+r)+(r+r) = r1+r1+1 := by dsimp only [r1]; simp only [add_assoc,add_comm,add_left_comm]
  have h3' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![a3,r3+r3+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(r3+r3)+(r3+r3)]] := by
    convert h3 using 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  have hrun : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 16,
    F pairCode ![a5,(1 : M)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(r3+r3)+(r3+r3)]] := by
    rw [heq]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h1,h2,h3']
  have hr := returnFrom16 r3
  dsimp only at hr
  rw [PA194StepperCompose.modelStepperCompose,hrun,hr]
#print axioms returnTo24
end models
end PA194Site32PositiveReturnFrom16
