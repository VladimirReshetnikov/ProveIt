import PA194ZeroReturnFrom16
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27HeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194SeedHeaderReturn19 PA194LeftOneWriteOne PA194ZeroReturnFrom16 PA194LeftRows PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fiveTo19 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let x := w3+1
    let x1 := x+x
    let x2 := x1+x1
    let x3 := x2+x2
    let x4 := x3+x3
    F PA194Stepper.stepper ![modelNumeral M 5,F pairCode ![modelNumeral M 17,F pairCode ![a4,w2]]] =
    F pairCode ![modelNumeral M 19,F pairCode ![(1 : M),x4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  have h17 := leftZero 17 18 (by decide) (by decide +kernel) (a3+a3+1) w1
  rw [(modelOdd a3).1,(modelOdd a3).2] at h17
  have h17' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![a3+a3+1,w2]]) =
      F pairCode ![modelNumeral M 18,F pairCode ![a3,w3+1]] := by
    convert h17 using 1 <;> dsimp only [w3,w2] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h18 := leftOneWriteOne 18 16 (by decide) (by decide +kernel) a3 w2
  rw [(modelDouble a2).1,(modelDouble a2).2,zero_add] at h18
  have h18' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![a3,w3+1]]) =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(w3+1)+(w3+1)]] := by
    convert h18 using 1 <;> dsimp only [w3,w2] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h16 := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  have h17e := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 4),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17',h18',h16,h17e,row18Odd]

theorem returnTo24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let x := w3+1
    let x1 := x+x
    let x2 := x1+x1
    let x3 := x2+x2
    let x4 := x3+x3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 5+rc,F pairCode ![modelNumeral M 17,F pairCode ![a4,w2]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),x4+1]] := by
  dsimp only
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let x := w3+1
  let x1 := x+x
  let x2 := x1+x1
  let x3 := x2+x2
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h5 := fiveTo19 w
  dsimp only at h5
  have hr := PA194SeedHeaderReturn19.returnTo24 x3
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 5,rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h5,hr]
#print axioms fiveTo19
#print axioms returnTo24
end models
end PA194Site27HeaderReturn
