import PA194Site28HeaderReturnPrefix
import PA194SeedHeaderReturn19
import PA194ZeroReturnFrom16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28HeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28HeaderReturnPrefix PA194SeedHeaderReturn19 PA194ZeroReturnFrom16 PA194SeedHeaderTo21 PA194BinaryDouble PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem twoTo19 (y : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let y1 := y+y
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 17,F pairCode ![a1,y2]]] =
    F pairCode ![modelNumeral M 19,F pairCode ![(1 : M),y4+1]] := by
  dsimp only
  have h17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17,row18Odd]

theorem returnTo24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let w1 := w+w
    let x := (w1+w1)+1
    let x1 := x+x
    let y := (x1+x1)+1
    let y1 := y+y
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(modelNumeral M 4+modelNumeral M 2)+rc,
      F pairCode ![modelNumeral M 17,F pairCode ![a5,(1 : M)+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),y4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let w1 := w+w
  let x := (w1+w1)+1
  let x1 := x+x
  let y := (x1+x1)+1
  let y1 := y+y
  let y2 := y1+y1
  let y3 := y2+y2
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h4 := fourReturnSteps (M := M) a1 w
  dsimp only at h4
  have h2 := twoTo19 (M := M) y
  dsimp only at h2
  have hr := PA194SeedHeaderReturn19.returnTo24 (M := M) y3
  dsimp only at hr
  have hx : (1 : M)+(w+w)+(w+w) = x := by
    dsimp only [x,w1]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hx]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 4+modelNumeral M 2,rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![rc,F PA194Stepper.stepper ![F addCode ![modelNumeral M 4,modelNumeral M 2],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h4,h2,hr]
#print axioms twoTo19
#print axioms returnTo24
end models
end PA194Site28HeaderReturn
