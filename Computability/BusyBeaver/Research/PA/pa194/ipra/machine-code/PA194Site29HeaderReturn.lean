import PA194Site29HeaderTo17
import PA194Site28HeaderReturnPrefix
import PA194Site28SecondReturn
import PA194SeedHeaderReturn19
import PA194ZeroReturnFrom16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29HeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194LeftOneWriteOne PA194SeedHeaderTo21 PA194Site28HeaderReturnPrefix PA194ZeroReturnFrom16 PA194BinaryDouble PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem row17oneOdd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 17 16 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem row16oneEven (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem sevenTo19 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let w1 := w+w
    let x0 := w1+w1+1
    let x1 := x0+x0+1
    let x2 := x1+x1
    let x3 := x2+x2+1
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5
    let x7 := x6+x6+1
    F PA194Stepper.stepper ![modelNumeral M 7,F pairCode ![modelNumeral M 17,F pairCode ![a6,x0]]] =
    F pairCode ![modelNumeral M 19,F pairCode ![(1 : M),x7]] := by
  dsimp only
  have heven16 := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  have heven17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 6),_] = _
  rw [PA194Stepper.modelStepperSucc,
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
      row17oneOdd,row16oneEven,sixteenZeroOddLeft,seventeenOneEvenLeft,heven16,heven17,row18Odd]
theorem returnTo24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let w1 := w+w
    let x0 := w1+w1+1
    let x1 := x0+x0+1
    let x2 := x1+x1
    let x3 := x2+x2+1
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5
    let x7 := x6+x6+1
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 7+rc,F pairCode ![modelNumeral M 17,
      F pairCode ![a6,(1 : M)+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),x7]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let w1 := w+w
  let x0 := w1+w1+1
  let x1 := x0+x0+1
  let x2 := x1+x1
  let x3 := x2+x2+1
  let x4 := x3+x3
  let x5 := x4+x4
  let x6 := x5+x5
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h7 := sevenTo19 (M := M) w
  dsimp only at h7
  have hr := PA194SeedHeaderReturn19.returnTo24 (M := M) x6
  dsimp only at hr
  have hx : (1 : M)+(w+w)+(w+w)=x0 := by dsimp only [x0,w1]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hx]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 7,rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h7,hr]
#print axioms returnTo24
#print axioms sevenTo19
end models
end PA194Site29HeaderReturn
