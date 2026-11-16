import PA194Site32ReturnToHeader
import PA194Site28SecondReturn
import PA194Site29ReturnHeader
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32SecondReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28SecondReturn PA194Site29ReturnHeader PA194LeftOneWriteOne PA194BinaryDouble PA194ZeroReturnFrom16 PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem eighteenOneOddLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)+1]] := by
  have h := leftOneWriteOne 18 16 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem to24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let y0 := (w+w)+(w+w)
    let y1 := y0+y0+1
    let y2 := y1+y1+1
    let t := (1 : M)+y2+y2
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 4,modelNumeral M 3+rc],
      F pairCode ![modelNumeral M 17,F pairCode ![a6,y0]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let y0 := (w+w)+(w+w)
  let y1 := y0+y0+1
  let y2 := y1+y1+1
  have h17 := seventeenZeroOddLeft (M := M) a5 (w+w)
  have h18 := eighteenOneOddLeft (M := M) a4 y0
  have h16a := oneFrom16Odd (M := M) a3 y1
  have h16b := PA194Site28ReturnHeader.oneFrom16 (M := M) a2 y2
  have heq : (y2+y2+1)+(y2+y2+1) = (1+1)+(y2+y2)+(y2+y2) := by simp only [add_assoc,add_comm,add_left_comm]
  rw [heq] at h16b
  have h4 : F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 17,F pairCode ![a6,y0]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(y2+y2)+(y2+y2)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17,h18,h16a,h16b]
  have hr := returnFrom16 y2
  dsimp only at hr
  rw [PA194StepperCompose.modelStepperCompose,h4,hr]
#print axioms eighteenOneOddLeft
#print axioms to24
end models
end PA194Site32SecondReturn
