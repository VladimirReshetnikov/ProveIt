import PA194Site29To84
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29SecondDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194LeftOneWriteOne PA194BinaryDouble PA194Site29To84 PA194Site28To84 PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem row69oneEven (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 69,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 33,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 69 33 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem row33zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 33,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 33 0 42 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row42one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 42,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 60,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 42 0 60 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem tenTo60 (l r : M) :
    let w := r+r+1
    let h := (w+w)+(w+w)+1
    let a := l+l
    let b := a+a+1
    let c := b+b+1
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 10,F pairCode ![modelNumeral M 115,
      F pairCode ![l+l,h+h+1]]] =
    F pairCode ![modelNumeral M 60,F pairCode ![d+d,r]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 9),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 9 = F Code.succ (fun _ => modelNumeral M 8) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 8 = F Code.succ (fun _ => modelNumeral M 7) from rfl,
      PA194Stepper.modelStepperSucc,
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
      row115oneEven,row67zero,row86one,row107one,row30zeroOdd,row36one,row49zero,row69oneEven,row33zero,row42one]
theorem eighteenTo60 (l r : M) :
    let w := r+r+1
    let r2 := w+w
    let u0 := r2+r2+1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a := a4+a4
    let b := a+a+1
    let c := b+b+1
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 18,F pairCode ![modelNumeral M 24,
      F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 60,F pairCode ![d+d,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let w := r+r+1
  let r2 := w+w
  have h8 := PA194Site29HeaderDispatch.eightSteps (M := M) l r2
  dsimp only at h8
  have h10 := tenTo60 (M := M) a4 r
  dsimp only at h10
  have hr : (1 : M)+(1+1)+(r2+r2)+(r2+r2) =
      ((w+w)+(w+w)+1)+((w+w)+(w+w)+1)+1 := by
    dsimp only [r2]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hr] at h8
  rw [show modelNumeral M 18 = modelNumeral M 8+modelNumeral M 10 by rw [←modelNumeralAdd]]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,modelNumeral M 10],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h8,h10]
#print axioms eighteenTo60
#print axioms tenTo60
end models
end PA194Site29SecondDispatch
