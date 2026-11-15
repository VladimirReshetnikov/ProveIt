import PA194Site28To84
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ThirdDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28To84 PA194Site28HeaderDispatch PA194SeedHeaderTo21 PA194RightRows PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem row70one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 70,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 70 0 2 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem eightMoreTo2 (l r : M) :
    let a := l+l+1
    let b := a+a
    let s := r+r+1
    let t := s+s
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 87,F pairCode ![b,t]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(b+b)+(b+b),r]] := by
  dsimp only
  have h87 := rowEvenLeft (M := M) 87 46 (by decide) (by decide +kernel)
  have h69 := rowEvenLeft (M := M) 69 94 (by decide) (by decide +kernel)
  have h70 := row70one (M := M)
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
      PA194Stepper.modelStepperZero]
  rw [h87,row46odd,row65one,row49zero,h69,row94zero,row50zero,h70]
  rfl
theorem sixteenTo2 (l r : M) :
    let s := r+r+1
    let t := s+s
    let u0 := t+t
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
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    F PA194Stepper.stepper ![modelNumeral M 16,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(a7+a7)+(a7+a7),r]] := by
  dsimp only
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  have h1 := PA194Site28HeaderDispatch.eightSteps (M := M) l ((r+r+1)+(r+r+1))
  have h2 := eightMoreTo2 (M := M) a5 r
  dsimp only at h1 h2
  rw [show modelNumeral M 16 = modelNumeral M 8 + modelNumeral M 8 by rw [←modelNumeralAdd]]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,modelNumeral M 8],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
#print axioms sixteenTo2
#print axioms row70one
#print axioms eightMoreTo2
end models
end PA194Site28ThirdDispatch
