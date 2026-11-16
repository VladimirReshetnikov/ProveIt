import PA194Site28HeaderDispatch
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28To84
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194LeftRows PA194BinaryDouble PA194FiniteControls PA194SeedHeaderTo21 PA194SeedHeaderDispatch PA194Site28HeaderDispatch
open PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row46odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 46,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 65,F pairCode ![l,(r+r)+(r+r)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 46 65 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem row65one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 65,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![l+l+1,r]] := by
  have h := rightOne 65 1 49 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row49zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 49,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 69,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 49 0 69 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row94zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 94,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 50,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 94 0 50 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row50zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 50,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 70,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 50 0 70 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem eightMoreSteps (l r : M) :
    let a := l+l+1
    let b := a+a
    let s := r+r
    let t := s+s
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 87,F pairCode ![b,t]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![b,t]] := by
  dsimp only
  have h87 := rowEvenLeft (M := M) 87 46 (by decide) (by decide +kernel)
  have h69 := rowEvenLeft (M := M) 69 94 (by decide) (by decide +kernel)
  have h70 := rowEvenLeft (M := M) 70 84 (by decide) (by decide +kernel)
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
theorem sixteenSteps (l r : M) :
    let s := r+r
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
    F PA194Stepper.stepper ![modelNumeral M 16,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![a6+a6,t]] := by
  dsimp only
  have h1 := PA194Site28HeaderDispatch.eightSteps (M := M) l ((r+r)+(r+r))
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  have h2 := eightMoreSteps (M := M) a5 r
  dsimp only at h1 h2
  rw [show modelNumeral M 16 = modelNumeral M 8 + modelNumeral M 8 by
    rw [←modelNumeralAdd]]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,modelNumeral M 8],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
#print axioms sixteenSteps
#print axioms row46odd
#print axioms row65one
#print axioms row49zero
#print axioms row94zero
#print axioms row50zero
#print axioms eightMoreSteps
end models
end PA194Site28To84
