import PA194Site27HeaderDispatch
import PA194Path29Header
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29HeaderDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194SeedHeaderTo21 PA194RightRows PA194Site27HeaderDispatch
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

theorem row88one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 88,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 98,F pairCode ![l+l+1,r]] := by
  have h := rightOne 88 1 98 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row98one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 98,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 115,F pairCode ![l,(1 : M)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := PA194LeftOneWriteOne.leftOneWriteOne 98 115 (by decide) (by decide +kernel) (l+l+1) r
  rw [(PA194BinaryDouble.modelOdd l).1,(PA194BinaryDouble.modelOdd l).2] at h
  exact h

theorem eightSteps (l r : M) :
    let u0 := r+r+1
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
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 115,F pairCode ![a5,(1 : M)+(1+1)+(r+r)+(r+r)]] := by
  dsimp only
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
  rw [row24,row26,row29,row34zero,row44one,row63zero,row88one,row98one]
#print axioms row88one
#print axioms row98one
#print axioms eightSteps
end models
end PA194Site29HeaderDispatch
