import PA194SeedHeaderDispatch
import PA194SeedHeaderTo21
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ThirdDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194SeedHeaderTo21 PA194RightRows
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

theorem row44one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 44,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 63,F pairCode ![l+l+1,r]] := by
  have h := rightOne 44 1 63 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row63zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 63,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 88,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 63 0 88 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row88zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 88,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 108,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 88 0 108 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row59one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 59,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 1,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 59 0 1 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem thirteenTo1 (l r : M) :
    let s := r+r+1
    let u0 := s+s
    let u1 := u0+u0
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
    let a6 := a5+a5
    F PA194Stepper.stepper ![modelNumeral M 13,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a6+a6)+(a6+a6),r]] := by
  dsimp only
  have h108 := rowEvenLeft (M := M) 108 46 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 12),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 12 = F Code.succ (fun _ => modelNumeral M 11) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 11 = F Code.succ (fun _ => modelNumeral M 10) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 10 = F Code.succ (fun _ => modelNumeral M 9) from rfl,
      PA194Stepper.modelStepperSucc,
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
      PA194Stepper.modelStepperZero]
  rw [row24,row26,row29,row34zero,row44one,row63zero,row88zero,h108,row46zero,row65zero,row91zero,row110zero,row59one]
  rfl
#print axioms thirteenTo1
end models
end PA194Site27ThirdDispatch
