import PA194Site27HeaderDispatch
import PA194Path32Header
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32HeaderDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194SeedHeaderTo21 PA194RightRows PA194Site27HeaderDispatch PA194LeftRows PA194Path27Header PA194Path32Header PA194BinaryDouble
open PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row63one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 63,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 89,F pairCode ![l+l+1,r]] := by
  have h := rightOne 63 1 89 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row89one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 89,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 69,F pairCode ![l+l+1,r]] := by
  have h := rightOne 89 1 69 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row69odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 69,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 94,F pairCode ![l,((r+r)+(r+r))+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 69 94 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem eightSteps (l r : M) :
    let u0 := r+r
    let u1 := u0+u0+1
    let u2 := u1+u1+1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 94,F pairCode ![a5,((r+r)+(r+r))+1]] := by
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
  rw [row24,row26,row29,row34zero,row44one,row63one,row89one,row69odd]
theorem path32Input (r : M) :
    let u0 := r+r
    let u1 := u0+u0+1
    let u2 := u1+u1+1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    modelWord (PA194SourceProgram.path 32) r = u6+u6+1 := by
  dsimp only
  rw [PA194Path32Header.path32]
  simp only [modelWord, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]

theorem pathTo94 (l r : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 24,
      F pairCode ![l,modelWord (PA194SourceProgram.path 32) r]]] =
      F pairCode ![modelNumeral M 94,F pairCode ![a5,((r+r)+(r+r))+1]] := by
  dsimp only
  rw [path32Input]
  exact eightSteps l r
#print axioms path32Input
#print axioms pathTo94
#print axioms row63one
#print axioms row89one
#print axioms row69odd
#print axioms eightSteps
end models
end PA194Site32HeaderDispatch
