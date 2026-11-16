import PA194Site31HeaderDispatch
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31MarkedTo106
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194Site31HeaderDispatch PA194StateOne PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem path31Any (r : M) :
    let u0 := r+r
    let u1 := u0+u0+1
    let u2 := u1+u1+1
    let u3 := u2+u2
    let u4 := u3+u3
    let u5 := u4+u4
    modelWord (PA194SourceProgram.path 31) r = u5+u5+1 := by
  dsimp only
  rw [PA194Path31Header.path31]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte]

theorem row108one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 108,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 106,F pairCode ![l+l,r]] := by
  have h := rightOne 108 0 106 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem markedTo106 (l u : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 7,modelNumeral M 1],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 31) (u+u+1)]]] =
    F pairCode ![modelNumeral M 106,F pairCode ![a6+a6,u]] := by
  dsimp only
  have h7 := PA194Site31HeaderDispatch.sevenSteps l (u+u+1)
  dsimp only at h7
  rw [←path31Any] at h7
  rw [PA194StepperCompose.modelStepperCompose,h7]
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,row108one]
#print axioms path31Any
#print axioms row108one
#print axioms markedTo106
end models
end PA194Site31MarkedTo106
