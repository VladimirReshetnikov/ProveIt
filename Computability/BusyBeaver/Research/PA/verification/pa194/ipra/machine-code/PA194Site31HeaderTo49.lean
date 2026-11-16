import PA194Site31HeaderDispatch
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31HeaderTo49
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194SeedHeaderTo21 PA194RightRows PA194LeftRows PA194Site31HeaderDispatch PA194Path27Header PA194Path31Header PA194BinaryDouble
open PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem row46odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 46,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 65,F pairCode ![l,((r+r)+(r+r))+1]] := by
  have h := leftZero 46 65 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem row65one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 65,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![l+l+1,r]] := by
  have h := rightOne 65 1 49 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem path31Input (z : M) :
    let r := z+z
    let u0 := r+r
    let u1 := u0+u0+1
    let u2 := u1+u1+1
    let u3 := u2+u2
    let u4 := u3+u3
    let u5 := u4+u4
    modelWord (PA194SourceProgram.path 31) r = u5+u5+1 := by
  dsimp only
  rw [PA194Path31Header.path31]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]

theorem to49 (l z : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 7,modelNumeral M 3],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 31) (z+z)]]] =
    F pairCode ![modelNumeral M 49,F pairCode ![a5,(z+z)+(z+z)]] := by
  dsimp only
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5
  have h7 := PA194Site31HeaderDispatch.sevenSteps l (z+z)
  dsimp only at h7
  rw [←path31Input] at h7
  have h108 := rowEvenLeft (M := M) 108 46 (by decide) (by decide +kernel) a5 z
  have h3 : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 108,F pairCode ![a6,z+z]]] =
      F pairCode ![modelNumeral M 49,F pairCode ![a5,(z+z)+(z+z)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h108,row46odd,row65one]
  rw [PA194StepperCompose.modelStepperCompose,h7,h3]
#print axioms row46odd
#print axioms row65one
#print axioms path31Input
#print axioms to49
end models
end PA194Site31HeaderTo49
