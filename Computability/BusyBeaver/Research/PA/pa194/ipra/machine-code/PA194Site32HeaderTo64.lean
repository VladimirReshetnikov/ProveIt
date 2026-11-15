import PA194Site32HeaderDispatch
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32HeaderTo64
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194SeedHeaderTo21 PA194RightRows PA194LeftRows PA194Site32HeaderDispatch PA194Path27Header PA194BinaryDouble
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

theorem row94one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 94,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 103,F pairCode ![l+l+1,r]] := by
  have h := rightOne 94 1 103 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row103odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 103,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 45,F pairCode ![l,((r+r)+(r+r))+1]] := by
  have h := leftZero 103 45 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem threeSteps (l r : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 94,
      F pairCode ![l,((r+r)+(r+r))+1]]] =
    F pairCode ![modelNumeral M 64,F pairCode ![l+l+1,r+r]] := by
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,row94one,row103odd,row45]

theorem pathTo64 (l r : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,modelNumeral M 3],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 32) r]]] =
    F pairCode ![modelNumeral M 64,F pairCode ![a5+a5+1,r+r]] := by
  dsimp only
  rw [PA194StepperCompose.modelStepperCompose,pathTo94,threeSteps]
theorem row64zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 64,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![l+l,r]] := by
  have h := rightZero 64 0 42 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem pathTo42 (l r : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 32) r]]] =
    F pairCode ![modelNumeral M 42,F pairCode ![a6+a6,r]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,pathTo64,row64zero]
#print axioms row64zero
#print axioms pathTo42
#print axioms row94one
#print axioms row103odd
#print axioms threeSteps
#print axioms pathTo64
end models
end PA194Site32HeaderTo64
