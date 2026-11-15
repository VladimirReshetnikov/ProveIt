import PA194Site31HeaderTo84
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31RootTo2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194RightRows PA194Site31HeaderTo49 PA194Site31HeaderTo84 PA194StateOne PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem row70one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 70,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l,r]] := by
  have h := rightOne 70 0 2 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem fiveSteps (l x : M) :
    let z := x+x+1
    F PA194Stepper.stepper ![modelNumeral M 5,F pairCode ![modelNumeral M 49,
      F pairCode ![l,(z+z)+(z+z)]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![((l+l)+(l+l))+((l+l)+(l+l)),x]] := by
  dsimp only
  let z := x+x+1
  have h69 := rowEvenLeft (M := M) 69 94 (by decide) (by decide +kernel) l z
  have h70 := row70one ((l+l)+(l+l)) x
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 4),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,PA194Site31HeaderTo84.row49zero,h69,
      PA194Site31HeaderTo84.row94zero,PA194Site31HeaderTo84.row50zero,h70]
  rfl

theorem rootTo2 (l x : M) :
    let z := x+x+1
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let v := a5+a5
    let v1 := v+v
    let v2 := v1+v1
    F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 7,modelNumeral M 3],modelNumeral M 5],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 31) (z+z)]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![v2,x]] := by
  dsimp only
  let z := x+x+1
  have h49 := PA194Site31HeaderTo49.to49 l z
  dsimp only at h49
  rw [PA194StepperCompose.modelStepperCompose,h49,fiveSteps]
#print axioms row70one
#print axioms fiveSteps
#print axioms rootTo2
end models
end PA194Site31RootTo2
