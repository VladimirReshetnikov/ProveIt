import PA194StandardCodeBridge
import PA194StepperZip
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194StandardStepperBridge
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory
open TableDispatch PackedStandard PA194StepperZip PA194StandardCodeBridge

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

/-- Any fixed finite literal blank run lifts to the exact stepper equation in
all candidate PRA models. This is a schema over external natural numbers, not
an internal model-length simulation theorem. -/
theorem literalBlankRun_allModels (n : Nat) (finish : M6.Zip.Conf)
    (h : M6.Zip.run PA194.Literal.machine n PA194Bounded.blankZip = some finish) :
    F PA194Stepper.stepper ![modelNumeral M n, modelNumeral M 0] =
      modelNumeral M (pack (PA194Bounded.encodeZip finish)) := by
  have hz : pack (PA194Bounded.encodeZip PA194Bounded.blankZip) = 0 := by rfl
  have he := PA194Bounded.zip_run_some n finish h
  have hs := PA194StepperZip.modelStepperZip PA194Bounded.blankZip n
  change F PA194Stepper.stepper ![n,pack (PA194Bounded.encodeZip PA194Bounded.blankZip)] =
    pack (PA194Bounded.encodeZip (PA194Bounded.zipRun n)) at hs
  rw [hz,he] at hs
  have hp := (modelStandardCode (M := M) PA194Stepper.stepper) (![n,0] : Fin 2 → Nat)
  have hv : (fun i => modelNumeral M ((![n,0] : Fin 2 → Nat) i)) =
      ![modelNumeral M n,modelNumeral M 0] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [hv,hs] at hp
  exact hp
#print axioms literalBlankRun_allModels
end models
end PA194StandardStepperBridge
