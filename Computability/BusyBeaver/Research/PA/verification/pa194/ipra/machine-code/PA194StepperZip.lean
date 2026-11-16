import PA194Stepper
import PackedStandard
set_option autoImplicit false
namespace PA194StepperZip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PackedClock PackedStandard List.Vector
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

def runFrom (c : PA194Bounded.Conf) (n : Nat) : PA194Bounded.Conf :=
  Nat.rec c (fun _ current => PA194Bounded.next current) n
def zipRunFrom (c : M6.Zip.Conf) (n : Nat) : M6.Zip.Conf :=
  Nat.rec c (fun _ current => PA194Bounded.zipTotalStep current) n

theorem zipRunFrom_binding (c : M6.Zip.Conf) (n : Nat) :
    PA194Bounded.encodeZip (zipRunFrom c n) = runFrom (PA194Bounded.encodeZip c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change PA194Bounded.encodeZip (PA194Bounded.zipTotalStep (zipRunFrom c n)) = PA194Bounded.next (runFrom (PA194Bounded.encodeZip c) n)
    rw [←PA194Bounded.zip_step_binding,ih]

theorem modelStepperFrom (c : PA194Bounded.Conf) (n : Nat) :
    F PA194Stepper.stepper ![n,pack c] = pack (runFrom c n) := by
  induction n with
  | zero =>
    have h := PA194Stepper.modelStepperZero (M := Nat) (pack c)
    exact h
  | succ n ih =>
    have h := PA194Stepper.modelStepperSucc (M := Nat) n (pack c)
    change F PA194Stepper.stepper ![n+1,pack c] = F encodedStep (fun _ => F PA194Stepper.stepper ![n,pack c]) at h
    rw [h,ih]
    change eval encodedStep (pack (runFrom c n) ::ᵥ nil) = _
    rw [evalPackedStep,unpackPack]
    rfl

theorem modelStepperZip (c : M6.Zip.Conf) (n : Nat) :
    F PA194Stepper.stepper ![n,pack (PA194Bounded.encodeZip c)] =
      pack (PA194Bounded.encodeZip (zipRunFrom c n)) := by
  rw [zipRunFrom_binding,modelStepperFrom]
#print axioms zipRunFrom_binding
#print axioms modelStepperFrom
#print axioms modelStepperZip
end PA194StepperZip
