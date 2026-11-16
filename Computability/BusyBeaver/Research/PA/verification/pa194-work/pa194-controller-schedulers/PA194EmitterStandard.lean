import PA194EmitterSchedulerCore
import PA194TargetGate

/-!
# The gate of the emitter `delta` and the gate of the upstream PA196 development

`PA194EmitterSchedulerCore.deltaGate` is a PRA code. This file evaluates it on the standard
numbers and identifies the value with the definition of the upstream snapshot:

```lean
theorem eval_deltaGate (a b c : Nat) :
    eval deltaGate (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil) = PA196.Commands.Code.bundle a b c
```

`PA196.Commands.Code.gate a b c` is `bundle a b c` under the guard `c ≠ a`, `c ≠ b` and `0`
otherwise, and `PA196.Commands.step` leaves `gate (h + y) (d + x) c` on top after AX. So the
gate formula of the schedulers with `delta` is the one of that development, not only a
transcription of a report. The statement is about the gate formula on standard numbers; it
does not identify the scheduler step with `PA196.Commands.step`.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194EmitterStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable
 PA194NumeralCode PA194TargetCantor PA194TargetLeaves PA194TargetLeavesStandard PA194TargetGate
 PA194EmitterScheduler

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- The value of the gate code in a model of the candidate PRA. -/
theorem deltaGate_value (a b c : M) :
    F deltaGate ![a,b,c] =
      negValue (impValue (impValue (eqValue a b) (allValue c (eqValue a b)))
        (impValue (memVacValue a b c) (separationTailValue a b c))) := by
  simp only [deltaGate, machineNeg_model, machineImp_model, machineAll_model, eq_model,
    memVac_model, separationTail_model, modelProjection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_def]
  all_goals rfl

#print axioms deltaGate_value
end models

section standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

/-- On the standard numbers the gate code is the unguarded gate of the upstream PA196
development. -/
theorem eval_deltaGate (a b c : Nat) :
    eval deltaGate (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil) = PA196.Commands.Code.bundle a b c := by
  have hh := deltaGate_value (M := Nat) a b c
  change eval deltaGate (List.Vector.ofFn ![a,b,c]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [memVacValue, separationTailValue, separationValue, pointValue, conjValue,
    PA196.Commands.Code.bundle, PA196.Commands.Code.eqVac, PA196.Commands.Code.memVac,
    PA196.Commands.Code.separationTail, PA196.Commands.Code.separation,
    PA196.Commands.Code.point, PA196.Commands.Code.conj,
    (primitive_standard _ _).1, (primitive_standard _ _).2.1, (primitive_standard _ 0).2.2.1,
    (primitive_standard _ _).2.2.2.2.1, (primitive_standard _ _).2.2.2.2.2]

#print axioms eval_deltaGate
end standard
end PA194EmitterStandard
