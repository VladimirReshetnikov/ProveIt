module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXPlan
public import PA196.Arithmetic.Scheduler.AXTypedFullPlan
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
/-- All264 actual macros, stopping before the separate35-row final gate. -/
theorem actual_pre_gate (v : Fin 6 → V) (tail bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 50 (materialize v tail Source.AXSymbolic.initial) bottom n)
      (config 3658 (materialize v tail PA196.Source.AXSymbolic.result) bottom n) :=
  plan_positive PA196.Arithmetic.Scheduler.AXBindings.full_plan (by decide) _ _ (run_actual v tail) bottom n
#print axioms actual_pre_gate
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX

