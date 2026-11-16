module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXFullPlan
public import PA196.Arithmetic.Scheduler.InternalAXGate
public import PA196.Arithmetic.Scheduler.InternalAXActualProfile
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

/-- The exact PA196 AX body and gate, over arbitrary PA-model
registers and with the repaired actual profile. -/
theorem encoded (t c d h y x tail bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 50 ⟨t,c,d,h,SourceCantorInternal.pairValue y (SourceCantorInternal.pairValue x tail),[]⟩ bottom n)
      (config 3799 ⟨CommandStep.gateValue (h+y) (d+x) c d,0,0,0,tail,
        CommandStep.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ bottom n) := by
  obtain ⟨k,cs,hk,hc⟩ := actual_pre_gate (valuation t c d h y x) tail bottom n
  rw [initial_profile,actual_profile] at hc
  obtain ⟨l,ds,hl,hd⟩ := gate
    (⟨ActualArithmeticGraph.eval HeadGraphs.bundleExpr (h+y) (d+x) c d,
      c,d+x,h+y,tail,CommandStep.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ : Store V) bottom n
  obtain ⟨es,he⟩ := CodedSource.trace_compose hc hd
  refine ⟨k+l,es,lt_of_lt_of_le hk (by simp),?_⟩
  have hv : (if d+x=c ∨ h+y=c then 0 else ActualArithmeticGraph.eval HeadGraphs.bundleExpr (h+y) (d+x) c d)=
      CommandStep.gateValue (h+y) (d+x) c d := by
    by_cases ha : c=d+x <;> by_cases hb : c=h+y <;>
      simp [CommandStep.gateValue,ha,hb,eq_comm]
  simpa only [hv] using he

/-- Covers every source-Cantor field value, including the zero alias. -/
theorem decoded (t c d h fields bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 50 ⟨t,c,d,h,fields,[]⟩ bottom n)
      (config 3799
        ⟨CommandStep.gateValue
            (h+SourceCantorInternal.decodeLeft fields)
            (d+SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields)) c d,0,0,0,
          SourceCantorInternal.decodeRight (SourceCantorInternal.decodeRight fields),
          CommandStep.schemaHeads
            (d+SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields))
            (h+SourceCantorInternal.decodeLeft fields) c d h ++ [t]⟩ bottom n) := by
  have hrun := encoded t c d h (SourceCantorInternal.decodeLeft fields)
    (SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields))
    (SourceCantorInternal.decodeRight (SourceCantorInternal.decodeRight fields)) bottom n
  simpa only [SourceCantorInternal.pairValue_decode] using hrun
#print axioms encoded
#print axioms decoded
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX

