module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXFullPlan
public import M6PA.Scheduler.InternalAXGate
public import M6PA.Scheduler.InternalAXActualProfile
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Every one of the3779 actual AX source leaves, over arbitrary PA-model
registers and with the repaired actual profile. -/
theorem encoded (t c d h y x tail bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 25 ⟨t,c,d,h,SourceCantorInternal.pairValue y (SourceCantorInternal.pairValue x tail),[]⟩ bottom n)
      (config 3910 ⟨ActualCommandStepGraph.gateValue (d+x) (h+y) c d,0,0,0,tail,
        ActualCommandStepGraph.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ bottom n) := by
  obtain ⟨k,cs,hk,hc⟩ := actual_pre_gate (valuation t c d h y x) tail bottom n
  rw [initial_profile,actual_profile] at hc
  obtain ⟨l,ds,hl,hd⟩ := gate
    (⟨ActualArithmeticGraph.eval ActualHeadGraphs.bundleExpr (d+x) (h+y) c d,
      c,d+x,h+y,tail,ActualCommandStepGraph.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ : Store V) bottom n
  obtain ⟨es,he⟩ := CodedSource.trace_compose hc hd
  refine ⟨k+l,es,lt_of_lt_of_le hk (by simp),?_⟩
  have hv : (if d+x=c ∨ h+y=c then 0 else ActualArithmeticGraph.eval ActualHeadGraphs.bundleExpr (d+x) (h+y) c d)=
      ActualCommandStepGraph.gateValue (d+x) (h+y) c d := by
    by_cases ha : c=d+x <;> by_cases hb : c=h+y <;>
      simp [ActualCommandStepGraph.gateValue,ha,hb,eq_comm]
  simpa only [hv] using he

/-- Covers every source-Cantor field value, including the zero alias. -/
theorem decoded (t c d h fields bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 25 ⟨t,c,d,h,fields,[]⟩ bottom n)
      (config 3910
        ⟨ActualCommandStepGraph.gateValue
            (d+SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields))
            (h+SourceCantorInternal.decodeLeft fields) c d,0,0,0,
          SourceCantorInternal.decodeRight (SourceCantorInternal.decodeRight fields),
          ActualCommandStepGraph.schemaHeads
            (d+SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields))
            (h+SourceCantorInternal.decodeLeft fields) c d h ++ [t]⟩ bottom n) := by
  have hrun := encoded t c d h (SourceCantorInternal.decodeLeft fields)
    (SourceCantorInternal.decodeLeft (SourceCantorInternal.decodeRight fields))
    (SourceCantorInternal.decodeRight (SourceCantorInternal.decodeRight fields)) bottom n
  simpa only [SourceCantorInternal.pairValue_decode] using hrun
#print axioms encoded
#print axioms decoded
end M6.Arithmetic.PA.InternalTrace.ModelAX

