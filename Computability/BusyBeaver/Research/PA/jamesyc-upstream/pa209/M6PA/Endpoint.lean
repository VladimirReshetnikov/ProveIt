module
public import M6PA.Calibration
public import M6.LogicalEndpoint
@[expose] public section
namespace M6.PA
/-- Natural blank nonhalting of the exact reviewed 209-state table under
ordinary first-order PA consistency. This is not yet PA's internal trace
transport or an unprovability theorem for an arithmetic sentence. -/
theorem literal_nonhalting (hcons : Consistent) :
    ¬ Zip.Halts Literal.machine Startup.blank :=
  LogicalEndpoint.blank_nonhalting (no_native_refutation hcons)

theorem literal_nonhalting_endpoint (hcons : Consistent) :
    Literal.workingLabels.length = 209 ∧
    Literal.workingLabels.length * 2 = 418 ∧
    (∀ q b, Literal.machine q b ≠ none → q ∈ Literal.workingLabels) ∧
    (¬ Zip.Halts Literal.machine Startup.blank) :=
  ⟨Literal.working_count,Literal.row_count,fun _ _ h => Bounds.domain h,
    literal_nonhalting hcons⟩

#print axioms literal_nonhalting
#print axioms literal_nonhalting_endpoint
end M6.PA
