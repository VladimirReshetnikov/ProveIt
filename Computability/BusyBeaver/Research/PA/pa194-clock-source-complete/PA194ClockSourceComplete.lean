import PA194ClockCanonical
import PA194CoverageComplete

/-! Standard natural-number source meaning of the exact PA194 clocks. -/
set_option autoImplicit false
namespace PA194ClockSourceComplete
open M6.Source PA194SourceProgram PA194ClockCanonical
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

theorem clock_iff_source :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, initialStore⟩ :=
  PA194ClockCanonical.clock_iff_source_of_coverage PA194CoverageComplete.coverage

theorem explicit_clock_iff_source :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, initialStore⟩ :=
  PA194ClockCanonical.explicit_clock_iff_source_of_coverage PA194CoverageComplete.coverage

#print axioms clock_iff_source
#print axioms explicit_clock_iff_source
end PA194ClockSourceComplete
