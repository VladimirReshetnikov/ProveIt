import PA194ClockSourceConditional
import PA194StartupComplete

/-! Standard-model clock/source equivalences with checked startup. -/
set_option autoImplicit false
namespace PA194ClockSourceStartup
open M6.Source PA194SeedBridge PA194SourceProgram
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

theorem startup : M6.Zip.Reach PA194RuntimeEngine.machine blank seedFrame := by
  change M6.Zip.Reach PA194RuntimeEngine.machine PA194StartupData.blank PA194StartupData.seedFrame
  exact PA194StartupComplete.startup_reach

theorem clock_iff_source_of_coverage
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673) :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, readFile seedFile⟩ :=
  PA194ClockSourceConditional.clock_iff_source hcoverage startup

theorem explicit_clock_iff_source_of_coverage
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673) :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, readFile seedFile⟩ :=
  PA194ClockSourceConditional.explicit_clock_iff_source hcoverage startup

#print axioms startup
#print axioms clock_iff_source_of_coverage
#print axioms explicit_clock_iff_source_of_coverage
end PA194ClockSourceStartup
