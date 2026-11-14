import PA194ClockSourceStartup
import PA194SeedFacts
set_option autoImplicit false
namespace PA194ClockCanonical
open M6.Source PA194SeedBridge PA194SourceProgram
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

def initialStore (r : Fin 9) : Nat := if r.val = 0 then 2 else 0

theorem seed_store : readFile seedFile = initialStore := by
  funext r
  exact PA194SeedFacts.logical_seed r

theorem clock_iff_source_of_coverage
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673) :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, initialStore⟩ := by
  simpa only [seed_store] using PA194ClockSourceStartup.clock_iff_source_of_coverage hcoverage

theorem explicit_clock_iff_source_of_coverage
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673) :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, initialStore⟩ := by
  simpa only [seed_store] using PA194ClockSourceStartup.explicit_clock_iff_source_of_coverage hcoverage

#print axioms seed_store
#print axioms clock_iff_source_of_coverage
#print axioms explicit_clock_iff_source_of_coverage
end PA194ClockCanonical
