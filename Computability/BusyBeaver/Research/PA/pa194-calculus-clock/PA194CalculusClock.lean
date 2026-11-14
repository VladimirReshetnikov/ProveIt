import PA194CalculusSoundness
import PA194CommandClock
set_option autoImplicit false
namespace PA194CalculusClock
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

theorem explicit_clock_iff_refutable :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔ PA194CalculusSoundness.Proved 1 :=
  PA194CommandClock.explicit_clock_iff_scheduler.trans PA194CalculusSoundness.initial_halts_iff_refutable

theorem bounded_clock_iff_refutable :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔ PA194CalculusSoundness.Proved 1 :=
  PA194CommandClock.bounded_clock_iff_scheduler.trans PA194CalculusSoundness.initial_halts_iff_refutable

#print axioms explicit_clock_iff_refutable
#print axioms bounded_clock_iff_refutable
end PA194CalculusClock
