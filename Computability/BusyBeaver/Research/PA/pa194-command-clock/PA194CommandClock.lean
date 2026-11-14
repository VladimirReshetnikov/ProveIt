import PA194CommandEquiv
import PA194ClockSourceComplete
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194CommandClock
open M6.Source PA194CommandRegisters PA194CommandRun PA194CommandEquiv PA194ClockCanonical
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

def initial : State := ⟨2,0,⟨0,0,0,0⟩⟩

theorem initial_config : config initial = ⟨.at 25, initialStore⟩ := by
  simp only [config,initial,commandConfig,Configuration.mk.injEq,true_and]
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rfl

theorem bounded_clock_iff_scheduler :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔ Halts initial := by
  rw [PA194ClockSourceComplete.clock_iff_source, ←initial_config, ←halts_iff]

theorem explicit_clock_iff_scheduler :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔ Halts initial := by
  rw [PA194ClockSourceComplete.explicit_clock_iff_source, ←initial_config, ←halts_iff]

#print axioms initial_config
#print axioms bounded_clock_iff_scheduler
#print axioms explicit_clock_iff_scheduler
end PA194CommandClock
