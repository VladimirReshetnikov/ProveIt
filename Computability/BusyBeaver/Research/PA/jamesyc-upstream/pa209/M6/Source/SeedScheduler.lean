module
public import M6.Source.SchedulerInvariant
public import M6.Source.SeedPrefix
@[expose] public section
namespace M6.Source

private theorem seed_config : SeedPrefix.seed = commandConfig 25 0 0 0 ⟨1,1,0,0⟩ := by
  apply congrArg (Configuration.mk (.at 25))
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The actual initial AX invocation reaches the arithmetic scheduler's exact
nine-wrapper initial state, including the saved1 over opaque tail4. -/
theorem seed_to_scheduler :
    ∃ m, 0 < m ∧ CycleSteps exactSites m SeedPrefix.seed
      (commandConfig 0 0 0 0 commandInitial) := by
  obtain ⟨m,hm,hs⟩ := ax_command 0 0 0 0 0 ⟨1,1,0,0⟩ commandInitial (by rfl)
  rw [show Cantor.pair 0 (Cantor.pair 0 0) = 0 from rfl] at hs
  exact ⟨m,hm,by simpa only [seed_config] using hs⟩

theorem seed_nonhalting (h : Scheduler.ArithmeticSafe) : ¬ CycleHalts exactSites SeedPrefix.seed := by
  obtain ⟨m,hm,hs⟩ := seed_to_scheduler
  intro hh
  have hout := (cycle_prefix_halting_iff hs (by simp [commandConfig])).mp hh
  exact Scheduler.source_scheduler_nonhalting h hout

theorem intermediate_nonhalting (h : Scheduler.ArithmeticSafe) :
    ¬ CycleHalts exactSites SeedPrefix.intermediate := by
  intro hh
  exact seed_nonhalting h (SeedPrefix.halting_iff.mpr hh)
#print axioms intermediate_nonhalting
end M6.Source

