module
public import M6.Source.CommandRunTransfer
public import M6.Source.SeedScheduler
@[expose] public section
namespace M6.Source

theorem seed_halts_iff_scheduler :
    CycleHalts exactSites SeedPrefix.seed ↔ CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) := by
  obtain ⟨m,hm,hs⟩ := seed_to_scheduler
  exact cycle_prefix_halting_iff hs (by simp [commandConfig])

theorem intermediate_halts_iff_scheduler :
    CycleHalts exactSites SeedPrefix.intermediate ↔
      CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) :=
  SeedPrefix.halting_iff.symm.trans seed_halts_iff_scheduler

/-- Exact external arithmetic/source calibration, including real startup's
intermediate AX location. PA-internal representability remains separate. -/
theorem intermediate_halts_iff_not_arithmeticSafe :
    CycleHalts exactSites SeedPrefix.intermediate ↔ ¬ Scheduler.ArithmeticSafe := by
  rw [intermediate_halts_iff_scheduler]
  constructor
  · intro hh hs
    exact Scheduler.source_scheduler_nonhalting hs hh
  · intro hn
    exact Classical.byContradiction (fun hno =>
      hn (CommandRunTransfer.arithmeticSafe_iff_source_nonhalting.mpr hno))
#print axioms intermediate_halts_iff_not_arithmeticSafe
end M6.Source

