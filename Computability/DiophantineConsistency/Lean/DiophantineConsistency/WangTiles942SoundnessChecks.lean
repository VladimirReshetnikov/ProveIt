import DiophantineConsistency.WangTiles942Soundness

/-! The actual blank run, strict time bound, arbitrary stride, and small
period obstruction; no machine-run or tiling calibration premise. -/

namespace DiophantineConsistency.WangTiles942SoundnessChecks

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942Periodic WangTiles942Soundness

set_option Elab.async false
set_option maxRecDepth 10000

example {N : ℕ} [NeZero N] (s : ℤ) (a : ZMod N → Fin 942)
    (h : MarkedWord N s a) :
    ∃ t : ℕ, t < N ∧ (DecimalMachine215.machine.run t).state = none :=
  marked_halts_before_period h

example {N : ℕ} [NeZero N] (s : ℤ) (a : ZMod N → Fin 942)
    (h : MarkedWord N s a) : KDenseBridge.BlankHalts DecimalMachine215.machine :=
  marked_blank_halts h

theorem no_marked_of_nonhalting
    (hn : ¬ KDenseBridge.BlankHalts DecimalMachine215.machine)
    {N : ℕ} [NeZero N] (s : ℤ) (a : ZMod N → Fin 942) : ¬ MarkedWord N s a :=
  fun h => hn (marked_blank_halts h)

-- The initialized machine at clock1 is live, so even periods1 and2
-- are excluded without assuming any least-period or unique-marker property.
theorem marked_period_gt_two {N : ℕ} [NeZero N] {s : ℤ}
    {a : ZMod N → Fin 942} (h : MarkedWord N s a) : 2 < N := by
  obtain ⟨t,ht,hh⟩ := marked_halts_before_period h
  by_contra hn
  have hc : t = 0 ∨ t = 1 := by omega
  rcases hc with rfl | rfl
  · change some (0 : Fin 215) = none at hh
    contradiction
  · rw [DecimalMachineInitialization.run_one] at hh
    change some (1 : Fin 215) = none at hh
    contradiction

#print axioms marked_halts_before_period
#print axioms marked_blank_halts
#print axioms no_marked_of_nonhalting
#print axioms marked_period_gt_two

end DiophantineConsistency.WangTiles942SoundnessChecks
