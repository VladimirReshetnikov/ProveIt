import DiophantineConsistency.WangMachineTraceBounds

/-! Sharp endpoint, halt-entry, stationary-halt, and unnormalized-tape checks. -/

namespace DiophantineConsistency.WangMachineTraceBoundsChecks

open SetTheory.BusyBeaver WangMachineTraceBounds

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private def enterHalt (m : Move) : Machine 1 where
  transition _ _ := ⟨true,m,none⟩

-- Entering halt still writes at 0 and moves to 1, whose old bit remains blank.
example : ((enterHalt .right).run 1).state = none ∧
    ((enterHalt .right).run 1).head = 1 ∧
    Tape.read ((enterHalt .right).run 1).tape 0 = true ∧
    Tape.read ((enterHalt .right).run 1).tape 1 = false := by decide +kernel

-- The opposite boundary also needs the inclusive head bound.
example : ((enterHalt .left).run 1).state = none ∧
    ((enterHalt .left).run 1).head = -1 ∧
    Tape.read ((enterHalt .left).run 1).tape 0 = true ∧
    Tape.read ((enterHalt .left).run 1).tape (-1) = false := by decide +kernel

-- Later halted steps neither move the head nor clear the written bit.
example (m : Move) (t : ℕ) : (enterHalt m).run (1+t) = (enterHalt m).run 1 := by
  apply run_eq_of_halted (enterHalt m) 1
  · cases m <;> rfl
  · omega

-- The tape bound cannot uniformly be tightened from |x|≥t to |x|≥t−1.
example : ¬ (∀ x : ℤ, (0 : ℤ) ≤ |x| →
    Tape.read ((enterHalt .right).run 1).tape x = false) := by
  intro h
  have hc := h 0 (by decide)
  have hv : Tape.read ((enterHalt .right).run 1).tape 0 = true := by decide +kernel
  rw [hv] at hc
  contradiction

-- No Nodup/support normalization is required for arbitrary initial tape reads.
example (M : Machine 1) :
    Tape.read (M.runFrom ⟨some (0 : Fin 1),7,[100,100]⟩ 10).tape 100 = true := by
  rw [runFrom_read_outside M _ 10 100 (by right; decide)]
  decide

-- A zero-state machine is already halted at the blank initial configuration.
example (M : Machine 0) (t : ℕ) : M.run t = initial 0 := by
  rw [run_eq_runFrom_initial]
  exact M.runFrom_of_halted (initial 0) rfl t

-- The time-zero sharp support bound includes the origin itself.
example {n : ℕ} (M : Machine n) (x : ℤ) : Tape.read (M.run 0).tape x = false :=
  run_read_of_abs_ge M 0 x (abs_nonneg x)

-- Left and right widths need not be equal, minimal, or related by divisibility.
example {n : ℕ} (M : Machine n) (T t : ℕ) (ht : t ≤ T) :
    -((T : ℤ)+2) < (M.run t).head ∧ (M.run t).head < (T : ℤ)+9 ∧
    ∀ x : ℤ, x ≤ -((T : ℤ)+2) ∨ (T : ℤ)+9 ≤ x →
      Tape.read (M.run t).tape x = false := by
  simpa using finite_trace_box M T (T+2) (T+9) (by omega) (by omega) t ht

-- A finite halt time yields the same blank walls for arbitrary later times.
example {n : ℕ} (M : Machine n) (T : ℕ) (hh : (M.run T).state = none) (t : ℕ) :
    -((T : ℤ)+1) < (M.run t).head ∧ (M.run t).head < (T : ℤ)+1 := by
  obtain ⟨hl,hr,_⟩ := halted_trace_box M T (T+1) (T+1) hh (by omega) (by omega) t
  exact ⟨by simpa using hl,by simpa using hr⟩

#print axioms step_head_bounds
#print axioms step_read_of_ne
#print axioms runFrom_head_bounds
#print axioms runFrom_read_outside
#print axioms run_eq_runFrom_initial
#print axioms run_head_bounds
#print axioms run_head_abs_le
#print axioms run_read_outside
#print axioms run_read_of_abs_ge
#print axioms finite_trace_box
#print axioms finite_trace_margins
#print axioms run_eq_of_halted
#print axioms halted_trace_box

end DiophantineConsistency.WangMachineTraceBoundsChecks
