module
public import M6.Source.CyclicDriver
@[expose] public section

namespace M6.Source

def cycleRun (sites : Array Site) : Nat → Configuration → Configuration
  | 0,c => c
  | n+1,c => cycleRun sites n (cycleStep sites c)

theorem CycleSteps.eq_run (h : CycleSteps sites n a b) : cycleRun sites n a = b := by
  induction h with
  | refl => rfl
  | cons _ ih => exact ih

theorem cycleRun_add (n m : Nat) (c : Configuration) :
    cycleRun sites (n+m) c = cycleRun sites m (cycleRun sites n c) := by
  induction n generalizing c with
  | zero => simp [cycleRun]
  | succ n ih => simpa only [Nat.succ_add,cycleRun] using ih (cycleStep sites c)

theorem cycleRun_stable (h : cycleStep sites c = c) (n : Nat) : cycleRun sites n c = c := by
  induction n with
  | zero => simp [cycleRun]
  | succ n ih => simpa only [cycleRun,h] using ih

private theorem cycle_halt_stable (h : c.control = .halted) : cycleStep sites c = c := by
  rcases c with ⟨q,r⟩
  simp only at h
  subst q
  rfl

def CycleHalts (sites : Array Site) (c : Configuration) : Prop :=
  ∃ n, (cycleRun sites n c).control = .halted

/-- A known finite prefix ending at a nonhalted state preserves and reflects
halting for the restarting source driver. An earlier halt cannot be skipped. -/
theorem cycle_prefix_halting_iff (h : CycleSteps sites n a b) (hb : b.control ≠ .halted) :
    CycleHalts sites a ↔ CycleHalts sites b := by
  constructor
  · rintro ⟨m,hm⟩
    by_cases hnm : n ≤ m
    · refine ⟨m-n,?_⟩
      have he : m = n+(m-n) := by omega
      rw [he,cycleRun_add,h.eq_run] at hm
      exact hm
    · have he : n = m+(n-m) := by omega
      have hs := cycleRun_stable (sites := sites) (cycle_halt_stable hm) (n-m)
      have hh := h.eq_run
      rw [he,cycleRun_add,hs] at hh
      exact False.elim (hb (hh ▸ hm))
  · rintro ⟨m,hm⟩
    refine ⟨n+m,?_⟩
    rw [cycleRun_add,h.eq_run]
    exact hm

#print axioms cycle_prefix_halting_iff
end M6.Source

