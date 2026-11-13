module
public import M6.Source.Semantics

@[expose] public section

namespace M6.Source

def run (sites : Array Site) : Nat → Configuration → Configuration
  | 0, c => c
  | n+1, c => run sites n (step sites c)

theorem Steps.eq_run (h : Steps sites n a b) : run sites n a = b := by
  induction h with
  | refl => rfl
  | cons h ih => exact ih

theorem run_stable (h : step sites c = c) (n : Nat) : run sites n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [run, h] using ih

theorem stable_steps (h : step sites c = c) (n : Nat) : Steps sites n c c := by
  induction n with
  | zero => exact Steps.refl _
  | succ n ih => exact Steps.cons (h.symm ▸ ih)

theorem Steps.append (ab : Steps sites n a b) (bc : Steps sites m b c) :
    Steps sites (n+m) a c := by
  induction ab with
  | refl => simpa using bc
  | cons h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons (ih bc)

/-- Distinct absorbing outcomes cannot both be reached, even at different times. -/
theorem stable_outcomes_unique (ab : Steps sites n a b) (ac : Steps sites m a c)
    (hb : step sites b = b) (hc : step sites c = c) : b = c := by
  have h₁ := (ab.append (stable_steps hb m)).eq_run
  have h₂ := (ac.append (stable_steps hc n)).eq_run
  rw [Nat.add_comm m n] at h₂
  exact h₁.symm.trans h₂

def Halts (sites : Array Site) (c : Configuration) : Prop :=
  ∃ n r, Steps sites n c ⟨.halted,r⟩

end M6.Source

