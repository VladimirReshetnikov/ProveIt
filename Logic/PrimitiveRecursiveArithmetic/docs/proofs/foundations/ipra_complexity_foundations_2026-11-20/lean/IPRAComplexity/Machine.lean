import Std

namespace IPRAComplexity

/-- A fixed deterministic transition system. Arithmetic instances use coded states. -/
structure Machine (State : Type) where
  step : State → State
  accepts : State → Bool
  /-- Accepting states are absorbing, so increasing a clock preserves acceptance. -/
  accept_absorbing : ∀ s, accepts s = true → step s = s

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

theorem iterate_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iterate f (a + b) x = iterate f b (iterate f a x) := by
  induction b with
  | zero => simp [iterate]
  | succ b ih => simp [iterate, ih]

theorem iterate_fixed {α : Type} (f : α → α) (s : α)
    (h : f s = s) (n : Nat) : iterate f n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterate, ih, h]

def Machine.acceptWithin {State : Type} (M : Machine State)
    (clock : Nat) (initial : State) : Bool :=
  M.accepts (iterate M.step clock initial)

theorem Machine.acceptWithin_add {State : Type} (M : Machine State)
    (t u : Nat) (s : State) (h : M.acceptWithin t s = true) :
    M.acceptWithin (t + u) s = true := by
  unfold Machine.acceptWithin at h ⊢
  rw [iterate_add, iterate_fixed M.step _ (M.accept_absorbing _ h)]
  exact h

theorem Machine.acceptWithin_mono {State : Type} (M : Machine State)
    (s : State) {t u : Nat} (h : t ≤ u)
    (ha : M.acceptWithin t s = true) : M.acceptWithin u s = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact M.acceptWithin_add t d s ha

/-- A finite trace is checked against its initial point and every adjacent pair. -/
def TraceOK {State : Type} (step : State → State)
    (initial : State) (trace : Nat → State) (t : Nat) : Prop :=
  trace 0 = initial ∧ ∀ i, i < t → trace (i + 1) = step (trace i)

theorem trace_unique {State : Type} (step : State → State)
    (initial : State) (trace : Nat → State) (t : Nat)
    (h : TraceOK step initial trace t) :
    ∀ i, i ≤ t → trace i = iterate step i initial := by
  intro i
  induction i with
  | zero => intro _; exact h.1
  | succ i ih =>
    intro hi
    rw [h.2 i (by omega), ih (by omega)]
    rfl

/-- A concrete arithmetic machine used as an executable example. -/
def countdown : Machine Nat where
  step := fun n => n - 1
  accepts := fun n => n == 0
  accept_absorbing := by
    intro s hs
    have : s = 0 := by simpa using hs
    subst s
    rfl

example : countdown.acceptWithin 7 5 = true := by decide
example : countdown.acceptWithin 4 5 = false := by decide

end IPRAComplexity
