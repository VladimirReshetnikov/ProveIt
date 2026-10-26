import BusyBeaver.Core
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Group.Abs

/-!
# Explicit finite bounds for actual blank machine traces

The bounds follow directly from the repository's write-before-move operational
semantics. They include entry into halt and stationary halted steps. No tape
normalization, tiling, or run-calibration hypothesis is used.
-/

namespace DiophantineConsistency.WangMachineTraceBounds

open SetTheory.BusyBeaver

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Every actual step moves by at most one, including a stationary halted step. -/
theorem step_head_bounds {n : ℕ} (M : Machine n) (cfg : Config n) :
    cfg.head - 1 ≤ (M.step cfg).head ∧ (M.step cfg).head ≤ cfg.head + 1 := by
  cases hs : cfg.state with
  | none => simp only [Machine.step, hs]; omega
  | some q =>
      simp only [Machine.step, hs]
      cases hm : (M.transition q (Tape.read cfg.tape cfg.head)).move <;>
        simp only [Move.apply] <;> omega

/-- A step changes no tape read away from its old head, regardless of its next state. -/
theorem step_read_of_ne {n : ℕ} (M : Machine n) (cfg : Config n)
    (x : ℤ) (hx : x ≠ cfg.head) :
    Tape.read (M.step cfg).tape x = Tape.read cfg.tape x := by
  cases hs : cfg.state with
  | none => simp only [Machine.step, hs]
  | some q =>
      simp only [Machine.step, hs]
      exact Tape.read_write_of_ne cfg.tape hx _

/-- Displacement bounds from an arbitrary initial configuration. -/
theorem runFrom_head_bounds {n : ℕ} (M : Machine n) (cfg : Config n) (t : ℕ) :
    cfg.head - (t : ℤ) ≤ (M.runFrom cfg t).head ∧
      (M.runFrom cfg t).head ≤ cfg.head + (t : ℤ) := by
  induction t with
  | zero => simp only [Machine.runFrom, Nat.cast_zero, sub_zero, add_zero, le_refl, and_self]
  | succ t ih =>
      have hs := step_head_bounds M (M.runFrom cfg t)
      rw [Machine.runFrom_succ]
      push_cast
      omega

/-- At the inclusive outer boundary, no write has yet occurred: the last
write used the head before the final move. This needs no support hypothesis. -/
theorem runFrom_read_outside {n : ℕ} (M : Machine n) (cfg : Config n)
    (t : ℕ) (x : ℤ)
    (hx : x ≤ cfg.head - (t : ℤ) ∨ cfg.head + (t : ℤ) ≤ x) :
    Tape.read (M.runFrom cfg t).tape x = Tape.read cfg.tape x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hh := runFrom_head_bounds M cfg t
      have hne : x ≠ (M.runFrom cfg t).head := by omega
      have hold : x ≤ cfg.head - (t : ℤ) ∨ cfg.head + (t : ℤ) ≤ x := by omega
      rw [Machine.runFrom_succ, step_read_of_ne M _ x hne]
      exact ih hold

theorem run_eq_runFrom_initial {n : ℕ} (M : Machine n) (t : ℕ) :
    M.run t = M.runFrom (initial n) t := by
  simpa only [zero_add, Machine.run] using M.run_add_eq_runFrom 0 t

/-- The actual blank-run head is in the closed interval [-t,t]. -/
theorem run_head_bounds {n : ℕ} (M : Machine n) (t : ℕ) :
    -(t : ℤ) ≤ (M.run t).head ∧ (M.run t).head ≤ (t : ℤ) := by
  rw [run_eq_runFrom_initial]
  simpa only [initial, zero_sub, zero_add] using runFrom_head_bounds M (initial n) t

theorem run_head_abs_le {n : ℕ} (M : Machine n) (t : ℕ) :
    |(M.run t).head| ≤ (t : ℤ) := abs_le.mpr (run_head_bounds M t)

/-- Sharp uniform blank-tape support: every position outside (-t,t) reads false. -/
theorem run_read_outside {n : ℕ} (M : Machine n) (t : ℕ) (x : ℤ)
    (hx : x ≤ -(t : ℤ) ∨ (t : ℤ) ≤ x) : Tape.read (M.run t).tape x = false := by
  rw [run_eq_runFrom_initial]
  have he := runFrom_read_outside M (initial n) t x (by
    simpa only [initial, zero_sub, zero_add] using hx)
  simpa only [initial, Tape.read, List.not_mem_nil, ↓reduceIte] using he

theorem run_read_of_abs_ge {n : ℕ} (M : Machine n) (t : ℕ) (x : ℤ)
    (hx : (t : ℤ) ≤ |x|) : Tape.read (M.run t).tape x = false := by
  exact run_read_outside M t x (le_abs'.mp hx)

/-- Independent left and right margins may be enlarged arbitrarily. -/
theorem finite_trace_box {n : ℕ} (M : Machine n) (T L R : ℕ)
    (hL : T < L) (hR : T < R) :
    ∀ t : ℕ, t ≤ T →
      -(L : ℤ) < (M.run t).head ∧ (M.run t).head < (R : ℤ) ∧
      ∀ x : ℤ, x ≤ -(L : ℤ) ∨ (R : ℤ) ≤ x → Tape.read (M.run t).tape x = false := by
  intro t ht
  have hh := run_head_bounds M t
  refine ⟨by omega, by omega, ?_⟩
  intro x hx
  apply run_read_outside M t x
  omega

/-- The concrete walls ±(T+1) enclose every head up to T and remain blank. -/
theorem finite_trace_margins {n : ℕ} (M : Machine n) (T : ℕ) :
    ∀ t : ℕ, t ≤ T →
      -((T : ℤ)+1) < (M.run t).head ∧ (M.run t).head < (T : ℤ)+1 ∧
      Tape.read (M.run t).tape (-((T : ℤ)+1)) = false ∧
      Tape.read (M.run t).tape ((T : ℤ)+1) = false := by
  intro t ht
  obtain ⟨hl,hr,hblank⟩ := finite_trace_box M T (T+1) (T+1) (by omega) (by omega) t ht
  refine ⟨by simpa using hl, by simpa using hr, ?_, ?_⟩
  · exact hblank _ (Or.inl (by omega))
  · exact hblank _ (Or.inr (by omega))

/-- Actual halted configurations remain fixed; no active-step premise is needed. -/
theorem run_eq_of_halted {n : ℕ} (M : Machine n) (T : ℕ)
    (hh : (M.run T).state = none) (t : ℕ) (ht : T ≤ t) : M.run t = M.run T := by
  have he : t = T + (t-T) := by omega
  rw [he, Machine.run_add_eq_runFrom]
  exact M.runFrom_of_halted (M.run T) hh (t-T)

/-- If the trace has halted by T, the same independently chosen margins work
at every later time too. The halt hypothesis is a conclusion to reuse, not an axiom. -/
theorem halted_trace_box {n : ℕ} (M : Machine n) (T L R : ℕ)
    (hh : (M.run T).state = none) (hL : T < L) (hR : T < R) :
    ∀ t : ℕ, -(L : ℤ) < (M.run t).head ∧ (M.run t).head < (R : ℤ) ∧
      ∀ x : ℤ, x ≤ -(L : ℤ) ∨ (R : ℤ) ≤ x → Tape.read (M.run t).tape x = false := by
  intro t
  by_cases ht : t ≤ T
  · exact finite_trace_box M T L R hL hR t ht
  · rw [run_eq_of_halted M T hh t (by omega)]
    exact finite_trace_box M T L R hL hR T (Nat.le_refl T)

end DiophantineConsistency.WangMachineTraceBounds
