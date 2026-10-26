/-!
# A reusable proof interface for bounded encoded-list scanners

This file deliberately imports only Lean's default prelude. The existing
numeric scanners can keep their definitions and exact supplied PR programs.
The interface requires their concrete one-step equations, and therefore does
not infer raw-code soundness from a parser or alter accepted inputs.

Prototype created against ProveIt commit
60e9c5d620c6c387d932876cfa2d9376f64ea56c.
-/

namespace ProofRefactor.ScannerCore

universe u v w

def iterate {S : Type u} (step : S → S) (fuel : Nat) (initial : S) : S :=
  fuel.rec initial (fun _ state => step state)

theorem iterate_succ {S : Type u} (step : S → S) (fuel : Nat) (initial : S) :
    iterate step (fuel + 1) initial = iterate step fuel (step initial) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (iterate step (fuel + 1) initial) =
      step (iterate step fuel (step initial))
    rw [ih]

theorem iterate_fixed {S : Type u} (step : S → S) (fuel : Nat) (state : S)
    (h : step state = state) : iterate step fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (iterate step fuel state) = state
    rw [ih, h]

theorem iterate_invariant {S : Type u} (step : S → S) (P : S → Prop)
    (preserved : ∀ s, P s → P (step s)) (fuel : Nat) (initial : S)
    (h : P initial) : P (iterate step fuel initial) := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact preserved _ ih

/-- Backward validity is useful when a scanner consumes both sides of a
relation. It keeps soundness over arbitrary raw initial states. -/
theorem iterate_preimage {S : Type u} (step : S → S) (P : S → Prop)
    (reflected : ∀ s, P (step s) → P s) (fuel : Nat) (initial : S)
    (h : P (iterate step fuel initial)) : P initial := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact ih (reflected _ h)

/-- Typed list execution. Failed rows abort, while an empty list is done. -/
def run {A : Type u} {H : Type v} (next : A → H → Option H) :
    List A → H → Option H
  | [], history => some history
  | row :: rows, history => (next row history).bind (run next rows)

theorem run_append {A : Type u} {H : Type v} (next : A → H → Option H)
    (rows more : List A) (history : H) :
    run next (rows ++ more) history =
      (run next rows history).bind (run next more) := by
  induction rows generalizing history with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.cons_append, run]
    cases h : next row history with
    | none => rfl
    | some updated => exact ih updated

theorem run_invariant {A : Type u} {H : Type v}
    (next : A → H → Option H) (P : H → Prop)
    (preserved : ∀ row history result,
      P history → next row history = some result → P result)
    (rows : List A) (history result : H) (initial : P history)
    (accepted : run next rows history = some result) : P result := by
  induction rows generalizing history with
  | nil =>
    cases accepted
    exact initial
  | cons row rows ih =>
    simp only [run] at accepted
    cases h : next row history with
    | none => simp only [h, Option.bind_none] at accepted; contradiction
    | some updated =>
      simp only [h, Option.bind_some] at accepted
      exact ih updated (preserved row history updated initial h) accepted

/-- Only the concrete boundary equations belong to each implementation. -/
structure Encoding {A : Type u} {H : Type v} {S : Type w}
    (next : A → H → Option H) (step : S → S) where
  state : List A → H → S
  reject : S
  reject_fixed : step reject = reject
  done_fixed : ∀ history, step (state [] history) = state [] history
  cons_step : ∀ row rows history,
    step (state (row :: rows) history) =
      match next row history with
      | none => reject
      | some updated => state rows updated

def Encoding.result {A : Type u} {H : Type v} {S : Type w}
    {next : A → H → Option H} {step : S → S}
    (e : Encoding next step) : Option H → S
  | none => e.reject
  | some history => e.state [] history

/-- Once enough rows have been consumed, further fuel cannot change the result. -/
theorem scan_run {A : Type u} {H : Type v} {S : Type w}
    {next : A → H → Option H} {step : S → S}
    (e : Encoding next step) (rows : List A) (history : H) (fuel : Nat)
    (enough : rows.length ≤ fuel) :
    iterate step fuel (e.state rows history) = e.result (run next rows history) := by
  induction rows generalizing history fuel with
  | nil => exact iterate_fixed step fuel _ (e.done_fixed history)
  | cons row rows ih =>
    cases fuel with
    | zero => cases enough
    | succ fuel =>
      have enough' : rows.length ≤ fuel := Nat.le_of_succ_le_succ enough
      rw [iterate_succ, e.cons_step]
      cases h : next row history with
      | none =>
        simp only [h, run, Option.bind_none, Encoding.result]
        exact iterate_fixed step fuel _ e.reject_fixed
      | some updated =>
        simp only [h, run, Option.bind_some]
        exact ih updated fuel enough'

end ProofRefactor.ScannerCore
