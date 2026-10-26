import Std

/-!
# A common proof kernel for annotated numeric scanners

This standalone prototype factors only the simulation argument. It does not
change any repository checker, numeric code, or supplied PR program.

Repository instances:
* AnnotatedRenameScan: valid = Row.valid; push = List.cons.
* AnnotatedBoundScan: valid = AnnotatedBound.valid; push = List.cons.
* AnnotatedLineScan.scan_list: valid = (AnnotatedLine.check history line = 1);
  push = the encoded checked output.
* AnnotatedAxiomContext.scan_list: valid = its dispatch check;
  push = the checked formula added to the context code.
-/

namespace RefactorPrototype.Scanner

universe u v
variable {Row : Type u} {History : Type v}

def iterate (step : Nat → Nat) (fuel initial : Nat) : Nat :=
  fuel.rec initial (fun _ acc => step acc)

theorem iterate_succ (step : Nat → Nat) (fuel initial : Nat) :
    iterate step (fuel + 1) initial = iterate step fuel (step initial) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (iterate step (fuel + 1) initial) =
      step (iterate step fuel (step initial))
    rw [ih]

theorem iterate_fixed (step : Nat → Nat) (fuel x : Nat) (hx : step x = x) :
    iterate step fuel x = x := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (iterate step fuel x) = x
    rw [ih, hx]

/-- Raw-state soundness may be proved by a one-step invariant without decoding
the whole remaining input to an external list. -/
theorem iterate_invariant (step : Nat → Nat) (P : Nat → Prop)
    (preserve : ∀ state, P state → P (step state))
    (fuel initial : Nat) (hinitial : P initial) : P (iterate step fuel initial) := by
  induction fuel with
  | zero => exact hinitial
  | succ fuel ih => exact preserve _ ih

/-- The semantic list execution; rejected rows abort. -/
def run (valid : Row → History → Bool) (push : Row → History → History) :
    List Row → History → Option History
  | [], history => some history
  | row :: rows, history =>
    if valid row history then run valid push rows (push row history) else none

/-- All representation-specific arithmetic is confined to these three laws.
The encoded empty history need not be nonzero: this theorem asserts simulation,
not that every terminal numeric value is accepting. -/
structure Implementation (valid : Row → History → Bool)
    (push : Row → History → History) where
  step : Nat → Nat
  encode : List Row → History → Nat
  reject : step 0 = 0
  done : ∀ history, step (encode [] history) = encode [] history
  cons : ∀ row rows history,
    step (encode (row :: rows) history) =
      if valid row history then encode rows (push row history) else 0

/-- The full scanner/list simulation, including excess fuel and rejection. -/
theorem run_simulation (valid : Row → History → Bool)
    (push : Row → History → History) (impl : Implementation valid push)
    (rows : List Row) (history : History) (fuel : Nat)
    (enough : rows.length ≤ fuel) :
    iterate impl.step fuel (impl.encode rows history) =
      match run valid push rows history with
      | none => 0
      | some result => impl.encode [] result := by
  induction rows generalizing history fuel with
  | nil =>
    exact iterate_fixed impl.step fuel (impl.encode [] history) (impl.done history)
  | cons row rows ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have enough' : rows.length ≤ fuel := Nat.le_of_succ_le_succ enough
      rw [iterate_succ, impl.cons]
      by_cases accepted : valid row history = true
      · simpa only [accepted, if_true, run] using ih (push row history) fuel enough'
      · simp only [accepted, run]
        exact iterate_fixed impl.step fuel 0 impl.reject

/-- Successful semantic execution preserves every inductive history invariant. -/
theorem run_invariant (valid : Row → History → Bool)
    (push : Row → History → History) (P : History → Prop)
    (preserve : ∀ row history, P history → valid row history = true →
      P (push row history))
    (rows : List Row) (history result : History)
    (initial : P history) (success : run valid push rows history = some result) :
    P result := by
  induction rows generalizing history with
  | nil => cases success; exact initial
  | cons row rows ih =>
    simp only [run] at success
    split at success
    next accepted =>
      exact ih (push row history) (preserve row history initial accepted) success
    next rejected => contradiction

#print axioms run_simulation
#print axioms run_invariant
#print axioms iterate_invariant

end RefactorPrototype.Scanner
