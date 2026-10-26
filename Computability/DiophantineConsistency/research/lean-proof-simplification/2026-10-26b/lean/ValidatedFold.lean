import Std

/-!
# A shared proof kernel for checked history folds

Prototype for ProveIt commit 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
This module does not replace any repository declaration. It isolates the
recursion common to AnnotatedRename, AnnotatedBound, and AnnotatedProofChecker.
It uses Lean's standard library only and makes no model-theoretic assertion.
-/

namespace DiophantineConsistency.Proposals.ValidatedFold

variable {Line Judgment : Type}

def run (valid : Line → List Judgment → Bool) (emit : Line → Judgment) :
    List Line → List Judgment → Option (List Judgment)
  | [], seen => some seen
  | line :: lines, seen =>
      if valid line seen then run valid emit lines (emit line :: seen) else none

theorem run_append (valid : Line → List Judgment → Bool) (emit : Line → Judgment)
    (p q : List Line) (seen : List Judgment) :
    run valid emit (p ++ q) seen =
      (run valid emit p seen).bind (run valid emit q) := by
  induction p generalizing seen with
  | nil => rfl
  | cons line lines ih =>
    simp only [List.cons_append, run]
    split <;> simp_all

theorem run_sound (valid : Line → List Judgment → Bool) (emit : Line → Judgment)
    (P : Judgment → Prop)
    (local_sound : ∀ line seen, (∀ j ∈ seen, P j) →
      valid line seen = true → P (emit line))
    (lines : List Line) (seen result : List Judgment)
    (hseen : ∀ j ∈ seen, P j) (h : run valid emit lines seen = some result) :
    ∀ j ∈ result, P j := by
  induction lines generalizing seen with
  | nil => cases h; exact hseen
  | cons line lines ih =>
    simp only [run] at h
    split at h
    next hv =>
      apply ih _ _ h
      intro j hj
      cases List.mem_cons.mp hj with
      | inl hj => exact hj ▸ local_sound line seen hseen hv
      | inr hj => exact hseen j hj
    next hv => contradiction

def Produces (valid : Line → List Judgment → Bool) (emit : Line → Judgment)
    (lines : List Line) (history : List Judgment) : Prop :=
  ∀ seen, run valid emit lines seen = some (history ++ seen)

theorem Produces.append
    {valid : Line → List Judgment → Bool} {emit : Line → Judgment}
    {p q : List Line} {hp hq : List Judgment}
    (h₁ : Produces valid emit p hp) (h₂ : Produces valid emit q hq) :
    Produces valid emit (p ++ q) (hq ++ hp) := by
  intro seen
  rw [run_append, h₁ seen]
  simp only [Option.bind_some]
  rw [h₂ (hp ++ seen), List.append_assoc]

theorem Produces.step
    {valid : Line → List Judgment → Bool} {emit : Line → Judgment}
    {p : List Line} {history : List Judgment}
    (hp : Produces valid emit p history) (line : Line)
    (hv : ∀ seen, valid line (history ++ seen) = true) :
    Produces valid emit (p ++ [line]) (emit line :: history) := by
  intro seen
  rw [run_append, hp seen]
  simp only [Option.bind_some, run, hv seen, if_true, List.cons_append]

/- The following generic recurrence is definitionally the scan recurrence
used by the repository. It does not require Nat-pairing or a chosen encoding. -/
def scan {State : Type} (step : State → State) (fuel : Nat) (initial : State) : State :=
  fuel.rec initial (fun _ acc => step acc)

theorem scan_succ {State : Type} (step : State → State) (fuel : Nat) (initial : State) :
    scan step (fuel + 1) initial = scan step fuel (step initial) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan step (fuel + 1) initial) = step (scan step fuel (step initial))
    rw [ih]

theorem scan_fixed {State : Type} (step : State → State) (fixed : State)
    (hfixed : step fixed = fixed) (fuel : Nat) : scan step fuel fixed = fixed := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan step fuel fixed) = fixed
    rw [ih, hfixed]

#print axioms run_append
#print axioms run_sound
#print axioms Produces.append
#print axioms Produces.step
#print axioms scan_succ
#print axioms scan_fixed

end DiophantineConsistency.Proposals.ValidatedFold
