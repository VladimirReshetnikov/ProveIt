import Mathlib.Logic.Function.Iterate

/-!
Shared iteration facts for the five annotated numeric scanner families.
The definition matches their existing Nat.rec implementation exactly.
This is an additive, checked interface, not a replacement proof of any
scanner's local checker soundness or primitive-recursive program realization.
-/
namespace DiophantineConsistency.ScannerCore

universe u
variable {S : Type u}

def scan (step : S → S) (fuel : Nat) (initial : S) : S :=
  fuel.rec initial (fun _ acc => step acc)

@[simp] theorem scan_zero (step : S → S) (initial : S) :
    scan step 0 initial = initial := rfl

theorem scan_succ (step : S → S) (fuel : Nat) (initial : S) :
    scan step (fuel + 1) initial = scan step fuel (step initial) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact congrArg step ih

theorem scan_fixed (step : S → S) {initial : S}
    (h : step initial = initial) (fuel : Nat) :
    scan step fuel initial = initial := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact (congrArg step ih).trans h

theorem scan_invariant (step : S → S) (P : S → Prop)
    (hstep : ∀ s, P s → P (step s)) {initial : S} (h : P initial)
    (fuel : Nat) : P (scan step fuel initial) := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact hstep _ ih

/-- A rejecting state can be included without assuming the input parses. -/
theorem scan_reject_or_invariant (step : S → S) (reject : S)
    (Good : S → Prop) (hreject : step reject = reject)
    (hstep : ∀ s, Good s → step s = reject ∨ Good (step s))
    {initial : S} (h : Good initial) (fuel : Nat) :
    scan step fuel initial = reject ∨ Good (scan step fuel initial) := by
  apply scan_invariant step (fun s => s = reject ∨ Good s) ?_ (Or.inr h) fuel
  intro s hs
  rcases hs with rfl | hs
  · exact Or.inl hreject
  · exact hstep s hs

/-- The old raw recursion can use the shared lemma without a definition change. -/
example (step : Nat → Nat) (hzero : step 0 = 0) (fuel : Nat) :
    fuel.rec 0 (fun _ acc => step acc) = 0 :=
  scan_fixed step hzero fuel

#print axioms scan_succ
#print axioms scan_fixed
#print axioms scan_invariant
#print axioms scan_reject_or_invariant

end DiophantineConsistency.ScannerCore
