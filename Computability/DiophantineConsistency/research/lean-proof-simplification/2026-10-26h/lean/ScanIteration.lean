import Init

/-! A proof-only iteration interface: concrete scanner definitions stay unchanged. -/
namespace ProofSimplification.ScanIteration

theorem rec_succ {α : Sort u} (f : α → α) (n : Nat) (x : α) :
    (n + 1).rec (motive := fun _ => α) x (fun _ acc => f acc) =
      n.rec (motive := fun _ => α) (f x) (fun _ acc => f acc) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

theorem rec_fixed {α : Sort u} (f : α → α) (x : α) (h : f x = x) (n : Nat) :
    n.rec x (fun _ acc => f acc) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg f ih).trans h

/-- This is the exact recursion shape shared by the five annotated scanners. -/
def scan (step : Nat → Nat) (fuel initial : Nat) : Nat :=
  fuel.rec initial (fun _ acc => step acc)

example (step : Nat → Nat) (fuel state : Nat) :
    scan step (fuel+1) state = scan step fuel (step state) :=
  rec_succ step fuel state

example (step : Nat → Nat) (h : step 0 = 0) (fuel : Nat) :
    scan step fuel 0 = 0 :=
  rec_fixed step 0 h fuel

example (step : Nat → Nat) (finished : Nat) (h : step finished = finished) (fuel : Nat) :
    scan step fuel finished = finished :=
  rec_fixed step finished h fuel

#print axioms rec_succ
#print axioms rec_fixed

end ProofSimplification.ScanIteration
