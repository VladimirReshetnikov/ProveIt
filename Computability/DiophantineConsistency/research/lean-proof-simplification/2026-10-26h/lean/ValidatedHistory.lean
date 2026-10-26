import Init

/-!
A shared proof interface for AnnotatedProofChecker, AnnotatedRename and
AnnotatedBound. Input rows and stored history elements may have different types.
-/
namespace ProofSimplification.ValidatedHistory

variable {I S : Type}

def run (valid : I → List S → Bool) (output : I → S) : List I → List S → Option (List S)
  | [], seen => some seen
  | row :: rows, seen =>
      if valid row seen then run valid output rows (output row :: seen) else none

theorem run_append (valid : I → List S → Bool) (output : I → S)
    (p q : List I) (seen : List S) :
    run valid output (p ++ q) seen = (run valid output p seen).bind (run valid output q) := by
  induction p generalizing seen with
  | nil => rfl
  | cons row rows ih => simp only [List.cons_append, run]; split <;> simp_all

theorem run_sound (valid : I → List S → Bool) (output : I → S) (P : S → Prop)
    (local_sound : ∀ row seen, (∀ a ∈ seen, P a) → valid row seen = true → P (output row))
    (rows : List I) (seen result : List S) (hs : ∀ a ∈ seen, P a)
    (hr : run valid output rows seen = some result) : ∀ a ∈ result, P a := by
  induction rows generalizing seen with
  | nil => cases hr; exact hs
  | cons row rows ih =>
      simp only [run] at hr
      split at hr
      next h =>
        apply ih _ _ hr
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact local_sound row seen hs h
        · exact hs a ha
      next h => contradiction

def Produces (valid : I → List S → Bool) (output : I → S)
    (rows : List I) (history : List S) : Prop :=
  ∀ seen, run valid output rows seen = some (history ++ seen)

theorem Produces.append {valid : I → List S → Bool} {output : I → S}
    {p q : List I} {hp hq : List S}
    (h1 : Produces valid output p hp) (h2 : Produces valid output q hq) :
    Produces valid output (p ++ q) (hq ++ hp) := by
  intro seen
  rw [run_append, h1 seen]
  simp only [Option.bind_some]
  rw [h2 (hp ++ seen), List.append_assoc]

theorem Produces.step {valid : I → List S → Bool} {output : I → S}
    {p : List I} {history : List S} (hp : Produces valid output p history) (row : I)
    (hv : ∀ seen, valid row (history ++ seen) = true) :
    Produces valid output (p ++ [row]) (output row :: history) := by
  intro seen
  rw [run_append, hp seen]
  simp only [Option.bind_some, run, hv seen, if_true, List.cons_append]

#print axioms run_append
#print axioms run_sound
#print axioms Produces.append
#print axioms Produces.step

/- Exact recursion shapes of the concrete modules, retained unchanged. -/
namespace Specialization

def rowRun (valid : S → List S → Bool) : List S → List S → Option (List S)
  | [], seen => some seen
  | row :: rows, seen => if valid row seen then rowRun valid rows (row :: seen) else none

theorem rowRun_eq (valid : S → List S → Bool) : rowRun valid = run valid id := by
  funext rows seen
  induction rows generalizing seen with
  | nil => rfl
  | cons row rows ih => simp only [rowRun, run, id_eq]; split <;> simp_all

example (valid : S → List S → Bool) (p q seen : List S) :
    rowRun valid (p ++ q) seen = (rowRun valid p seen).bind (rowRun valid q) := by
  simpa only [rowRun_eq] using run_append valid id p q seen

example (valid : S → List S → Bool) (P : S → Prop)
    (local_sound : ∀ row seen, (∀ a ∈ seen, P a) → valid row seen = true → P row)
    (rows seen result : List S) (hs : ∀ a ∈ seen, P a)
    (hr : rowRun valid rows seen = some result) : ∀ a ∈ result, P a := by
  rw [rowRun_eq] at hr
  exact run_sound valid id P local_sound rows seen result hs hr

def judgmentRun (valid : I → List S → Bool) (output : I → S) :
    List I → List S → Option (List S)
  | [], seen => some seen
  | line :: lines, seen =>
      if valid line seen then judgmentRun valid output lines (output line :: seen) else none

theorem judgmentRun_eq (valid : I → List S → Bool) (output : I → S) :
    judgmentRun valid output = run valid output := by
  funext rows seen
  induction rows generalizing seen with
  | nil => rfl
  | cons row rows ih => simp only [judgmentRun, run]; split <;> simp_all

example (valid : I → List S → Bool) (output : I → S) (p q : List I) (seen : List S) :
    judgmentRun valid output (p ++ q) seen =
      (judgmentRun valid output p seen).bind (judgmentRun valid output q) := by
  simpa only [judgmentRun_eq] using run_append valid output p q seen

end Specialization

end ProofSimplification.ValidatedHistory
