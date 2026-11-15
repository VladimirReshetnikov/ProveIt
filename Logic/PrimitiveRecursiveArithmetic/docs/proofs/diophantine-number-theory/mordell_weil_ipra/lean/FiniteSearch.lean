import Std

/-!
Finite search used by the constructive descent interface.
These are native Lean lemmas, not iPRA object-language derivations.
Every recursion is over a supplied finite list; no unbounded search occurs.
-/

namespace MordellWeilIPRA.FiniteSearch

universe u

def first? {α : Type u} (test : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if test x = true then some x else first? test xs

theorem first_sound {α : Type u} (test : α → Bool)
    (xs : List α) (x : α) (hx : first? test xs = some x) :
    x ∈ xs ∧ test x = true := by
  induction xs with
  | nil => simp [first?] at hx
  | cons y ys ih =>
      by_cases hy : test y = true
      · simp only [first?, hy, ↓reduceIte] at hx
        have heq : y = x := Option.some.inj hx
        subst x
        exact ⟨by simp, hy⟩
      · simp only [first?, hy] at hx
        obtain ⟨hmem, htest⟩ := ih hx
        exact ⟨List.mem_cons_of_mem y hmem, htest⟩

theorem first_complete {α : Type u} (test : α → Bool)
    (xs : List α) (hex : ∃ x, x ∈ xs ∧ test x = true) :
    ∃ x, first? test xs = some x ∧ test x = true ∧ x ∈ xs := by
  induction xs with
  | nil => simp at hex
  | cons y ys ih =>
      by_cases hy : test y = true
      · refine ⟨y, ?_, hy, ?_⟩
        · simp [first?, hy]
        · simp
      · have htail : ∃ x, x ∈ ys ∧ test x = true := by
          obtain ⟨x, hmem, htest⟩ := hex
          rcases List.mem_cons.mp hmem with heq | hrest
          · subst x
            exact False.elim (hy htest)
          · exact ⟨x, hrest, htest⟩
        obtain ⟨x, hfind, htest, hmem⟩ := ih htail
        refine ⟨x, ?_, htest, List.mem_cons_of_mem y hmem⟩
        simp [first?, hy, hfind]

/-- The default makes the search total even when the promise fails. -/
def select {α : Type u} (test : α → Bool) (fallback : α)
    (xs : List α) : α :=
  (first? test xs).getD fallback

theorem select_correct {α : Type u} (test : α → Bool)
    (fallback : α) (xs : List α)
    (hex : ∃ x, x ∈ xs ∧ test x = true) :
    test (select test fallback xs) = true ∧
      select test fallback xs ∈ xs := by
  obtain ⟨x, hfind, htest, hmem⟩ := first_complete test xs hex
  simpa [select, hfind] using And.intro htest hmem

def bounded (test : Nat → Bool) (bound : Nat) : Nat :=
  select test 0 (List.range bound)

theorem bounded_correct (test : Nat → Bool) (bound : Nat)
    (hex : ∃ i, i < bound ∧ test i = true) :
    test (bounded test bound) = true ∧ bounded test bound < bound := by
  have hlist : ∃ i, i ∈ List.range bound ∧ test i = true := by
    obtain ⟨i, hib, hit⟩ := hex
    exact ⟨i, List.mem_range.mpr hib, hit⟩
  have h := select_correct test 0 (List.range bound) hlist
  simpa [bounded] using h

end MordellWeilIPRA.FiniteSearch
