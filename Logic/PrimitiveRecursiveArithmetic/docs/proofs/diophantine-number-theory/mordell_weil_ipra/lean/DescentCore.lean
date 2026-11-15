import Std

/-!
# Constructive Mordell--Weil descent: the finite-fuel kernel

This file proves a native Lean theorem. It is NOT a derivation in the
first-order iPRA proof calculus. The inputs below are explicit hypotheses;
in particular `decompose` is not a theorem about every elliptic curve.

The executable core uses only primitive recursion on natural-number fuel.
For an iPRA instance, the point representation and every input operation
must separately be supplied by fixed primitive-recursive terms, and the
input laws must separately be proved in the object calculus.

No `axiom`, `sorry`, `Classical`, choice, or unbounded minimization is used.
-/

namespace MordellWeilIPRA

universe u

/-- A compact additive word over two finite families of points.
`double` avoids duplicating an entire child expression in the output. -/
inductive Word (repCount baseCount : Nat) where
  | base : Fin baseCount → Word repCount baseCount
  | representative : Fin repCount → Word repCount baseCount
  | add : Word repCount baseCount → Word repCount baseCount →
      Word repCount baseCount
  | double : Word repCount baseCount → Word repCount baseCount
  deriving Repr, DecidableEq

namespace Word

def eval {α : Type u} {r b : Nat}
    (add : α → α → α) (base : Fin b → α) (rep : Fin r → α) :
    Word r b → α
  | .base i => base i
  | .representative i => rep i
  | .add x y => add (eval add base rep x) (eval add base rep y)
  | .double x => add (eval add base rep x) (eval add base rep x)

/-- Number of constructors in a compact word. -/
def size {r b : Nat} : Word r b → Nat
  | .base _ => 1
  | .representative _ => 1
  | .add x y => 1 + size x + size y
  | .double x => 1 + size x

/-- The nonnegative coefficient of a base generator. -/
def baseCoeff {r b : Nat} (i : Fin b) : Word r b → Nat
  | .base j => if i = j then 1 else 0
  | .representative _ => 0
  | .add x y => baseCoeff i x + baseCoeff i y
  | .double x => 2 * baseCoeff i x

/-- The nonnegative coefficient of a quotient representative. -/
def repCoeff {r b : Nat} (i : Fin r) : Word r b → Nat
  | .base _ => 0
  | .representative j => if i = j then 1 else 0
  | .add x y => repCoeff i x + repCoeff i y
  | .double x => 2 * repCoeff i x

end Word

/-- Input interface for the descent theorem.

`base` enumerates every point with height at most `cutoff`.
`rep` is a supplied finite list of representatives. The total functions
`child` and `repIndex` witness the quotient step whenever the point is
above the cutoff. Their existence is an assumption, not inferred from a
finite Selmer upper bound.

The direction of `decompose` is chosen for a direct rewriting proof.
No algebraic group laws are needed for the core: an application to an
abelian group interprets `add` as its addition law.
-/
structure DescentData (α : Type u) where
  add : α → α → α
  height : α → Nat
  cutoff : Nat
  repCount : Nat
  baseCount : Nat
  rep : Fin repCount → α
  base : Fin baseCount → α
  repIndex : α → Fin repCount
  baseIndex : α → Fin baseCount
  child : α → α
  baseComplete : ∀ p, height p ≤ cutoff → base (baseIndex p) = p
  decompose : ∀ p, cutoff < height p →
    add (add (child p) (child p)) (rep (repIndex p)) = p
  contract : ∀ p, cutoff < height p →
    2 * height (child p) ≤ height p + cutoff

namespace DescentData

variable {α : Type u} (D : DescentData α)

theorem child_lt (p : α) (hp : D.cutoff < D.height p) :
    D.height (D.child p) < D.height p := by
  have hc := D.contract p hp
  omega

/-- One descent step, frozen once the base region is reached. -/
def next (p : α) : α :=
  if D.height p ≤ D.cutoff then p else D.child p

theorem next_of_small (p : α) (hp : D.height p ≤ D.cutoff) :
    D.next p = p := by
  simp [next, hp]

theorem next_of_large (p : α) (hp : D.cutoff < D.height p) :
    D.next p = D.child p := by
  have hn : ¬ D.height p ≤ D.cutoff := by omega
  simp [next, hn]

/-- A fixed number of frozen descent steps; structural recursion only. -/
def run (D : DescentData α) : Nat → α → α
  | 0, p => p
  | n + 1, p => run D n (D.next p)

theorem run_of_small (n : Nat) (p : α)
    (hp : D.height p ≤ D.cutoff) : D.run n p = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change D.run n (D.next p) = p
      rw [D.next_of_small p hp]
      exact ih

/-- A coarse explicit bound, sufficient to avoid a termination search. -/
theorem run_height (n : Nat) (p : α) :
    D.height (D.run n p) ≤ D.cutoff + (D.height p - n) := by
  induction n generalizing p with
  | zero =>
      simp only [run, Nat.sub_zero]
      omega
  | succ n ih =>
      by_cases hp : D.height p ≤ D.cutoff
      · rw [D.run_of_small (n + 1) p hp]
        omega
      · have hlarge : D.cutoff < D.height p := by omega
        change D.height (D.run n (D.next p)) ≤
          D.cutoff + (D.height p - (n + 1))
        rw [D.next_of_large p hlarge]
        have hrec := ih (D.child p)
        have hdrop := D.child_lt p hlarge
        omega

theorem run_reaches_base (p : α) :
    D.height (D.run (D.height p) p) ≤ D.cutoff := by
  have h := D.run_height (D.height p) p
  simpa using h

/-- Construct a compact word, using a specified finite fuel budget.
At zero fuel the output is a base atom. Correctness is asserted only
when the budget is at least the input height. -/
def build (D : DescentData α) : Nat → α → Word D.repCount D.baseCount
  | 0, p => .base (D.baseIndex p)
  | n + 1, p =>
      if D.height p ≤ D.cutoff then .base (D.baseIndex p)
      else .add (.double (build D n (D.child p)))
        (.representative (D.repIndex p))

theorem build_correct (n : Nat) (p : α) (hp : D.height p ≤ n) :
    Word.eval D.add D.base D.rep (D.build n p) = p := by
  induction n generalizing p with
  | zero =>
      change D.base (D.baseIndex p) = p
      apply D.baseComplete p
      omega
  | succ n ih =>
      by_cases hs : D.height p ≤ D.cutoff
      · simp only [build, hs, ↓reduceIte, Word.eval]
        exact D.baseComplete p hs
      · have hl : D.cutoff < D.height p := by omega
        have hd := D.child_lt p hl
        have hb : D.height (D.child p) ≤ n := by omega
        simp only [build, hs, ↓reduceIte, Word.eval]
        rw [ih (D.child p) hb]
        exact D.decompose p hl

theorem build_size (n : Nat) (p : α) :
    Word.size (D.build n p) ≤ 3 * n + 1 := by
  induction n generalizing p with
  | zero => simp [build, Word.size]
  | succ n ih =>
      by_cases hs : D.height p ≤ D.cutoff
      · simp [build, hs, Word.size]
      · simp only [build, hs, ↓reduceIte, Word.size]
        have h := ih (D.child p)
        omega

/-- An explicit total generator-word function. -/
def coordinates (p : α) : Word D.repCount D.baseCount :=
  D.build (D.height p) p

theorem coordinates_correct (p : α) :
    Word.eval D.add D.base D.rep (D.coordinates p) = p := by
  exact D.build_correct (D.height p) p (Nat.le_refl _)

theorem coordinates_size (p : α) :
    Word.size (D.coordinates p) ≤ 3 * D.height p + 1 := by
  exact D.build_size (D.height p) p

/-- Finite generation in its direct constructive, word-producing form. -/
theorem finite_generation (p : α) :
    ∃ w : Word D.repCount D.baseCount,
      Word.eval D.add D.base D.rep w = p := by
  exact ⟨D.coordinates p, D.coordinates_correct p⟩

end DescentData

end MordellWeilIPRA
