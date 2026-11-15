import Std

/-!
# Finite search from a supplied bound

This file proves the elementary finite-search layer relevant to an effective
version of Mordell--Faltings. It does not prove a height bound for curves and
does not assert Faltings' theorem.

`point n` is a decidable predicate on canonical natural-number codes. The
computations below are primitive recursive when `point` and any supplied bound
function are primitive recursive. The Lean functions themselves allow an
arbitrary Boolean predicate; no claim that every Lean function is primitive
recursive is intended.

Positive finiteness means existence of a complete finite list. An existential
proposition in Lean's `Prop` is not silently converted to executable data: the
executable construction `certifiedEnumeration` takes a bound function as an
explicit argument.

The proofs use no `classical`, `axiom`, or `sorry`. The final `#print axioms`
commands audit kernel dependencies. Lean verification of these lemmas is not,
by itself, a derivation in an arithmetized iPRA calculus.
-/

namespace ConstructiveFiniteSearch

/-- A list contains exactly the codes satisfying `point`. Duplicates, if any,
do not affect completeness; `enumerate` itself searches each code once. -/
def Complete (point : Nat → Bool) (codes : List Nat) : Prop :=
  ∀ n, n ∈ codes ↔ point n = true

/-- A numerical upper bound on every point code. -/
def CodeBound (point : Nat → Bool) (bound : Nat) : Prop :=
  ∀ n, point n = true → n ≤ bound

/-- Positive finiteness, with a finite list as the existential witness. -/
def PositiveFinite (point : Nat → Bool) : Prop :=
  ∃ codes : List Nat, Complete point codes

/-- Existence of a numerical code bound. -/
def Bounded (point : Nat → Bool) : Prop :=
  ∃ bound : Nat, CodeBound point bound

/-- A cardinality bound is a different proposition: any duplicate-free list
of points has length at most `count`. No converse to positive finiteness is
asserted here. -/
def CardinalityBound (point : Nat → Bool) (count : Nat) : Prop :=
  ∀ codes : List Nat, codes.Nodup →
    (∀ n, n ∈ codes → point n = true) → codes.length ≤ count

/-- This negative formulation also carries no asserted finite-list witness. -/
def NoInjectiveSequence (point : Nat → Bool) : Prop :=
  ¬ ∃ sequence : Nat → Nat,
    (∀ i j, sequence i = sequence j → i = j) ∧
    (∀ i, point (sequence i) = true)

/-- The codes in `[0, bound]`, in descending order. Using this direct
primitive recursion keeps the arithmetic structure visible. -/
def interval : Nat → List Nat
  | 0 => [0]
  | bound + 1 => (bound + 1) :: interval bound

theorem mem_interval (bound n : Nat) : n ∈ interval bound ↔ n ≤ bound := by
  induction bound with
  | zero => simp [interval]
  | succ bound ih =>
      simp only [interval, List.mem_cons, ih]
      constructor
      · intro hn
        rcases hn with heq | hle
        · subst n
          exact Nat.le_refl _
        · exact Nat.le_trans hle (Nat.le_succ bound)
      · intro hn
        rcases Nat.eq_or_lt_of_le hn with heq | hlt
        · exact Or.inl heq
        · exact Or.inr (Nat.lt_succ_iff.mp hlt)

/-- Exhaustive search of the finite interval `[0, bound]`. -/
def enumerate (point : Nat → Bool) (bound : Nat) : List Nat :=
  (interval bound).filter point

/-- The exact specification of bounded search. -/
theorem mem_enumerate (point : Nat → Bool) (bound n : Nat) :
    n ∈ enumerate point bound ↔ point n = true ∧ n ≤ bound := by
  simp [enumerate, mem_interval, and_comm]

/-- Bounded search never returns a spurious point. -/
theorem enumerate_sound (point : Nat → Bool) (bound n : Nat)
    (h : n ∈ enumerate point bound) : point n = true :=
  ((mem_enumerate point bound n).mp h).1

/-- Every point in the search interval occurs in the result. -/
theorem enumerate_complete_below (point : Nat → Bool) (bound n : Nat)
    (hp : point n = true) (hb : n ≤ bound) :
    n ∈ enumerate point bound :=
  (mem_enumerate point bound n).mpr ⟨hp, hb⟩

/-- A supplied global bound is exactly what upgrades bounded search to a
complete enumeration. -/
theorem complete_enumerate_iff (point : Nat → Bool) (bound : Nat) :
    Complete point (enumerate point bound) ↔ CodeBound point bound := by
  constructor
  · intro complete n hn
    exact ((mem_enumerate point bound n).mp ((complete n).mpr hn)).2
  · intro bounded n
    constructor
    · exact enumerate_sound point bound n
    · intro hn
      exact enumerate_complete_below point bound n hn (bounded n hn)

/-- A primitive-recursive maximum operation, returning zero on the empty list. -/
def listBound : List Nat → Nat
  | [] => 0
  | n :: rest => max n (listBound rest)

/-- Every entry of a list is at most its computed maximum. -/
theorem le_listBound_of_mem {codes : List Nat} {n : Nat}
    (h : n ∈ codes) : n ≤ listBound codes := by
  induction codes with
  | nil => simp at h
  | cons head tail ih =>
      rcases List.mem_cons.mp h with hhead | htail
      · subst n
        exact Nat.le_max_left head (listBound tail)
      · exact Nat.le_trans (ih htail) (Nat.le_max_right head (listBound tail))

/-- A complete list supplies a global code bound, including when it is empty. -/
theorem bound_of_complete (point : Nat → Bool) (codes : List Nat)
    (complete : Complete point codes) : CodeBound point (listBound codes) := by
  intro n hn
  exact le_listBound_of_mem ((complete n).mpr hn)

/-- Positive finiteness and existence of a numerical code bound are
constructively equivalent for a decidable predicate on natural codes. -/
theorem positiveFinite_iff_bounded (point : Nat → Bool) :
    PositiveFinite point ↔ Bounded point := by
  constructor
  · intro h
    obtain ⟨codes, complete⟩ := h
    exact ⟨listBound codes, bound_of_complete point codes complete⟩
  · intro h
    obtain ⟨bound, bounded⟩ := h
    exact ⟨enumerate point bound, (complete_enumerate_iff point bound).mpr bounded⟩

/-- An executable complete-list candidate from an explicit bound function. -/
def certifiedEnumeration {Input : Type}
    (point : Input → Nat → Bool) (bound : Input → Nat) (input : Input) : List Nat :=
  enumerate (point input) (bound input)

/-- The conditional correctness theorem exposes the missing global bound as
an ordinary hypothesis. It is not assumed as an axiom. -/
theorem certifiedEnumeration_complete {Input : Type}
    (valid : Input → Prop) (point : Input → Nat → Bool) (bound : Input → Nat)
    (boundCorrect : ∀ input, valid input → CodeBound (point input) (bound input))
    (input : Input) (hvalid : valid input) :
    Complete (point input) (certifiedEnumeration point bound input) :=
  (complete_enumerate_iff (point input) (bound input)).mpr
    (boundCorrect input hvalid)

/-- In the reverse direction an explicit family of complete lists yields an
explicit family of bounds. -/
theorem listBound_complete_family {Input : Type}
    (valid : Input → Prop) (point : Input → Nat → Bool)
    (codes : Input → List Nat)
    (complete : ∀ input, valid input → Complete (point input) (codes input))
    (input : Input) (hvalid : valid input) :
    CodeBound (point input) (listBound (codes input)) :=
  bound_of_complete (point input) (codes input) (complete input hvalid)

/-- Empty-list completeness is equivalent to the absence of any point. -/
theorem complete_nil_iff (point : Nat → Bool) :
    Complete point [] ↔ ∀ n, point n ≠ true := by
  constructor
  · intro complete n hn
    exact List.not_mem_nil ((complete n).mpr hn)
  · intro absent n
    constructor
    · intro hn
      exact False.elim (List.not_mem_nil hn)
    · intro hn
      exact False.elim (absent n hn)

end ConstructiveFiniteSearch

#print axioms ConstructiveFiniteSearch.mem_enumerate
#print axioms ConstructiveFiniteSearch.mem_interval
#print axioms ConstructiveFiniteSearch.complete_enumerate_iff
#print axioms ConstructiveFiniteSearch.le_listBound_of_mem
#print axioms ConstructiveFiniteSearch.bound_of_complete
#print axioms ConstructiveFiniteSearch.positiveFinite_iff_bounded
#print axioms ConstructiveFiniteSearch.certifiedEnumeration_complete
#print axioms ConstructiveFiniteSearch.listBound_complete_family
#print axioms ConstructiveFiniteSearch.complete_nil_iff
