import Std

/-!
# The proof-theoretic core of arbitrary possible outputs

This file isolates the short logical argument from the substantial arithmetic
coding work. It has no `axiom` declarations and no unfinished proof terms.
Every arithmetic/metamathematical assumption is a field or an explicit
parameter. In particular, this is **not** a claim that the PA instance has
already been implemented.

Intended interpretation:
* `Code` is a type of codes for partial computable programs;
* `run e x y` says that the actual standard computation of `e` on `x` halts
  with output `y`;
* `halts e x y` is its arithmetized halting sentence;
* `provable` is PA theoremhood;
* `isModel M` says that `M` is a first-order model of PA;
* `realizes M p` is first-order sentence satisfaction.

The field `finiteComputation` is numerical computation verification, NOT
reflection of all PA theorems. The field `modelOfUnrefuted` is the classical
deduction theorem followed by first-order completeness.

The two fields of `SelfSearch` follow from a computable proof search and
Kleene's recursion theorem. Its `findsRefutation` field deliberately returns
an unspecified output. A proof excluding `n` can be preceded by a proof
excluding a different number; the actual first output is the one used in the
contradiction.

Validation status: source reviewed, but not compiler-checked in the authoring
environment (no Lean executable was available). Run the accompanying check
command before treating this file as kernel-checked.
-/

namespace FlexibleOutput

universe u v w

/-- Explicit interfaces needed by the short metamathematical argument. -/
structure ArithmeticInterface where
  Code : Type u
  Sentence : Type v
  Model : Type w
  run : Code → Nat → Nat → Prop
  halts : Code → Nat → Nat → Sentence
  neg : Sentence → Sentence
  provable : Sentence → Prop
  isModel : Model → Prop
  realizes : Model → Sentence → Prop
  consistent : ∀ p, provable p → provable (neg p) → False
  finiteComputation : ∀ {e : Code} {x y : Nat},
    run e x y → provable (halts e x y)
  modelOfUnrefuted : ∀ p,
    (¬ provable (neg p)) → ∃ M, isModel M ∧ realizes M p

/-- Operational facts about the self-referential proof-search program. -/
structure SelfSearch (A : ArithmeticInterface.{u, v, w})
    (e : A.Code) : Prop where
  /-- Every actual halt reports an output whose negation was proved. -/
  haltsAfterRefutation : ∀ {y : Nat},
    A.run e 0 y → A.provable (A.neg (A.halts e 0 y))
  /-- Any refutation eventually makes the search halt, perhaps elsewhere. -/
  findsRefutation :
    (∃ n, A.provable (A.neg (A.halts e 0 n))) →
      ∃ m, A.run e 0 m

variable {A : ArithmeticInterface.{u, v, w}} {e : A.Code}

/-- A real halt would give PA proofs of a sentence and its negation. -/
theorem no_standard_halt (s : SelfSearch A e) :
    ∀ n, ¬ A.run e 0 n := by
  intro n h
  exact A.consistent (A.halts e 0 n)
    (A.finiteComputation h) (s.haltsAfterRefutation h)

/-- PA cannot exclude any particular output of the self-search program. -/
theorem no_output_refutation (s : SelfSearch A e) :
    ∀ n, ¬ A.provable (A.neg (A.halts e 0 n)) := by
  intro n hn
  cases s.findsRefutation (Exists.intro n hn) with
  | intro m hm => exact no_standard_halt s m hm

/-- Every prescribed standard output occurs internally in some PA model. -/
theorem every_output_has_model (s : SelfSearch A e) :
    ∀ n, ∃ M, A.isModel M ∧ A.realizes M (A.halts e 0 n) := by
  intro n
  exact A.modelOfUnrefuted (A.halts e 0 n)
    (no_output_refutation s n)

/-- The intended result at input zero, expressed at the explicit interface. -/
def UniversalAtZero (A : ArithmeticInterface.{u, v, w})
    (e : A.Code) : Prop :=
  (∀ n, ¬ A.run e 0 n) ∧
  (∀ n, ∃ M, A.isModel M ∧ A.realizes M (A.halts e 0 n))

theorem universalAtZero_of_selfSearch (s : SelfSearch A e) :
    UniversalAtZero A e :=
  And.intro (no_standard_halt s) (every_output_has_model s)

/--
The remaining construction obligation is exactly a self-search fixed point.
No property of a particular numeric output is hidden in this assumption.
-/
theorem exists_universalAtZero
    (fixedPoint : ∃ e : A.Code, SelfSearch A e) :
    ∃ e : A.Code, UniversalAtZero A e := by
  cases fixedPoint with
  | intro e s =>
    exact Exists.intro e (universalAtZero_of_selfSearch s)

/--
If the chosen implementation ignores its input, its standard partial function
is nowhere defined. This statement needs no internal PA proof of that fact.
-/
theorem nowhere_defined_of_ignoresInput (s : SelfSearch A e)
    (ignoresInput : ∀ x y, A.run e x y ↔ A.run e 0 y) :
    ∀ x y, ¬ A.run e x y := by
  intro x y h
  exact no_standard_halt s y ((ignoresInput x y).mp h)

/--
Optional strengthening: standard-model soundness for the halting sentences
makes every individual halting sentence undecidable. This extra hypothesis
is not used by the arbitrary-output theorem above.
-/
theorem no_output_proof (s : SelfSearch A e)
    (standardSoundness : ∀ n, A.provable (A.halts e 0 n) → A.run e 0 n) :
    ∀ n, ¬ A.provable (A.halts e 0 n) := by
  intro n hn
  exact no_standard_halt s n (standardSoundness n hn)

#print axioms no_standard_halt
#print axioms no_output_refutation
#print axioms every_output_has_model
#print axioms exists_universalAtZero

end FlexibleOutput
