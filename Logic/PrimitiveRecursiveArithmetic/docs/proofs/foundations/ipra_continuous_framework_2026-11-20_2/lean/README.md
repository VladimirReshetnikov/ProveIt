# Checked finite observation kernel

This directory builds with Lean **4.32.0** and the bundled standard library.
It has no external package dependencies.

```bash
lake build
lake env lean Audit.lean
```

## Verification status

The complete project was compiled successfully in this research session.
Every declaration in the five `.lean` files has a proof or definition; there
are no `sorry`, `admit`, or custom `axiom` declarations.  The explicit audit
reports `propext` and `Quot.sound` for the principal arithmetic proofs and
transfer theorem, and no `Classical.choice` or `sorryAx`.

**These are Lean semantic theorems, not new terms of `Prf PRAAx`.**
The distinction matters: functions such as `Nat → Nat` and arbitrary types
in `ScoreNet` live in Lean's metatheory.  They are not quantified objects of
first-order iPRA.  The separate `ObjectTheoryPlan.lean.txt` describes the
precise specialization and proof-reification work still required.

## Contents

| File | What is proved |
| --- | --- |
| `FiniteExtrema.lean` | Two-sided error calculus; actual nonempty minimum/maximum folds; explicit argmin/argmax; least-minimizer property; extrema transfer along a two-sided total correspondence. |
| `CompactQuantifier.lean` | Finite-net infimum/supremum bounds; explicit approximate witnesses; coherence between unrelated nets; perturbation bounds. |
| `ContinuousSyntax.lean` | Single-sort, arity-indexed continuous syntax and finite-model semantics; approximate elementarity with no increase of a uniform atomic error under min, max, truncated complement, inf, or sup. |
| `Examples.lean` | A two-endpoint net and a three-point net attain the error bound exactly for a quantified tent function. |
| `Audit.lean` | `#print axioms` for the principal exported theorems. |

## Exact quantitative interfaces

`Close e a b` means `a ≤ b + e ∧ b ≤ a + e`.  Scores are natural
numerators at one common positive denominator `D`; hence a score error `e`
means rational error `e/D`.  Shifting a bounded signed interval to a
nonnegative interval preserves all these inequalities.  Each finite family
is indexed by `0, ..., n`, so there is no unhandled empty minimum.

If all corresponding scores differ by at most `e`, the finite minima and
maxima differ by at most `e`, even when their index sets have different
sizes.  The correspondence must cover both index sets.  It need not be
functional or injective.

For a `ScoreNet` with mesh error `δ` and evaluation error `η`, the finite
minimum `l` and returned point `p` satisfy

```
l ≤ value(x) + δ + η          for every x
value(p) ≤ l + η
value(p) ≤ value(x) + δ + 2η  for every x.
```

For two nets of the same value function with errors `(δ,η)` and `(δ',η')`,
their minima and maxima differ by at most `max(δ,δ') + η + η'`.  The
chosen minimizer points need not be close to each other.

`Continuous.formula_transfer` quantifies in Lean over each fixed finite
single-sort formula, models, and total correspondence. Atom interpretations must be
uniformly close for **all related tuples of the formula's relevant arities**.
The identical error bound works after arbitrary finite nesting of the
listed quantifiers and connectives.  This does not cover a new connective
with Lipschitz constant greater than one without an adjusted budget; it
also makes no claim about exact real comparisons or first-order model
compactness. The paper's many-sorted extension is proved in prose and remains
a Lean generalization, obtained by indexing carriers, variables, and binders
by sorts and using totality separately for each quantified sort.

## Reproduction

`lean-toolchain` pins `leanprover/lean4:v4.32.0`; the observed compiler
reported source commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The dependency manifest is empty.  Intermediate `.olean`, `.ilean`, `.lake`,
and downloaded toolchain files are not needed in the delivered archive.
