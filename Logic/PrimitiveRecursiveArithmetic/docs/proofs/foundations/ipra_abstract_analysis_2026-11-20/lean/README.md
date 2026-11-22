# Checked finite-observation and error-budget kernel

## Verification status

`QuantitativeKernel.lean` and `Examples.lean` compile with **Lean 4.32.0**,
compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, with no Mathlib
dependency. The source contains no `sorry`, no new axiom declaration, and no
unfinished theorem. The exact replay and axiom reports are in
`verification.log`.

These are ordinary Lean theorems about explicit syntax, finite evaluation, and
rational arithmetic. **They are not derivations of type `Prf PRAAx`.** The
separate `OBJECT_LANGUAGE_PLAN.md` gives the object-language invariants, coding,
and existing ProveIt interfaces required for that further step.

The axiom audit matters:

| Result | Reported Lean axiom dependencies |
|---|---|
| `positive_transfer` | None |
| `allFin_true`, `anyFin_true` | `propext` |
| `eval_correct` | `propext`, `Quot.sound` |
| Rational error and clock theorems | `propext`, `Classical.choice`, `Quot.sound` |

The arithmetic dependencies are inherited from Lean's standard `Rat` library:
even `Rat.pow_zero`, `Rat.mul_comm`, and `Rat.le_trans` report these standard
axioms. This is a statement about the host proof's dependency closure, not a
claim that the mathematical argument needs a choice principle. Its proposed
object-iPRA implementation clears denominators and uses quantifier-free
induction on integer or natural polynomial inequalities.

## Replay

With Lean/Elan installed and the pinned toolchain available:

```bash
cd lean
bash replay.sh
```

For a standalone Lean distribution, set `LEAN_LAKE_BIN` to its `bin/lake`
executable:

```bash
LEAN_LAKE_BIN=/absolute/path/to/lean-4.32.0-linux/bin/lake bash replay.sh
```

The script checks the compiler version, builds the library, prints the axiom
reports, and typechecks the examples. It makes no network request for project
dependencies; there are none. Toolchain installation is separate. Build output
under `.lake/` is disposable and is not part of the research deliverable.

## Positive formulas and finite nets

`Env X` is a sequence of values used for de Bruijn variables. `push x ρ` binds
the newest variable at index zero. `Related R ρ σ` says that the two
environments are related pointwise.

`PosFormula Atom` has constructors for atoms, truth, falsity, conjunction,
disjunction, universal quantification, and existential quantification. An atom
includes its terms: the semantic atomic interpretation is supplied as
`Atom → Env X → Prop`. Quantifiers range over the chosen bounded sort `X`.
`Holds` gives the complete recursive semantics.

`positive_transfer` assumes a relation `R : X → Y → Prop`, explicit selectors
`forth : X → Y` and `back : Y → X`, and proofs that each selector chooses a
related point. If an atomic assertion in an `R`-related source environment
implies the target atomic assertion, the same implication holds for every
positive formula. Existential quantification uses `forth`; universal
quantification uses `back`. No selection by choice is used.

For a finite metric net, `forth` is the given net selector and `back` is
inclusion of the net centers. Source and target atoms can have different error
margins. The proof preserves the same atomic margin through every connective
and quantifier: there is **no additional loss proportional to quantifier
depth**. Atomic uniform-continuity estimates must already account for all
terms and arguments of that atom.

This theorem does not assert that a net is a finite submodel. Terms can still
be evaluated in the ambient dense domain. Closure of the net under the
signature operations would be a separate hypothesis.

### Executable finite evaluation

`allFin` and `anyFin` are primitive recursions implementing the two Boolean
folds over `Fin n`. They correctly handle empty folds. `eval` interprets a
formula over the finite domain `Fin n`, using a supplied Boolean atomic
evaluator. `eval_correct` proves that it returns `true` exactly when `Holds`
does, with atomic truth defined by that Boolean evaluator.

Applications to structures use a nonempty finite domain and an actual
environment. In particular, an environment `Nat → Fin 0` does not exist;
the empty-fold lemmas do not silently create one.

For an iPRA instance, the atomic evaluator must be a **fixed primitive
recursive program**, or a finite table. The generic Lean function parameter
does not certify primitive recursiveness. No universal total evaluator for
arbitrary PR programs is assumed. At a fixed finite signature, the syntax
interpreter has a primitive recursive coding and an explicit finite recursion
bound; it is not an evaluator for arbitrary programs supplied by code.

## Perturbed contractions

The basic rational theorem is

```text
x(0) ≤ R,
x(j+1) ≤ q*x(j) + ε,
0 ≤ q, 0 ≤ E, ε ≤ (1−q)*E
    imply
x(j) ≤ q^j*R + E.
```

`perturbed_contraction` uses the equivalent stationary-reserve hypothesis
`q*E + ε ≤ E`; `perturbed_contraction_of_noise` uses the displayed form.
Neither theorem needs `q < 1` for the finite invariant. That restriction
enters when a useful clock is selected.

The additional theorems prove the complete explicit clock used in the report:

| Declaration | Conclusion |
|---|---|
| `reciprocal_decay` | `(1+nδ)(1−δ)^n ≤ 1`, for `0 ≤ δ ≤ 1` |
| `block_halving` | `(1−δ)^h ≤ 1/2`, if `hδ ≥ 1` |
| `block_decay` | `(1−δ)^(ht) ≤ 2^(−t)` |
| `amplitude_absorb` | `C * 2^(−C) ≤ 1`, for natural `C` |
| `shifted_amplitude` | `C * 2^(−s−C) ≤ 2^(−s)` |
| `radius_at_clock` | `R*(1−δ)^[h(n+R+3)] ≤ 2^(−n−3)` |
| `solver_budget` | The final error at that clock is at most `2^(−n−2)` |

Specifically, let `h,C,R,n` be natural numbers, let `0 ≤ δ ≤ 1`, and assume
`hδ ≥ 1` and the cleared bound `2λ ≤ δC`. Put

```text
k = n + 3 + C,
N = h * (n + R + 3),
ε = 2λ * 2^(−k).
```

If a rational majorant `x` starts below `R` and satisfies
`x(j+1) ≤ (1−δ)x(j)+ε`, then `solver_budget` proves
`x(N) ≤ 2^(−n−2)`. It uses the stationary reserve `E=C*2^(−k)`.

Actual norm distances may be irrational. The analytic application must
separately prove that they are bounded by the supplied rational majorant.
This file does not identify an irrational norm with a rational number, assume
the existence of a solution, formalize Hilbert-space completion, or prove the
PDE application. Those steps are developed mathematically in the report and
their object-language proof obligations are listed in the plan.

## Files

- `QuantitativeKernel.lean`: complete checked definitions and proofs.
- `Examples.lean`: a finite quantified sentence and an instance of the solver
  budget, checked by the compiler.
- `Audit.lean`: public theorem dependency reports.
- `OBJECT_LANGUAGE_PLAN.md`: coding, quantifier-free invariants, exact ProveIt
  interfaces, and the finite two-run coherence argument.
- `PROVENANCE.json`: compiler and inspected repository source identities.
- `verification.log`: actual successful replay output.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `replay.sh`: build
  configuration and replay entry point.
