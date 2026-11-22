# Lean artifacts and formalization status

The package supplies a **formalization outline**, not a completed or compiled
Lean proof of the full analytic theorem.

| File | What it supplies | Status |
| --- | --- | --- |
| `FiniteCore.lean` | Finite integer telescoping, two-sided accumulated error bounds, row cancellation, and the square boundary identity, using Lean's standard library. | Proof scripts written; no Lean compiler available here. These are host-level theorems. |
| `RepositorySlice.lean` | Adapters to ProveIt's actual object-level finite-FTC derivations, plus signed polynomial certificates for the square boundary and the three-dimensional curl/pullback identity. | Written against inspected pinned source; not compiled. Conclusions use `Γ ⊢[PRAAx]`. |
| `StokesBlueprint.lean.txt` | All coding layers, effective input contracts, intended theorem statements, arithmetic induction invariants, and the path from finite estimates to names, chains, and pullbacks. | Explicit design document, not a compilable Lean module. |

There are no `sorry` declarations or new axioms in the two `.lean` files. That
fact does **not** establish that they compile. No compilation success is claimed.
The curl polynomial was independently expanded with exact symbolic arithmetic;
its residual is zero. That check validates the algebraic expression, not its
Lean elaboration or the analytic chain rule.

## Pinned repository baseline

The inspected ProveIt source was pinned at
`a5688a1b37d62046c894691c3c41f7bdd53976ca`. Its dependency inventory specifies
Lean `v4.32.0` and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` for the root workspace.

Useful existing object-level results include:

- `Analysis/FiniteFTC.lean`: `ftc_upper`, `ftc_lower` explicitly use
  `PRA.qfInd` to derive the accumulated signed-error inequalities.
- `Analysis/TaggedFTC.lean`: corresponding variable-width finite estimates.
- `Core/Fubini.lean`: finite interchange of nested sums. The relevant theorem
  is named `LeanProofs.IPRA.fubini`.
- `Core/SumLemmas.lean` and `Core/SumSplit.lean`: finite addition, congruence,
  splitting, and reindexing tools.
- `Analysis/RiemannRefinement.lean`: object-level finite refinement estimates.
- `Foundations/DyadicNames.lean` and `Foundations/UniformCertificates.lean`:
  arithmetic for dyadic errors and their transport.

These files were read as source snapshots. Their transitive dependencies and
compiled objects were not installed or rebuilt here. Use the repository's
canonical provider configuration for a replay; do not substitute a historical
copy with the same module name.

Some nearby repository results have a different status. In particular,
`Topology/BoundarySquare.lean` proves an ambient Lean/Mathlib simplicial
identity, and `Analysis/PullbackCertificates.lean` proves specific polynomial
certificates for hypergeometric substitutions. Neither is already an
object-level general differential-form Stokes theorem. The integration plan
does not treat them as one.

## Replay commands

With a compatible Lean installation, the standalone finite file can be checked
without ProveIt or Mathlib:

```sh
lean FiniteCore.lean
```

For the repository adapter, use a complete ProveIt checkout at the pinned
commit, with its dependencies installed according to its own setup instructions:

```sh
cd /path/to/ProveIt
lake env lean /absolute/path/to/stokes_ipra/lean/RepositorySlice.lean
```

These are instructions for a future replay, not a log of commands successfully
run in this environment. The `.lean.txt` blueprint is not a build target.

## The crucial formal distinction

A theorem about arbitrary `Nat → Int` functions in ambient Lean is a useful
model of the finite argument. To establish provability **in iPRA**, however,
the relevant functions must become fixed primitive-recursive object terms,
and the resulting rational inequalities must be derived in the object proof
system. The required induction invariants are denominator-cleared finite-sum
equalities or inequalities. They are quantifier-free.

The input regularity and differentiability contracts may be universally
quantified first-order formulas. Their instances are hypotheses in the finite
proof; the induction is not performed on those quantified contracts. The
outline also avoids a uniform total evaluator for arbitrary primitive-recursive
codes, arbitrary-real order decisions, unbounded search, countable choice,
and a blanket classical compactness principle.

## Remaining implementation work

1. Add the rational/grid/precision macros as concrete `PTm` definitions, with
   substitution lemmas matching the repository's syntax conventions.
2. Build the scaled signed local estimates from the effective Taylor contract,
   and apply the existing finite FTC to every coordinate slice.
3. Sum the slices and prove the multidimensional grid-reordering identities.
4. Formalize the finite refinement bound and the regular integral-name
   construction, including the chosen extensional equality relation.
5. Implement finite oriented cubical chains, face restriction, and general
   double-boundary cancellation internally.
6. Formalize the arithmetic of effective jets, the represented-input
   composition adapter, and general pullback/exterior-derivative commutation.
7. Combine these object derivations into the main theorem, run a clean build,
   and audit the proof's axioms and exact import/provider closure.

Each step has a concrete mathematical lemma and proof invariant in the
blueprint and report. None is hidden behind a claimed automatic translation
from a theorem about classical real manifolds.
