# Lean artifacts: presentations, certificates, and finite witnesses

All eight standalone modules listed in `build.sh` compile with Lean 4.32.0.
They import only `Std` and the supplied local modules. There is no `sorry`,
custom `axiom`, or `opaque` declaration. Successful compilation is not a claim
that every theorem of the paper has a completed object-iPRA derivation.

Run `bash build.sh` with Lean 4.32.0 on `PATH`, or set `LEAN_BIN` to that
version's executable. Build products are placed in `.build/` and are not
needed in the delivered source archive. `validation/lean_build.txt` records
the checked build and its axiom audit.

## Exact proof status

| Module | Status and meaning |
|---|---|
| `ObjectKernel.lean` | Three pinned upstream modules, with import lines replaced by `import Std`; the object syntax, axioms, and deduction rules are unchanged. |
| `ObjectFusion.lean` | Actual `Prf PRAAx` theorem: a local commuting-square derivation yields its finite-iteration derivation. |
| `ObjectSimulation.lean` | Actual `Prf PRAAx` theorem: a local preservation derivation for a two-variable quantifier-free relation yields its iterated preservation derivation. |
| `SquaringTransport.lean` | Actual `Prf PRAAx` proof constructors for repeated squaring across a supplied multiplicative map, plus an unconditional successor example. |
| `PrimitiveEigenvalue.lean` | Host Lean theorem: finite integer eigenvector and Bezout certificates force a positive reduced denominator to equal one. |
| `EigenvalueBound.lean` | Host Lean theorem: a checked maximizing coordinate yields the absolute-column bound for an integral eigenvalue. |
| `FiniteAlgebraTargets.lean` | Complete executable certificate and enumeration definitions; explicit unproved target propositions; proved conditional reduction from grid completeness to enumeration completeness. |
| `FiniteAlgebraExamples.lean` | Executable exact-rational diagnostics for the paper's four-point elliptic section. `#eval` output is a computation, not an object-iPRA proof. |

The main unproved target is `FiniteAlgebra.Targets.GridCompletenessGoal`.
The file defines it; it does not postulate or prove it. The human paper gives
the proof and the formalization plan supplies its missing Lean components.
Even a future host proof of this target must still be reified into fixed PR
syntax with actual `Prf PRAAx` derivations to finish the object formalization.

## Axiom audit

Every printed object-proof construction depends only on Lean's `propext` and
`Quot.sound`. The integer eigenvalue and column-bound theorems also have only
these dependencies (`weighted_eigen_equation` needs only `propext`). They do
not depend on `Classical.choice` or `sorryAx`.

The target programs use the standard library's `Rat` implementation. Its
proof dependencies include `Classical.choice`, so the host theorem
`enumeration_of_gridCompleteness` prints `propext`, `Classical.choice`, and
`Quot.sound`. This is a dependency of the host rational representation; it
does not add a classical rule to `PRAAx`. The intended object translation
uses explicit integer/positive-denominator pairs and Euclidean normalization.

## Upstream provenance

The snapshot is ProveIt commit `b0f6f535ffc16324683fef2c263260a88ae03755`.
The untouched files in `upstream/`, their Git blob hashes, and the exact
standalone transformation are recorded in `UPSTREAM_SOURCES.json`.
`python3 verify_provenance.py` checks the frozen bytes and the three embedded
sections. `NativeBiInterpretation.lean` is included as a reference for the
final transfer theorem; it is not a standalone build target. The original
repository license is retained in `LICENSE-ProveIt.txt`.

## Integration into ProveIt

For integration in the existing repository, replace `import ObjectKernel` at
the start of `ObjectFusion.lean` by `import ConciseIPRA.PR` and place the new
modules on the appropriate Lake module path. Do not import the standalone
`ObjectKernel` alongside the original modules: it deliberately defines the
same constants for a dependency-light standalone build. The downstream
proofs use the original namespaces and API. The native transfer additionally
requires `import ConciseIPRA.NativeBiInterpretation`.
