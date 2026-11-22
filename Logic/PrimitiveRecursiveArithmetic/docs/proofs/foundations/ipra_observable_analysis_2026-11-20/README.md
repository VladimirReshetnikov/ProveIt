# Continuous mathematics in iPRA

## Shared error budgets, constructive integration, and stable homotopies

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

Start with **paper/report.pdf**. The complete editable LaTeX source is
**paper/report.tex**, its eight section files, and the included bibliography
and figure. The report provides full human arguments under explicit
quantitative presentation assumptions, a compiled Lean finite kernel, and
an exact path to the remaining object-language formalization.

## Main results

1. **A reusable observation and completion interface.** Fixed primitive-recursive
   presentations, explicit rational error contracts, regular names, represented
   distance, and a shifted extension theorem. The represented part of a
   completion is distinguished from the entire classical completion.
2. **Output-specific error certificates.** Reverse sensitivity weights are the
   least nonnegative linear certificate on an acyclic computation graph.
   A separate dual supersolution verifier also handles already proved cyclic
   error inequalities. Shared values are computed once, and only the requested
   observable needs to be certified.
3. **Coherent measure and integration.** A single measured Boolean algebra
   supports common refinements, a measure-algebra completion, L1 lattice
   operations, bounded multiplication, quantitative Vitali/dominated
   convergence, represented Fubini, and explicit spatial-tail reduction.
   A supplied L1 majorant produces its own amplitude-tail modulus.
4. **A probability sort for continuous model theory.** Exact finite transport
   has a bounded forest-enumeration algorithm and a fast finite certificate
   interface. Actual rational probability laws form explicit finite nets.
   Lipschitz expectations and fixed continuous formulas then have finite
   evaluators. An exact moment-optimization example has value 1/8 and an
   explicit attaining law.
5. **Normed-algebra and complex analysis.** Finite Neumann identities,
   two-sided approximate inverses, geometric doubling, Horner evaluation,
   majorized power series, noncommutative derivatives and an explicit
   quadratic remainder share the same numerical framework. An infinite
   dimensional convolution-algebra example controls a holomorphic function
   uniformly on the unit disk.
6. **Algebraic topology and categories.** A small contraction defect produces
   a genuine represented bounded contracting homotopy. Applying the construction
   to a mapping cone produces a chain-homotopy inverse and its witnesses.
   Explicit perturbation margins preserve this construction. A boundary
   observation can be certified with fewer terms than the entire homotopy.

These are quantitative versions of established mathematical constructions,
with explicit finite arithmetic extraction and additional reusable providers.
The report credits the substantial completion, finite-net, gluing, demand,
and small-gain frameworks already present in ProveIt. It makes no claim to
have newly discovered the underlying classical integration or perturbation
theorems.

## Exact verification status

The standalone **Lean 4.32.0** project builds successfully using only **Std**.
It contains no `sorry`, `admit`, or new axiom declarations. Checked theorems
include the noncommutative geometric left/right residual identities, the
square-zero differential's finite corrected-contraction identity, the exact
and supersolution weighted-budget implications, exchange of finite sums,
and bounded minimum optimality/stability.

**The new main analytic theorems have not yet been compiled into ProveIt's
embedded `Prf PRAAx` derivations.** The report and `lean/ProofRoadmap.md`
specify the concrete coding, numerical statements, quantifier-free loop
invariants, and existing repository providers required for that step.
Law fields in blueprint structures are obligations, not asserted instances.

The axiom audit is explicit. The Neumann and homotopy kernels use `propext`
and, for some results, `Quot.sound`; they do not use `Classical.choice`.
The concrete rational-budget and minimum theorems inherit `Classical.choice`
from the standard `Rat` arithmetic library. This package is therefore not
described as a complete constructive Lean formalization or a checked iPRA
interpretation theorem.

The five Python example programs use exact fractions or integers for their
acceptance checks. They validate finite implementations and selected
constants. They do not replace the universal proofs or complete the
object-language translation.

## Artifact map

| Path | Contents |
| --- | --- |
| `paper/report.pdf` | Complete mathematical report. |
| `paper/report.tex`, `paper/sections/`, bibliography files | Complete editable LaTeX source. |
| `paper/figures/` | Derived moment geometry and geometric-sum operation counts. |
| `lean/ObservableAnalysis/` | Checked finite kernels and typed specifications. |
| `lean/build.log`, `lean/verification.json` | Actual compiler output, source hashes, and axiom audit. |
| `lean/ProofRoadmap.md` | Remaining constructive and object-iPRA implementation work. |
| `code/` | Exact-rational reference implementations and optional figure generator. |
| `evidence/` | Numerical receipts, source provenance, claim status, mathematical and PDF review records. |
| `verify.py` | Runs all five exact-arithmetic example programs. |
| `build_pdf.py` | Rebuilds the report and checks its final log. |
| `Makefile` | Convenient reproduction targets. |
| `MANIFEST.sha256` | SHA-256 hashes of all other packaged files. |

## Reproduce

Python 3.10 or newer, with no third-party packages needed for the examples:

```sh
python3 verify.py
```

Run without `-O`; the finite checks intentionally use assertions.

With Lean 4.32.0 installed:

```sh
cd lean
lake build
```

All local Lean source dependencies are included. The compiler distribution
and disposable `.lake` build cache are not included. No Mathlib checkout is
needed for this standalone build.

With a configured TeX Live/pdfLaTeX installation:

```sh
python3 build_pdf.py
```

Set `IPRA_PDFLATEX` to an alternate pdfLaTeX executable if necessary.
The script performs three passes and checks for unresolved references,
missing characters, and overfull boxes. Visual layout inspection is a
separate step, recorded in the PDF review receipt.

To regenerate the optional illustration, install Matplotlib and run:

```sh
python3 code/plot_observations.py
```

The generated PDF figure is already included; Matplotlib is not needed to
rebuild the report or run the mathematical examples.

## Source baseline and intended integration

The repository source review is pinned to:

```text
VladimirReshetnikov/ProveIt
b2341af5370cd8a43f72ebb2341c0d7d7395b634
```

The repository was inspected, not rebuilt or modified. `evidence/source_manifest.json`
records 21 selected root-review sources with immutable Git blob identities;
the category and measure audits record their additional selected sources.
This is not a repository-wide audit. The existing proof calculus,
bounded-syntax compiler, and realizer interfaces should be reused when the
new providers are integrated.

For incorporation into ProveIt, the package can be placed under the existing
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/` structure or
submitted as an incoming archive according to the repository's usual process.
No remote branch, commit, or pull request was created by this task.
