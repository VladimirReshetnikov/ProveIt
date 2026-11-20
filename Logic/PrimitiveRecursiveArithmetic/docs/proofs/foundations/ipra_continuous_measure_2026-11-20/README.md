# Continuous mathematics in iPRA

## Measures, stochastic operators, and homological transfer

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

Start with **paper/report.pdf**. The complete editable report is
**paper/report.tex** together with **paper/sections/** and **paper/references.tex**.

This is an extension of the current ProveIt presentation framework. It focuses
on continuous and abstract mathematics: measure and integration, represented
operator categories, integrated continuous formulas, holomorphic parameter
integrals, and quantitative algebraic topology. It explicitly distinguishes
uniform, L1, convergence-in-measure, strong-action, and operator-norm data.

## Main results

1. **A corrected, limit-producing Vitali theorem.** The earlier expectation
   packet's separate-tail inequality fails at `x=2K, y=-K`. The replacement
   uses Lipschitz clipping and the stable metric
   `rho(f,g) = integral min(1, abs(f-g))`:

   `norm1(f-g) <= tail_K(f) + tail_K(g) + 2*K*rho(f,g)`.

   A uniform tail cutoff and a Cauchy-in-measure rate give an explicit PR
   diagonal sampler for an integrable limit. Integrability and the limit's
   tail bound are conclusions. The old checked common-dominator truncation
   theorem is a different, correct result and remains explicitly credited.

2. **Derived analytic data.** A regular L1 name of a dominating function
   supplies an amplitude cutoff. Finite conditional averages extend by
   contraction, obey the tower law, and converge to each named input with a
   rate derived from its actual approximation levels. The L1 error bound
   does not require a smallest positive cell mass; a pointwise posterior
   query does require a positive mass margin.

3. **Compositional continuous operators.** Strong action routines on dense
   simple functions extend to bounded maps and compose with explicit
   precision schedules. Finite conditional projections do not converge to
   the identity in operator norm, so the construction does not assume that
   false approximation. The probability-preserving category, its independent
   tensor, and the limitation on copy maps are stated precisely.

4. **Integration in continuous model evaluation.** Tent partitions give
   rational probability quadratures. A finite evaluator handles mixed
   infimum, supremum, and expectation binders, preserving their order and
   range guards. Weighted local errors can save precision on low-mass terms.
   The two formulas `sup_y E_x |x-y|` and `E_x sup_y |x-y|` have values
   `1/2` and `3/4`; the reference evaluator preserves their gap.

5. **Holomorphic parameter integration.** L1 coefficient names, a rational
   majorant, and a radius gap give series and derivative-tail schedules,
   justify differentiation under the integral, and allow unbounded spatial
   factors. A complete example constructs `integral_0^1 1/(1-z*t) dt` by
   its series, including the value at `z=0`.

6. **Quantitative homological transfer.** A signed perturbation proof gives
   exact finite nilpotent formulas, finite residual certificates, Banach
   Neumann tails, perturbation stability, and explicit filling witnesses.
   Supplied local chain models permit non-acyclic overlaps. Small perturbations
   preserve equivalence to the updated small complex, not necessarily its
   original homology; the report gives an explicit counterexample.

## Exact formal status

The report contains full human-readable constructive arguments. The
standalone Lean project was compiled with **Lean 4.32.0**, using only `Init`
and `Std`. It has **58 proved theorem declarations**, plus two constructors
with proved contract fields. The axiom audit covers all 60 declarations and
reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no
admitted proofs or new correctness axioms in the checked project.

These are **host Lean theorems**. The package does **not** supply completed
new `Prf PRAAx` derivations for the analytic results. It includes explicit
denominator-cleared invariants and a source-accurate plan for constructing
those derivations using ProveIt's existing arithmetic backend.

The checked core includes finite weighted errors, the repaired clipping
estimate, probability-refinement invariance, and regular-name action
construction/composition. `VitaliBlueprint.lean` contains fully typed
definitions and goals for the stronger completed-name assembly. Its goal
definitions do not assert proofs. The homological matrix blueprint is an
uncompiled outline and is excluded from the checked build.

The Python programs validate finite implementations and sample constants with
exact fractions. They do not prove the universal theorems or check iPRA proofs.

The report also proves limitations: boundedness and uniform integrability
cannot automatically provide a uniform computable martingale-convergence
rate; L1 errors do not control suprema; the entire atomless event algebra is
not a compact sort; and an approximate square-zero matrix is not an exact
chain complex. No unrestricted interpretation of analysis in first-order
iPRA is claimed.

## Artifact map

| Path | Contents |
|---|---|
| `paper/report.pdf` | Complete typeset research report. |
| `paper/report.tex`, `paper/sections/`, `paper/references.tex` | Complete editable LaTeX sources. |
| `lean/ContinuousMeasure/` | Checked finite kernels, presentation/action interfaces, and typed Vitali blueprint. |
| `lean/Audit.lean`, `lean/Examples.lean`, `lean/README.md` | Axiom audit, exact examples, and detailed verification scope. |
| `blueprints/HomologicalPlan.lean.txt` | Explicit matrix definitions and theorem targets; uncompiled outline. |
| `blueprints/ObjectArithmeticPlan.txt` | Fully specified natural-number form of the finite Vitali endpoint. |
| `code/measure_examples.py` | Coherent towers, clipping, conditional averages, Vitali budgets, unbounded example, and martingale obstruction. |
| `code/operator_logic_examples.py` | Finite kernels/tensors, tail-sensitive error, conditioning, influence budgets, and binder-preserving formula evaluator. |
| `code/complex_integral_examples.py` | Exact polynomial integral brackets and geometric/derivative-tail checks. |
| `code/homological_examples.py` | Signed perturbations, nonzero finite differential defects, nilpotent cases, and filling transport. |
| `validation/` | Actual Lean replay, numerical results, independent review, and PDF build/layout records. |
| `evidence/source_manifest.json` | Immutable upstream source URLs, Git blob identifiers, and SHA-256 hashes. |
| `evidence/claims_status.json` | Claim-by-claim hypotheses and exact verification status. |
| `verify.py`, `build_pdf.py`, `Makefile` | Reproduction entry points. |
| `MANIFEST.sha256` | Integrity hashes of the other deliverable files. |

## Reproduce

The Python examples use only Python's standard library. Run from the package
root, without `-O`:

```sh
python3 verify.py
```

With the pinned Lean toolchain installed through Elan:

```sh
bash lean/replay.sh
```

Or point to a standalone distribution:

```sh
LEAN_LAKE_BIN=/absolute/path/to/lean-4.32.0-linux/bin/lake bash lean/replay.sh
```

To rebuild the PDF, use an installed TeX Live/pdfLaTeX distribution with
AMS, Latin Modern, geometry, microtype, booktabs, enumitem, xurl, hyperref,
fancyhdr, and listings packages:

```sh
python3 build_pdf.py
```

On a minimal Debian-style installation whose formats are missing, the helper
creates local format/font-map files from the installed resources. It makes
no system changes and does not download missing packages. PDF rendering and
visual review are separate from the compiler check.

`make verify` runs the examples, Lean replay, and PDF build. The default
`lake` command must then be available, or set `LEAN_LAKE_BIN` as above.
Toolchain binaries, TeX formats, `.lake` caches, and intermediate page images
are not bundled.

## Repository baseline

The targeted review is pinned to ProveIt commit
`b2341af5370cd8a43f72ebb2341c0d7d7395b634`. The package credits the existing
completion, continuous-model, finite-probability, error-DAG, complex-series,
and finite perturbation work. The existing object-iPRA modules were inspected,
not rebuilt in this session. No branch, pull request, or remote repository
file was changed.
