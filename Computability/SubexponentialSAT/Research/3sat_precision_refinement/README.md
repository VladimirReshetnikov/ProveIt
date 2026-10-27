# Sharper precision for subexponential 3SAT

Research memorandum for Vladimir Reshetnikov, October 26, 2026.

**Start with `report.pdf`.** Its complete editable LaTeX source is `report.tex`.

## Result and status

The report analyzes OpenAI's October 25, 2026 manuscript at commit
`42907c9e999cc00d6abe7a50bfc1023250edd1b9`.

The proved refinement uses the exact number of Hermite interpolation
conditions and the exact two-adic recovery loss. It replaces the source's
dominant working-precision bound `(24 + o(1)) M D / u` by at most
`(6 + o(1)) M D / u`. This halves the leading constant in the standard
exponential upper bound for weighted mode enumeration. The report also
solves the real full-loss taper minimax problem exactly.

**The logarithmic asymptotic order is unchanged by that proved refinement.**
The report separately proposes a structured-mode summation method that,
if the stated missing algorithmic hypothesis is established, would yield
`poly(n,m) * 2^{O(n log log n / log n)}` for general fixed-width CNF and
`poly(n,m) * 2^{O(n / log n)}` at fixed clause density. Those stronger rates
are conditional. No implementation or proof of the missing summation
algorithm is included.

The Python code is a set of exact schedule routines and finite algebraic
prototypes. It is not a complete subexponential SAT solver. The source Lean
formalization was inspected for scope but was not rebuilt.

## Contents

| File or directory | Purpose |
| --- | --- |
| `report.tex`, `report.pdf` | Complete mathematical report, with proofs and source links |
| `code/precision_schedule.py` | Exact source and refined precision schedules; JSON CLI |
| `code/verify_precision_schedule.py` | Exact recovery tests, independent multiplier checks, and precision-boundary tests |
| `code/mode_network.py` | Small Cauchy deformation and compressed mode-rank contraction |
| `code/verify_mode_network.py` | Direct sum / mode sum / compressed contraction comparisons |
| `code/verify_bounds.py` | Independent taper, Hermite, and partition-family checks |
| `results/` | Machine-readable outputs and clearly labeled exponent-scale comparisons |
| `notes/` | Detailed supporting derivations and conditional assumptions |
| `source_manifest.json` | Pinned upstream URLs, Git blob IDs, and SHA-256 hashes |
| `MANIFEST.sha256` | Checksums of the packaged deliverables |

The original paper is linked rather than bundled. Source bytes inspected
for the analysis were checked against the Git blob identifiers recorded
in `source_manifest.json`.

## Reproduce the checks

Python 3.10 or later is sufficient; no third-party Python packages are
required. Run from the extracted archive directory:

```sh
python3 code/verify_precision_schedule.py
python3 code/verify_mode_network.py
python3 code/verify_bounds.py
```

On Windows, `python` may be used in place of `python3`. The scripts write
their results under `results/` using paths relative to the package, so
they can also be invoked from another working directory.

Example of the reference precision routine:

```sh
python3 code/precision_schedule.py --wires 1000 --packet-exponent 12 --levels 6 --input-precision 1001 --strategy linear
```

The other refined strategies are `equal-loss` and `finite-optimal`.
The output includes the published source baseline. The latter two
strategies round continuous optima upward; they do not claim exact
integer minimax optimality.

## Verification performed for this package

All recorded checks passed:

- 7 precision-module unit tests and 40 exact Hermite recovery fixtures.
- 304 direct precision multiplier checks and 304 sharp precision-boundary checks.
- 9 mode-network unit tests and 11 exact identity fixtures.
- 133,376 direct Boolean assignment pairs, 847 feasible mode tuples,
  and 456 invalid rank strings handled correctly.
- 5,460 exhaustive taper profiles, 92,840 finite-tail checks, and
  46 direct rational Hermite products in the independent bounds verifier.
- Four exact binary-family witnesses and seven complete schedule comparisons.

These finite checks support the local algebra and implementations. They
do not replace the report's proofs, establish the conditional summation
hypothesis, certify practical speed, or replay the source Lean development.

## Rebuild the PDF

With a standard TeX Live or MiKTeX installation that provides `latexmk`
and the packages named in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The included PDF was compiled from the included source and visually
reviewed after rendering. No external figures or bibliography downloads
are required for compilation.

## Primary sources

- [Paper directory](https://github.com/openai/math/tree/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026)
- [Quantitative contraction appendix](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex)
- [Quantitative reduction appendix](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex)
- [Formalization scope](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/lean/docs/378.md)

This package has not been committed to or published in any GitHub repository.
