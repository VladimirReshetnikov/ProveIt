# Gaussian Polylogarithms Beyond Parity

**Exact relation modules, an octahedral proof of the mixed harmonic sum, and global angular-zero geometry**

Research continuation prepared for ProveIt, 10 October 2026. The article is 35 pages. Its baseline is the consolidated manuscript at commit [`9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`](https://github.com/VladimirReshetnikov/ProveIt/tree/9bc738d3be22b8586a24693f19fb2e2a50ecd1bf/Analysis/Polylogarithms/docs/manuscript).

## Main results

- The manuscript's odd-weight rank conjecture is proved, with a complete polynomial kernel, even-weight ranks, explicit separating integer vectors, and a quadratic-arithmetic normal-form algorithm. A character calculation gives the analogous rank at every cyclotomic level N >= 3.
- The manuscript's S4 identity is proved by an exact 869-row rational certificate using all-depth double shuffle and octahedral pullbacks. Two independently implemented word verifiers regenerate every row and the target.
- A companion S2 identity, absent from the pinned manuscript, is proved by a 25-row certificate. The full small coefficient table is printed in the article.
- For real a >= 1 and b > 0, the principal branch of F(a,b;z) has no nonzero zeros on the slit plane C \ [1,infinity). Its zero at the origin has multiplicity two.
- Angular zeros exist uniquely at every radius 0 < rho <= 1. At integer outer order they increase strictly with either index and decrease strictly with radius. A strict sixth-root sign theorem and limiting comparisons follow.
- A rational coefficient formula gives the angular-zero expansion to every finite exponential order, uniformly in b > 0 and 0 < rho <= 1. The supplied table includes all 17 nonzero scales below 9, with collisions combined.
- The universal Euler enclosure has the optimal constant one: E_N - 2^(-N) < g(a,b) < E_N. Exact rational endpoints are implemented for positive integer indices.

See `CLAIM_STATUS.md` for hypotheses and proof status. None of these matrix results asserts independence of evaluated periods. The normalized-radius conjecture is explicitly unproved, and the infinite exponential-scale series is not asserted to converge at fixed a.

## Contents

| Path | Purpose |
|---|---|
| `article.tex` | Complete article source, with an embedded bibliography; only the included figure PDFs are external inputs. |
| `article.pdf` | Compiled article. |
| `figures/` | Vector figures, PNG previews, and a script that renders the recorded numerical data. |
| `code/` | Exact verifiers, normal-form and Euler evaluators, coefficient generators, and optional numerical diagnostics. |
| `data/` | Rational word certificates, zero brackets, coefficient tables, verification receipts, and clearly labelled numerical data. |
| `patches/manuscript_text_corrections.patch` | Three proposed editorial/logical corrections, represented by four exact text replacements. |
| `INTEGRATION.md` | Mapping of the results to the existing manuscript and a suggested integration order. |
| `CLAIM_STATUS.md` | Precise theorem/conjecture boundaries and parameter scopes. |
| `SHA256SUMS.txt` | SHA-256 digest of every delivered file except the digest manifest itself. |

## Reproduce the exact verification

The recorded environment used Python 3.12.14. From the extracted directory:

```bash
python -m pip install -r code/requirements.txt
python code/run_verification.py
```

All nine exact verification groups passed in the recorded run and in a second run invoked from `/tmp`. The runner is read-only with respect to the reference certificates. It checks source/data hashes in its receipt, regenerates every identity row, replays the independent word implementation, checks the coefficient table and rational root signs, tests the universal Euler evaluator, and checks the finite matrix examples against the analytic formulas.

The identity, coefficient, interval, and Euler subset needs only Python's standard library:

```bash
python code/run_verification.py --certificates-only
```

Do not use `python -O`: the runner explicitly rejects optimization mode because the proof replays use assertions. The detailed commands and dependency boundaries are in `code/README.md`.

To produce a new receipt and log without changing the supplied ones:

```bash
python code/run_verification.py --receipt my_verification.json --log my_verification.log
```

The finite rank checks validate an implementation of the all-weight proof; they do not prove an infinite pattern by extrapolation. The word certificates, in contrast, are finite rational equalities and become proofs of the two particular identities once their analytically justified generating relations are supplied. The article provides those justifications, including degree-one regularization for conditionally convergent colored sums.

## Build the article

With a normal TeX Live installation containing the packages named in the preamble:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Equivalently, run `make` or run `pdflatex` enough times to resolve the contents and references. The delivered PDF was built with pdfTeX 1.40.25 / TeX Live 2023. The final log had no unresolved references or citations, no overfull or underfull boxes, and no LaTeX warnings. The bibliography is embedded, so BibTeX and network access are unnecessary. Both vector figure PDFs are included.

To regenerate the figures and optional diagnostics, install the additional dependencies in `requirements-all.txt`. Figure generation reads the recorded diagnostic data:

```bash
python -m pip install -r requirements-all.txt
python figures/generate_figures.py
```

The plotted roots are floating-point illustrations, not interval certificates. The separate rational zero certificates are checked by `code/certify_zeros.py` and by the exact runner.

## Practical exact evaluator

```bash
python code/universal_euler.py 4 1 400
```

This returns the exact rational interval of width 2^(-400) for the Gaussian value g(4,1). The new constant one is valid at every positive integer harmonic exponent, including b = 1. The analytic theorem is broader and allows real a >= 1, b > 0, but exact rational endpoints require integer parameters.

## Provenance and integration

`code/upstream/` contains two unchanged, explicitly attributed source-code snapshots from the pinned repository revision so that the matrix comparison is reproducible. `data/source_snapshot_sha256.json` identifies the manuscript source files read for this continuation. The theorem and certificate claims are new relative to that revision; the established parity, double-shuffle, and octahedral methods are cited in the article. No exhaustive worldwide-priority claim is made.

The supplied patch was checked against an isolated copy of the pinned source. It was not applied to the user's repository. `INTEGRATION.md` explains how to promote the two conjectures after their proofs and artifacts have been incorporated, and why the existing depth-two obstruction should be retained.

