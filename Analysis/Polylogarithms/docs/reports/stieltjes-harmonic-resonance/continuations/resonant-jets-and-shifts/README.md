# Resonant Gamma Jets and Directional Zeta Identities

A research continuation prepared for Vladimir Reshetnikov and the ProveIt project, 10 October 2026.

The article contains complete analytic proofs, domains and normalization conventions, independent numerical and exact symbolic diagnostics, a source audit, and twelve further research questions. Its primary targets are questions 3, 4, and 7 in the incoming **Nested Harmonic Jets and Gamma Renormalization** report.

## Main results

- An all-degree discrete Stieltjes product identity with an exact finite-cutoff remainder.
- The complete polar germ of double Hurwitz zeta at `(1,1)`, every transverse directional finite part, curved-path and reparametrization corrections, and every regular Taylor coefficient.
- A finite partition algorithm for every Laurent coefficient of the fully labelled symmetrization at arbitrary depth and independent directions.
- Every fixed-argument spectral derivative at every Gamma zero, expressed by Bell polynomials and finitely many normalized Stieltjes antiderivatives. A closed second-derivative evaluation is included.
- A continuous-argument two-shift Lerch reflection and complete complementary-shift double-polylogarithm reductions, with derivative and primitive formulas.
- An all-order polynomial calculus for normalized spectral weights, exact local finite differences, and an alternating Vandermonde theorem for any number of factors. Its examples include a six-term second-derivative evaluation and a 24-term fifth-derivative evaluation. Logarithmic multiplicities and higher poles are also treated.

## Mathematical status

The algorithmic part of Nested Harmonic Jets question 7 is solved; arithmetic minimality is not. Ordered depth-two transverse paths and all fully symmetrized higher-depth directions are handled; general individual ordered higher-depth germs and a canonical algebra-preserving renormalization remain open. The source's current short `S6` and `S8` arithmetic evaluations remain conjectural.

Classical symmetric-sum, parity, and first-derivative multiplicative-anomaly results retain their attribution. The article does not claim exhaustive literature priority. A typographical denominator correction in Gurel's arXiv:2504.14563v2, Theorem 1.1, is derived explicitly. No fresh substantive error was found in the relevant current repository proofs audited here.

## Files

| Path | Purpose |
|---|---|
| `article.pdf` | Complete typeset article |
| `article.tex` | Main LaTeX file |
| `article_singlefile.tex` | Complete standalone LaTeX source with all sections and references included |
| `sections/` | Eight modular source sections |
| `references.tex` | Bibliography, including the pinned source baseline |
| `build.py` | Local PDF build command |
| `verification/` | Six independent check programs and a replay runner |
| `results/` | Recorded results, replay logs, runtime information, and PDF QA record |
| `integration/INTEGRATION_NOTES.md` | Placement, dependencies, labels, and status guidance |
| `integration/theorem_index.json` | Machine-readable theorem labels and article locations |
| `integration/source_manifest.json` | Pinned repository revision and SHA-256 hashes of inspected sources |
| `integration/result_status.json` | Proved/partial/open classification of source targets |
| `MANIFEST.sha256` | Hashes of the deliverable files |

## Build the article

From the extracted package directory:

```bash
python build.py
```

The build uses `latexmk` and `pdflatex` from TeX Live. If `latexmk` is unavailable, the script runs `pdflatex` three times. Required packages are the usual AMS, Latin Modern, geometry, mathtools, booktabs, longtable, enumitem, microtype, xurl, fancyhdr, hyperref, bookmark, and needspace packages. No bibliography tool, external figures, shell escape, source-repository checkout, or network access is required.

## Replay the checks

Use Python 3.10 or later. The recorded environment used mpmath 1.3.0 and SymPy 1.14.0.

```bash
python -m pip install -r requirements.txt
python verification/run_all.py --jobs 3
```

The full replay may take several minutes. Use `--jobs 1` to reduce concurrent resource use. Individual scripts may also be run directly; they write their reports to `results/`. The fixed precision and thresholds are recorded in the code and JSON outputs. Failure returns a nonzero exit code.

Exact checks include 44 Stieltjes/directional/partition identities, seven base-invariance polynomial checks, and three fully symbolic Vandermonde checks. The partition tests enumerate 11,808 distinct labelled tuples at depths two through five with genuine half-integer exponents and rational shifts.

Numerical diagnostics compare independent representations: Hermite integrals versus Stieltjes endpoint values, Cauchy coefficients of Euler–Maclaurin double-zeta continuations, the original spectral product versus the Gamma-zero coordinate formula, and Mellin quadrature versus shifted-gap reductions. They corroborate the proofs; they are not interval certificates, formal proof-assistant output, or proofs of arithmetic independence.

## Source baseline

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Revision: `16c7e342d7a4a15f59911f322eb90b7f96c2a8b5`.

Both `Analysis/Polylogarithms/docs/manuscript` and all five archives present in `docs/incoming` at this revision were used. The SHA-256 source manifest identifies the exact downloaded material. Repository integration is proposed; this package does not imply that any remote branch was modified.

