# Sharp Fixed-Phase Order of Rvachev Quadrature

Research manuscript prepared with ChatGPT, 29 September 2026.

## Main results

For the normalized Rvachev lattice quadrature at mesh parameter M = 2^d,
the maximal polynomial exactness at a fixed phase is exactly d+1. The two
known special phases both fail at degree d+2. The article proves this for
all d >= 0, with a signed leading term and relative error less than 1/4.

For M = 2^(r-1)m with m positive and odd, the article gives an exact
next-defect identity, an explicit sufficient nonvanishing inequality, and
eventual maximality. An entirely elementary sufficient cutoff is

    J = max(2, 1 + ceil(log2(m)))
    r >= 2*J*(m+1) + 4.

The article also proves a stationary-point classification for the first
defect, stability under C^1 perturbations, a parity-dependent exponential
expansion, and sharp-order consequences for deconvolved synthesis and
uniform-grid refinement.

## Files

- `article.tex`: self-contained LaTeX source, including bibliography.
- `article.pdf`: compiled 21-page article.
- `build.sh`: serial three-pass PDF build.
- `reproducibility/verify.py`: independent exact and numerical checks.
- `requirements.txt`: numerical-check dependency used for this run.
- `validation/exact_results.json`: 978 passed exact assertions and rational outputs.
- `validation/numerical_results.json`: 960 passed numerical assertions and diagnostics.
- `validation/artifact_validation.json`: build, rendering, and artifact metadata.

## Build the article

A TeX Live installation with newtx, amsmath/amsthm, mathtools, microtype,
geometry, booktabs, array, longtable, enumitem, fancyhdr, xurl, hyperref,
and cleveref is required. From this directory run:

```sh
bash build.sh
```

The bibliography is embedded in the source; BibTeX is not needed. There
are no external figure or font files in the package.

## Reproduce the checks

The exact component needs only Python's standard library:

```sh
py reproducibility/verify.py --exact-only
```

For the numerical component:

```sh
uv run --no-project --with mpmath==1.3.0 python reproducibility/verify.py --numeric-only
```

With no option, the program runs both sets. Results are written to
`validation-rerun/`, or to the directory given by `--output-dir`; only
`--output-dir validation` overwrites the recorded results. The exact dyadic evaluator rejects non-dyadic
arguments rather than silently rounding them.

## Status and boundaries

These are ordinary analytic proofs, not new Lean-verified declarations.
No Lean build was run. The numerical component uses high-precision
floating-point arithmetic, not directed-rounding intervals; its assertions
are diagnostics and are not claimed as certified real-number inequalities.
The main theorems are proved analytically without assuming test success.

The general all-level, all-integer-mesh maximality question remains open in
this manuscript. Every dyadic mesh is settled, and for every fixed odd
part all sufficiently large refinement levels are settled with an explicit
cutoff. A failed sufficient test does not establish an exceptional mesh.

The earlier repository article already proves first-superconvergent phase
completeness and classifies optimal uniform phase filters. Those results
are credited, not claimed as new here. Novelty relative to the entire
literature has not been independently certified.

## Repository provenance

Inspected ProveIt snapshot:

    23dd71d2d3d5e85d2b97a8cc45f55e735d69a4ae

Primary baseline manuscript:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/
    drafts/inverse-and-sampling/comb-interpolation/
    Optimal_Phase_Filters/article.tex

Baseline title: "Complete Superconvergence Phases and Optimal Phase
Filters for Rvachev Quadrature", dated 28 September 2026. It explicitly
leaves fixed-phase next-degree maximality as a further research question.

Relevant Lean module:

    Analysis/FabiusFunction/Lean/FabiusFunction/
    RvachevSuperconvergentSynthesis.lean

The article contains full source references and a proof-dependency ledger.
No repository files were changed.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 56 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the program `ed. (2026-09-29)`.
The byline "prepared with ChatGPT" is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. One note, at the end of the
  introduction's paragraph on the earlier phase-filter manuscript, records
  that this article answers Question 1 ("Fixed-phase maximality beyond the
  first extra degree") of `../Optimal_Phase_Filters/` for every dyadic mesh
  and, from the explicit level of Theorem `thm:elementary` on, for every odd
  part, while the finitely many lower levels of each non-dyadic mesh remain
  open; that the completeness of the first-failing-level phase set is also
  Theorem `thm:phase-zero-set` of the canonical synthesis
  `../comb_interpolation_synthesis/`; and that the phase-uniform sharpness
  of exactness through degree `nu_2(M)` is machine-checked as
  `Fabius.exists_shift_tsum_shifted_monomial_ne_integral_nat_real`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/CompositeMeshSharpness.lean`).
  Neither is cited by the article, and its fixed-phase results have no Lean
  statement. A reciprocal note now stands after Question 1 in
  `../Optimal_Phase_Filters/article.tex`. The title page no longer sets a
  PDF page anchor (it duplicated the destination `page.1`).
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (MiKTeX pdfTeX 1.40.29): 21 pages as delivered, no error, undefined
  reference or citation, duplicate destination, or overfull box; the page
  carrying the note was rendered and inspected.
- `reproducibility/verify.py`: new option `--output-dir`, default
  `validation-rerun/`, so a plain run no longer overwrites the recorded
  `validation/` results; the JSON files are written with LF line endings on
  Windows too. A rerun of the amended program on a copy (2026-09-29,
  `uv run --no-project --with mpmath==1.3.0 python reproducibility/verify.py`,
  Python 3.13.5; 978 exact and 960 numerical checks passed) reproduced
  `validation/exact_results.json` and `validation/numerical_results.json`
  byte for byte.
- `validation/artifact_validation.json`: a build record, filed as data. Its
  three delivered file digests were verified (3/3) on filing (batch 56).
  After the amendments above its `pdf_pages`, `pdf_bytes` and `sha256`
  entries were recomputed for the filed `article.tex`, `article.pdf` and
  `reproducibility/verify.py`, and a key `editorial_amendment` says so; its
  other fields describe the delivered build.
- `README.md`: the commands and output location under "Reproduce the
  checks", and this section.
