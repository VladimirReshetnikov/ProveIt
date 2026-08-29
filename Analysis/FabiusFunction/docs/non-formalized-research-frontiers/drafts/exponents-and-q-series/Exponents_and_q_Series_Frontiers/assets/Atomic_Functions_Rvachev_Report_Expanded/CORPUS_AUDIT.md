# Corpus audit and provenance boundary

## Source materials

The report was prepared from four supplied files:

- `source/rvachev_source_scan.pdf` — the surviving printed Russian pages;
- `source/rvachev_source_ocr.tex` — OCR-derived LaTeX transcription;
- `source/Atomic_Functions_Rvachev_Report_previous.tex` — earlier English report;
- `source/Atomic_Functions_Rvachev_Report_previous_revision.tex` — later English report.

The scan is authoritative whenever it resolves an OCR ambiguity.  Formulae that cannot be
read uniquely are reconstructed only when forced by neighboring equations, the Fourier
convention, or an independently derivable invariant.  Otherwise the report states the
recoverable mathematical content without inventing an exact damaged string.

## Exhaustive pinned audit

The attached later report carried an exhaustive source-level audit pinned to:

- repository: `VladimirReshetnikov/ProveIt`;
- commit: `cc0be20ab445b3f284cb884ebc3c1fc0cd6c54f4`;
- date: 28 August 2026;
- scope: every `*.tex` recursively below `Analysis/FabiusFunction/docs`;
- inventory: 67 TeX documents.

That audit enumerated every path, reviewed titles, abstracts, section structures, theorem
registers, conclusions, and intersecting source formulae, and used the repository's archive
and consolidation manifests to avoid counting frozen duplicates as independent work.

## Live reconciliation

Before finalization, the pinned audit was reconciled with the live `main` branch at:

- commit: `c853d2e8fb9b326742339c7672fe0e130211873a`;
- branch timestamp: 29 August 2026 UTC.

The current recursive tree, draft manifest, consolidation records, and targeted source
searches were checked.  The live manifest explicitly records that the earlier report's
q-Gaussian derivative Gram geometry, q-Pochhammer pivots, theta-function Riesz bounds,
log-Weibull leading-jet law, and proved differentiated all-orders `Fup_n` Edgeworth expansion
have been incorporated into Part VI of the canonical exponent-and-q-series frontier volume.
Those results are therefore labeled as attached-report/current-corpus results in the final
report, not as new discoveries of this revision.

## Nonduplication searches for the new theorems

The following title-, keyword-, and formula-level searches were made against the pinned
inventory and then repeated against the live GitHub source index and manifests.

### Rogers-Szego / q-binomial orthogonalization

Search phrases included:

- `Rogers-Szego derivative`;
- `q-binomial Gram-Schmidt`;
- `Gaussian-binomial orthogonalization`;
- `inverse q-Gaussian Gram`;
- the coefficient pattern
  `(-1)^(n-k) q^(n-k) [n choose k]_(q^2)`.

No equivalent theorem, transform, recurrence identification, or inverse-Gram formula was
located.

### Schur minors and total positivity

Search phrases included:

- `Schur derivative Gram`;
- `Schur-Vandermonde q-Gaussian minor`;
- `strict total positivity`;
- `sparse derivative Gram determinant`;
- generalized minors of `q^((i-j)^2)`.

No equivalent mixed-minor formula or total-positivity theorem was located.

### Refined leading-jet tail

Search phrases included:

- `jet tail log log correction`;
- `two-term log-Weibull`;
- `square-root-log exponential moment`;
- `Orlicz threshold`;
- `boundary divergence leading coefficient`.

The corpus contained the leading staircase/log-Weibull law, but no `log log` correction, no
matching two-sided refinement, and no exact exponential-integrability threshold.

These negative searches establish only **corpus-relative nonduplication**.  Rogers-Szego
polynomials, Schur polynomials, total positivity, and q-binomial inversion are classical
objects; the claim is that their precise derivative-tower synthesis and the stated jet-tail
refinement were not found in the audited `ProveIt` corpus.

## Numerical boundary

`experiments.py` checks, but does not prove:

- the `h_3` fixed point, mass, symmetry, and central plateau;
- the exact geometric local-degree distribution;
- q-Gaussian determinant and theta-symbol bounds;
- the new q-binomial residual orthogonality, norms, and inverse transform;
- selected Schur-Vandermonde mixed minors;
- Gaussian, first-order, and second-order `Fup_n` Edgeworth errors;
- the refined jet-tail residual and below/at/above-threshold partial sums.

Every theorem has an independent proof in the report.  The computations are reproducibility
and indexing diagnostics, not evidence substituted for proof.
