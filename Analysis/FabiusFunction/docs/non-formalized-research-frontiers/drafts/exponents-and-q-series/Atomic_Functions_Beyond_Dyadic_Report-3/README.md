# Atomic Functions Beyond the Critical Dyadic Case

This archive contains an English reconstruction and expansion of the supplied
Russian chapter on Rvachev atomic functions.  The report follows the notation,
typography, and theorem conventions of the `ProveIt` Fabius-function corpus.

The document explicitly distinguishes four kinds of statements:

- **[S]** translated or cleanly reconstructed from the supplied source;
- **[R]** connected to results already present in the repository or classical literature;
- **[N]** proved in this report;
- **[C]** conjectural or proposed for future work.

## Main files

- `Atomic_Functions_Beyond_Dyadic.tex` — LaTeX source.
- `Atomic_Functions_Beyond_Dyadic.pdf` — compiled report.
- `experiments.py` — fully reproducible numerical experiments, with detailed comments.
- `figures/` — vector PDF and raster PNG versions of all figures.
- `data/` — CSV audit tables for gap geometry, exact norms, tube and distance laws,
  moment formulae, Gaussian scaling, periodicity, and Gamma-zeta Fourier modes.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums of the files in the release, excluding the checksum file itself.

## Rebuild

From this directory:

```bash
python experiments.py --output .
latexmk -pdf -interaction=nonstopmode -halt-on-error Atomic_Functions_Beyond_Dyadic.tex
```

The pseudorandom seed is fixed at `20260828`.  For the random-series experiment at
`a=2.6`, the omitted series tail is bounded deterministically by `1e-12`.

## Scope and provenance

The supplied OCR transcription and page images are the translation basis.  Damaged
indices are reconstructed only when the surrounding formulas determine them; unresolved
literal details are recorded in the OCR ledger rather than silently invented.  The current
repository corpus and its manifests were used to align notation and to avoid intentional
formula-level duplication.  The labels **[N]** therefore mean “proved here and not found as
an exact statement in the audited repository snapshot,” not a claim of priority over all
published literature.
