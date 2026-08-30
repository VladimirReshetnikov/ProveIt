# Dyadic Stein--Koopman and q-Oscillator Calculus

This archive accompanies the report

**Dyadic Stein--Koopman and q-Oscillator Calculus for the Fabius--Rvachev Law**

prepared on 30 August 2026 for Vladimir Reshetnikov's `ProveIt` Fabius-function program.

## Main files

- `dyadic_stein_koopman_frontier.tex` — complete LaTeX source.
- `dyadic_stein_koopman_frontier.pdf` — rendered 32-page report.
- `experiments.py` — deterministic, extensively commented exact-symbolic and numerical experiments.
- `data/` — generated exact formulas and numerical tables.
- `figures/` — vector and raster versions of the two plots used in the report.
- `CORPUS_AUDIT.md` — the repository comparison protocol and nonduplication boundary.
- `BUILD.sh` — reproducible regeneration and compilation commands.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS.txt` — checksums for the delivered files.

## Reproduce the experiments

From this directory, run:

```bash
python -W error experiments.py --sample-size 300000 --max-dyadic-depth 120
```

The script performs exact rational and symbolic checks before running the Monte Carlo experiment. It then regenerates the files under `data/` and `figures/`.

The exact verification layer checks, among other things:

1. the Appell--Koopman eigenvalue identity through degree 10;
2. the differential-dilation Stein identity through degree 10;
3. exact reconstruction of all polynomials through degree 10;
4. the finite transfer-determinant identity through degree 8;
5. exact dyadic Fabius and Stein-kernel values through depth 120.

The stochastic experiment is used only to illustrate the already-proved lag-correlation formulas and is not part of any proof.

## Compile the report

With a reasonably complete TeX Live installation:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_stein_koopman_frontier.tex
```

The build used pdfLaTeX from TeX Live 2025. The PDF was also rendered page-by-page and preflighted with PyMuPDF and Poppler utilities.

## Tested environment

- Python 3.13.5
- SymPy 1.14.0
- mpmath 1.3.0
- NumPy 2.3.5
- Matplotlib 3.10.8

The source contains no network calls. Exact arithmetic is kept separate from floating-point evaluation so numerical approximation cannot conceal a symbolic failure.

## Status and priority convention

The report rigorously proves the statements labeled theorem, proposition, lemma, or corollary under their stated hypotheses. Conjectures and research problems are explicitly labeled. “New” means that the claim was not located in the inspected repository corpus under the stated normalizations; it is not an unconditional claim of worldwide publication priority.
