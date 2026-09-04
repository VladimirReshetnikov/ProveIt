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
- The former `SHA256SUMS.txt` delivery ledger was retired repository-wide on
  2026-09-01; its final snapshot remains recoverable from Git history.

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
pdflatex -interaction=nonstopmode -halt-on-error dyadic_stein_koopman_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error dyadic_stein_koopman_frontier.tex
pdflatex -interaction=nonstopmode -halt-on-error dyadic_stein_koopman_frontier.tex
```

The original build used pdfLaTeX from TeX Live 2025. The PDF was also rendered page-by-page and preflighted with PyMuPDF and Poppler utilities.

The repository copy uses the supplied PNG figure companions to avoid the
Type-3 fonts embedded by the vector plots, and falls back to Latin Modern Mono
when `inconsolata.sty` is unavailable.  The checked-in PDF was rebuilt for
exactly three pdfLaTeX passes with embedded/subset Libertinus prose fonts;
`pdf_inspect.txt` and `pdf_preflight.txt` retain the arrival-time preflight.
The current source was rebuilt from clean auxiliaries on 2026-08-31 in exactly
three strict serial passes, producing 30, 32, and 32 pages. The 1,913-line,
81,554-byte source has SHA-256
`61cf3646a6a04b7c1824323630f8eab1eeb29bfe58eed9f228f816913cd6846f`;
the synchronized 854,688-byte PDF has SHA-256
`0515e770996b039841926343bf136ac4fa918501545b1b74bcd747638e5f3d3a`.
All 32 pages are A4 at rotation zero and have nonblank extractable text. All 25
font entries are embedded and subset, five are Libertinus, and none is Type 3.
The final log has no unresolved reference/citation, rerun request, overfull
box, or TeX error. Its eight underfull notices are benign; the remaining
notices are expected math-font size substitutions on the display title and
the explicit disabled-shell-escape notice. PDF metadata is complete, and
physical pages 1, 14, 18, and 32 were rendered and inspected.

## Tested environment

- Python 3.13.5
- SymPy 1.14.0
- mpmath 1.3.0
- NumPy 2.3.5
- Matplotlib 3.10.8

The source contains no network calls. Exact arithmetic is kept separate from floating-point evaluation so numerical approximation cannot conceal a symbolic failure.

## Status and priority convention

The report rigorously proves the statements labeled theorem, proposition, lemma, or corollary under their stated hypotheses. Conjectures and research problems are explicitly labeled. “New” means that the claim was not located in the inspected repository corpus under the stated normalizations; it is not an unconditional claim of worldwide publication priority.
