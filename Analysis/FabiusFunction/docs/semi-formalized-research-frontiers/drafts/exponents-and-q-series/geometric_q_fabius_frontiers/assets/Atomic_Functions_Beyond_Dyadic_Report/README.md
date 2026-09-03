> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Atomic_Functions_Beyond_Dyadic_Report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions Beyond the Critical Dyadic Case

This package contains the English reconstruction and substantial expansion of the attached Russian chapter on Rvachev atomic functions.  The report follows the notation and proof-status conventions used in the `ProveIt` Fabius-function corpus, while keeping translated source statements, repository/literature connections, newly proved results, and conjectures visibly separate.

## Package contents

- `Atomic_Functions_Beyond_Dyadic.tex` — complete LaTeX source.
- `Atomic_Functions_Beyond_Dyadic.pdf` — compiled 30-page report.
- `experiments.py` — fully commented, deterministic numerical experiments.
- `figures/` — five figures in both PDF and PNG formats.
- `data/` — CSV audits for geometry, derivative norms, moments, periodicity, and Gamma–zeta Fourier modes.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums for every packaged file except the checksum manifest itself.

## Mathematical scope

The reconstructed source material includes:

- the Fourier-product criterion for compactly supported solutions of differential–functional equations;
- the generalized densities
  \[
  \widehat h_a(t)=\prod_{j\ge 1}\operatorname{sinc}(t a^{-j}),\qquad a>1;
  \]
- the probabilistic representation of `h_a` as the density of a geometrically weighted sum of independent uniform random variables;
- the full-measure spline structure for `a>2` and the critical Rvachev function `h_2=up`;
- moment recurrences, dyadic values, Thue–Morse signs, polynomial reproduction, and the opening of the `Fup` hierarchy.

The main additional results developed in the report are:

1. an exact identification of the nonanalytic set for `a>2` with a two-map Cantor attractor;
2. the exact local polynomial degree on every complementary gap;
3. closed `L^1` and `L^∞` norms for all derivatives;
4. a geometric zeta function, complete complex-dimension lattice, and exact tube formula;
5. a geometric distribution for the local polynomial degree and its critical exponential limit as `a↓2`;
6. Bernoulli-number cumulants, complete Bell-polynomial moments, and their `q`-Lambert structure;
7. Gaussian and uniform parameter limits;
8. an exact arbitrary-base negative-Laplace decomposition with Gamma–zeta Fourier coefficients;
9. a Lambert-`W_{-1}` endpoint program, explicit conjectures, and a research agenda.

## Proof-status legend

The report uses four markers throughout:

- **[S]** — translated or cleanly reconstructed from the attached source;
- **[R]** — established repository or literature connection;
- **[N]** — theorem or formula proved in this report;
- **[C]** — conjecture or presently unproved research direction.

The OCR source is damaged in several formulas.  Those places are recorded in the reconstruction ledger.  The report does not silently manufacture literal transcriptions where a superscript or index cannot be recovered reliably from the printed page.

## Build the PDF

A reasonably complete TeX Live installation is sufficient.  From the package directory, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Beyond_Dyadic.tex
```

The source uses standard TeX Live packages including `amsmath`, `amsthm`, `mathtools`, `mathrsfs`, `booktabs`, `longtable`, `tabularx`, `graphicx`, `microtype`, `hyperref`, and `cleveref`.  Libertinus is used when installed, with Latin Modern as a fallback.

The supplied PDF was built with pdfTeX and TeX Live 2025/dev.  All fonts are embedded.

## Reproduce the experiments

Python 3.10 or later is recommended.  Install the dependencies and regenerate all figures and tables with:

```bash
python -m pip install -r requirements.txt
python experiments.py --output .
```

The numerical layer requires no network access.  Figures are deterministic.  The Monte Carlo validation uses the fixed seed `20260828`, so the generated CSV table is reproducible.  A clean rerun was checked against the packaged PNG figures and CSV files byte-for-byte; PDF figure streams may differ only in creation metadata.

## Repository audit and nonduplication scope

The living canonical TeX documents and the current consolidated frontier volume were inspected directly.  The reorganized frontier drafts and frozen historical archive were audited through the repository-maintained global manifests, with targeted source-level comparisons wherever a title, formula, or parameter range intersected this report.  Superseded archived duplicates were not counted as independent mathematical sources.

“New” therefore means new relative to the audited repository snapshot and the literature explicitly cited in the report.  It is not a claim of worldwide historical priority.  The report’s appendix records the corpus layers, the formula-level nonduplication test, and the exact limits of that audit.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
