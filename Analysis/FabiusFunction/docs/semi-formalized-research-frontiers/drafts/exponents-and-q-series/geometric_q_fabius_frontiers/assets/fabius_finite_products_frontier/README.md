> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part V** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/fabius_finite_products_frontier/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Finite dyadic sinc products and Rvachev spline approximants

This archive accompanies **Finite Dyadic Sinc Products and Exact Transport Geometry: Piecewise-polynomial approximants to Rvachev's up-function**.

The report studies the inverse Fourier transforms

\[
\Phi_N(\xi)=\prod_{j=1}^N \operatorname{sinc}(\xi/2^j),
\qquad u_N=\mathcal F^{-1}\Phi_N,
\]

as compactly supported dyadic box splines converging to Rvachev's normalized up-function `u`.

## Main files

- `finite_sinc_frontier.tex` — complete LaTeX source.
- `finite_sinc_frontier.pdf` — rendered 28-page report.
- `finite_sinc_experiments.py` — fully commented numerical experiment and figure generator.
- `requirements.txt` — exact Python package versions used for the bundled run.
- `CORPUS_AUDIT.md` — repository pin, novelty boundary, and source hashes.
- `figures/` — vector PDF figures and PNG previews.
- `data/` — CSV tables, generated LaTeX row fragments, and numerical diagnostics.

## Reproduce the numerical layer

The bundled run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, and Matplotlib 3.10.8.

```bash
python -m venv .venv
source .venv/bin/activate          # PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python finite_sinc_experiments.py --output . --grid-power 18 --max-stage 10
```

The command reconstructs `u` and `u_N` from their period-two Fourier series on a grid of `2^18` points, regenerates all CSV files and figures, and prints the reference entropy/Fisher constants. It requires about 0.8 GB of peak memory in the supplied environment. A smaller exploratory run can use `--grid-power 16`; the exact identities remain visible, but the smallest-stage-relative errors are less accurate.

The program performs no network access and has no hidden data dependencies.

## Build the report

The bundled PDF was compiled with LuaHBTeX 1.18.0 and `latexmk` 4.86:

```bash
latexmk -lualatex -interaction=nonstopmode -halt-on-error finite_sinc_frontier.tex
```

The report uses Libertinus text and mathematics. A reasonably complete TeX Live installation with `libertinus`, `unicode-math`, `mathtools`, `cleveref`, `booktabs`, `longtable`, `listings`, and `microtype` is required.

## Numerical verification summary

For the `2^18`-point run:

- `∫u = 1`;
- `max u = 1.0000000000000004`;
- `∫|u'| = 2`;
- `∫|u''| = 8.0000000000000018`;
- `h(u) ≈ 0.29703991282607117`;
- `I(u) ≈ 11.800710543419124`;
- `∫u''²/u ≈ 1619.745753584979`;
- largest relative `W_1` error for `2 ≤ N ≤ 10`: `2.17e-7`;
- largest relative stop-loss-height error: `1.10e-8`.

The report distinguishes proved exact identities from weighted endpoint asymptotics that are supported numerically but remain conjectural.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
