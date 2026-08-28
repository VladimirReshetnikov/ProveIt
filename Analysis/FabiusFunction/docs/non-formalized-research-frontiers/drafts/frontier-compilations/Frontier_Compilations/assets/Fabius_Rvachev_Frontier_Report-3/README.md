# Zero-Divisor-Preserving q-Richardson Extrapolation

This retained companion directory preserves the reproducible computations and source data
that accompanied source report III of the consolidated volume

> **Zero-Divisor-Preserving q-Richardson Extrapolation for the Fabius–Rvachev Sinc Product**

prepared from a recursive audit of the LaTeX documentation under
`Analysis/FabiusFunction/docs` in Vladimir Reshetnikov's `ProveIt` repository.
The formerly standalone manuscript now appears in the consolidated frontier volume: its
source is `../../Frontier_Compilations.tex`, and its rendered PDF is
`../../Frontier_Compilations.pdf`. Those volume files are referenced rather than duplicated
here. Paths below are relative to this companion directory unless stated otherwise.

## Audited snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Commit: `7f4e6e6fdd57f756f303b20f56b5382627e5e1d4`
- Subtree: `Analysis/FabiusFunction/docs`
- TeX sources audited: **68**

The exact path inventory is in `corpus_manifest.txt`; the generated, line-breakable
LaTeX rendering used by the report is `corpus_manifest_table.tex`.

## Main mathematical outcomes

The report develops two theorem packages that were not found in the audited corpus.

1. A factorized geometric q-Richardson transform is applied only to the zero-free tail
   of the infinite sinc product. Multiplication by the exact finite prefix then gives a
   holomorphic approximant that preserves every included zero and its multiplicity.
   The same exact Bernoulli–zeta logarithmic remainder survives after cancellation, so
   Bell-polynomial and Cauchy estimates certify the complete zero-normalized local germ.

2. For the positive logarithmic error magnitudes `M_r(q,a)`, uniform same-parity
   nesting is classified exactly by

   ```text
   M_{r+2}(q,a) < M_r(q,a) for every 0 < a < 1
       iff q^(r+1) (1+q) <= 1.
   ```

   When this inequality fails, the two same-parity errors cross exactly once. For the
   dyadic Rvachev product, `q=1/4`, all orders are nested and form two monotone chains.

Novelty is claimed relative to the pinned repository corpus and the targeted literature
search recorded in the report, not as an unconditional worldwide priority claim.

## Retained companion contents

- `../../Frontier_Compilations.tex` — source of the consolidated volume containing this report.
- `../../Frontier_Compilations.pdf` — rendered consolidated volume.
- `corpus_manifest.txt` — exact recursive path inventory.
- `corpus_manifest_table.tex` — breakable LaTeX form of the inventory.
- `code/frontier_experiments.py` — fully commented high-precision experiment suite.
- `data/*.csv` — all numerical tables used in the report.
- `figures/*.png` — all generated figures used in the report.
- `experiment_summary.txt` — compact run summary.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums for the retained files.

## Reproduce the numerical experiments

Python 3.10 or newer is recommended. From this asset directory:

```bash
python -m venv .venv
# Linux/macOS:
. .venv/bin/activate
# Windows PowerShell:
# .venv\Scripts\Activate.ps1

python -m pip install -r requirements.txt
python code/frontier_experiments.py --output-dir .
```

The script has no network dependency. It regenerates `data/`, `figures/`, and
`experiment_summary.txt`. It performs internal consistency checks between the closed
q-Lagrange identities, exact coefficient series, and direct sinc products. With the
versions used to prepare the original package, a complete run takes only a few seconds.

## Rebuild the consolidated PDF

A reasonably complete TeX Live installation is sufficient. From this companion directory,
run exactly three serial `pdflatex` passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
```

These commands rebuild `../../Frontier_Compilations.pdf`. The document uses
Libertinus when available and falls back to Latin Modern.

## Verification notes

The retained numerical outputs were regenerated from a clean temporary directory and
compared byte-for-byte with the included CSV and PNG files when the standalone package was
prepared. Before consolidation, its PDF was rendered page by page at 180 dpi and visually
inspected for clipping, overlap, broken glyphs, and unreadable equations. The consolidated
PDF is built and inspected at the volume level.
