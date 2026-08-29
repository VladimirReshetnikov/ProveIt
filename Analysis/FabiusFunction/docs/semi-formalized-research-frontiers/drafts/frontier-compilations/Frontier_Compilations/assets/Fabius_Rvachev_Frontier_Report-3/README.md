# Zero-Divisor-Preserving q-Richardson Extrapolation

This archive accompanies the report

> **Zero-Divisor-Preserving q-Richardson Extrapolation for the Fabius–Rvachev Sinc Product**

prepared from a recursive audit of the LaTeX documentation under
`Analysis/FabiusFunction/docs` in Vladimir Reshetnikov's `ProveIt` repository.
The report is now displayed as Part III of
[`../../Frontier_Compilations.tex`](../../Frontier_Compilations.tex); this
directory retains only its supporting assets.

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

## Supporting-asset contents

- `corpus_manifest.txt` — exact recursive path inventory.
- `corpus_manifest_table.tex` — breakable LaTeX form of the inventory.
- `code/frontier_experiments.py` — fully commented high-precision experiment suite.
- `data/*.csv` — all numerical tables used in the report.
- `figures/*.png` — all generated figures used in the report.
- `experiment_summary.txt` — compact run summary.
- `requirements.txt` — Python dependencies.
- `SHA256SUMS` — checksums for the retained supporting files.

## Reproduce the numerical experiments

Python 3.10 or newer is recommended. From the archive root:

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
versions used to prepare the archive, a complete run takes only a few seconds.

## Rebuild the consolidated PDF

A reasonably complete TeX Live installation is sufficient. From this asset directory,
move to the consolidated-volume directory and run the repository-required three passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
rm -f *.aux *.log *.out *.toc
```

The canonical output is
[`../../Frontier_Compilations.pdf`](../../Frontier_Compilations.pdf).

## Verification notes

The packaged numerical outputs were regenerated from a clean temporary directory and
compared byte-for-byte with the included CSV and PNG files. Before consolidation, the
standalone PDF was rendered page by page at 180 dpi and visually inspected for clipping,
overlap, broken glyphs, and unreadable equations.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Frontier_Compilations.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
