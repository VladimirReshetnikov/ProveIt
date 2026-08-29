# Closing the Rvachev-Lagrange Loop

This package accompanies the report on exact fixed-radius synthesis of
Lagrange polynomials by literal shifts of Rvachev's `up` function and the
resulting self-representation/projector algebra.

## Contents

- `Rvachev_Lagrange_Loop_Report.tex` - complete LaTeX source.
- `Rvachev_Lagrange_Loop_Report.pdf` - compiled 28-page report.
- `self_representation_experiments.py` - exact and numerical experiments,
  with detailed comments.
- `results/` - generated CSV and JSON data.
- `figures/` - generated PDF and PNG figures used by the report.
- `REPOSITORY_SNAPSHOT.txt` - pinned repository provenance.
- `requirements.txt` - Python dependencies.
- `SHA256SUMS` - checksums for all packaged files except the checksum file.

## Rebuild the report

From this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error Rvachev_Lagrange_Loop_Report.tex
```

A sufficiently complete TeX Live installation is required. The source uses
only standard packages and contains its bibliography inline.

## Reproduce the experiments

Python 3.10 or later is recommended:

```bash
python -m pip install -r requirements.txt
python self_representation_experiments.py
```

The full run regenerates all files in `results/` and `figures/`. A faster
smoke test is available as:

```bash
python self_representation_experiments.py --quick
```

The exact path uses rational arithmetic for dyadic nodes and verifies
`B_tilde D = I` through degree 8. The floating-point path computes projector
norms through degree 12 and compares equispaced and Chebyshev-Lobatto
interpolation. No network access is used.
