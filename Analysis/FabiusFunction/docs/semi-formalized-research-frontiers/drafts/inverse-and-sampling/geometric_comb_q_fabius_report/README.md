# Geometric-Comb Interpolation and the Fabius--Rvachev Boundary Layer

This package contains the source, rendered PDF, reproducibility program,
data, and figures for a manuscript on interpolation at
`c, cq, ..., cq^n`, together with its Fabius/Rvachev specialization.

The report was written against ProveIt commit
`e5175d5eb78d66f4e31db3bc506541b9bae12c57` (30 August 2026). Its Lean-status
boundary was rechecked at intake head
`ffcdbdac47246bd553f272bd1ceac441f8dd4f0c`; the relevant formal files did not
change between those commits.

## Mathematical and formal status

“Theorem,” “proposition,” “lemma,” and “corollary” in the PDF mean that the
manuscript supplies a proof. They do not automatically mean Lean-checked.

Existing Lean declarations cover important finite inputs: q-Pochhammer and
Gaussian-binomial identities, complete-homogeneous geometric specialization,
evaluation-at-zero geometric Lagrange weights and residual moments, their
finite rational l1 norm, the inverse-dyadic Fabius moment identity, Rvachev
Appell deconvolution, and exact finite polynomial synthesis by shifted
Rvachev atoms.

No one-to-one Lean declaration was found for the report's Jackson
divided-difference theorem, Gaussian Newton basis pair, arbitrary-evaluation
interpolation residual, analytic Newton convergence, boundary-layer/global
Lebesgue asymptotics, Newton--Jackson quadrature, Fabius boundary-residue and
fixed-jet estimates, gap bound, or Gaussian--Appell cardinal/right-inverse
packaging. The two-sided Fabius gap law, second-order Lebesgue expansion, and
Hermite saddle law remain conjectural. See the PDF status ledger and
`INTAKE_AUDIT.md` for exact declaration names and boundaries.

The hostile intake read-through repaired two substantive scope issues: the
Hermite convergence corollary now requires a centered analytic disk of radius
greater than `c`, as used by its proof, and the numerical output is described
as a top-gap maximization rather than an independently certified finite-degree
global maximization.

## Package contents

- `geometric_comb_q_fabius_report.tex` — complete LaTeX source.
- `geometric_comb_q_fabius_report.pdf` — normalized A4 rendering.
- `geometric_comb_experiments.py` — exact-rational and logarithmic numerical
  checks; it writes all files under `data/` and `figures/`.
- `requirements.txt` — exact replay environment pins.
- `data/lebesgue_data.csv` — endpoint and top-gap Lebesgue diagnostics.
- `data/fabius_interpolation_data.csv` — exact-rational Fabius interpolation
  diagnostics converted to plotting fields.
- `data/identity_checks.txt` — exact identity-check transcript and selected
  Newton coefficients.
- `figures/*.pdf` — four vector plots with embedded/subset CID TrueType fonts
  and no Type 3 fonts.
- `figures/*.png` — raster counterparts of the four plots.
- `ARRIVAL_SHA256SUMS.txt` — verbatim verified ledger of the 16-file arrival
  payload.
- `NUMERICAL_REPLAY.txt` — pinned replay command, versions, comparisons, and
  output hashes.
- `INTAKE_AUDIT.md` — provenance, mathematical/Lean-status, editorial, build,
  and validation audit.
- `pdf_preflight.json` — machine-readable final PDF checks.
- `SHA256SUMS.txt` — exhaustive final ledger, excluding itself by convention.

## Reproduce the numerics

Python 3.13.14 was used for the normalized replay. From this directory:

```bash
python -m venv /tmp/geometric-comb-replay
/tmp/geometric-comb-replay/bin/python -m pip install -r requirements.txt
/tmp/geometric-comb-replay/bin/python geometric_comb_experiments.py
```

The script has no runtime network or random input. Exact algebraic and Fabius
computations use `fractions.Fraction`; only the positive Lebesgue sums,
one-dimensional top-gap optimization, and plotting use floating point. PDF
font type 42 and fixed artifact metadata make two consecutive pinned replays
byte-identical.

A successful replay ends with:

```text
All exact identity checks passed.
Endpoint Lebesgue limit: 8.25598793577825006554414084943
Global asymptotic prefactor: 1.75421915716734780836138830414
```

## Rebuild the PDF

The final archive was built from a clean auxiliary state with exactly three
strict serial passes:

```bash
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode geometric_comb_q_fabius_report.tex
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode geometric_comb_q_fabius_report.tex
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode geometric_comb_q_fabius_report.tex
```

The final PDF is 68 A4 pages and 818043 bytes. Its SHA-256 is
`bcd2559f1e6f4be608c291c6ef5de48108c3b0d78139ecf1a5672942d72d9b92`; the
final TeX has 3575 lines and SHA-256
`37e71ad371673a8c301d1b2f23e516cf34b904fb98f22e18448e4dedfe939c08`.
Geometry, fonts, extractable text, build diagnostics, and
all-page visual inspection are recorded in `pdf_preflight.json` and
`INTAKE_AUDIT.md`. Build auxiliaries are intentionally absent.

## Provenance and checksums

No source ZIP attributable to this package was present in the audited
workspace. Accordingly, no archive hash is invented. The delivered
`SHA256SUMS.txt` verified 16/16 payload entries before edits and is preserved
verbatim as `ARRIVAL_SHA256SUMS.txt`. The normalized `SHA256SUMS.txt` has 20
entries, covers every other regular package file, and
excludes itself to avoid a recursive checksum.
