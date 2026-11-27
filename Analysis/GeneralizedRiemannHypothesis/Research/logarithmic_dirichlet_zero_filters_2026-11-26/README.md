# Positive averaging with logarithmic support at Dirichlet zeros

Prepared for Vladimir Reshetnikov, 26 November 2026.

## Main result

For any fixed finite Dirichlet family, a positive even probability density can
cancel every nonzero zero ordinate up to height B, to prescribed aggregate
multiplicity, with support half-width O(log B). Its Fourier transform is
uniformly at most exp(-c B log B) at every real frequency of magnitude at
least B. This improves the O((log B)^2) support in the inspected ProveIt
balancing packet. Jensen's formula proves that the logarithmic support order
is optimal, including the weaker distinct-zeta-ordinate cancellation problem.

Using Dirichlet GRH, the same construction averages the ramp prime errors in
all reduced residue classes on scales between X/(log X)^C and X(log X)^C.
With the explicitly stated square-root weight and central-zero bias, the
remaining error is O(X^(-1)(log X)^A).

The mathematical proofs are in `logarithmic_zero_filters.pdf` and its LaTeX
sources. The new theorem is not Lean-formalized. Global priority of the exact
arithmetic formulation is unverified; classical positive interpolation and
Fourier-Gram arguments are credited in the report. The improvement relative
to the supplied research packet is explicit and proved.

## Contents

- `logarithmic_zero_filters.pdf`: complete report.
- `logarithmic_zero_filters.tex`: main source; four additional TEX files are included by it.
- `code/positive_filters.py`: finite positive-filter construction.
- `code/verify_exact.py`: exact rational posterior certificate for a synthetic clustered multiset.
- `code/run_numerical_demo.py`: high-precision zeta illustrations and figures.
- `code/build_report.py`: portable build helper, including a local fallback for an uninitialized TeX format.
- `figures/`: the two figures, in PDF and PNG formats.
- `evidence/`: recorded computations, source and literature audits, immutable repository provenance, and selected upstream source excerpts with their license and attribution.
- `formalization_roadmap.md`: exact scope and suggested dependencies for a future Lean formalization.
- `SHA256SUMS`: digests of the delivered files except the checksum file itself.

## Reproduce

Use Python 3 with the packages in `requirements.txt`, plus a TeX distribution.

```bash
python3 code/verify_exact.py
python3 code/run_numerical_demo.py
python3 code/build_report.py
```

On a normally configured TeX installation, the PDF can instead be rebuilt by:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error logarithmic_zero_filters.tex
```

The exact certificate uses rational Taylor intervals to enclose the exact
matrix. Floating point proposes coefficients only; every decisive assertion
is checked using rational arithmetic. The zeta illustrations use mpmath
approximations and do not certify a complete exact zero list or multiplicities.
The analytic proof is independent of these illustrations.

## Scope details

- Central modes cannot be removed by a probability kernel; they remain in the bias.
- The support optimality concerns exact cancellation of the prescribed low frequencies, not every approximate averaging problem.
- The continuous kernel is independent of the averaging center for each fixed cutoff. A finite atomic quadrature selected afterward may depend on the center.
- No assumption about zero simplicity, disjoint character zero sets, or rational independence of ordinates is used.
- The explicit support constant is conservative. At the small numerical cutoffs in the report, the older construction is narrower. The improvement is in asymptotic order.
- RH and Dirichlet GRH are the verified input theorems. No claim for arbitrary Artin or automorphic L-functions is made.

## Pinned source snapshots

- `lsernau/grh-lean`: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `VladimirReshetnikov/ProveIt`: `dedc2966ea6f59cc0a8fd0327d68cda31bce6df1`.

The upstream excerpts retain their Apache-2.0 license, notice, and attribution.
They are evidence of the mathematical input and its analytic interfaces, not a
self-contained build of the entire upstream Lean project.
