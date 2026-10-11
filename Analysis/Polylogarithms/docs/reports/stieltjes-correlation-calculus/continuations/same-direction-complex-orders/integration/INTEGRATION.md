# Suggested integration

## Destination

A suitable new report folder is:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/same-direction-complex-orders/`

Preserve the delivered article, code, run receipts, source audit, and claim
status before adapting the notation to the collective manuscript. Do not
overwrite the preceding integer-only report: it remains the provenance of
the finite connected master.

## Dependency placement

The connected entire family belongs immediately after the connected
coordinates in `bilinear-mellin-hurwitz/sections/03-master.tex`, or in the
corresponding canonical continuation once that material is integrated.
The ordinary Stieltjes kernel and primitive section can be cross-referenced
from the manuscript's Stieltjes integration/differentiation chapters.
The logarithmic Gamma generator and depth theorem depend on the profile
transform, not on any Gaussian conjectural reduction.

`manuscript_insert.tex` is a compact insertion using the prefix `sdco:` for
all labels. It contains short proofs and cites the complete article for
expanded analytic arguments. It expects standard `amsmath`, `amssymb`,
`amsthm`, and `hyperref` support, and a `theorem` environment.

Add a bibliography entry with key `SDCO2026` referring to the preserved
standalone article. `check_insert.tex` demonstrates that entry and is a
compilable syntax-check harness, not a separate research report.

## Proposed status-ledger update

Suggested wording, after the normal analytic intake review:

> The same-direction complex-order spectral representation is proved for
> positive scales z,w, Re(N)>0 and -2<Re(beta)<Re(N). The double Barnes
> master is entire in both orders. Its connected one-contour specialization
> recovers the existing positive-integer double-Hurwitz master exactly; an
> independent equal-scale beta–Newton series is absolutely and locally
> normally convergent with all fixed order/logarithmic derivatives.
> This resolves the representation part of reciprocal-lerch-convolutions
> Question 8. Generic finite closure, arithmetic minimal depth, and the
> canonical S6/revised S8 conjectures remain open here.

Additional proposed entry:

> The connected double-Hurwitz difference extends entirely in both indices
> through a smooth divided-difference kernel. Its zero-index boundary gives
> all-index ordinary Stieltjes–Gamma moments and fully anchored Hurwitz-zeta
> primitives. A paired Gamma-residue generator supplies all logarithmic
> moments, with a proved cancellation lowering the explicit multiple-zeta
> depth bound from r+2 to at most r+1. A polynomial algorithm supplies finite
> Hurwitz closure when one spectral order is nonpositive and the stated
> beta-kernel parameters are integral.

Do not delete broader open questions merely because the representation part
has been answered. Do not relabel inherited positive-integer identities or
classical specializations as previously open theorems.

## Required safeguards

- Preserve `E_a(0)=1` and whole-expression continuation at resonances.
- Preserve the `Gamma(1+lambda) Gamma(1-lambda)` factor in the paired residue
  generator; it supplies the even-zeta coefficients.
- Distinguish `H_n^star` in Newton coefficients from `H_(k-1)^star` in the
  Gamma products.
- Record the exact contour inequalities and ordinary-integral domains.
- Do not identify numerical diagnostics with interval certificates.
- Reconcile the six uninspected incoming archives before making a claim of
  exhaustive novelty or zero overlap.

## Replaying the insertion

From the package root:

```sh
mkdir -p build/integration
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/integration integration/check_insert.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/integration integration/check_insert.tex
```

On platforms without `mkdir -p`, create the directory normally first.
No changes to the remote repository are made by these commands.
