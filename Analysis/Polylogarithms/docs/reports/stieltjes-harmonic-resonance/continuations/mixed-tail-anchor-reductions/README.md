# Mixed Hurwitz-Tail Moments, Zeta-Anchor Reductions, and Stieltjes Transport

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

## Read

`article.pdf` is the complete article. `article.tex` is its standalone source,
including the bibliography and all three finite anchor-certificate tables.
No local image assets or external bibliography files are needed to compile it.

## Principal results

The article reduces the source anchors J7, K8, and K9 explicitly. K8 uses ordinary
zeta products and zeta(5,3); J7 and K9 use only ordinary zeta products. Exact
certificates use 3, 17, and 54 classical relation rows, respectively.

It proves a finite compiler for every regular centered moment of arbitrary
integer-order Hurwitz-tail products, including odd and unequal orders. The
uniform MZV weight ceiling is W-1, improved to W-2 for odd centered degree.
A separate all-degree formula for the (2,3) family yields the ordinary sum

    sum_n [(23*x + 232*x^3 + 240*x^5)*A_n*B_n - 120*x^2 - 76] = -15,

where x=n+1/2, A_n=zeta(2,n+1), B_n=zeta(3,n+1). The complete bracket is the
summand. A direct finite telescoper proves this independently of MZV reduction.

The successive differences of any such tail product give all-index Stieltjes
identities, all polygamma orders, anchored Gamma-ratio sums, and Hurwitz-zero
order-derivative primitives. Their coefficients have explicit finite
multiple-zeta and multiple-polylogarithm representations.

## Attribution and scope

The all-power repeated-even-tail recurrence and the fifth/sixth-power generators
already appear in the Bernoulli-cancellation source. Unequal even-order products
are already covered by the lattice-contact source. Those results are credited,
not claimed again. The new explicit anchor reductions, the arbitrary-integer
compiler and refined ceiling, the (2,3) formulas, and the combined transport
realizations are the proposed continuation.

Novelty is relative to the specifically inspected source passages. This is not
an exhaustive historical-priority claim. The incoming directory listing and
intake instructions were read, but its binary archives were not exhaustively
extracted. See `SOURCE_AUDIT.md` and `provenance.json`.

No Gaussian S6 or revised S8 conjecture, general unequal-tail prefix conjecture,
or arithmetic-independence assertion is resolved by this article. No remote
repository changes or proof-assistant formalization were made.

## Verify

The supplied run uses Python 3.13 and the package versions in `requirements.txt`.
The code uses ordinary Python 3.10+ language features.

```sh
python -m pip install -r requirements.txt
python verification/run_all.py
```

The exact suite passes 369 assertions, including three corruption controls.
The numerical suite performs 40 comparisons at 90 working decimal digits.
These are diagnostics, not interval certificates. Exact rational certificate
checks and the analytic proofs have separate roles. Replaying rewrites the
corresponding files under `results/`.

For only the exact checks:

```sh
python verification/run_all.py --exact-only
```

For a new ordinary mixed moment:

```sh
python verification/compute_moment.py 2 3 --degree 5 --reduce
```

The generic compiler supports larger weights, but the optional standard-coordinate
reducer is deliberately restricted to weights 2 through 9. Unsupported requests
raise an error rather than silently dropping terms.

## Build

A standard TeX installation with pdfLaTeX and the usual AMS, Latin Modern,
mathrsfs, microtype, geometry, booktabs, fancyhdr, hyperref, and bookmark packages
is required.

```sh
python build.py
```

The builder performs three passes in a temporary directory, checks for overfull
boxes and unresolved references, and writes `article.pdf` and a build receipt.
Alternatively, run pdfLaTeX on `article.tex` three times.

## Integration

`integration/INTEGRATION.md` proposes a report location and status wording.
`integration/manuscript-fragment.tex` contains a short optional excerpt.
`CLAIM_STATUS.json` distinguishes proved, inherited, diagnostic, and unresolved
claims. The manuscript contains six concrete further-research directions.
