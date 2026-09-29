# Amplitude–Slope Compensation in Feedback Transseries

**Sharp regularity, negative-ray summation, and damping-induced condensation**  
Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## The question answered

The inspected ProveIt regularity and negative-ray summation drafts explicitly
ask how rapidly decaying positive amplitudes interact with large feedback
slopes. This package develops a necessary-and-sufficient classification for

    U(q) = sum_{j>=1} c_j q^j exp(lambda_j U(q)),
    c_1 = 1, 0 < c_j <= 1, lambda_j >= 0,
    d_j = -log(c_j).

The results also cover positive exponentially bounded amplitudes by an explicit
positive rescaling. The actions remain the integers j.

## Main results

* Ordinary convergence holds exactly when `lambda_j = O(j + d_j)`.
* For each `s > 0`, the forward and inverse series are Gevrey-s exactly when
  `lambda_j^(1/(s+1)) = O(j log(j+1) + d_j)`. This is also equivalent to a
  uniform Gevrey-s expansion of the literal inverse on a closed left half-disc.
* At `s = 1`, the same condition is equivalent to fine Borel–Laplace summability
  of both series on the negative ray. Their sums are inverse functions and
  satisfy the literal, absolutely convergent kernel.
* Under `d_j/(j log(j+1)) -> infinity`, the exact forward factorial-normalized
  type is `(s+1)^(s+1) limsup lambda_j/d_j^(s+1)`.
* If `d_j ~ b j^beta` and `lambda_j ~ a j^p`, with `p > beta > 1`, the type is
  an actual coefficient-root limit. Under the positive Lagrange ensemble, one
  action carries asymptotically all amplitude cost and has size
  `((p/beta) n/b)^(1/beta)` in probability.

The article includes complete proofs, an explicit weighted inverse Bessel
representation, a sharper Borel continuation region, phase diagrams with
logarithmic endpoints, counterexamples to overbroad extensions, ten further
research topics, and a prospective formalization roadmap.

## Status and limits

These are conventional mathematical proofs, not Lean-verified results. Global
publication priority has not been established. The source review was focused,
not an exhaustive claim-by-claim review of every repository document.

“Fine summability” means a fixed-width neighborhood of one Borel ray, not an
open arc of summation directions. The package does not prove general
resurgence, a multiplicative coefficient equivalent, a local central limit
law, or an exact forward/inverse type identity. The distinction between a
limsup type and an all-degree root limit is explicit in the article.

No repository file, branch, or persistent Library file was modified.

## Contents

- `article.tex`, `article.pdf`: self-contained source and compiled article.
- `code/verify.py`: exact rational coefficient checks and two inverse-value
  certificate routes; standard library only.
- `code/diagnostics.py`: logarithmic floating-point coefficient diagnostics.
- `data/exact_checks.json`: 1,353 successful exact assertions, 12 models at
  order 12, a rational inverse interval, and an independent literal-kernel
  sign/derivative certificate.
- `data/diagnostics.json`: full-coefficient diagnostics through degree 512 and
  separately labeled one-action lower-bound diagnostics.
- `SOURCE_NOTES.md`: pinned repository provenance and primary references.
- `requirements.txt`: tested diagnostic dependency versions.
- `build.sh`: three-pass PDF build.
- `data/build_info.json`: build/test environment and PDF inspection summary.
- `SHA256SUMS`: checksums for the deliverable files except itself.

## Reproduce

The exact verification requires Python 3.10 or newer and no third-party package:

```sh
python code/verify.py --order 12
```

The recorded diagnostics used Python 3.13.5, NumPy 2.3.5, and SciPy 1.17.0.
The pinned diagnostic packages require Python 3.11 or newer:

```sh
python -m pip install -r requirements.txt
python code/diagnostics.py --order 512
```

The diagnostic recurrence uses quadratic storage and roughly cubic arithmetic
work. Its output is not an interval certificate. Both scripts accept `--output`
to avoid replacing their included recorded data. The exhaustive exact program
has an exponential composition-enumeration component; its order is deliberately
restricted to 2–18.

Build with a standard TeX Live installation:

```sh
sh build.sh
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.
No external notation file, font file, bibliography database, or repository
checkout is required. The scripts make no network requests.

## Exact inverse certificate

For `c_1=1`, `c_j=2^(-j^2)` for `j>=2`, and `lambda_j=j^3`, the package certifies

    -0.010106452308614 < Q(-0.01) < -0.010106452306282.

The stored rational interval is tighter than these display decimals and has
width less than `2.331e-12`. The first route evaluates ten exponential inverse
blocks and a geometric tail. The second evaluates the first fifteen actions of
the literal kernel at the rational endpoints, bounds its tail, and proves a
positive derivative on `|q| <= 1/50`. Thus opposite endpoint residual signs
independently certify a unique literal root.

Finite tests support implementation and algebraic consistency. The infinite
analytic and asymptotic assertions depend on the proofs in the article, not on
agreement of a finite table with a conjectured formula.
