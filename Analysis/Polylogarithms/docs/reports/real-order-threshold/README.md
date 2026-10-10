# The Sharp Real-Order Threshold for Harmonic Polylogarithms

**ProveIt Contributors — 9 October 2026 (America/Los_Angeles)**

The standalone research article is `article/real_order_threshold.pdf`; its complete editable source is `article/real_order_threshold.tex`.

For `F(a,b;z) = sum_{n>=1} H_(n-1)^(b) z^n / n^a`, with positive real a,b, the principal result is a sharp theorem: a finite signed Hausdorff-moment representation exists **if and only if a+b >= 1**. Above the threshold its density has exactly one negative-to-positive crossing. At equality it necessarily has a positive endpoint atom of mass `1/a` at 1 and a strictly negative density of the same mass.

This extends the existing signed-kernel and slit-plane zero-free theory from `a >= 1` to the full closed region `a+b >= 1`. On the critical line the normalized angular displacement is proved strictly increasing with radius. Other results include a dual left-atom theorem, a positive double kernel valid at every positive pair of orders, elementary critical-kernel series, completely monotone Hurwitz identities, and strict Hankel positivity.

The exact arithmetic suite proves `Im F(1/10,9/10;i) < -0.52`. Consequently, the earlier Euler error constant one cannot be extended beyond its **stated** `a >= 1` domain without modification. A second certificate gives `Im F(1/10,1;i) < -0.53` in the strictly supercritical region, where the boundary series converges ordinarily. The old theorem is not contradicted. On `a+b = 1`, boundary values are analytic/Abel values; the ordinary boundary series diverges.

## Scope and status

All main theorems have written analytic proofs. The project is not proof-assistant formalized and this delivery is not an independent peer review. Exact rational certificates are separate from floating-point diagnostics. The existing `S6` identity and the broader finite-b normalized-radius conjecture remain unresolved here. `CLAIM_STATUS.md` gives the detailed status ledger.

The baseline is pinned to repository commit:

`28357e8ca63dd78327db91d9be239d75e4462879`

See `data/provenance.json` and `integration/INTEGRATION.md`. No upstream file or branch was modified.

## Replay the exact certificates

Python 3.10 or later suffices; **no third-party package is needed**:

```bash
python code/certify.py
```

This checks eight Gaussian enclosures and twelve angular brackets using exact integers and `fractions.Fraction`, including 7,430 integer-root inequalities. The supplied rational root proposals are merely candidates; all signs and analytic tails are recomputed. Eleven brackets have uniqueness supplied by the theorem; the one subcritical bracket asserts existence only.

Fractional finite centers are algebraic, not rational. Integer nth-root inequalities enclose them by rational intervals. Outward integer-grid rounding prevents a hidden floating-point acceptance step.

## Optional symbolic and numerical audits

Install the packages listed in `requirements-diagnostics.txt`, then run:

```bash
python code/audit.py
python code/critical_identities.py
python code/certify.py
```

The first script verifies nine symbolic identities, performs 50 independent moment quadratures, and regenerates candidate root brackets. The second checks 21 exact Bernoulli coefficients and performs critical-series, Laplace, and conjectural-constant diagnostics. The third certifies the proposed brackets afresh. Quadrature discrepancies and the 15-point conjecture grid are **not rigorous error bounds or proofs**.

## Rebuild and integrity

With `pdflatex` and the usual mathematical LaTeX packages installed:

```bash
python code/verify_manifest.py
python code/build_article.py
```

The build uses a temporary directory and requires stable references, no overfull boxes, and no missing glyph warnings. The manifest command verifies the originally delivered bytes. Rebuilding changes PDF metadata and the build receipt, so a successful rebuild can intentionally invalidate the original manifest. Verify the delivered manifest before rebuilding, or preserve an untouched copy.

## Integration

Suggested destination:

`Analysis/Polylogarithms/docs/reports/real-order-threshold/`

The `integration` directory supplies an editorial insertion and precise scope notes. Preserve the original proofs and certificates; add the extension rather than replacing the `a >= 1` theorem with a claim that its old error bound holds everywhere.
