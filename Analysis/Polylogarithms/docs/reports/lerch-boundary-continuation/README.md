# Boundary Singularities and Zero Bifurcations in the Stieltjes–Lerch Derivative Family

Research continuation for Vladimir Reshetnikov's **ProveIt** project, prepared 9 October 2026 (Pacific time).

**Read `article.pdf` for the complete statements and proofs.** Its editable source is `article.tex`. The inspected repository snapshot is `6ec0b2c11ba3932107aa1e8bdf20627e3ced86fc`.

## Main results

The normalization throughout is

`F_{n,k}^rho(a) = (-1)^(n+k) D_{n,k}^rho(a)`,

where `D` is the kth parameter derivative of the Lerch logarithmic coefficient, and at `rho=1` is the kth parameter derivative of the nth generalized Stieltjes constant. The article gives the exact connection with polylogarithmic order derivatives.

| Result | Status and scope |
|---|---|
| Two simple positive zeros for index n=2 | Proved for every k>=1 and every rho in [0,1]. |
| Complete first-order index-two branch shape | The upper branch decreases; the lower branch has exactly one nondegenerate minimum. |
| Minimum parameter enclosure | Exact rational certificate: 0.91560506 < rho_min < 0.91560508. |
| Pole-cancelled Abel identity | Proved, convergent for 0<eta<2*pi, rho=exp(-eta), at every n>=0 and k>=1. |
| Sharp endpoint regularity | The family, and each simple endpoint zero branch, are C^(k-1) but not C^k at rho=1. |
| First-order endpoint directions | Alternating directions, conditional on endpoint saturation; unconditionally instantiated for n=1,2,3,4 by exact signs. |
| Eventual negative parameter derivatives | For fixed n and any fixed finite R, all derivatives of zero branches through order R are negative for sufficiently large k, uniformly on [0,1]. No optimized explicit threshold is claimed. |
| Weak-deformation classification | All-index fractional-power splitting theorem, with an explicit nonzero coefficient and complete sufficiently-small-positive-rho real zero counts. |
| Index-three inner-gap fold | Exactly one nondegenerate fold in the specified inner Stieltjes-zero gap. Additional lower-parameter outer folds are not excluded. |

The complete index-two geometry and differentiated large-k theorem resolve precise portions of the manuscript's monotonicity question. An unrestricted all-k monotonicity extension is false. This does **not** identify a false theorem already proved in the source manuscript.

## Evidence levels

The analytic results have ordinary mathematical proofs. Finite sign inputs are verified by exact rational interval arithmetic and explicitly proved remainder bounds. Separate high-precision computations are **diagnostics, not proofs of equality or certified decimal locations**. Nothing here is proof-assistant formalized or independently refereed. Literature priority has not been established; the contribution is stated relative to the inspected manuscript. Classical Lerch identities and the existing zero bound retain their attribution.

## Reproduce the exact checks

Python 3.10 or later suffices for the exact scripts; no third-party package is needed.

```sh
python verification/certify.py
python verification/certify_minimum.py
python verification/test_algebra.py
python verification/test_integration.py
```

The first command regenerates 14 endpoint sign certificates and 120 weak-deformation coefficient certificates. The second regenerates the minimum-parameter enclosure. The third runs nine regression-test groups, including 289 kernel-derivative identities and 1,014 finite deformation-jet polynomial identities. The fourth runs three chapter-consistency and installer-guard tests.

Run these normally, without Python's `-O` flag: assertions are part of the replay checks.

## Optional independent diagnostics

The supplied outputs were computed with Python 3.13.5 and mpmath 1.3.0 at 45 decimal working precision.

```sh
python -m pip install -r requirements.txt
python verification/numerical_checks.py identity
python verification/numerical_checks.py roots
python verification/numerical_checks.py minimum
python verification/numerical_checks.py fold
```

The identity mode compares a direct spectral sum with the convergent Abel expansion in six cases. Root computations are safeguarded within sign brackets and check crossing directions and ordering. The minimum uses a direct series; the fold uses an independent Appell–Laplace integral. The exact certificate scripts do not import mpmath.

A single replay driver is also available: `python verification/run_validation.py --numeric` regenerates the exact certificates and all optional diagnostics, then records command results in `verification/validation.json` and `verification/validation.log`.

## Build the article

A standard LaTeX installation with pdfLaTeX, AMS packages, Latin Modern, geometry, microtype, hyperref, bookmark, fancyhdr, xurl, booktabs, and tabularx is sufficient.

```sh
make pdf
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times. The PDF in the package has already been compiled and visually checked. No external figure, bibliography database, or font file is required.

## Integration

See `INTEGRATION.md` before applying anything. The `integration` directory contains a full namespaced chapter, bibliography entries, exact editorial replacement anchors, and a dry-run-by-default local installer. No remote repository changes have been made. The installer requires the inspected source blobs and refuses to overwrite new files or silently patch a different snapshot.

## File map

- `article.tex`, `article.pdf`: full research article.
- `verification/`: exact certifiers, numerical diagnostics, tests, and validation metadata.
- `data/`: full rational certificate endpoints and explicitly non-interval diagnostics.
- `integration/`: additive manuscript chapter, bibliography fragment, and guarded local integration support.
- `INTEGRATION.md`: mapping to existing chapter labels and suggested review order.
- `AUDIT.md`: scope corrections, proof dependencies, and limitations.
- `PROVENANCE.json`: repository and primary-source provenance.
- `SHA256SUMS`: file-integrity manifest.

The seven further-research sections in the article include the unresolved outer-fold exclusion, sharp monotonicity thresholds, higher-index bifurcations, joint endpoint/high-order limits, a certified Abel evaluator, arithmetic extensions, and formal verification.
