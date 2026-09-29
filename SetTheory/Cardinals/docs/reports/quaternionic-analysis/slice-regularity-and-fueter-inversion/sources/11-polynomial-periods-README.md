# Polynomial Periods and Sharp Residue Hierarchies
## for the Global Inverse Fueter Map

A 25-page research article prepared for Vladimir Reshetnikov, September 2026.

The package extends the quaternionic period-obstruction construction in
ProveIt's report on slice regularity and global Fueter inversion to every
ambient dimension 2h+2, h >= 1. It then proves a residue filtration and sharp
singularity and physical-energy bounds.

## Files

- `article.tex`: complete LaTeX source, including bibliography.
- `article.pdf`: compiled article.
- `code/verify.py`: exact symbolic checks and numerical diagnostics.
- `data/verification.json`: complete recorded results.
- `data/verification.log`: readable output from the executed full suite.
- `PROOF_AUDIT.md`: mathematical scope, dependencies, and pitfalls checked.
- `requirements.txt`: Python versions used for reproduction.
- `build.sh`: three-pass PDF build.

## Main results and where to find them

Theorem 5.2 proves the moving Hermite-polynomial differential identity by an
all-order finite-jet spanning argument. Theorem 6.1 uses it to construct a
global inverse exactly when all polynomial periods vanish. Theorem 7.3 gives
an explicit period splitting and a real cokernel of dimension 2h*d*b, where
d is the real coefficient-module dimension and b is the number of holes.
Theorem 7.4 identifies the smallest inverse cover and rules out any finite
inverse cover when the obstruction is nonzero.

Theorem 9.3 proves that the residue polynomials admitting a target of growth
O(|z-p|^-s) are exactly

    ((t-u)^2 + v^2)^(h-s) * P_<2s(E),  p = u + i v,  0 <= s <= h.

Theorem 10.2 gives the optimal axial-pair leading constant. Theorem 11.2 gives
the optimal physical L2 energy divergence, including its exact constants.
Corollary 11.3 classifies the residue classes admitting local physical Lp
representatives for p >= 1. Section 12 works out explicit six-dimensional
examples. Section 14 proposes ten further research directions.

## Scope and research status

These are written proofs, not Lean-verified results and not referee-validated
claims. The general arguments do not rely on extrapolation from the code.
Historical priority has not been established by the focused literature check.
The standard radial mapping formula, local inversion, and polynomial kernel
are credited to existing theory rather than claimed as discoveries.

The hypotheses matter: the targets are smooth and axial, the planar domain is
connected and lies strictly in the upper half-plane, and the map is the
unnormalized h-th power of the ambient Laplacian. The constructive finite
cokernel theorem assumes a bounded domain with finitely many regular boundary
components. The general zero-period criterion has no finite-connectivity
assumption. Sharp size constants use the axial-pair norm, not the maximum over
all Clifford directions. Zero residue by itself does not imply removability.

## Repository provenance

Inspected snapshot:

    fbba58593dc0622aa914972896150d4848f935b5

Relevant report:

    SetTheory/Cardinals/docs/reports/quaternionic-analysis/
    slice-regularity-and-fueter-inversion/README.md

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/tree/fbba58593dc0622aa914972896150d4848f935b5/SetTheory/Cardinals/docs/reports/quaternionic-analysis/slice-regularity-and-fueter-inversion

This was a targeted inspection, not an exhaustive proof audit of ProveIt.
The quaternionic starting formulas are rederived in the article.

## Rebuild the PDF

A standard TeX Live installation with pdfLaTeX and the packages named in the
source is sufficient. The bibliography is embedded; BibTeX is not needed.

    sh build.sh

The script performs three passes. It preserves the failing pass log if a build
fails and removes ordinary LaTeX intermediates after a successful build.

## Reproduce the diagnostics

With Python 3.10 or later:

    python -m pip install -r requirements.txt
    python code/verify.py

To capture a fresh readable log as well:

    python code/verify.py > data/verification.log 2>&1

The script writes its JSON output relative to its own directory, so it can be
invoked from any working directory. `--quick` reduces the real-monomial test
range only. Running it updates the retained JSON results and elapsed time.

The full recorded run passed: closedness for h=1..8, 60 real and 13 imaginary
Hermite-identity cases, normalization identities for h=1..8, period quadrature
for h=1..4, and asymptotic checks at all ten levels 1 <= s <= h <= 4.
Numerical quadrature and sampled maxima are diagnostics, not interval-certified
zero tests or certified global maxima. The article proves the all-order
statements separately.
