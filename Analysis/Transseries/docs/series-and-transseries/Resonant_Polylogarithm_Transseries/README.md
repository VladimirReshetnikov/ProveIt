# Resonant Polylogarithm Transseries
## Gamma Borel Kernels, Cyclotomic Order Jets, and Sharp Dilogarithm Reversion

Research contribution prepared for Vladimir Reshetnikov and the ProveIt project,
11 October 2026. The article contains conventional proofs, not Lean proofs.
Independent mathematical review and a broader priority search remain appropriate.

## Main result

Let `F_2(x) = -Li_2(-exp(x))`, let `y > pi^2/6`, and put
`u = sqrt(2*y - pi^2/3)`. The exact-core inverse series

    F_2^{-1}(y) = u + sum_{N>=1} (-1)^(N-1) a_N(u) exp(-N*u)

has positive rational Laurent-polynomial coefficients `a_N(u)` given by a
finite formula in Theorem 6.1. Its exact auxiliary-variable radius is

    R(u) = exp(-u) * t/(1-t),
    u^2 = 2*Li_2(t) + log(1-t)^2,     0 < t < 1.

The negative point `q = -R(u)` is the unique dominant singularity. Theorem 7.1
proves its square-root structure and exact coefficient asymptotic. The physical
series converges **if and only if `y >= pi^2/4`**, with absolute convergence at
equality. The inverse itself still exists below that threshold; only this chart
fails there.

The other principal results are the Gamma-product Borel kernel for integer
order derivatives, its finite periodic-weight digamma and cyclotomic dictionary,
the harmonic Bell-polynomial formula for every late order-derivative coefficient,
and an interior-fold extension with a general polylogarithm feedback term.

## Contents

`article.pdf` is the 22-page article; `article.tex` is its self-contained source.
`code/verify.py` and `data/` contain exact finite regressions and numerical
reproduction records. `code/differentiation_pitfall.py` records a version-specific
numerical differentiation problem discovered during the checks.
`SOURCES.md`, `CORRECTIONS_AND_SCOPE.md`, and `INTEGRATION.md` document attribution,
limits, and proposed repository placement. `theorem_map.csv` gives result labels,
numbers, pages, and status. `BUILD_VALIDATION.json` and `SHA256SUMS.txt` document
the delivered build and its files.

## Reproduce

The retained run used Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0, and NumPy 2.3.5.
Use Python 3.11 or newer with the pinned dependencies; the tested interpreter
was 3.13.5. A normal TeX Live installation with the packages in the source is
sufficient; no custom font files or external images are needed.

```sh
python -m pip install -r requirements.txt
python code/verify.py --output-dir replay --max-n 256
make pdf
```

The replay directory protects the delivered evidence from accidental overwrite.
`--skip-borel` is available for a shorter run, but its use is explicitly recorded
as a skipped check. It was **not used in the final retained verification**.
`make pitfall` reruns the numerical differentiation diagnostic.

## Verification status

The retained full run passed 118 exact assertions, three complex-ray Borel
reconstructions, twelve higher-order-jet comparisons, six pairs of periodic
kernel/Fourier-tail comparisons, six characteristic-radius checks, and eight
inverse approximations. Ten large-sector diagnostics reach N=256. The Borel,
jet, radius, and inverse calculations use 65 decimal digits; the larger-sector
positive convolutions use binary64. A printed zero error means zero at the
working precision, not an exact analytic certificate.

The complete Sommerfeld expansion, Gamma reflection, finite Fourier transform,
Lagrange inversion, arithmetic-averaging obstruction, and square-root transfer
are not claimed as new general results. The model-specific sharp reversion
package and order-jet synthesis are proposed contributions. The audit did not
establish a new error in the accepted repository theorems actually inspected,
and it did not review the entire repository. No remote repository file was
changed. The boundary-feedback law proposed in Research Question 1 is explicitly
not proved here.
