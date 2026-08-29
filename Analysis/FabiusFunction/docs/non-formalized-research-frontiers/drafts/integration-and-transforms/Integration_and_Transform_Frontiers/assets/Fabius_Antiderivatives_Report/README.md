# Antiderivatives of Monomially Weighted Fabius-Type Functions

> **Consolidation note.** The standalone report source and PDF were absorbed
> into Part I of the
> [consolidated volume](../../Integration_and_Transform_Frontiers.tex). This
> directory now contains only supporting assets; Git history preserves the
> former standalone files.

This package accompanies the research report prepared on 27 August 2026.
The source audit is tied to ProveIt commit
`32d6d36c51d803289e6d6a0dc0c37753766eba47` and is documented in Sections 1
and Appendix A of the report. The report now also carries a later
formalization-status update for the integer Volterra core; that update does
not alter the snapshot-relative novelty audit.

## Package contents

- `../../Integration_and_Transform_Frontiers.tex` — canonical consolidated source.
- `../../Integration_and_Transform_Frontiers.pdf` — rendered consolidated volume.
- `numerical_experiments.py` — commented exact and high-precision checks.
- `verification_output.txt` — deterministic output from the default run.
- `fractional_power_checks.csv` — machine-readable comparison table.
- `requirements.txt` — pinned Python dependency.
- `PDF_VALIDATION.txt` — structural/rendering validation summary.
- `SHA256SUMS` — checksums for all package files other than itself.

## Main results represented in the report

The machine-checked integer core consists of the normalized Volterra operator,
its equality with literal repeated integration for continuous Banach-valued
inputs, affine covariance, local basepoint and zero-tail Taylor-jet identities,
the arbitrary finite polynomial and natural-monomial commutators, the signed
Fabius primitive ladder at every real endpoint, and the bounded Fabius ladder
and finite natural-monomial formulas on the full range `x ≤ 1`.
The four affine/basepoint declarations below were focused-build verified at
compiled checkpoint `e109088ed`.

The generic affine and basepoint declarations have the following exact scope.
The forward form `normalizedVolterra_affine` is valid for an arbitrary real
normed target and every real scale `c`, including `c = 0` and negative `c`;
`normalizedVolterra_comp_affine` is the inverse form and assumes `c ≠ 0`.
`normalizedVolterra_basepoint_shift` assumes only interval integrability on
the two local pieces from `a` to `b` and from `b` to `x`, requires no ordering
of those endpoints, and includes `n = 0`.
`normalizedVolterra_succ_eq_taylor_of_eq_zero` retains only integrability from
`a` to `b` and is the positive-order result when the input vanishes on
`uIoo b x`; it requires no endpoint order or endpoint values. These general
operator identities do not themselves provide explicit Fabius/up coefficients
or assemble a piecewise formula.

The report also develops an absolutely and locally uniformly convergent
Newton–Volterra series for arbitrary complex powers, negative-power and
Mellin/Newton identities, the exterior branches of a global bounded piecewise
formula, complete folded formulas for Rvachev's up-function, formulas for
reflected and complementary Fabius transforms, exact higher derivatives,
Riemann–Liouville orders, and first- and higher-order primitives of the inverse
Fabius function. It derives inverse-primitive and order-statistic asymptotics
from the repository's now-formalized inverse endpoint equivalent and clearly
labels conjectural refinements. Those complex/fractional/Mellin,
global-piecewise, Rvachev-folded, and inverse developments remain
research-frontier material unless a separate repository source explicitly
supplies a Lean counterpart.

## Lean crosswalk

- `FabiusFunction.NormalizedVolterra`
  - `normalizedVolterra`
  - `iteratedPrimitive_eq_normalizedVolterra`
  - `normalizedVolterra_affine`
  - `normalizedVolterra_comp_affine`
  - `normalizedVolterra_basepoint_shift`
  - `normalizedVolterra_succ_eq_taylor_of_eq_zero`
  - `normalizedVolterra_kernel_pow`
  - `normalizedVolterra_polynomial`
  - `normalizedVolterra_monomial`
- `FabiusFunction.FabiusAntiderivatives`
  - `normalizedVolterra_extendedFabius`
  - `normalizedVolterra_fabiusReal_of_le_one`
  - `normalizedVolterra_pow_mul_extendedFabius`
  - `normalizedVolterra_pow_mul_fabiusReal_of_le_one`

## Rebuild the PDF

A TeX Live installation with `pdflatex` and the packages imported by the
source is sufficient.  Build three times so references, the table of contents,
and page numbers all settle, then remove the sidecars:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && rm -f *.aux *.log *.out *.toc)
```

## Reproduce the numerical checks

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py
```

The default run uses 85 decimal digits, moments `d_0,...,d_1500`, and centered
moments `c_0,...,c_700`.  It uses exact `fractions.Fraction` arithmetic for the
terminating identities and `mpmath` for nonintegral, negative, and complex
powers.  No Monte Carlo sampling is used.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Integration_and_Transform_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
