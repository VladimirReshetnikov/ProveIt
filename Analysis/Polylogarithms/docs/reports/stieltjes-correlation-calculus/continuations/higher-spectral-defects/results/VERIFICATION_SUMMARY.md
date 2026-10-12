# Verification summary

The analytic and algebraic proofs are in `article.tex` / `article.pdf`.
These records test formulas and implementations; they are not substitutes for
proof, independent peer review, proof-assistant verification, or interval certification.

## Exact finite assertions

**432 passed**, using SymPy 1.14.0 with Python 3.13.5.

- `double_zero_polynomials`: 60.
- `harmonic_coefficients`: 60.
- `beta_local_moments`: 32.
- `confluent_log_square`: 62.
- `anchored_primitive_algebra`: 128.
- `all_jet_mass_ladder`: 48.
- `Stieltjes_pole_jets`: 42.

## Numerical comparisons

**87 passed** at 35 decimal-digit working precision, using mpmath 1.3.0.
The scaled residual is `abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))`.
The acceptance threshold was `1e-23`; the largest recorded residual was
`9.17825989122e-35`. This is not a rigorous error bound.

The complete suite was executed in stages because tool invocations have time
limits. Final checkpoint replay verified all stored passing records and the
unchanged evaluation profile. The elapsed-time field in the final JSON refers
only to its last invocation, not to the entire research or test run.

- `spectral_jet_routes`: 24.
- `Gamma_second_defect`: 6.
- `cutoff_invariance`: 3.
- `ordinary_arctangent`: 4.
- `ordinary_log_square`: 3.
- `digamma_polarization`: 3.
- `reflected_polylogarithm`: 3.
- `integer_polylog_endpoint`: 1.
- `negative_second_polylogs`: 8.
- `mass_Gamma_covariance`: 3.
- `two_mass_spectral`: 3.
- `repeated_mass`: 1.
- `bilateral_mass_polylogs`: 2.
- `confluent_covariance`: 3.
- `finite_polygamma_resolvents`: 9.
- `shift_primitives`: 9.
- `logarithmic_beta_jets`: 2.

The independent representations include beta and Gamma integrals, ordinary
logarithm-square sums, finite polygamma formulas, reflected polylogarithms,
and Pochhammer-Hurwitz expansions. Some routes share mpmath's Hurwitz-zeta
implementation. No validated quadrature or tail error estimator is delivered.

## Build and layout

The article compiled to 25 pages with no unresolved citations/references,
LaTeX warnings, or overfull boxes. All pages were rendered for inspection,
including a final rerender after the squared-mass domain clarification.
The manuscript integration fragment also compiled independently without
warnings. Math-delimiter control codes in extracted PDF text are font-encoding
artifacts, not control characters in the TeX source; the rendered equations
were inspected.

## Reproduction

Run `python code/verify_exact.py` and `python code/verify_numeric.py`.
A compatible interrupted checkpoint can be resumed with `--resume`; the
profile guard rejects a changed precision or quick/full selection.
Run `python code/verify_manifest.py` before rebuilding or rerunning checks
when checking the original delivered bytes. Rebuilt files or new run receipts
will naturally have different hashes.
