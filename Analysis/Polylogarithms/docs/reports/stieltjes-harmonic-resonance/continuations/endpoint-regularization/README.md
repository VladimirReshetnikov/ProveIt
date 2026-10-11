# Endpoint Regularization of Logarithmic Harmonic Polylogarithms

**ProveIt / Analysis / Polylogarithms — research continuation, 10 October 2026**

The complete article is `article/endpoint_regularization.pdf`; its standalone
LaTeX source is alongside it. The report develops exact identities, not a
numerical search for relations. All universal results stated as theorems have
written proofs. Independent mathematical review is still appropriate.

## Main results

The article defines `E_m(z;a)` by strictly ordered lattice indices `n+a`, with
outer weight `z^(n+a)` and fully symmetrized prescribed logarithmic powers.
For unweighted depth `d`, it is denoted `E_(d)(z;a)`.

* A normally convergent compensated product gives every sharp-cutoff polynomial
  in generalized Stieltjes constants and Hurwitz-zeta spectral derivatives.
  The finite operator `Gamma(1 + d/dL)` gives its Abel endpoint polynomial.
* With one arbitrary logarithmic decoration, at every depth greater than one
  on the lattice `a=1`, all positive-index Stieltjes constants cancel from the
  explicit endpoint formula. The remaining atoms are Euler's constant,
  ordinary zeta values, and a single spectral zeta derivative.
* The full unweighted family has the exact beta moment
  `integral_0^1 (1-z)^(b-1) E_(d)(z;a) dz = B(a,b)/b^d`, for `a,b>0`, `d>=1`.
  Parameter differentiation yields polygamma and generalized-harmonic log
  moments. Gamma-weighted harmonic sums and Catalan-number specializations
  follow. Ordinary zero-based primitives have a Gauss hypergeometric generator.
* Repeated `dz/z` primitives have higher hypergeometric generators. At every
  positive integer shift, all unweighted endpoint values are coefficients of
  the classical height-one Gamma quotient with an explicit finite deletion.
* Diagonal and arbitrary-ray spectral constants have explicit correction
  formulas. They are not the same as cutoff or Abel constants. Rational-shift
  root filtering also changes the endpoint logarithmic scale.

The symmetric-sum principle, Gamma regularization, and unshifted height-one
Gamma identity are classical. The paper attributes them and proves its
normalization-specific extensions and consequences. No worldwide priority,
period independence, minimum numerical depth, or resolution of the existing
`S6`/`S8` conjectures is claimed.

## Contents

| Path | Purpose |
|---|---|
| `article/endpoint_regularization.tex` | Complete standalone source |
| `article/endpoint_regularization.pdf` | Compiled article, proofs and research questions |
| `code/coefficients.py` | Exact finite multivariate coefficient engine |
| `code/verify_exact.py` | Rational and symbolic regression tests |
| `code/verify_numerical.py` | Independent high-precision comparisons |
| `code/endpoint_diagnostics.py` | Direct Abel-sum endpoint diagnostics |
| `results/coefficient_catalog.json` | Ten explicit coefficient examples |
| `results/exact_checks.json` | Executed exact assertions, grouped by test |
| `results/numerical_checks.json` | Full numerical comparisons and residuals |
| `results/endpoint_diagnostics.json` | Thirty-two direct endpoint diagnostics |
| `SOURCE_AUDIT.md` | Reviewed source paths, attribution and scope limitations |
| `PROPOSED_CORRECTIONS.md` | One targeted wording correction and convention safeguards |
| `corrections/*.tex` | Optional editorial insertions; not automatic patches |
| `provenance.json` | Repository snapshot, environment and build status |

## Validation actually executed

**2,600 exact assertions passed.** They include rational finite products,
set-partition formulas, two independent Gamma-transfer implementations,
one- and two-decoration formulas, higher logarithmic insertions, differential
recurrences, diagonal constants, integer and half shifts, finite deletion,
and exact root-of-unity filters. The root filters account for 1,947 of these
assertions; this is a regression count, not a count of distinct theorems.

**158 numerical comparisons passed at 60 decimal digits.** The largest
observed absolute residual was approximately `7.83e-55`. These are ordinary
floating-point comparisons, not interval-certified enclosures or proofs.

**32 direct endpoint diagnostics** cover four contents, two shifts and four
values of epsilon. The largest sums have 3,500,000 terms. These diagnostics
show convergence toward the proved complete subtraction polynomial; they do
not purport to recover many digits of the endpoint constant by extrapolation.

The general analytic identities rest on the written proofs. No Lean, other
proof assistant, or Wolfram execution was performed.

## Reproduction

Tested environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, NumPy 2.3.5.
The scripts use no network access. A conventional TeX Live installation with
`latexmk` and the packages declared in the source rebuilds the PDF.

```sh
python -m pip install -r requirements.txt
make exact
make numerical
make diagnostics
make pdf
```

Or run directly:

```sh
python code/verify_exact.py
python code/verify_numerical.py
python code/endpoint_diagnostics.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error endpoint_regularization.tex
```

`make test` runs exact and numerical checks, without the larger endpoint
arrays. `make diagnostics` may use several hundred megabytes of memory; allow
about 1 GB for the process. The scripts replace their corresponding result
files, so run them on a copy when preserving the original recorded evidence.
`make clean` removes only LaTeX auxiliaries and Python bytecode, not the PDF
or result files.

For a quick coefficient example:

```sh
python code/coefficients.py
```

The formal symbols `g0,g1,...` mean `gamma_r(a)`; `z2_1` means `zeta'(2,a)`;
`z3_2` means `zeta''(3,a)`; `G` is Euler's constant; `z2,z3,...` are ordinary
zeta values. Symbols are used for polynomial checking, with no claim of
arithmetic independence.

## Integration and review boundary

Suggested placement:

`Analysis/Polylogarithms/docs/reports/endpoint-regularization/`

The report is pinned to repository commit
`fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`. The canonical README, main driver,
selected depth/integration material, alternating-harmonic README, and incoming
listing/intake instructions were inspected. The binary contents of the five
incoming ZIPs were **not** inspected. This package therefore does not certify
nonoverlap with those payloads or audit the entire canonical manuscript.

No repository files were changed, no Git commit or push was made, and the
editorial fragments were not applied. Compare the package with the incoming
work and review the proofs before editing the canonical manuscript.
