# A Universal Beta Formula for Gamma Normal Forms

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.
Mathematical derivations and computational checks with OpenAI assistance.

## Main result

`article.pdf` and the self-contained `article.tex` prove an explicit formula for **every coefficient** in the functional integration-by-parts normal form of

`A_0 = 1, A_(m+1) = u_0 A_m - D A_m, D u_j = u_(j+1)`.

On substituting `u_j = psi^(j)(x)`, this is the hierarchy
`(-1)^m Gamma(x) (1/Gamma(x))^(m)`.

A monomial is functional when it is a pure power of `u_0` or its largest positive derivative index occurs at least twice. For a functional monomial with highest index `d`, the coefficient is a finite polynomial beta integral. The parity condition is both necessary and sufficient for nonvanishing; every nonzero coefficient has sign `(-1)^d`.

The proof solves the predecessor's mixed `u_2^b u_3^2` question and all higher-multiplicity sectors of this particular hierarchy. It uses polynomial-background transport of the inherited affine square identity, followed by extraction of the highest quadratic variation. It does not assume higher-order numerical patterns.

The article also supplies the complete finite-jet generating function, exact normalized primitives, harmonic endpoint identities, logarithmic beta moments, finite Hurwitz and Lerch endpoints, all-order Stieltjes averages and anchored primitives, and explicit degree-eight trigamma, Stieltjes, polylogarithm, and log-sine evaluations.

## Entry points

- `article.pdf`: complete research article, with proofs, provenance, limitations, and further questions.
- `article.tex`: one-file LaTeX source; no external bibliography or figures required.
- `verification/gamma_coefficients.py`: exact coefficient API using only the Python standard library.
- `verification/independent_ibp.py`: independent rational reduction, not the beta algorithm.
- `verification/check_exact.py`: coefficient, support/sign, primitive, and corruption checks.
- `verification/check_analytic.py`: exact endpoint algebra and high-precision diagnostics.
- `data/normal_coefficients.csv`: every functional coefficient slot through weight 32, including zeros.
- `data/primitive_certificates.json`: full `A`, `N`, and endpoint primitive `H` at weights 4, 8, 11, 14, 18.
- `data/exact_checks.json`, `data/analytic_checks.json`: detailed machine-readable receipts.
- `integration/INTEGRATION.md`: additive repository plan and corrections.
- `integration/universal_gamma_normal_forms.tex`: compact theorem/proof fragment for a host manuscript.
- `SOURCE_AUDIT.md`, `data/source_manifest.json`: inspected-source identity and limitations.

## Exact API example

Run from this directory:

```python
from fractions import Fraction
from verification.gamma_coefficients import coefficient

assert coefficient((0, 0, 1, 2)) == -55       # [u_2 u_3^2] N_11
assert coefficient((0, 1, 0, 3)) == Fraction(-3185, 3)
assert coefficient((0, 0, 2, 2)) == -3640     # [u_2^2 u_3^2] N_14
assert coefficient((0, 1, 0, 2)) == 0        # parity-forbidden
```

The tuple lists exponents of `u_0, u_1, ...`. Missing trailing exponents are zero. An optional `weight=` argument selects a specific `N_m`; a weight mismatch returns zero. Negative or nonintegral exponents raise `ValueError`.

## Reproduce

The exact checks require Python 3.10 or later, and were tested with Python 3.13.5. The analytic checks additionally use mpmath 1.3.0 and SymPy 1.14.0; `requirements.txt` records the tested versions.

```sh
python verification/check_exact.py
python verification/check_analytic.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `bash verify_and_build.sh`. Do not use Python's `-O` flag: the verification programs intentionally rely on assertions and reject optimized execution. `check_exact.py --weight N` supports `N >= 14`; larger weights rerun the independent reduction rather than merely extrapolating the coefficient formula.

The recorded default run has 8,350 independent coefficient comparisons through weight 32, 8,317 support/sign checks, 29 full polynomial primitive identities, 19 homotopy comparisons, 32 Appell checks, 1,684 mixed-square comparisons, two rejected corrupted certificates, 20 exact endpoint-algebra assertions, and 20 numerical diagnostics.

## Scope and evidence

The all-order result is proved in the article. The finite exact computations are independent implementation checks. Floating-point diagnostics are not interval proofs; the largest recorded scaled residual is about `4.82e-34`, in a quadrature-refinement test whose tolerance is `1e-31`.

The normal-form complement and affine square kernel are inherited. The special-function transforms use established methods, credited in the article. Historical priority beyond the inspected sources is not asserted. The original Gaussian S6, revised S8, and general unequal harmonic-tail moment-prefix rank questions are not solved. There is no proof-assistant formalization in this package.

No connected repository content was modified. Proposed corrections include the affine report's bibliography page range (456–471, not 456–473) and a duplicated paragraph observed in a particular manuscript README blob. See the source audit before applying any correction to a moving branch.
