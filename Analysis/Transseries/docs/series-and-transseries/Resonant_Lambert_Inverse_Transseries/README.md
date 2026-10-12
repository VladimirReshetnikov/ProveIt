# Double Resonance and Nested Stokes Geometry in Polylogarithmic Lambert Inversion

Research contribution prepared for Vladimir Reshetnikov / ProveIt, 12 October 2026.

## Read first

`article.pdf` is the 22-page article; `article.tex` is its complete, standalone
LaTeX source, including bibliography. It has no external figure or bibliography
file dependencies. `CLAIMS.md` separates established background, proved
refinements, and unproved extensions. `AUDIT.md` records the limited audit and
substantive integration safeguards. `PROVENANCE.md` identifies the repository
snapshot and inspected sources.

The study uses the established two-index Lambert family, specialized to

    F_epsilon(t) = sum_{a,b>=1} (a/b)^epsilon exp(-ab t)/(ab).

The contributions proposed for integration are the explicit resonant jet
normalization, second-jet parity/Stokes identity, uniform arcsinh inverse chart,
core-fold displacement, rational inverse-sector coefficient calculus and sharp
Borel radius, and exact nonlinear inverse Stokes transport. The ordinary inverse
sector series has radius ZERO at every fixed positive slow parameter; it is not
advertised as a convergent analytic-tail chart.

The final inverse splitting and the arithmetic-averaging defect are different
quantities. The latter has leading coefficient exactly -1. Plain arithmetic
averaging is not equated with general nonlinear median resummation.

## Contents

- `article.tex`, `article.pdf`: full article and conventional proofs.
- `verification/verify.py`: independent finite exact tests and numerical diagnostics.
- `verification/results.json`: recorded successful run, with versions and precision.
- `verification/run.txt`: successful run summary.
- `verification/coefficients.txt`: the first eight exact coefficient polynomials.
- `CLAIMS.md`, `AUDIT.md`, `PROVENANCE.md`: status and source scope.
- `integration/README-entry.md`: proposed descriptive cross-link text.
- `Makefile`, `requirements.txt`, `requirements-full.txt`: reproducibility helpers.

## Build and verify

A TeX installation containing the ordinary AMS, Latin Modern, geometry,
microtype, fancyhdr, hyperref, and xurl packages is sufficient.

```sh
make pdf
python -m pip install -r requirements.txt
python verification/verify.py --output verification/results.json
```

The required Python packages are SymPy and mpmath. SciPy is optional; installing
`requirements-full.txt` also enables the independent Mellin quadrature. The
recorded run includes that optional check. Use `--skip-lateral` to omit only the
higher-precision lateral inverse root diagnostics. Verification itself requires
no network access.

The exact part checks all inverse coefficients through q^8, including an
independent substitution, signs, degree, valuation, and Catalan leading terms.
The numerical part checks reflection at real and complex order, parity jets,
coalescence, uniform core roots, displaced core folds, direct sums, the Mellin
completion, and the lateral inverse splitting and averaging defect.

These numerical results are floating-point diagnostics, NOT interval-certified
error bounds. A zero printed residual means rounding to zero at the working
precision, not an exact equality certificate. The all-order theorems rely on the
written proofs, not on extrapolation from tests. No Lean formalization or
independent peer review is claimed.

## Integration

The repository was inspected at commit
`6207c3d40047fd8d1400a4d509fee71c9a3a8132`. No repository file was modified and no
commit or pull request was created. A suitable standalone topic directory is
`Resonant_Lambert_Inverse_Transseries` under the Transseries research documents,
with a cross-link from Polylogarithms. The ZIP can first be placed in
`docs/incoming` for the repository's normal integration process.

The five incoming archives were inventoried, not extracted. Three relevant
library draft counterparts were compared through selected statements; their
byte identity with particular ZIP members was not established. No source-specific
error in the inspected mathematical statements was established. The audit does
not imply validation of the complete repository or all incoming packages.

## Novelty and unresolved work

The two-index Lambert family and general resurgent structure are prior work of
Broadhurst–Dorigoni and Dorigoni–Kleinschmidt. The article cites those sources and
proves the required specialization directly. The detailed inverse/jet refinements
are proposed contributions; worldwide priority has not been established.
Section 11 states further questions. In particular, the hyperbolic large-order
amplitudes there are explicitly conjectural, and full continuation of the inverse
Borel transform is not proved here.
