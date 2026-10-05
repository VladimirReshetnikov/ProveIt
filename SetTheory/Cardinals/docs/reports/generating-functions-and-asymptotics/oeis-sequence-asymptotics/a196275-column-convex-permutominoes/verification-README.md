# Independent exact and numerical verification: A196275

**Status:** every explicit check passed in ordinary Python and `python -O`. This
is reproducible finite validation, **not** a proof, interval certificate, or a
claim of prior publication. The analytical proof and independent proof audit
are separate artifacts. No OEIS entry or other external service was modified.

## Contents

- `verify_a196275.py`: exact-integer triangle, independent rational generating
  function division, symbolic logarithmic coefficients, positive quadrature,
  precision/cancellation checks, mixed-sector tests, and inverse diagnostics
- `verification_results.json`: full numerical and exact-check summary
- `verification_results_exact_counts.json`: exact integer counts, n = 1,...,1000
- `verification_results_optimized.json`: results of the complete `python -O` run
- `verification_results_optimized_exact_counts.json`: its companion exact counts
- `run_manifest.json`: normal/optimized agreement, check-sentinel results, hashes
- `oeis_b196275.txt`: current OEIS table, n = 1,...,200, fetched 2026-10-02 UTC
- `source_manifest.json`: primary-source links and SHA-256 hashes
- `render_validation_tables.py`: generates `validation_summary.tex` from JSON
- `validation_summary.tex`: author-ready TeX fragment with compact labeled tables

Downloaded `tomas2015.pdf`, extracted text, and page image are local source-review
materials; they are not needed in the reproducibility bundle. Cite the original
source link instead of redistributing those review materials.

## Reproduce

Requirements used: Python 3.12.14, mpmath 1.3.0, SymPy 1.14.0. The actual interpreter
version is recorded in JSON. No network requests occur in the verification
program. Use the supplied frozen OEIS table for deterministic checks.

```sh
cd /path/to/verification
python verify_a196275.py
python -O verify_a196275.py --output verification_results_optimized.json
python render_validation_tables.py
```

The default run takes approximately a minute or two on the research machine.
`--quick` omits mixed-sector and continuous-inverse quadratures. `--max-n`,
`--gf-n`, and `--round-n` control finite ranges. All checks use explicit raised
exceptions; none depend on Python `assert`, so `-O` cannot remove them.

## Primary input and indexing

Tomás, *On the Enumeration of Permutominoes*, Section 5.2, physical PDF page 11:
<https://cmup.fc.up.pt/main/sites/default/files/publications/aptomas_FCT2015.pdf>.
The recurrence counts row-convex objects by the number r of reflex vertices.
Set n = r+1 and P(n,p) = R(r,p). Rotation/transposition equates the count with
column-convex permutominoes. In this convention a_1=1, a_2=4, a_3=22.

The OEIS entry <https://oeis.org/A196275> has offset 1. The frozen b-file came
from <https://oeis.org/A196275/b196275.txt>. It contains all indices 1,...,200;
all match the triangle exactly. The entry credits its table to Vaclav Kotesovec,
computed by Anthony J. Guttmann. The artificial b_0=1/2 is not an OEIS count.

The triangle uses prefix sums, requiring O(M^2) integer arithmetic operations
and O(M) integers for its current row through n=M. Integer bit size grows with M;
the arithmetic-operation bound is not a bit-complexity claim. The program also
retains all row totals to write the exact count table.

## Independent exact checks

For B(z) = -(2-z)log(1-z) / [2z(2-z+log(1-z))], write B=N/D, where

- D_0=2, D_1=-2, D_j=-1/j for j>=2
- N_0=1, N_j=1/(j+1)-1/(2j) for j>=1

Rational formal division determines the coefficients without using the
triangle. It agrees exactly with a_n/(n+1)! through n=250. The integer triangle
was run through n=1000. The first 10 rows and first 12 rational b_n are in JSON.

Symbolic Gamma-moment generation independently recovers every supplied
coefficient C_(0,k) for k=0,...,4 and C_(1,0), C_(1,1). JSON gives all C_(j,k)
for 0<=j<=2 and 0<=k<=6. With A=1-gamma, the next two are

C_(0,5) = 6A^5 - 10pi^2 A^3 - 120A^2 zeta(3) + pi^4 A/2
          - 144zeta(5) + 20pi^2 zeta(3)

C_(0,6) = 7A^6 - 35pi^2 A^4/2 - 280A^3 zeta(3) + 7pi^4 A^2/4
          - 1008A zeta(5) + 140pi^2 A zeta(3) - 5pi^6/24
          + 280zeta(3)^2

These coefficients were derived here from the supplied formula; they are not
attributed to an external publication.

## Precision and spectral checks

Let h = 1/[1-W_0(exp(-1))], k = (2h-1)(h-1)/2, and
r_n = a_n/(n+1)! - k h^n. Computing that difference at fixed precision eventually
loses every residual digit. The script increases subtraction precision by at
least ceil(n log10(1.386)) guard digits. Its primary residual computation instead
uses the positive scaled integral

r_n = [1/(2N)] integral_0^infinity exp(-v) H(v/N) dv, N=n+1,
H(u)=w(exp(-u)).

An `expm1` representation near u=0 keeps H accurate even for n=10^96. Quadrature
is performed at 90 decimal working digits; sample repeats at 65 digits agree
to more than 55 relative digits. The far tail is cut after a precision-dependent
point. This and precision stability are **not rigorous quadrature bounds**.
Every displayed numerical discrepancy is observational rather than certified.

Selected exact-count residuals through n=1000 agree with the integral to more
than 65 relative digits. Direct t-integrals independently check n=0,1,2,4,10.
The atom mass is 2k = 0.683822263043591015767850033979...; the continuous mass
integrates to 1-2k = 0.316177736956408984232149966021....

The cancellation test is intentionally bad: at n=500, 50-digit subtraction
returns about -4.02e21, whereas the stable positive residual is
2.4464646945801111e-5. A negative naive result is numerical cancellation, not
contradictory mathematical evidence.

## Logarithmic and mixed sectors

JSON records normalized 2N(log N)^2 r_n, partial log sums through k=6, and
relative errors for n=100,1000,10^6,10^12,10^24,10^48,10^96. Asymptotic sums need
not improve monotonically when terms are added at a fixed modest n. At n=1000,
for example, the exact normalized value is 0.97490240171868359..., the k=3 sum
is 0.97668481279752611..., and the k=4 sum is 0.96752332614616697....

Independent integral evaluations of the coefficient functions F_0,F_1,F_2 at
n=100,1000,10000,10^6 illustrate the predicted mixed-sector scales. Finite log
truncations are not used to resolve the smaller inverse-power sectors.

## Inversion and rounding

Use F(x)=k Gamma(x+2) h^x on x>=1. Finite checks at **every n=1,...,200** give
0 < F^{-1}(a_n)-n < 1/2. The maximum observed shift is at n=1:
0.0426892402655283715454876463759.... The all-positive-index rounding result is
an analytical theorem in the proof/audit, not a consequence of this finite run.

Forward count rounding is different: F(4)=151.3783527882391469..., so nearest
integer rounding gives 151 although a_4=152. It is the first failure.

For the spectral interpolation in X=x+1, the script chooses exact envelope
locations X_*=5,10,25,50,100 and takes y to be the envelope at X_*. It solves the
full positive-integral equation and checks the first two exponential shifts:

u_1 = -S/p,
u_2 = S S'/p^2 + S^2/(2p) - F_log'' S^2/(2p^3),
p = psi(X_*+1)+log h.

It uses 98 to 138 working digits, enough to resolve the observed second-sector
remainders. At X_*=100, including u_2 improves observed relative error from
2.25e-18 to 6.44e-36. JSON also scales the errors by S^2/p and S^3/p to expose
the expected orders. These checks concern the specified spectral interpolation;
they do not select an interpolation of arbitrary discrete data.
