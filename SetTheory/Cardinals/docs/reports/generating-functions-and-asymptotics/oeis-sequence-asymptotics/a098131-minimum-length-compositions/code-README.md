# Exact code and optional experiments

## Counting routines

compositions.py exposes a_count(n,s), b_count(n,s),
a_gf_coefficients(limit,s), and b_gf_coefficients(limit,s). All arguments
are nonnegative Python integers; booleans and nonintegral types are
rejected explicitly. Counts use arbitrary-precision integers.

The a-count routine uses the stars-and-bars binomial sum. The b-count
routine takes the corresponding termwise binomial difference. The GF
routines use finite coefficient arrays and cumulative summation for each
multiplication by (1-q)^(-1). In particular, the b-GF is computed directly
from q^(k(k+s)) (1+...+q^(k-1))/(1-q)^(k-1), not by subtracting two
copies of the a-GF routine. The empty composition gives a_s(0)=1 and
b_s(0)=0.

## All-order coefficients

coefficients.py exposes coefficients(v,s,J), returning C0 through CJ as
Fraction values. Parameters v and s must be int or Fraction with v>0 and
s>=0; J must be a nonnegative integer, not bool. Floats are rejected.
For optional approximate evaluation, convert a high-precision decimal
string to Fraction explicitly, understanding that it approximates the
transcendental coordinate.

The generator obtains the analytic correction from the formal logarithm
of (1-exp(-z))/z, uses harmonic-number formulas for core derivatives,
forms the truncated exponential by its logarithmic-derivative recurrence,
and applies exact Gaussian moments. It is an arbitrary fixed-order
algorithm; memory and runtime grow with J. It makes no claim of a
convergent infinite expansion or certified floating evaluation.

independent_coefficients.py does not import the primary generator. Its
core derivatives are obtained from the polynomial recurrence
Q_0=v^2, Q_r=r Q_{r-1}+Q'_{r-1}; B1, B2 and B3 are separately explicit.
It forms exp(A) as 1+A+A^2/2!+... with truncated bivariate multiplication,
and verifies all odd Gaussian coefficients vanish. It supplies an
independent exact C0..C3 comparison, not an independent higher-order
check. A J5 smoke check in the primary routine tests result shape and
agreement of its first four coefficients only.

## Mandatory finite test scope

check_exact.py performs 12,366 exact positive checks and 87 input-rejection
tests, 12,453 total:

- Enumerate every ordered composition for 1<=n<=13 and s=0,...,5
- Compare both binomial formulas to independently multiplied GFs for
  0<=n<=400 and s=0,...,5
- Check b_s=a_s-a_{s+1} on that grid
- Check finite eventual strict monotonicity on the stated n<=400 grids
- Compare 24 attributed fixture terms for each of the three OEIS sequences
- Compare C0..C3 at 30 rational pairs: v in {1,3/2,2,5,10,100} and
  s in {0,1,2,5,1/2}, totaling 120 independent coefficient comparisons
- Check the displayed C1 formula, truncation consistency, derivative
  polynomials Q2=2D,Q3=2E,Q4=2F, empty and first nonempty cases
- Reject invalid argument domains explicitly, including float and bool

The rational s=1/2 coefficient tests exercise polynomial algebra. The
composition-count theorem itself is stated for nonnegative integer s.
Finite monotonicity tests are not a proof of eventual monotonicity.
No finite test proves the asymptotic remainder or inverse-envelope theorem.

## Optional separate dependencies

- diagnose_float.py uses mpmath at 80 decimal digits by default. It reports
  a_s forward errors for s=0,1,2,5, b_0 forward errors, and smooth inverse
  correction errors at n=10^3,10^4,10^5,10^6. Use --max-n and --dps to
  restrict the experiment. It produces no certified bounds
- check_symbolic.py uses SymPy. It compares symbolic C1/C2 constructions,
  the displayed C1 formula, odd Gaussian vanishing, and 24 rational C2
  evaluations against the Fraction generator. It reports the C2
  denominator and polynomial degrees, and verifies the leading C2 term and
  C1 probability difference. Use --show-expression to print the expanded
  C2 numerator. These algebra checks do not prove an analytic remainder

Neither dependency is imported by the mandatory mathematical checker,
replay, manifest verifier, guard tests, or build. Optional commands only
print JSON; neither writes package files. All validation uses explicit
exceptions rather than assertions removed by python -O.
