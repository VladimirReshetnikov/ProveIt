Reproducible checks for complex transseries reversion
====================================================

Run:
    python verification/verification.py

To skip figure generation:
    python verification/verification.py --no-figures

Tested with Python 3.12.14, mpmath 1.3.0, NumPy 2.3.5, and Matplotlib 3.10.8.
The script writes results.json, numerical_table.tex, and two PDF/PNG figures.

Exact checks
------------
1. Gaussian-rational coefficients of the inverse of
       delta + x exp(-delta) + y exp(-i delta) = 0
   are verified through total degree 10: 65 nonconstant coefficients.
   Both direct substitution and a separately constructed formal fixed-point
   iteration are checked with actual assertions.

2. For every total degree N=1,...,12, dominance walls are obtained directly
   from pairwise differences of the actions m+i n, 1<=m+n<=N.  The wall set
   equals {-atan(p/q): 1<=p,q<=N, gcd(p,q)=1}; its size is
       2 sum_{k=1}^N phi(k) - 1.
   In particular, N=3,6,12 give 7,23,91 interior walls.

3. The first 25 Catalan/Bessel coefficient identities are verified with
   exact fractions, together with 24 quadratic Catalan recurrences.
   For F(z)=z+a/z and B(w^(-k-1))=zeta^k/k!,
       B(g-id) = -a I_1(2 sqrt(a) zeta)/(sqrt(a) zeta).
   The expression (q-sqrt(q^2-4a))/2 is the POSITIVE displacement q-g(q).

4. Membership of m+n/sqrt(2) in a displayed integer continuation-cost
   budget L is computed exactly from integer squares.  The added zero
   location records the nonempty return path +1/sqrt(2),-1/sqrt(2), of
   cost sqrt(2); it does not represent the cost-zero empty path.
   The counts at L=2,4,6,8 are 13,47,105,183, including this zero location.

Numerical checks
----------------
All numerical checks use 110 decimal digits in mpmath.  They are floating-
point consistency checks, NOT interval arithmetic or a replacement for
the article's proofs.

For a=1/3 and b=1/4, inverse roots at w=4-3i and w=6-4i are checked against
total-degree truncations N=1,2,4,8,12.  Every measured error is less than
the theoretical tail bound
    kappa^(N+1) / ((N+1)*(1-kappa)),
where kappa=e*(|a|exp(-Re w)+|b|exp(Im w))<1 and the disk radius is 1.
The root equation residuals are required to be below 1e-100.

The positive Bessel-kernel Laplace integral is also compared with the
algebraic positive displacement at a=1/4 and q=2, with absolute difference
required to be below 1e-100.

Figure interpretation
---------------------
finite_angular_atlases: finite lower-right-quadrant ordering atlases at
degrees 3,6,12.  These are ordering walls, not claims of analytic Stokes
discontinuities.

cost_filtered_locations: possible projected locations with continuation
cost at most 8, with projections near zero at four increasing budgets.
The global additive projection is dense, but each plotted budget is
finite.  The figure does not assert that every candidate is an actual
singularity of a particular function.

Quartic saddle extension
------------------------
Run:
    python verification/quartic_saddle_checks.py

This produces quartic_saddle_results.json, quartic_saddle_table.tex, and
quartic_saddle_scaling.pdf/.png.  The finite sums are evaluated by stable
log-sum-exp at 100 decimal digits for N=50,100,200,500,1000,2000.  Only
coarse finite-error tolerances are asserted; the script does not claim
that numerical observations prove asymptotic convergence.

Independent derivation of the constants used in the comparison:
    r(p) = sqrt(p^2+(1-p)^2),
    Phi(p) = 1+log r(p)+p log A+(1-p)log B
             -p log p-(1-p)log(1-p).
Uniform Stirling expansion in an interior neighborhood gives a summand
    exp(N Phi(p))/(2 pi N^2 r(p) sqrt(p(1-p))) * (1+O(1/N)).
Multiplication by N for the Riemann sum and ordinary Laplace asymptotics
give
    D_N ~ C_2 R^N N^(-3/2),
    R=exp(Phi(p_*)),
    C_2=1/(sqrt(2pi) r(p_*) sqrt(p_*(1-p_*)) sqrt(-Phi''(p_*))).
For A=0.2 and B=0.1, the script independently checks the curvature against
automatic high-precision differentiation and evaluates the constants.

At A=B=1/(e sqrt(2)), the saddle at p=1/2 is quartic:
    Phi(1/2+s) = -(16/3)s^4+(128/15)s^6-(256/7)s^8+O(s^10).
The listed rational coefficients are checked exactly.  The quartic
Laplace integral and the amplitude at p=1/2 give
    D_N ~ C_4 N^(-5/4),
    C_4=3^(1/4) Gamma(1/4)/(2 sqrt(2) pi).

The cubic critical example a=b=(1-i)/2, z0=0, w0=1-i is checked with exact
Gaussian rationals: F'(0)=F''(0)=0 and F'''(0)=i.  Its input moduli at w0
are both 1/(e sqrt(2)).

The same script also checks the uniform quartic crossover at
    (tau,eta) = (0.4,0.7), (-0.5,0), (0,1),
    beta_N = pi/2 + tau/sqrt(N), delta_N=eta/N^(3/4),
    A=q exp(delta_N/2), B=q exp(-delta_N/2).
For N=100,500,2000 it compares
    N^(5/4) D_N / [2 e q cos(beta_N/2)]^N
with
    (sqrt(2)/pi) integral_R exp(4 tau u^2 + eta u - 16 u^4/3) du.
The common amplitude q cancels algebraically before evaluation; the
result is independent of q>0.  It checks reduction at tau=eta=0 against
the original symmetric degree sum and against the Gamma-value constant.
Results are included in quartic_saddle_results.json, and a separate
quartic_crossover_table.tex contains the nine finite comparisons.
