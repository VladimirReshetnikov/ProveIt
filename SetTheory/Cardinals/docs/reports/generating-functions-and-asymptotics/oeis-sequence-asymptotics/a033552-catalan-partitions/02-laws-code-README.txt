CATALAN-PART PARTITION LAW DIAGNOSTICS
===================================

Reproduction
------------
From the package directory:

    python code/verify.py

Run a smaller calculation without plots:

    python code/verify.py --sizes 100 1000 10000 --no-plots

Python >= 3.10 and mpmath are required. matplotlib is optional and is used
only to render the two figures. No spreadsheet package is used. The supplied
run used Python 3.12.14, mpmath 1.3.0, matplotlib 3.10.8, and 60 decimal
digits. Exact coefficient and moment calculations use Python integers.

The default sizes are n = 100, 1000, 10000, 100000, 1000000. The running
time on the supplied workspace is recorded in data/verification.json.
Working memory and arithmetic cost are roughly linear in n times the
number of allowed Catalan sizes, with several arrays of Python integers.

Files generated
---------------
data/verification.json: constants, run metadata, exact integer moment
  numerators, moment and largest-index diagnostics, and total variation.
data/moments_table.tex: means, variances, and mixed covariance.
data/edge_errors_table.tex: leading and first-corrected edge CDF errors.
data/tv_table.tex: exact-coefficient TV values and the Gaussian limit.
data/phase_functions.json: phase mean, variance, and a covariance derivative.
figures/phase_functions.pdf and .png: periodic largest-index moments.
figures/tv_universality.pdf and .png: Gaussian TV curve and finite data.

The LaTeX table snippets require booktabs and mathematical packages providing
\mathbb and \operatorname. Figures require graphicx.

Definitions and algorithms
-------------------------
The allowed parts are C_k = binomial(2k,k)/(k+1), k >= 1. The duplicated
C_0=1 is excluded. p(n) is OEIS A033552. N is the number of parts, J the
largest occupied Catalan index, and t solves

    sum_k C_k / (exp(t*C_k)-1) = n.

The real interpolation r(x) is

    x*log(4) - log(pi)/2 + loggamma(x+1/2) - loggamma(x+2).

m solves r(m)=log(1/t), M=floor(m), theta=m-M.

The integer DP accumulates the sums of 1, N, and N^2 over partitions.
Snapshots after each new allowed part give the distribution of J and the
mixed numerator sum N*J. All exact numerators are retained as decimal
integer strings in verification.json.

The edge limit is G_h=product_{j>h}(1-exp(-u_j)), u_j=4^(j-theta).
The first correction coefficient is

    D_h = G_h * [-A_h + (V_h-A_h^2)/2 - (3/2)*L_h],

where A_h=sum u/(exp(u)-1), V_h=sum u^2 exp(u)/(exp(u)-1)^2, and
L_h=sum (j-theta)u/(exp(u)-1), with sums over j>h. Error tables compare
G_h and G_h+D_h/m with the exact-coefficient CDF. The maxima are over the
recorded finite integer range, not formally certified global suprema.

For TV of the upper vector k>K, b_s is the number of tail partitions of
s and p_K is the prefix partition count. The computation uses

    ( sum_{s<=n} |b_s*p_K(n-s)/p(n) - b_s*exp(-ts)/F_tail|
      + 1 - sum_{s<=n} b_s*exp(-ts)/F_tail ) / 2.

This reduction is exact before numerical evaluation because the likelihood
ratio is constant on tail vectors having the same mass. The Gaussian
limit d(a) is evaluated at a=K/M and also a=K/m, with both values retained.
The main table and figure use K/M, as labelled.

Checks performed
----------------
1. First 62 terms match the OEIS entry inspected on 2026-10-05 (UTC):
   https://oeis.org/A033552 . The expected values are visible in verify.py.
2. A separate logarithmic-derivative recurrence agrees through n=300.
3. Exhaustive multiplicity enumeration agrees for count, N, N^2, J, J^2,
   and N*J through n=40.
4. At n=100, K=2, and the test parameter t=0.08, direct enumeration
   of the full tail vectors gives the
   same total variation as the mass-collapsed coefficient formula.
5. Counts at powers of ten through one million match the earlier Catalan
   partition report's exact integer results.
6. Each conditional tail-mass distribution sums to one up to floating
   summation tolerance.

Scope of the numerical claims
-----------------------------
Integer counts and moment numerators are exact. All saddle values, infinite
products, infinite sums, and displayed errors are numerical diagnostics,
not rigorous interval enclosures. Exponential product tails and extreme
phase thresholds are cut off as recorded in verification.json. Theoretical
remainder estimates require mathematical proof and are not established by
these tests.

The JSON subgroup exploratory_unproved_refinements records candidate finer
mean, variance, and mixed-covariance asymptotics for possible future work.
These candidates are explicitly not claims of the accompanying article
and do not appear in its main tables. The phase covariance gamma is a
limit of covariances with truncated energy, not a covariance with an
L2-convergent two-sided total energy (the latter does not exist).
