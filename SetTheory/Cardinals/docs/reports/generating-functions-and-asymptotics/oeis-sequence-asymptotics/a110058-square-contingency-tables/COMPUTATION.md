# Exact finite computations and reproducibility

The article contains the analytic arguments. These programs check finite
algebraic identities and finite counts only. No receipt is a certificate for
asymptotic localization, tail bounds, a logarithm branch, analytic remainders,
novelty or discrete inverse error.

## Fixed supported domain

A degree tuple d=(d_1,...,d_r) has diagram cost

    c = sum_i (d_i-2)/2.

The evaluator accepts 1 <= r <= 6, integer degrees 3 <= d_i <= 8, even total
degree at most 18, and 1 <= c <= 3. Booleans and floating-point values are
rejected. Tuples are sorted for the multiset computation. There are eighteen
supported sorted tuples. They are independently listed as fixtures and obtained
by integer partition enumeration. The graph budget is 100,000 connected labelled
graphs per degree tuple. The formal power-sum expansion is capped at 200,000
monomials, checked during construction. All these guards remain active under
optimized Python. Internal moment sublists may have odd total degree or be
empty, while retaining the degree and resource bounds.

The calculation works over Python integers and `fractions.Fraction`. No
integer-to-decimal safety limit is disabled: the cap is 640 digits. This finite
program is not an implementation of an arbitrary-order analytic theorem.

## Geometric logarithm

For a geometric random variable with probability mass 2^(-k-1), k >= 0, its
moment generating function is G(t)=1/(2-exp(t)). The graph program computes
moments and cumulants by exact recurrences:

    M_0 = 1,
    M_j = sum_(k=0)^(j-1) binomial(j,k) M_k,
    K_j = M_j - sum_(k=1)^(j-1) binomial(j-1,k-1) K_k M_(j-k).

After removing mean and Gaussian terms, the logarithmic interaction is

    h(z) = -i z - log(2-exp(i z)) + z^2
         = sum_(j>=3) b_j i^j z^j,
    b_j = K_j/j!.

Through degree eight the real b_j are

    1, 13/12, 5/4, 541/360, 223/120, 47293/20160.

The verifier independently expands the displayed logarithm in SymPy and checks
each coefficient exactly. It recomputes every interaction weight instead of
simply trusting the weight stored beside a graph result.

## Connected-Wick Laurent evaluator

Write S_d=sum_(i,j) X_ij^d with covariance

    Cov(X_ij,X_kl) = (n delta_ik + n delta_jl - 1)/(2 n^2).

The joint cumulant of the S_(d_i) is the sum over connected Wick multigraphs on
the r labelled vertices. Loops consume two half-edges. For a graph with m_ij
parallel edges, its half-edge pairing multiplicity is

    product_i d_i! / (product_(i<=j) m_ij! * 2^(sum_i m_ii)).

The integer pairing count is checked. Degree-preserving vertex permutations
are used only to combine equal graph contributions; their orbit sizes restore
full labelled multiplicity. The total connected labelled-graph count must equal
the sum of the orbit sizes, and overlapping orbits are rejected.

Each covariance edge has row, column or constant color. With E edges,
A nonconstant edges, R row-index equality components and C column-index equality
components, its contribution after summing cell indices is

    (-1)^(E-A) n^(R+C+A-2E) / 2^E.

The program groups parallel-edge choices by exact multinomial coefficients and
expands loops separately. It calculates every Laurent coefficient, not only the
coefficient needed for the final asymptotic expansion. For each connected tuple
it also checks that the maximal Laurent exponent is at most 1-c.

For a degree multiset the logarithmic interaction weight is

    i^(sum d_i) product_i b_(d_i) / product_d multiplicity(d)!.

This is the ordered cumulant expansion's 1/r! after collecting repeated degrees.
All total degrees in the public computation are even, so the weights are real
rationals. Summing the eighteen weighted Laurent polynomials and retaining
exponents 0,-1,-2 gives

    1/4 - 3/(2n) + 223/(32n^2).

The n^-2 contribution from costs one and two is 35/8, and that from cost three
is 83/32. Lower Laurent powers are preserved in the individual rows; these are
not claimed to be complete higher-order logarithmic coefficients because
higher-cost diagrams would also contribute there.

## Independent formal-factorization verifier

This second implementation contains no multigraph generator, graph-isomorphism
reduction, connected-graph filtering or edge-color enumeration. It uses formal
independent Gaussian variables A_i, B_j and C with variances 1, 1 and -1/n.
The linear forms

    (A_i+B_j+C)/sqrt(2n)

have precisely the target covariance. The negative variance is an algebraic
Wick functional, not a real probability distribution.

Expanding products of cell power sums yields monomials in power sums of the A
and B variables and powers of C. For a list of power sums, equality partitions
of their chosen indices identify the coinciding summands. A partition with k
blocks contributes the falling factorial (n)_k, multiplied by the usual Gaussian
moments of the total degree in each block. Odd moments vanish. This obtains
joint moments as full rational Laurent polynomials.

The independent set-partition cumulant formula is then

    kappa(Y_1,...,Y_r)
      = sum_pi (-1)^(|pi|-1) (|pi|-1)! product_(B in pi) E product_(j in B) Y_j.

Every computed Laurent polynomial must equal the graph receipt in full. The
verifier separately reconstructs geometric coefficients, weights and the
aggregate through n^-2.

## Fixed symbolic density extension

For a geometric variable of mean lambda, the program expands

    -log(1-lambda*(exp(t)-1))

in the truncated polynomial ring through degree eight, using the finite
composition sum over powers of exp(t)-1. This is independent of the moment-to-
cumulant recurrence used in the density-one graph program. It additionally
checks kappa_(d+1)=lambda*(1+lambda)*d/dlambda(kappa_d), and the reflection
identity kappa_d(-1-lambda)=(-1)^d*kappa_d(lambda) for 2 <= d <= 8.

Put u=lambda*(1+lambda) and A=u/2. A Gaussian joint cumulant of total degree 2E
scales from the density-one covariance by A^(-E). The density checker regenerates
the Gaussian Laurent polynomials using the local independent power-sum
factorization, multiplies by the symbolic interaction weights, and verifies
exactly

    B0 = 1/3 - 1/(6u),
    P1 = -3/2,
    P2 = 1171/180 + 11/(12u) + 1/(60u^2) + 1/(180u^3).

At lambda=1, u=2, these reduce to 1/4, -3/2 and 223/32. Every diagram's three
relevant symbolic contributions is recorded. The computation has no numerical
density input, configurable arbitrary order, private import, numerical fitting
or interpolation. It proves finite rational identities; it supplies neither
compact-uniform analytic constants nor a finite-density numerical certificate.

## Canfield--McKay comparison coefficients

The checked square normalization is

    T(n,s) = binom(n+s-1,s)^(2n) / binom(n^2+n*s-1,n*s)
             * (1+1/n)^(n-1) * exp(-1/2 + Delta/(2n)).

Let Q denote the same expression with Delta=0, and let

    G = H(lambda)^(n^2) / [(2*pi*u)^(n-1/2) * n^(n-1)],
    H(lambda) = (1+lambda)^(1+lambda) / lambda^lambda.

The checker constructs the formal Stirling expansion of log Gamma from the
Bernoulli corrections 1/(12z)-1/(360z^3), forms the two binomial expressions at
scales n and n^2, and includes the expansion of (n-1)log(1+1/n)-1/2. It verifies
that the coefficients of log(Q/G) through n^-2 are

    1/3-1/(6u),
    -3/2,
    83/90+1/(12u)+1/(60u^2)+1/(180u^3).

Subtracting the last coefficient from P2 and multiplying by two gives

    67/6 + 5/(3u),

as the coefficient of n^-1 in Delta. It becomes 12 at density one. This is a
finite exact coefficient comparison; Stirling remainder control and any
conclusion that 0 < Delta < 2 eventually are supplied by the article. The code
makes no finite-n assertion of that inequality.

## Independent n=1 and n=2 Gaussian checks

At n=1 there is one Gaussian cell with variance 1/2. Each joint moment is its
one-variable Gaussian moment at the sum of the degrees.

At n=2 use three independent Gaussians a,b,w of variance 1/8. The four cells are

    a+b+w, a-b+w, -a+b+w, -a-b+w.

Their covariance equals the target covariance. The code expands their power
sums by ordinary multivariate polynomial multiplication, integrates each
variable independently, and applies the set-partition cumulant formula. It
checks all eighteen degree multisets at both n values. These checks share no
graph connectedness or formal negative-variance machinery.

Two sampled values alone would not verify a full Laurent identity. That role
is supplied by the formal-factorization verifier; the n=1,2 tests are additional
independent finite checks.

## Exact small-size table counts

The main counter places a full labelled row at each recursion. Its state is
the multiset of residual column capacities. Sorting this state is a memoization
symmetry only: distinct labelled row choices remain distinct summands, including
when several choices lead to the same sorted residual state. Thus no quotient
by column permutations is taken.

It reproduces a_n for n=0,...,5 as

    1, 1, 3, 55, 10147, 22069251.

A second counter enumerates all weak compositions of n for each row, uses
unsorted labelled residual capacities and checks the same values for n=0,...,3.
Both methods include an explicit empty-table convention. These are finite exact
counts, not data used to fit the asymptotic coefficients.

## Separate floating-point diagnostics

`code/diagnostics.py` contains an immutable short count fixture for
n=4,5,6,8,10,13 from the cited OEIS b-file. It evaluates

    D1 = n*log(a_n/L_n),
    D2 = n^2*(log(a_n/L_n)+3/(2n))

using mpmath at fixed 80-digit working precision, and prints both six decimal
places and 25 significant digits. The rounded values reproduce the article's
diagnostic table. The input counts at n=4,5 are covered by the independent
public DP receipt; larger counts are source data. The script does not recompute
those larger counts or infer any coefficients by fitting them.

This separate output is floating-point arithmetic, not outward-rounded
interval arithmetic. It is not one of the four exact/guard receipts and cannot
certify a finite-n remainder, monotonic approach to the limit, an omitted-term
sign, or an inverse ceiling. Precision and the six accepted dimensions are
fixed; unsupported input values to its callable dimension check are rejected.

## Formal inverse reversion

Set a=log(4), b=log(4*pi), r=sqrt(log(Y)/a), L=log(r), and define

    F2(x) = a*x^2 - x*log(x) - b*x + log(x) + b/2 + 1/4
            + C1/x + C2/x^2,
    C1 = -3/2, C2 = 223/32.

The checked ansatz is x=r+d+e/r+f/r^2+g/r^3, with

    d = (L+b)/(2*a),
    e = (a*d^2+d-L-b/2-1/4)/(2*a),
    f = (e-d+d^2/2-C1)/(2*a),
    g = (f-a*e^2+d*e-d^3/6-e+d^2/2+C1*d-C2)/(2*a).

The independent check treats a,b,L,C1,C2 as formal symbolic quantities, puts t=1/r,
and substitutes the ansatz into F2(x)-a/t^2. It uses the finite logarithm series
for log(1+d*t+e*t^2+f*t^3+g*t^4) and reciprocal series to the orders needed.
The coefficients of t^-1, t^0, t^1 and t^2 all cancel identically over the
rationals in a,b,L. The receipt includes the pre-substitution coefficients and
records their exact cancellation.

This exact cancellation does not establish an analytic big-O estimate. In
particular, the explicit truncated ansatz and the implicitly defined root of
F2(x)=log(Y) have distinct truncation errors. The article explains any claimed
O(L^5/r^4) error for the displayed explicit inverse and O(r^-4) sequence error
for the implicit F2 inverse. The executable checks neither prove nor strengthen
those estimates.

## Hardened output, build and actual-ZIP replay

Every public checker writes only to stdout unless an explicit new external
output is requested. Output validation rejects existing paths, source-tree
outputs, live or dangling symlink ancestors, dot/dot-dot components, backslashes
and missing parents. Final file and output-directory creation is exclusive.
The guard test suite exercises finite input bounds, the integer conversion cap,
CLI rejection, source-manifest rejection and unsafe ZIP-member rejection. It
also checks that no public Python source contains an `assert` statement.

The builder verifies all source hashes before work and checks source-tree
immutability afterward. It compares fresh deterministic receipts with expected
bytes and cannot rewrite the expected receipts. Every Python subprocess gets
`-B`, deterministic hash settings and `PYTHONINTMAXSTRDIGITS=640`.

The TeX format creation and all document passes explicitly use
`-no-shell-escape`. The format, auxiliary files and TeX caches are created from
disposable copies outside the package. The PDF must match the reference PDF
byte for byte on the chosen toolchain; failures are visible rather than being
silently repaired by replacing a reference artifact.

Actual-ZIP replay requires the input archive to match the trusted package
before executing extracted code. It compares complete member bytes and
metadata, complete ZIP bytes, PDFs and receipts from independent ordinary and
optimized-Python extractions. It checks both source trees, the trusted package
and input archive remain unchanged. Archive guards limit inputs to 500 regular
stored members and 32 MiB of uncompressed content. This is an integrity and
reproducibility workflow, not a general sandbox for arbitrary archives or a
security proof against hostile concurrent filesystem changes.
