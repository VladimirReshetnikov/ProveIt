# Finite computation details

This note documents the algorithms shipped with Report235. The article provides
the analytic remainder bounds and the global optimization proof. Code receipts
record finite arithmetic checks and numerical corroboration only.

## Exact integer law and adjacent recurrence

For r of n's parity, 0 ≤ r ≤ n, put k=(n-r)/2 and m=(n+r)/2. The unnormalized
weight is

    w_n(r) = m^k m!/(k! r!).

The total is A360592(n). In particular w_n(n)=1 and

    w_n(r+2)/w_n(r) = k (1+1/m)^k / ((r+1)(r+2)).

`finite_weights` uses integer powers and binomial coefficients from the defining
sum. `recurrent_weights` starts from w_n(n)=1 and works backward with exact
fractions, checking integrality at every step. Equality of the complete weight
vectors is checked for n=0,1,2,3,8,9,19,20,60,99,100,199,200. The receipt also
records the raw marked moment sums through degree four and marked-polynomial
values at 1/2, 1 and 3/2. These finite integer checks are independent of the
asymptotic coefficient formulas.

## Defect and scalar generators

The exact defect relative to the Poisson kernel has finite-order coefficients

    D_j(r) = (-1)^(j+1) { r^(j+1)/(2j(j+1))
                 + (1/j) sum_{h=0}^{r-1} ((r-2h)^j-r^j) }.

All operations in the coefficient generator are symbolic over the rationals.
With t=n^(-1/2), free c and u=t(r-c/t), use weight(t)=2 and weight(u)=1.
Cancel the constant -3c²/4, expand the exponential through weighted degree
2K+1 and average using centered Poisson moments. The associated Stirling
numbers count partitions with no singleton blocks and obey

    B(d,k) = k B(d-1,k) + (d-1) B(d-2,k-1).

An independent differential-operator calculation and Touchard formulas check
these steps. Formal logarithm coefficients satisfy the finite recurrence

    L_j = C_j - (1/j) sum_{i=1}^{j-1} i L_i C_(j-i).

Applying (c d/dc)^h produces the marked cumulant coefficients. The exact mean
and variance coefficient identities are additionally checked by expanding finite
weighted raw moments before taking their quotient and cumulant. This supplies
an arithmetic cross-check; the justification for the analytic error control
comes from the finite-moment proof in the article, not differentiation of a
pointwise asymptotic remainder.

For the signed-density generator c instead denotes theta=t*mu. It returns
P_K and its **ordinary** Poisson expectation. Exact parity-conditioned
normalization uses the parity filter described in the article; the printed
ordinary expectation is not mislabeled as an exact conditioned normalizer.

## Cubic comparison and characteristic-function derivatives

`checks.py` independently builds the binomial-to-Poisson logarithm and compares
its weighted-degree-five truncation to the normalized marked density. The exact
difference is

    (5/8) t (u³ - 3 theta t u).

It checks both the cubic and linear pieces against the third Charlier
polynomial. The computation also checks the symbolic derivative map used in
fine localization. Write p=1-v/nu, f(p,w)=log(1+p w)/p and L=nu f(p,w). Then

    partial_nu L = f + (1-p) partial_p f,
    partial_v L  = -partial_p f.

The three roots use w=exp(i angle)-1, w=-1-exp(i angle), and w=-2. The numerical
program differentiates the quotient of the exact parity-filtered characteristic
functions analytically, including the second root and denominator. It then
checks these derivatives against numerical differentiation. Scaled real/imaginary
Jacobian columns, minimum singular values and finite-displacement ratios are
reported for both parities near 10^4, 10^6 and 10^10. The finite nondegeneracy
checks do not substitute for uniform convergence along the full parameter
segment in the proof.

## Supplementary exact residue coupling checks

The article's supplementary log-concave coupling lemma has a separate finite
rational check in `code/coupling.py`, included by `checks.py`. This is a general
coupling calculation, not a numerical extension of the critical model to a
higher modulus.

There are 2,520 weight/modulus/shift cases. Supports have N+1 points with
N=0,…,20; moduli are q=2,…,7. Four exact positive log-concave weight families
are used: uniform, geometric adjacent ratio 1/100, geometric adjacent ratio 100,
and the decreasing rational adjacent ratios (2N+3-k)/(k+1), k=0,…,N-1.
For each family and modulus, the support starts at -q-1, -1, 0, q-1 or 2q+1.
Thus the fixtures include singleton supports, missing residues, both support
endpoints and translated supports crossing or lying below zero.

All probabilities and CDF cut points are exact fractions. For every present
pair of actual residue labels a<b, define K_a=(X_a-a)/q, retaining its possibly
negative index support. The checks verify

    F_a(k) ≤ F_b(k) ≤ F_a(k+1)

at every relevant integer k, with exact zero and one values outside support.
They combine all conditional and unconditional CDF breakpoints into one
partition of (0,1). Every open cell midpoint and every interior CDF breakpoint
is tested with lower quantiles. At each level the conditional quantiles have
range at most q-1, and each lies within q-1 of the unconditional quantile.
The cell convention also covers values between breakpoints, since lower
quantiles are constant on the corresponding right-closed intervals.

The receipt reports case, residue-pair, interlacing and quantile-cell counts,
maximal gaps by modulus and boundary fixtures. The finite checker explicitly
rejects nonpositive, inexact or non-log-concave weights, unsupported moduli,
noninteger/oversized shifts and oversized supports. Its accepted function
bounds are 1–41 points, q=2,…,7 and shifts between -1000 and 1000. These are
executable resource limits, not limitations on the theorem. Every test uses
explicit exceptions and remains active under optimized Python.

## Numerical windows and tails

The numerical marked mass is anchored at a parity-compatible r0 near mu with
relative weight 1. It is propagated both ways using the exact adjacent ratio.
The inclusive parity-compatible window lies inside

    lambda ± (18 sqrt(lambda) + 100),

clipped to [0,n]. Let S be the sum of relative weights on that window. The
probabilities used for the finite TV sum are w_rel/S, that is, the exact target
law conditioned to the window up to arithmetic error.

Reference Poisson and binomial masses have one log-gamma anchor at the left
endpoint and are propagated by their exact two-step ratios. They retain their
full parity normalization and are not renormalized on the window. This is
independent of the asymptotic signed-density approximation.

For mean nu and integer bounds lo ≤ nu ≤ hi, the ordinary Chernoff expression
for probability outside [lo,hi] is the sum of applicable terms

    exp(-nu+x-x log(x/nu)),  x=lo-1 and x=hi+1.

The lower term is omitted for lo=0 and is exp(-nu) for lo=1. These also bound
ordinary binomial tails with mean nu because its exponential moments are
bounded by the Poisson exponential moments. Divide by the actual parity-event
probability, either

    (1 + (-1)^a exp(-2nu))/2

or

    (1 + (-1)^a (1-2nu/M)^M)/2,

to bound a conditioned reference tail. All reported windows contain every
reference mean; this condition is checked explicitly.

For the marked law, the global inequality Delta_n(r) ≤ 1/(4n) holds on its whole
finite support. Its truncated normalizer relative to the original conditioned
Poisson is computed at the anchor:

    Z_window = Q_(lambda,a)(r0) exp(Delta_n(r0)) S.

The full normalizer is at least this positive quantity. Therefore a valid
analytic target-tail bound is

    tau_P ≤ exp(1/(4n)) Q_(lambda,a)(outside window) / Z_window.

No asymptotic approximation to the denominator is inserted. `Z_window` is
computed from the exact log-gamma weight identity at r0. The bound is safe as
an analytic expression; its printed floating-point evaluation is not an
outward-rounded certificate.

If Q is a fully normalized reference and P_window is the target conditioned to
the window, the program reports

    T_window = (1/2) sum_{r in window} |P_window(r)-Q(r)|.

The true total variation differs by at most

    tau_P + tau_Q/2.

Indeed the interior contribution changes by at most tau_P/2, and the omitted
exterior contribution is at most (tau_P+tau_Q)/2. This is the separate analytic
truncation allowance recorded for every TV estimate. It does not include
floating-point roundoff. Reported mean, variance and scaled signed-density
remainders are explicitly window computations.

## Hardened output and replay behavior

All public checks print to stdout unless an explicit new external output is
requested. Output validation rejects preexisting paths, source-tree outputs,
symlink ancestors, dot/dot-dot and backslash components and missing parents.
The final create is exclusive. Guards remain active under `-O` because they use
explicit exception checks, never Python `assert` statements.

The build checks the entire source manifest before doing work and verifies
source immutability afterward. It compares freshly computed receipts with the
frozen originals; it cannot update them. Every Python child receives `-B`, a
640-digit integer conversion limit and deterministic hash-seed settings.

Both TeX invocations, including creation of the private format, have shell
escape disabled. Auxiliary files and TeX caches belong to a disposable working
directory. Final build outputs go only into the exclusively created external
directory.

The actual-ZIP replay checks every original member against the trusted source
before execution, rebuilds two independent extractions under normal and optimized
Python, and requires every member, metadata field recorded by the format and
all archive bytes to agree. Equality of the whole ZIP catches metadata outside
the explicitly reported subset as well. It verifies unchanged input/source
trees and complete PDF and receipt equality. Version-dependent failures are
reported, never repaired by silently replacing expected artifacts.
