# Infinite genuine-compiler candidates with the main exponential congruence omitted

## Status and exact omitted condition

This is a follow-on to sealed Research Report 37. It does not alter that packet. It proves a more specific sufficiency result in the unwrapped odd-input sector: after fixing an actual compiler, the ordinary input, one admissible q, and even Z=1, s=t=1, infinitely many choices satisfy **every test in Report 37 except the main exponential congruence**

    2^p = X (mod H),  H=4Y(X+1)+3.

This congruence remains unresolved on the constructed family. The theorem supplies neither a full negative zero nor a positivity theorem. The reduced system is nonempty, so any proof excluding all negative zeros must use additional information, including the omitted congruence. Outer packing, positive input loading, and the exact first/main Pell ratio are simultaneously compatible on a fixed genuine-compiler slice. No candidate is proved either to satisfy or to fail the omitted congruence, so logical independence of that equation is not claimed.

The existence proof is a shrinking-target argument with an explicit discrepancy error, not an appeal to equidistribution alone. It varies the X scale; it does not attempt to use density inside the old bounded fixed-X interval.

## 1. Fixed genuine compiler and explicit outer constants

Fix any valid complete75 compiler export and x>=1, with the notation and exact hypotheses of Report 37. In particular retain the actual fixed K0, MC, MF0, MFsrc=MF0+B-1, b and d_cell. Do not replace them by freely selected mask numerals.

Write

    u=2*d_cell*x+b, W=2^u=2^b B^(2x).

Choose any even q satisfying

    q=1 (mod B-1), 3 does not divide q,
    q >= W+u-b+2.                                      (1)

Such a choice is explicit: q=B^(2x+2) works. Indeed b<=d_cell makes W<=B^(2x+1), and

    q-W >= (B-1)B^(2x+1) > 2*d_cell*x+1.

Here B>=16 and d_cell>=4, so the elementary exponential bound gives the last strict inequality. B is a power of two, so q is even and coprime to 3; its repunit relation is exact.

Fix, from now on,

    J=(q-1)/(B-1), Q=q^2-1,
    M=(MC+q MFsrc)J,
    C=W+1, Z=1, alpha=q-C-u+b,
    s=t=1, Y=q^3,
    L0=q(q-1)Q.

These are genuine source constants or positive source witnesses. In particular alpha>=1, W is even, C is odd, and MC is even by the actual modified compiler recipe. Consequently M is even.

The parity premise is source-specific and is additional to the abbreviated inequality list in Report 37. The modified compiler note explicitly states `MC even` at lines 34--46, equations (2)--(3): https://github.com/VladimirReshetnikov/ProveIt/blob/d5bd4a67b41b89688a079997574a94bcd855bb83/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md#L34-L46 . Its recipe is `MC=MC0-2Rrad^e_*`. The inherited complete77 materializer, lines 73--76, gives `MC0=B-1-sum(Rrad^e for e in positions if e!=1)`: https://github.com/VladimirReshetnikov/ProveIt/blob/d5bd4a67b41b89688a079997574a94bcd855bb83/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_77.py#L73-L76 . Start selector 0 is a retained position, and every other retained position is strictly positive. Thus the sum has exactly one odd summand, Rrad^0=1; B-1 is odd and Rrad is even. MC0 is therefore even, and subtracting `2Rrad^e_*` preserves parity. These two source files are preserved as inert context snapshots. No stronger residue class for MC is assumed.

For integer r>=1 take just the one progression

    w_r=1+(q-1)r, X_r=q^3 w_r, E_r=X_r Y.             (2)

Define the fixed integer

    P0=Q*((1+q*(K0+q^3))*C-q^2-W)-M,
    p0=P0 mod L0, 0<=p0<L0.                           (3)

Because Q and C are odd, q is even and M,W are even, P0 is odd. Thus p0 is odd and nonzero; L0 is even. Every integer

    p=p0+L0 k                                         (4)

is odd and satisfies the exact outer packing and transport congruences for every r. No coprimality or favorable choice of a native mask is needed.

### Exact congruence calculation

Let D_r=1+q(K0+X_r). The difference X_r-q^3 is q^3(q-1)r, so

    Q(D_r C-q^2-W)-M = P0 + L0*q^3*C*r.

Hence (4) is equivalent to

    p+M = Q(D_r C-q^2-W) (mod L0).                    (5)

Given p>0 satisfying (5), put

    N=(p+M)/Q,
    F=(N-1+q^2)/q,
    z=((K0+X_r)C-F)/(q-1).                            (6)

All three displayed divisions are integral. Reduction of (5) modulo qQ gives N=1 mod q, so the recovered marker is precisely Z=1. Rearranging (5) gives transport integrality. Conversely these identities give

    -p=(q^2-1-qF)Q+M,
    (K0+X_r)C=F+z(q-1).

There is also a division-free affine form. With the integer lattice coordinate `ell_lattice=(p-P0)/L0`, exact cancellation gives

    F=(K0+q^3)C+(q-1)*ell_lattice,
    z=q^3*C*r-ell_lattice.                            (6a)

Thus the entire outer block at these fixed markers is a two-integer affine family in r and ell_lattice. Its remaining positivity conditions are the two strict linear inequalities in (6a); the ratio will isolate ell_lattice. Positivity of F and z will follow from the index asymptotics below. This is a parametrization using the actual fixed compiler values throughout.

## 2. The exact ratio center and its curvature

For real X sufficiently large, set

    A(X)=Y(X+1)+2, P(X)=2XY^2+1,
    alpha(X)=log(A+sqrt(A^2-1)),
    beta(X)=log(P+sqrt(P^2-1)),
    K(X)=sqrt(P^2-1)/(2sqrt(A^2-1)),
    delta0=one half of log(1+1/Y)>0,
    S(X)=alpha(X)+beta(X)/2.

Define the real function

    f(X)=((XY+1)*beta(X)/2 + log Y + delta0 - log K(X))/S(X). (7)

For n=(XY+1-p)/2, the logarithm of the exact Pell ratio is

    log(psi_A(p)/(2psi_P(n)))
      = log K(X)+p alpha(X)-n beta(X)
        +log(1-exp(-2p alpha(X)))-log(1-exp(-2n beta(X))). (8)

The non-tail part of (8) at p=f(X) is exactly log Y+delta0, strictly inside the target interval (log Y,log(Y+1)). The slope with respect to p is S(X).

Put a0=log(2Y)>0 and l=log X. Then, with Y fixed,

    alpha=l+a0+O(1/X),
    beta=l+2a0+O(1/X),
    log K=log Y+O(1/X),

and, crucially,

    f(X)=YX/3 + (2Y a0/3)*X/(3log X+4a0) + 1/3+O(1/log X), (9)
    f''(X)= -2Y a0/(9X(log X)^2)*(1+O(1/log X)).       (10)

The second statement is not obtained by differentiating an uncontrolled O-term. To justify it, write z=1/X and v=1/(3log X+4a0). The three remainders in alpha,beta,log K are real analytic functions of z vanishing at zero. Subtracting the first two terms in (9) from the exact formula (7) leaves

    1/3+v G(z,v)

for a function G real analytic near (0,0). In this rearrangement, expressions such as (epsilon_beta(z)-epsilon_alpha(z))/z are analytic because their numerators vanish at zero. Thus the second derivative of the remainder is O(1/(X^2(log X)^2)); differentiating the explicit X/(3log X+4a0) term gives (10). This also supplies uniform upper/lower derivative bounds on every sufficiently large dyadic interval.

An explicit form of that analytic remainder can remove any ambiguity. Let eps_a(z), eps_b(z), eps_K(z) be respectively alpha-log X-a0, beta-log X-2a0, and log K-log Y, and set eps_D=2eps_a+eps_b and eps_diff=eps_b-eps_a. Then

    G(z,v) = [ (2Y/3)*(eps_diff/z)
                 +(2/3)*(a0+eps_diff)+2delta0-2eps_K
                 -(2Y*a0/3)*v*(eps_D/z) ] / (1+v*eps_D).

Every divided numerator vanishes at z=0. More explicitly, put a1=(Y+2)/Y and b1=1/(2Y^2). The analytic functions are

    eps_a = log((1+a1*z+sqrt((1+a1*z)^2-z^2/Y^2))/2),
    eps_b = log((1+b1*z+sqrt((1+b1*z)^2-z^2/(4Y^4)))/2),
    eps_K = (1/2)*log(((1+b1*z)^2-z^2/(4Y^4))
                      /((1+a1*z)^2-z^2/Y^2)).

Their real branches are analytic near z=0 and have zero constant terms. Since v'=-3v^2/X, the explicit leading term has second derivative `-2Y*a0*v^2*(1-6v)/X`; the remainder has second derivative O(1/(X^2(log X)^2)). Thus (10) follows with controlled derivatives.

Define

    g(r)=(f(X_r)-p0)/L0,
    c0=q^3(q-1).

Then (10) gives

    g''(r)= -K0_star/(r(log r)^2)*(1+O(1/log r)),
    K0_star=2Y*a0*c0/(9L0)>0.                         (11)

K0_star is an analytic constant, unrelated to the compiler K0. All implied constants depend only on the already fixed compiler/input/q (in fact most depend only on q). They do not depend on r, the dyadic endpoint or the Fourier frequency used below.

## 3. A proved shrinking-target lemma

We use two standard analytic-number-theory inequalities, stated precisely enough to expose the quantitative step.

1. If a C^2 real phase h on an interval of N consecutive integers satisfies lambda<=|h''|<=C lambda, its exponential sum is O_C(N sqrt(lambda)+1/sqrt(lambda)). This is the second-derivative estimate, for example Olivier Robert, *On van der Corput's k-th derivative test for exponential sums*, Theorem 1 (2016), DOI 10.1016/j.indag.2015.11.009, Section 3.1. Primary full text: https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf
2. The Erdős–Turán inequality bounds interval counting error by O(N/(Hf+1)+sum_(1<=h<=Hf) |sum exp(2*pi*i*h*g(r))|/h), uniformly in the target interval. One primary research source stating this form is A. Mukhopadhyay, O. Ramaré and G. K. Viswanadham, *Discrepancy estimates for generalized polynomials*, Lemma 6: https://ramare-olivier.github.io/Maths/Discrepancy-V_5.pdf

Apply the first estimate on N<=r<2N using (11), for frequency h. Uniformly for 1<=h<=Hf, it gives

    |sum exp(2*pi*i*h*g(r))|
       << sqrt(hN)/log N + sqrt(N)*log N/sqrt(h).      (12)

The derivative-comparability constant is fixed; multiplication by h does not change it. Taking Hf=floor((log N)^4), the second inequality therefore gives an interval counting error

    O(N/(log N)^4 + sqrt(N)*log N) = o(N/log N).      (13)

Indeed the first frequency sum is O(sqrt(N Hf)/log N), and the second is O(sqrt(N) log N), because sum h^(-3/2) converges. This is the required shrinking-target estimate; qualitative equidistribution by itself would not suffice.

Let

    kappa0=delta0/(8L0)>0.

Use the interval [0,kappa0/log(2N)) in the circle. Equations (12)--(13) imply that, for all sufficiently large integers N, at least

    (delta0/(32L0))*N/log N                             (14)

integers r in [N,2N) satisfy

    0 <= fractional_part(g(r)) < kappa0/log r.         (15)

For clarity, the leading count before the error is kappa0*N/log(2N); for sufficiently large N at least half remains, and log(2N)<=2log N. The implied threshold N0 is a finite constant depending on the fixed data. No numerical value for that potentially enormous threshold, and no uniform feasible complexity bound, is claimed.

## 4. Exact Pell acceptance and all strict constraints

For every sufficiently large r satisfying (15), define

    k=floor(g(r)), p=p0+L0*k,
    n=(X_r*Y+1-p)/2.                                 (16)

Here k in (16) is only an integer lattice quotient; the supplied first Pell coefficient will be denoted k_first below. Because p0 is odd and L0 even, p is odd and n is integral.

By construction

    0<=f(X_r)-p<L0*kappa0/log r.

As S(X_r)~(3/2)log r, eventually S(X_r)<=2log r, and consequently the non-tail part of (8) lies between log Y+3delta0/4 and log Y+delta0. Both p and n tend linearly to infinity; the two exact Binet tails therefore have total absolute value below delta0/4 for all sufficiently large r. Thus the *exact integer* Pell values satisfy

    Y < psi_A(p)/(2psi_P(n)) < Y+1.                   (17)

This is acceptance, not merely a necessary real-window test. The fixed interior margin controls the omitted tails rigorously.

The center expansion and (16) imply

    p/(X_r Y) -> 1/3,
    p-X_rY/3 -> +infinity,
    n/(X_rY) -> 1/3,
    d_def=2n-p=X_rY+1-2p ~ X_rY/3.

It follows, simultaneously for all sufficiently large selected r, that

    p>=13 odd, u<p, n<=p-1, (p+1)/2<=n,
    2n+p-1=E_r,
    2p+6<=E_r<=3p-3,
    p<X_r q^4,
    4^d_def>X_r.

Every strict source/index bound in Report 37 survives. The inequalities are eventual statements with a single threshold enlarged to cover their finite list; none is inferred from a finite experiment.

The recovered outer F in (6) has asymptotic

    F/X_r -> Y/(3qQ)=q^2/(3(q^2-1)) < 1.

Hence F>q eventually, and since C=W+1>1,

    (K0+X_r)C-F>0.

Thus z in (6) is a positive integer. Every raw, marker, packing and transport equation holds with the fixed positive alpha,C,Z,W. Moreover H>W, so W=2^u is exactly the least input residue; the input index is e=u. All tests of Report 37 now hold except the explicitly withheld main congruence.

## 5. Theorem and literal one-residual realization

**Theorem (all but the main exponential congruence).** For every valid fixed complete75 compiler export and every x>=1, choose q by (1), for example q=B^(2x+2). There is N0 such that for each integer N>=N0, at least the quantity (14) distinct scales w_r with N<=r<2N admit odd main indices p satisfying every condition of the exact negative-zero predicate in Report 37 except `2^p=X_r mod H`. The fixed witnesses have `W=2^u, Z=1, C=W+1, s=t=1`, and every compiler numeral is unchanged. In particular the reduced predicate with that one congruence omitted has infinitely many solutions on each genuine compiler/input slice. Here N measures the progression index r, not the size of w: the counted actual scales lie in `[1+(q-1)N, 1+2(q-1)N)`. The density constant in (14) and its eventual threshold are allowed to depend on the fixed data.

This can be expressed directly in the literal source. Write

    c=psi_A(p), D=chi_A(p), k_first=2psi_P(n), tau=chi_P(n),
    eta=c-k_first*Y, zeta=k_first-eta,
    h=(k_first+p-1)/E_r.

The ratio and representative identity make these positive integers and give restored R=-p. Define the input witnesses and ordinary strong/auxiliary witnesses exactly as in Report 37, using e=u and its all-odd-p auxiliary construction. Those are all positive; their equations do not require the main exponential congruence.

Put

    r_main = (D-a*c-X_r) mod H
           = (2^p-X_r) mod H, 0<=r_main<H,
    ga=floor((D-a*c-X_r)/H)>0.                        (18)

All 29 raw supplied coordinates are now strictly positive integers. Every retained raw comparison is zero except possibly

    D - (X_r+a*c+ga*H) = r_main.                      (19)

Thus the raw sum-of-squared-residuals polynomial takes the exact value r_main^2 on this family. This is not a zero unless r_main=0.

In positive21, the triangular main root is D'=D-r_main=X_r+a*c+gaH>0. All comparisons except possibly its main norm vanish, and that norm residual is

    (D')^2-Delta*c^2-1 = -r_main*(2D-r_main).

Its saved sum-of-squares value is therefore `[r_main*(2D-r_main)]^2`. Since D>H>r_main, this vanishes if and only if r_main=0. This precise residual description does not relax the original theorem: the unresolved modular condition remains exactly the difference between these integer tuples and full child zeros.

## 6. A separate sharpened outer estimate in the unwrapped sector

Every putative full negative zero in this sector has q>W>=2B^2>K0. Since X>=q^3,

    K0(q^2-1)<q^3<=X,
    q(q^2-1)(K0+X)<Xq^3.

From positive transport and packing,

    p<Q*(Z+q(K0+X)C-q^2)-M
      <qQ(K0+X)C <CXq^3.                            (20)

The middle strict inequality uses Z<q<q^2 and M>0. Hence ts<3C, strengthening the earlier ts<3q and the looser estimate involving C(1+1/q). This consequence alone does not force a sign. It is separate from the family theorem, which satisfies (20) eventually.

## 7. What remains unresolved and what this advances

The construction reduces one explicit infinite candidate family to the single congruence `2^p=X_r mod 4Y(X_r+1)+3`. There is no proved hit of that congruence, and no proof that it always fails. The full question remains open.

The new content is not the congruence parametrization alone. It is the simultaneous realization of its lattice, the exact Pell ratio, every bounded first-index condition, positive input loading, packing and transport at fixed q,Z,s,t and genuine compiler constants. The shrinking-target estimate is essential because the allowable index window is of order 1/log r. Neither the old fixed-X density construction nor qualitative equidistribution justifies this result.

There is also a purely integer enumeration of these candidates: enumerate r, use Report 37's finite exact ratio search at its associated q,w,s=t=1, and retain the resulting p only if p=P0 mod L0 and the fixed-marker outer tests pass. The theorem guarantees infinitely many retained r. This enumeration does not need to decide an equality at a transcendental window endpoint. No practical search bound is claimed.

This family is not a complete parametrization of all possible negative zeros. Excluding its main congruence would eliminate this family only. Finding a hit would, by Report 37's explicit reconstruction, yield a full negative zero; the present theorem does not supply one.

The sealed Report 37 TeX source read for this continuation has SHA256 `57d6598d60389b2fc283f89f47b29ef5905af259ebe0ea69433a8838f9749001`. Its mathematical source and prior reduction are inherited, unchanged. No upstream code, saved schedule, repository mutation, or upload is used here.


## 8. Corroboration and reproducible scope

The new own checker uses unconditional exception checks, deterministic JSON stdout, optional external `--output`, and byte-exact `--expect`. It never executes the saved upstream schedule. Its exact results are:

- Five formal multivariate polynomial identities: transport, negative packing, lattice progression, the positive21 one-residual identity, and the analytic G rearrangement after clearing denominators
- 36 structural exponent/loading-bound fixtures, without any claim that a fixed compiler export was materialized
- 864 outer algebra/parity fixtures, without a Pell-ratio or full-zero claim
- 48 exact main Pell/floor-residual fixtures, all explicitly subsystem checks
- Authentication of the sealed Report 37 TeX, unchanged projection JSON, and two parity-source snapshots, with static checks on ga's root role

These checks corroborate the algebra. The nonzero curvature and shrinking-target conclusions rely on the general proof and the two stated analytic-number-theory estimates, not on observed numerical frequencies or floating-point experiments. No selected large-r genuine-compiler tuple has been materialized, and no main-congruence hit has been found or claimed.
