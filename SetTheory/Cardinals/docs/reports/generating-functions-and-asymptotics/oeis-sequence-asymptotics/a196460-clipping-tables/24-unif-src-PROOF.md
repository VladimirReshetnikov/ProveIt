# Uniform growing-order sector truncations for A196460

4 October 2026, UTC. A separate continuation, not a revision of the fixed-order
article or its audit. All statements below are proved here; finite arithmetic
checks are corroboration. No novelty, formal-verification, or publication claim
is made. The growing-order inverse problem is not addressed.

## 1. Exact object and sharp conclusions

For integers n>=1 and 0<=k<=2n define

    P_k(n) = sum_(r+c=k; 0<=r,c<=n) binom(n,r)binom(n,c)2^(rc),
    S(n,k) = P_k(n)2^(-nk),
    a_n = sum_(j=0)^n binom(n,j)(1+2^j)^n,
    A_n = a_n/2^(n^2) = sum_(k=0)^(2n) S(n,k).

The last identity follows by expanding the single sum, complementing both
binomial indices, and grouping by their sum. All sectors are strictly positive.
For 0<=M<2n put

    R_(n,M) = A_n - sum_(k=0)^M S(n,k),
    E_(n,M) = R_(n,M)/S(n,M+1) - 1.

**Theorem 1 (all truncation orders, exact optimal bound).** For every n>=32,

    0 <= E_(n,M) <= K_n
      := 3(3n^2+n+1) / [n(13n^2-15n+2)]                 (1)

simultaneously for every integer 0<=M<2n. Equality on the right holds uniquely
at M=2n-4. Consequently the first omitted exact sector dominates every possible
tail, uniformly over all growing truncation orders, and

    sup_(0<=M<2n) n E_(n,M) -> 9/13.

In particular 9/13 is the optimal asymptotic uniform constant. More explicitly,

    K_n = 9/(13n) + (174n+21)/[13n(13n^2-15n+2)].        (2)

The elementary proof below deliberately uses the convenient threshold 32.
It makes no claim that 32 is the smallest possible threshold.

**Theorem 2 (the actual clipping-table count).** Let C_n=a_n+1 and merge its
additional contribution only into the terminal sector:

    S_C(n,k)=S(n,k) for k<2n,
    S_C(n,2n)=2S(n,2n).

Then C_n/2^(n^2)=sum_k S_C(n,k). For n>=32, simultaneously for 0<=M<2n,

    0 <= [sum_(k=M+1)^(2n) S_C(n,k)]/S_C(n,M+1)-1 <= 1/n.  (3)

The upper equality occurs uniquely at M=2n-2. The terminal truncation
M=2n-1 is exact. Thus the sharp asymptotic uniform constant is 1 in this
convention.

Without keeping the additional 2^(-n^2) explicitly or merging it as above,
Theorem 1 does not extend unchanged to C_n: at M=2n-1 its remainder is twice
S(n,2n). The relative excess is exactly 1 there, rather than O(1/n).

## 2. Complement symmetry and a raising identity

In the summand of S(n,2n-k), substitute r=n-u, c=n-v, with u+v=k. Since

    -n(r+c)+rc = -n^2+uv,

binomial symmetry gives the exact identity

    S(n,2n-k) = 2^(-n^2)P_k(n).                          (4)

For w_(r,c)=binom(n,r)binom(n,c)2^(rc), the binomial raising identity gives

    (k+1)P_(k+1)(n)
      = sum_(r+c=k) w_(r,c)[(n-r)2^c+(n-c)2^r].          (5)

Indeed, raising r gives every target weight multiplied by its new r, and
raising c gives it multiplied by its new c. Their sum is k+1; factors n-r
and n-c automatically remove forbidden boundary moves.

Put lambda=ln 2, h=r-k/2 and A=n-k/2. The bracket in (5) is

    2^(k/2)[2A cosh(lambda h)+2h sinh(lambda h)].

Since A>=0 and h sinh(lambda h)>=0,

    P_(k+1)/P_k >= [(2n-k)/(k+1)]2^(k/2)                 (6)

for 0<=k<2n. For a high-sector ratio write l=2n-k, so 1<=l<=n
when n<=k<2n. Applying (6) at l-1 and using (4) yields

    S(n,k+1)/S(n,k) = P_(l-1)/P_l
      <= g_(n,l) := l 2^(-(l-1)/2)/(2n-l+1).             (7)

The sequence l 2^(-(l-1)/2) has maximum 3/2 at l=3: compare l=1,2,3
directly, then its successive ratio (l+1)/(sqrt(2)l) is less than 1 for
l>=3. Therefore

    g_(n,l) <= q_n := 3/[2(n+1)]                         (8)

for all 1<=l<=n.

## 3. A universal discrete-Gaussian bound for low sectors

For 0<=k<=n, the distribution of h in (5) is proportional to

    b(h)2^(-h^2),
    b(h)=binom(n,k/2+h)binom(n,k/2-h).

Its lattice is the integers if k is even and the half-integers if k is odd.
The function b is symmetric, and is extended by zero beyond its allowed
support. For h>=0 its successive ratio is

    b(h+1)/b(h)
      = [(A-h)(k/2-h)]/[(k/2+h+1)(A+h+1)] <= 1.

For any nonnegative increasing function f of |h|, reweighting a symmetric
discrete Gaussian by this decreasing b cannot increase its expectation.
Explicitly, if X,Y are independent base Gaussian variables, then

    (b(X)-b(Y))(f(|X|)-f(|Y|)) <= 0.

Taking expectations proves Cov(b,f)<=0 and hence E_b f<=E f. The required
expectations converge absolutely; b has finite support.

Take f(x)=cosh(lambda x)+x sinh(lambda x), which is increasing on x>=0.
For n>=2 and k<=n, A>=1, so the bracket divided by 2A 2^(k/2) is at most
f(|h|). We now give an explicit bound E f<8 for either lattice.

For integer h the Gaussian denominator is at least 1 and
f(j)<=(1+j)2^j. Thus the expectation is at most

    1+2 sum_(j>=1)(j+1)2^(-j(j-1))
      <= 13/2 + 2 sum_(j>=3)(j+1)4^(-j)
      = 481/72 < 8.                                    (9)

Here j(j-1)>=2j for j>=3. For half-integer h=m+1/2, the denominator
is at least 2*2^(-1/4). The same bound for f gives an expectation at most

    sqrt(2) sum_(m>=0)(m+3/2)2^(-m^2)
      <= sqrt(2)[3/2+sum_(m>=1)(m+3/2)2^(-m)]
      = 5sqrt(2) < 8.                                  (10)

Consequently (5) implies the explicit low-sector estimate

    P_(k+1)/P_k <= 8[(2n-k)/(k+1)]2^(k/2),
    S(n,k+1)/S(n,k) <= d_n := 16n 2^(-n/2)              (11)

for n>=2 and 0<=k<=n. The deliberately loose second bound is sufficient.

At n=32, d_n=1/128 and (n+1)d_n=33/128<3/2. For n>=32 the latter
quantity decreases: its successive ratio is (n+2)/(sqrt(2)n)<1.
Thus d_n<=q_n for every n>=32. Together with (7)--(8), this proves

    S(n,k+1)/S(n,k) <= q_n<1                            (12)

for every 0<=k<2n, whenever n>=32. In particular the S sectors decrease
strictly, and by (4) the P sectors increase strictly.

By summing a finite geometric majorant, (12) alone already proves

    0<=E_(n,M)<=q_n/(1-q_n)=3/(2n-1).                   (13)

This establishes full all-M uniformity before refining the constant.

## 4. Locating the unique worst tail

Write j=M+1 and l=2n-j. Then 0<=l<=2n-1, and (4) gives exactly

    E_(n,M)=H_l,
    H_0=0,
    H_l=(P_0+...+P_(l-1))/P_l  (l>=1).                 (14)

For later use (12) also gives

    H_l <= [P_(l-1)/P_l]/(1-q_n).                       (15)

### Low first-omitted sectors: j<n

Their first forward ratio is at most d_n by (11); all later ratios are
at most q_n. Therefore H_l<=d_n/(1-q_n). The quantity
n*d_n/(1-q_n) decreases for n>=32: n^2*2^(-n/2) decreases since
((n+1)/n)^4<2, and 1/(1-q_n) also decreases. At 32 it equals 11/42.
Thus every such tail satisfies

    nH_l <= 11/42 < 9/13.                               (16)

### High first-omitted sectors with l>=5

Here l<=n. For 5<=l<n the ratio of the bounds in (7) is

    g_(n,l+1)/g_(n,l)
      = [(l+1)/l][(2n-l+1)/(2n-l)]/sqrt(2)
      <= (6/5)(34/33)/sqrt(2) < 1                       (17)

when n>=32. Consequently

    g_(n,l) <= g_(n,5)=5/[8(n-2)],
    H_l <= 5(n+1)/[4(n-2)(2n-1)].                      (18)

The bound in (18) is strictly less than H_3 for n>=32. Substituting the
formula for H_3 below and cross-multiplying positive denominators gives

    7n^4-146n^3+101n^2-46n+24 > 0.

This follows already for n>=21 from n^3(7n-146)>0 and
101n^2-46n+24>0.

### The four small nonzero values of l

Directly from the finite definition,

    P_0=1, P_1=2n, P_2=3n^2-n,
    P_3=(13n^3-15n^2+2n)/3,
    P_4=(27n^4-66n^3+41n^2-2n)/4.

Therefore

    H_1=1/(2n),
    H_2=(2n+1)/[n(3n-1)],
    H_3=3(3n^2+n+1)/[n(13n^2-15n+2)],
    H_4=4(13n^3-6n^2+5n+3)/[3n(27n^3-66n^2+41n-2)].    (19)

Equation (2) shows nH_3>9/13. In contrast nH_1<9/13;
nH_2<9/13 for n>22; and nH_4<9/13 for n>=28. For the last comparison,
the positive-denominator numerator difference is

    53n^3-1470n^2+847n-210
      = n^2(53n-1470)+847n-210 >0  (n>=28).

These strict comparisons, (16), (18), and H_0=0 cover every possible l.
They prove Theorem 1 and the uniqueness assertion. Formula (2) proves
the limiting optimal constant without an interchange of a limit and an
uncontrolled supremum: the supremum was computed exactly for every n>=32.

## 5. The extra full clipping table

For l>=1 the merged-terminal relative excess in Theorem 2 is

    J_l=H_l+1/P_l;                                     (20)

for l=0 the first omitted sector is the merged terminal one, so J_0=0.
At l=1, J_1=1/n. For l>=2, strict increase of P_l and Theorem 1 imply

    J_l <= H_3+1/P_2 < 1/n.

The last comparison has positive denominators and reduces exactly to

    12n^3-71n^2+30n-1 >0,

which holds for n>=6. This proves Theorem 2, with the unique maximizer
l=1 corresponding to M=2n-2. If the terminal sector is not merged, the
same bound applies to all M<=2n-2, but the last truncation has relative
excess exactly 1. The beyond-fixed-orders term is never discarded.

## 6. Leading polynomial terms have a different uniformity boundary

Define the positive leading coefficient

    alpha_k = sum_(r=0)^k 2^(r(k-r))/[r!(k-r)!].

The statements above use exact P_k(n), not alpha_k n^k. Their distinction
is material when k grows. For 0<=k<=n, express their ratio as a weighted
mean of the products

    B_(n,r,c)= product_(i=0)^(r-1)(1-i/n)
               product_(i=0)^(c-1)(1-i/n),  r+c=k,

with weights proportional to 2^(rc)/(r!c!). The elementary product
inequality product(1-x_i)>=1-sum x_i gives

    1-k(k-1)/(2n) <= P_k(n)/(alpha_k n^k) <= 1.          (21)

An informative upper bound holds over the whole range 0<=k<=2n:

    P_k(n)/(alpha_k n^k) <= exp[-k(k-2)/(4n)].           (22)

For a valid pair r,c<=n, use log(1-x)<=-x and
r(r-1)+c(c-1)=k(k-2)/2+2h^2, where h=r-k/2. Invalid pairs have zero
binomial contribution and satisfy the same upper bound automatically.
The exponent in (22) can be positive at k=1, which is harmless.

For any integer sequence 0<=k(n)<=2n, (21)--(22) prove the equivalence

    P_(k(n))(n)/(alpha_(k(n)) n^(k(n))) -> 1
       if and only if k(n)^2/n -> 0.                   (23)

Necessity follows by taking any subsequence with k^2/n bounded below:
then k tends to infinity and the upper bound is bounded away from 1.
Sufficiency follows from (21), since k=o(sqrt(n)) eventually has k<=n.

A more detailed central correction is also elementary. For n>=3 and
0<=k<=n set

    U=k(k-2)/(4n),
    epsilon=k(k-1)(2k-1)/[12n^2(1-(k-1)/n)].

Then

    exp(-epsilon)(1-2/n)
      <= exp(U) P_k(n)/(alpha_k n^k) <= 1,              (24)

so the corrected ratio differs from 1 by at most epsilon+2/n.
To prove this, the weights of h for alpha_k are proportional to
binom(k,k/2+h)2^(-h^2). The binomial factor is decreasing in |h|, so the
reweighting argument of Section 3 applies. The base Gaussian second
moment is less than 2 on either lattice. Explicit bounds are

    E_(integers) h^2
      <= 1+2 sum_(j>=2)j^2 4^(-j) =107/54<2,
    E_(half-integers) h^2
      <= sum_(m>=0)(m+1/2)^2 4^(-m)=41/27<2.

For the half-integer bound use m(m+1)>=2m and the denominator lower
bound 2*2^(-1/4). For the integer bound use j^2>=2j for j>=2.
Finally, for 0<=x<1,

    -x-x^2/[2(1-x)] <= log(1-x) <= -x.

Summing this over the product defining B bounds its logarithm between
-U-h^2/n-epsilon and -U-h^2/n. The sum of squared indices is at most
sum_(i=0)^(k-1)i^2; this gives exactly the displayed epsilon. Average
and use E exp(-h^2/n)>=1-E h^2/n>=1-2/n to obtain (24).

In particular, uniformly for k=o(n^(2/3)),

    P_k(n)/(alpha_k n^k)
      = exp[-k(k-2)/(4n)] [1+O(1/n+k^3/n^2)].           (25)

If k/sqrt(n)->c with 0<c<infinity, the uncorrected ratio tends to
exp(-c^2/4), rather than 1. Thus the square-root boundary in (23) is sharp.
These are single-sector coefficient statements. Replacing every retained
P_k in a truncation by only its leading monomial need not preserve a
remainder on the scale of the first omitted sector: errors in earlier
sectors can be much larger. No such substitution is asserted.

## 7. Evidence and scope

The fresh standard-library checker `check_sectors.py` constructs all P_k(n)
directly by integer arithmetic, without loading source code or coefficient
fixtures. It checks exact complement and raising identities, squares the
lower-ratio inequality to remove irrational powers, checks global ratio
bounds for n>=32, computes every admissible tail maximum, and checks the
elementary leading-coefficient bounds. Completed ranges and exact maxima
are recorded in `evidence/mathematics.json`; the accompanying log states
the counts. The calculations do not replace the all-n inequalities above.

The successful run covers n=1..128: 16,640 complement identities, 16,512
raising identities and squared lower bounds, 15,520 global-ratio checks,
97 complete sharp-tail comparisons for each of a_n and merged C_n, and
2,498 elementary leading-sector comparisons. `check_algebra.py` separately
verifies the three polynomial differences used for strict comparisons,
their positive-coefficient shifts at the stated thresholds, the Gaussian
geometric sums, and 129 exact alpha-weight second moments. Its results
are in `evidence/algebra.json` and the accompanying log.

The input preservation boundary comprises the two named source packet
directories and all their descendants, plus each adjacent ZIP and receipt.
The before snapshot was taken after initial inert reading of the supplied
proof and audit, before this new arithmetic checker was run. The after
snapshot compares object sets, bytes/hashes, sizes, modes and nanosecond
modification times. Access times are excluded because reading can change
them. No input was executed, modified, chmodded, restored or retimestamped.
The article being packaged elsewhere was not edited.

This continuation proves uniform finite-sector statements, including every
growing order 0<=M<2n. It proves no uniform growing-order logarithmic or
inverse expansion, no convergence of an infinite series at noninteger
arguments, and no exact integer inverse obtained by flooring an approximate
real inverse. Such questions remain separate. Attribution of A196460 and
its previously known leading asymptotic remains as in the supplied source
and audit; no additional priority search or novelty inference is made here.
