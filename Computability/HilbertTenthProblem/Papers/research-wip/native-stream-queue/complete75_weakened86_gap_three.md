# Exact exclusion of gap three in the negative-index86 branch

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with **R<0 and mu>0** must satisfy

    p odd, n<p<=2n-5.

The [preceding index-gap theorem](complete75_weakened86_index_gap.md)
gave n<p<=2n-3. This note excludes the remaining equality p=2n-3
by a finite exact certificate. It does **not** settle larger odd gaps,
the mu<0 branch, or universal soundness of the86 candidate. Its source
remains86=48M+38A with19 positive supplied coordinates and degree203;
the established75/87 bounds are unchanged.

The [checker](complete75_weakened86_gap_three.py) and
[receipt](complete75_weakened86_gap_three.json) specify the complete
finite search. Necessary inequalities first bound q,p,w. For each of
the237 remaining triples, exact polynomial coefficient signs make both
ratio tests monotone after division by a positive power of Y. Certified
integer endpoints then exclude every allowed Y=sq^3. This is an
exhaustion of a proved necessary domain, not a sample of formal Pell
assignments or an assertion that any listed row is a complete zero.

The [gap-five successor](complete75_weakened86_gap_five.md) further
excludes p=2n-5 using the exact main-root congruence and40 necessary
triples. On the same R<0,mu>0 branch it gives n<p<=2n-7; gaps at
least7 and mu<0 remain unresolved. This note's proof and source are unchanged.

## 1. Retained necessary inequalities

Assume for contradiction that R<0, mu>0 and p=2n-3 at a positive
candidate zero. By the preceding theorem p is odd and p>=13, so
n=(p+3)/2>=8. Retain

    q=(B-1)J+1>=16, B=2^d, d>=4, J>=1,
    X=wq^3, Y=sq^3, w,s>=1,
    A=Y(X+1)+2, P=2XY^2+1,
    c=psi_A(p), k=2*psi_P(n), kY<c<k(Y+1).

Write b_p=psi_2(p) and

    U=(2q^2-3)b_p+3p-1.

The wrap congruence and ratio growth proved in the index-gap note give

    Y<=U,
    (X+1)^((p-3)/2)<8Y^2(Y+1).                     (1)

Also b_p>=p, so U+1<=2q^2*b_p and U<2q^2*b_p. Thus

    (X+1)^((p-3)/2)<64q^6*b_p^3.                   (2)

The global main-root argument in the
[positive-index note](complete75_weakened86_positive_index.md),
Section5, gives independently

    X<=2^p.                                        (3)

It is important to retain(3): it uses the actual computed main root,
not just the two ratio inequalities. No Boolean packing or dyadic
conclusion about q is assumed here.

## 2. Uniform finite bounds on q and p

Since X+1>q^3, inequality(2), divided by q^6 and followed by a positive
cube root, implies the exact necessary condition

    q^((p-7)/2)<4b_p.                               (4)

The ordinary recurrence b_(r+1)=4b_r-b_(r-1) implies the skipped
recurrence

    b_(p+2)=14b_p-b_(p-2)<14b_p                     (5)

for p>=3. When p increases by2, the left side of(4) is multiplied
by q>=16 while the right side is multiplied by less than14.
Consequently, once(4) fails at one odd index, it fails at every larger
odd index for the same q.

Exact integer recurrence evaluations give

    16^68>=4b_143,
    316^3>=4b_13, b_13=7865521.

The first inequality rules out p>=143 for every q>=16. The second,
together with(5), rules out q>=316 for every odd p>=13. Hence

    13<=p<=141, p odd, 16<=q<=315.                  (6)

The checker uses integer powers only. It also checks that p=141 and
q=315 pass the respective endpoint tests, although those tests alone
do not establish solutions. In particular, compiler bases B>=512 are
already excluded from gap three by q>=B and(6).

Since B<=q<=315, the remaining compiler relation q=(2^d-1)J+1
requires 4<=d<=8. Exhausting these d and positive J gives exactly36
possible q values. For each q and each odd p in(6), apply(4) and(2).
If e=(p-3)/2 and

    L=floor_root(64q^6*b_p^3-1,e),

then strict inequality(2) requires

    w<=floor((L-1)/q^3).

Intersect this with w<=floor(2^p/q^3) from(3). These operations give
exactly87 nonempty(q,p) pairs and237 triples(q,p,w), using only
q in{16,31,32,46,61,63,64}. The receipt records every pair bound and
every triple. The integer root routine certifies L^e<=N<(L+1)^e;
no floating logarithm, root or rounded division is used.

Before imposing(3), the other necessary bounds leave139 pairs and930
triples. Those larger counts are recorded to make the role of the
computed main-root inequality explicit.

## 3. Exact ratio polynomials and their monotonic signs

Fix one of the237 triples and set X=wq^3, n=(p+3)/2. Regard Y as a
positive real variable and define the integer polynomials

    c(Y)=psi_(2+(X+1)Y)(p),
    k(Y)=2*psi_(1+2XY^2)(n),
    F(Y)=Y*k(Y)-c(Y),
    G(Y)=(Y+1)*k(Y)-c(Y).                            (7)

The two strict ratios hold exactly when F(Y)<0<G(Y).
Both polynomials have degree p+2. Their coefficients are obtained by
the exact recurrence

    psi_(a+z)(0)=0, psi_(a+z)(1)=1,
    psi_(a+z)(r+1)=2(a+z)*psi_(a+z)(r)-psi_(a+z)(r-1),

using a=2 for c and a=1 for k, followed by the displayed substitutions.
The checker verifies, separately for F and G at every triple, that

    every coefficient below degree p is strictly negative;
    every coefficient of degree p or higher is nonnegative;
    the leading coefficient is strictly positive.                    (8)

These are474 exact finite coefficient-sign certificates, not an
unproved uniform assertion over arbitrary parameters.

Condition(8) proves that F(Y)/Y^p and G(Y)/Y^p are strictly increasing
on Y>0. Each negative low-degree term becomes a negative coefficient
times a negative power of Y, which strictly increases; every remaining
term is nondecreasing. The denominator Y^p is positive, so each original
polynomial changes sign at most once, from negative to positive.
This elementary argument requires neither a numerical root approximation
nor a general polynomial root-finding oracle.

## 4. Certified integer endpoints exclude every scale

The complete remaining scale range is

    Y=sq^3, 1<=s<=Smax=floor(U/q^3).

For each triple the source locates the last multiplier t in this range
for which F(tq^3)<0. It then verifies an endpoint certificate:

* If t=0, F(q^3)>=0. Monotonicity from(8) rules out the lower strict
  ratio at every positive multiplier.
* Otherwise F(tq^3)<0 and either t=Smax or F((t+1)q^3)>=0.
  It also verifies G(tq^3)<=0. Every larger allowed multiplier fails
  the lower ratio, while every multiplier at most t fails the upper ratio.

Thus neither case permits F<0<G. All237 triples receive one of these
certificates. The complete list of integer t values is in the receipt.
Direct Pell recurrence evaluation supplies the endpoint values, and an
independent Horner evaluation of the certified coefficient arrays agrees
at every recorded endpoint. Bisection is used only to locate t; the
verified endpoint inequalities and(8) establish exhaustiveness.

This rules out p=2n-3 under the actual positive-domain assumptions.
The earlier theorem made 2n-p a positive odd integer at least3.
It must therefore be at least5, giving n<p<=2n-5.

## 5. An excluded ratio-only regression and the remaining gap

The separate exact tuple

    q=16, p=13, n=8, w=64, s=131074

does satisfy both strict ratios in(7), with X=2^18 and
Y=536879104. It is nevertheless excluded by(3), since2^18>2^13.
The source checks this as a regression against dropping the main-root
condition. It is not a candidate zero: neither the complete native
equations nor the full ordinary-input system is asserted for this tuple.

The finite exclusion above concerns only gap three with R<0 and mu>0.
The full strong norm, first/main norms, both ratios, the original fixed
compiler relation, and the computed main-root bound remain in force.
Larger odd gaps and the negative input-root branch are unresolved. No
operation reduction, universal86 theorem, false-input zero or general
lower bound is claimed.

```sh
python3 complete75_weakened86_gap_three.py
```

Author receipt generation and a fresh default replay pass. All five local
links resolve. The root reviewer completed the full proof/source review
and a fresh default replay without findings. Independently generated
closed Chebyshev binomial formulas reproduced all474 coefficient arrays
and their sign patterns, without the checker's recurrence helper. The
same independent closed formula evaluated all237 endpoint certificates;
all passed. That review also checked the complete finite-domain reduction
and the inherited main-root justification for X<=2^p.
A second reviewer completed the full proof/source review and a fresh
default replay without findings. Its separate verifier rebuilt all237
triples using direct integer inequalities without the root routine,
all474 coefficient arrays using the explicit Chebyshev/binomial formula,
and all237 boundary certificates using its own Pell recurrence. These
independent checks also passed and retain the theorem's stated scope.
