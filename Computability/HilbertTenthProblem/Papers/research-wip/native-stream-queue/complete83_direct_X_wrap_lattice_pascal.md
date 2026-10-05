# Direct-X83 wraps: a factor-seven bound and one authentic index/sign candidate

Every wrapped full positive zero of the existing direct-X83 proposal on
an authentic compiler slice satisfies

    7*v*X*s < q.                                      (1)

This strengthens the previous vXs<q bound for all sizes, without extending
the earlier finite census. Moreover, for fixed (q,X,s,v) there is at most
one pair (R,epsilon) compatible with both the exact Pell-ratio interval
and the literal outer index congruence. The two possible unit signs are
not two independent surviving candidates.

These are necessary conditions, not exclusion of every wrap or a new
universal83 theorem. The source remains unchanged. The no-wrap obligation
q|X is separate. Root owns that investigation; this note does not infer
dyadic q from parity or canonical half-binomial divisibility.

## 1. Exact inherited hypotheses

Use the notation and positive-zero conclusions of
`complete83_direct_X_wrap_isolation_pascal.md`:

    q>=16 even, Y=s*q^3, E=XY,
    A=Y(X+1)+2, P=2XY^2+1,
    c=psi_A(R), k=2psi_P(n), Y<c/k<Y+1,
    R<2n<2R, 2n=R+epsilon+vXY,
    epsilon in {−1,1}, R=3 modulo4,
    (2q−1)(q^2−1)<R<q^3(q−1).

For a wrap v>=1, the previous theorem gives Xs<q and vXs<q.
Its Jacobi argument excludes every square X, so in particular X>=2.
Define

    L=log(2A^2/P), M=log(2P),
    E0=q^4*(A^(-2)+P^(-2)).                         (2)

All logarithms are natural. The already proved exact Pell error bound is

    |log psi_C(j)−(j−1)log(2C)|<j/C^2,

and hence the ratio error is strictly less than E0. We use it only where
R,n<q^4. Also

    L>log4, E0<1,
    L<log(4X), M>log(4X)+6log q.                    (3)

For the upper bound on L, P>2XY^2 and X>=2 imply

    2A^2/P < (X+1+2/Y)^2/X < 4X,

since Y>=q^3>2. The lower bound on M is immediate from Y>=q^3.

## 2. Bootstrap the wrap bound twice

The strict lower ratio c/(k/2)>2Y and its error bound yield

    vXY < R*(L/M)+(2−epsilon)
                     −2log(4AY)/M+2E0/M
          < R*(L/M)+3.                             (4)

The last inequality is valid for both signs, because 2−epsilon<=3 and
log(4AY)>1>E0. It does not assume that the positive integer R lies in the
unwrapped branch.

Initially X<q and q>=16 give

    log(4X)<log(4q)<=1.5log q,
    L/M < 1/5.

Divide (4) by q^3 and use R<q^3(q−1):

    vXs < (q−1)/5+3/q^3 < q/5.                     (5)

Thus X<q/5. In particular 4X<q, so the same inequalities (3) now give

    L/M < log(4X)/(log(4X)+6log q) < 1/7.

Substitution back into (4) proves

    vXs < (q−1)/7+3/q^3 < q/7,

since 3/q^3<1/7 for q>=16. This proves (1). It excludes the entire
Xs>=q/7 sector and reduces each surviving wrap multiplicity to
v<q/(7Xs). No congruence or logarithm is numerically approximated in this
all-size argument.

## 3. The actual outer rows remove the remaining two-sign ambiguity

For a fixed authentic q, the supplied repunit coordinate is fixed as
J=(q−1)/(B−1), and the exact outer source is

    R=(q*(q−F)−Z)*(q^2−1)+(MC+q*MF_source)*J.

Consequently R belongs to the one arithmetic progression

    R=r0 modulo N, N=q^2−1,
    r0=((MC+q*MF_source)*J) mod N.                  (6)

This uses the source's shifted field-mask numeral. It is not obtained
from decoded binary masks or from an assumption q=B^T.

For a fixed surviving (q,X,s,v), write the previous two ratio intervals as

    I_epsilon=(a_epsilon,b_epsilon),
    a_epsilon=[2log(4AY)+(epsilon+vXY−2)M−2E0]/L,
    b_epsilon=[2log(4A(Y+1))+(epsilon+vXY−2)M+2E0]/L.

They have a common width w<1. The plus interval is the minus interval
translated by 2M/L>14, by Section2; hence they are disjoint. Their convex
hull has width

    2M/L+w < 2M/log4+1=log_2(2P)+1
            < 9log_2 q+1 < q^2−1.                  (7)

For the penultimate inequality, the inherited wrapped bound gives
Y<q^4/X and therefore 2P<4q^8/X+2<q^9 for q>=16.
For the last, log_2 q<q and 9q+1<q^2−1 already suffice.

An open interval shorter than N contains at most one point of the
progression (6). Therefore **at most one pair (R,epsilon)** can satisfy
the ratio and authentic outer congruence. This is stronger than the
previous one-integer-per-sign assertion.

An explicit external necessary test is to form

    R*=r0+N*(floor((a_minus−r0)/N)+1).

If R* lies outside the convex hull, or inside its gap rather than one
of the two intervals, the tuple is impossible. Otherwise the containing
interval uniquely determines epsilon. All other conditions, including
the outer bounds, R=3 modulo4, the main projection, shared input index
and transport, still have to hold. This real-interval criterion is a
proof tool, not a new paid gate or an implementation inside the83 source.

## 4. Why the first-index congruence alone does not close the gap

**Review remark 1 (retained rejected congruence-only shortcut).** It is
not valid to infer that the exact first Pell norm and its signed index
unit rule out a nonzero wrap. They have a positive completion for every
wrap and either sign, before coupling to the main ratio.

Precisely, let X,Y be positive integers with Y even, let R>=3 be odd,
let v>=1 and epsilon in {−1,1}, and put

    P=1+2XY^2, n=(R+epsilon+vXY)/2,
    k=2psi_P(n), tau=chi_P(n),
    h=(k−R−epsilon)/(XY).                           (8)

Then n is an integer at least2. The integer polynomial psi_T(n)
satisfies psi_1(n)=n, so P−1 divides psi_P(n)−n. Therefore

    k−2n is divisible by 4XY^2,
    h=v+(k−2n)/(XY) is a positive integer,
    h=v modulo4Y.                                  (9)

Positivity follows from psi_P(n)>n for P>1,n>=2. The two exact equations

    tau^2−XY^2*(XY^2+1)*k^2=1,
    k−hXY−R=epsilon                               (10)

hold. Choosing any eta from1 to k−1 and zeta=k−eta gives positive supplied
first coordinates; setting c=kY+eta supplies both positive ratio slacks
as abstract coordinates. What is *not* supplied is the same c satisfying
the main norm with recovered index R, or the main/input projection and
authentic outer rows. Those couplings are precisely the remaining issue.
Every congruence of the exact first Pell equation, including higher powers
of Y or XY, already holds in (8). Such congruences alone cannot invalidate
this positive partial completion.

This boundary is compatible with the weak scale/index size window as
well. For each even q>=16, set X=2, Y=q^3, R=3q^3+3 and v=1. Then
R=3 modulo4, the strict outer *numerical* R bounds hold, R<2n<2R and
7vXs=14<q, for either sign. Equations (8)–(10) apply symbolically.
These scalar choices do not claim the authentic outer congruence (6),
the main ratio at c=psi_A(R), or a full compiler zero. No enormous Pell
integer needs to be materialized to prove this exact partial statement.

## 5. Scope and dependencies

The input-index classification in `direct_X_authentic_outer_root.md`
still gives u or A*u<=R. The even alternative also implies
u*s*(X+1)<q, directly from its displayed inequality and the outer upper
bound; it is not claimed as an independent new theorem here. None of
Sections2–4 supplies a full wrapped tuple, excludes all such tuples,
or resolves even nondyadic scales on the no-wrap branch.

The complete boundary, wrap-isolation and authentic-outer notes were read
as inert proof text. The new theorems use handwritten algebra only, and
the earlier q<=64 census was not enlarged. A discarded fresh scalar
diagnostic tested whether X*(XY^2+1)*(A^2−1) is square for
1<=X<=1000 and1<=Y<=300; its sole hit was (X,Y)=(2,1). This check
does not contribute any theorem, field-disjointness claim or full-zero
evidence in this note. No predecessor helper, saved source array,
builder or archived program was executed or imported. No repository or
Git state was changed. Dependency hashes and the exact note binding are
recorded in the companion JSON.
