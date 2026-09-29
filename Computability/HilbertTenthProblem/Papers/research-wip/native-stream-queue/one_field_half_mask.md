# A 51-operation bounded one-field mask module

This is an arithmetic module, **not a universal certificate**. It replaces
the two-field inverse packing by one field and chooses a square word power
so that the retained 43-operation Pell kernel can test a mask occupying
exactly half of each cell. The full source costs **51 = 30M + 21A**. A
universal computation compiler for this single field has not been supplied.
In particular this note does not remove the input-typing mask from the
76-operation compiler: that compiler uses it before proving its carry bounds.

## 1. Exact predicate and source

Fix an even integer d >= 6, B = 2^d, and an odd integer m with

    0 < m < B-1, popcount(m) = d/2.

These are fixed numerals. For positive input parameters n,F, the module has
positive existential witnesses exactly when, for some integer N >= 1,

    n^2 = B^N, 0 < F < n^2,
    F AND [m*(B^N-1)/(B-1)] = 0.                         (1)

AND and powers occur only in the mathematical specification, not as paid
primitives. Supply positive J and the seventeen coordinates of the unchanged
fixed-minus kernel (including its index r). Compute q=n*n and D0=q*n, and
impose

    (B-1)*J = q-1,
    r = (q-F)*(q-1) + m*J.                              (2)

Attach all ten kernel equations from
[the complete76 proof](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md), Section 2,
with X=w*D0 and Y=s*D0. The coefficient remains (i*c^2)^2; the weakened
single-product candidate is not used.

There are twelve equations and eighteen positive existential coordinates
in addition to the two positive parameters n,F. Thus a containing certificate
that supplies n,F existentially has twenty positive coordinates in this
module. Derived arithmetic registers, including q, are not extra supplied
coordinates.

## 2. Bounds before interpreting powers or digits

The positive repunit equation gives q >= B >= 64. Put M=m*J. The fixed
inequality 0<m<B-1 gives 0<M<q-1, without any power assumption. If F>=q,
then F=q gives r=M>0, so **positivity alone does not exclude this boundary**.
We retain it through the kernel argument and exclude it only afterwards.
For F>=q+1, positivity does exclude the tuple, because

    r <= -(q-1)+M < 0.

The actual preliminary bounds are sufficient:

    F<=q, 7<=m<=M<=r<q^2, D0^2=q^3, D0>=512.

Here m>=2^(d/2)-1>=7 follows from its population, and the upper bound on r
uses F>=1 and M<q-1. In particular we do not assume r>=q or D0<r^2 at
this stage.

For arbitrary positive kernel witnesses,

    X,Y >= D0, XY >= q^3 > r+1,
    a=Y*(X+1)>q^3>2r+1,
    4r/a < 4/q <= 1/16 < 1/2.

To check the smaller possible index explicitly, the first norm has
P=2XY^2+1>A=a+2. Its index congruence gives its Pell index t>=r+1, since
XY>r+1. The ratio c>Yk>k then gives main index p>=t+1>=r+2>=9. Thus
c>= (2A-1)^8>A*(A^2-1)^2, and c>Yk>2r+1. These are the relaxed rank
lemma's required growth hypotheses. That lemma and the unchanged signed
half-parameter argument recover p=2r+1. The first-index comparison then
recovers t=r+1.

The remaining ratio and exponent argument is
[the direct scale argument](../../1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md),
Section 5, with this D0. Its elementary estimates give

    Y>=X^r, a>X^(r+1),
    2^(3(2r+1))=8*64^r < X^(r+1), X^3<=X^r,

using X>=512 and r>=7. Thus the exponent criterion is applicable before
power decoding. After decoding, X=2^(2r+1)>32r makes the ratio error less
than 1/2; the binomial tail is less than 1/4. Consequently it recovers

    X=2^(2r+1), D0 divides binom(2r,r).

Since n^3 divides X, n is a power of two. The repunit equation says
2^d-1 divides q-1. The order of 2 modulo 2^d-1 is exactly d, so q=B^N
for some N>=1. This recovers the required geometry from actual equations.

## 3. Boundary exclusion, exact mask recovery and positive converse

Now q=2^(dN), D0=2^(3dN/2), and popcount(M)=dN/2. If F=q, then r=M,
whose population dN/2 is strictly smaller than the valuation 3dN/2 forced
by the kernel. This excludes the boundary without a new instruction.
Only now infer F<q and r>=q. For 0<F<q and
0<M<q-1 the inverse-packing identity, including its overflow case, gives

    popcount((q-F)*(q-1)+M) <= dN+popcount(M)=3dN/2,

with equality exactly when F AND M=0. This is the same integer identity
proved in Section 6 of the direct scale dependency, with its large radix
replaced by q and its packed operand replaced by F. The central-binomial
valuation equals popcount(r). Thus the kernel forces equality and (1).

Conversely suppose (1). Choose J=(q-1)/(B-1) and r from (2).
Every chosen coordinate is positive, q<=r<q^2, D0<r^2, and
popcount(r)=3dN/2. Because m and J are odd, M is odd. The mask condition
forces F even, so r=(q-F)*(q-1)+M is odd. The retained positive fixed-minus
converse therefore supplies all remaining kernel coordinates at this exact
r and scale D0. In particular D0<r^2<2^(2r+1) ensures the power quotient
w is positive and integral; the binomial-floor construction and its valuation
give the positive quotient s. The auxiliary rank coefficient is unchanged.
This is a parametric existence proof, not a materialization of those large
Pell coordinates.

## 4. Paid schedules and compiler boundary

The eight outer operations, in order, are

    q=n*n; qm1=q-1; repunit=(B-1)*J; D0=q*n;
    M=m*J; gap=q-F; rproduct=gap*qm1; rcalc=rproduct+M.

They cost 5M+3A. With the unchanged 25M+18A kernel the complete module
costs **51=30M+21A**. Fixed B-1 is a free numeral; n^3 is
explicitly computed in two products shared with q.

This leaves a concrete compiler question: can a complete universal verifier
encode its data and local validity in one masked field, with every other
obligation paid within 24 operations? The current two-field compiler cannot
be substituted: its bound on each inner-radix coefficient assumes that its
separate data field is already typed. A proof that the single field recovers
both data typing and computation is still missing.

There is also a temporal alignment change. Here d is even but the retained
power has odd exponent 2r+1. It cannot directly be a whole-cell shift.
Computing 2X costs one multiplication and removes that parity obstruction,
but does not prove alignment or the required completeness congruence. Those
remain compiler obligations. The 51 count is not a universal bound.

## 5. Evidence

The adjacent checker expands twelve independent source polynomials against
the full schedule and retains the exact auxiliary-norm
residual correction. It exhausts small masks and fields, includes overflow
cases, and tests the pre-power bounds on square q that need not be powers
of two. It records the F=q boundary and its strict valuation deficit
explicitly. These finite checks corroborate the general proof; they do not
construct the missing universal compiler or materialize astronomical Pell
witnesses.

Author checks and an independent full scoped proof/source/receipt review
pass, including the pre-power endpoint argument and all twelve source maps.
Fresh default replay matches the receipt. No Lean formalization is claimed.
