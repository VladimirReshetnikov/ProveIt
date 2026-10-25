# Linear binomial radius and a signed radix in one residue class

## Fixed equations and exact scope

The four literal equations in this component have independently unrestricted
integer variables and are sums of squares of the quadratic residuals in their
`equation.json`. In ordinary ZFC, each has an integer zero if and only if there
is a finite syntactic ZFC refutation. Equivalently its integer nonsolvability
is equivalent to Con(ZFC). This statement composes the arithmetic proof below
with the inherited numerical C222 and ZF/ZFC calibration; it neither proves
consistency nor supplies a newly compiled end-to-end formalization.

The immediate sources are the 241/242-variable factorial-free equations from
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25`. Their pinned literal copies are
`sources/factorial_free241.json` and `sources/factorial_free242.json`.
The important unbounded predecessor is that package's **report/main.tex**:
its sharpened binomial selector hypothesis is R >= lcm(1,...,t)^2. The older
review/FACTORIAL_FREE_BINOMIAL_CRT.md proves a weaker factorial-square
threshold and must not be substituted for the sharpened theorem here.
The signed-radix treatment of low binomial tails is credited to the incoming
Shared Factorial Error report. Its Bv=M unit-radix argument is NOT imported:
our different residue-class argument is proved below.

Two semantic changes are made, followed by exact affine elimination:

* Replace q=(2z+1)^2 by q=4z+1. This excludes q=0 and q=-1, but does not
  assume positivity. The remaining unit q=1 is excluded arithmetically.
* Replace the binomial radius R=F^2 by R=F, retaining F=[2(t+1)]^t.
  A classical least-common-multiple bound proves this sufficient.

The mod4-only controls retain R=F^2. The linear endpoints make both changes.
Neither semantic change is asserted to give a bijection of all witness
tuples with the predecessor. The exact restriction/restoration bijections
certified by RESTORATION.json apply **after** the semantic source edits.

## 1. The classical lcm bound, with an elementary proof

Write Lambda_n=lcm(1,...,n), with Lambda_1=1. We prove Lambda_n <= 4^n.
For n>=2 put k=ceil(n/2). Then

    Lambda_n divides Lambda_k * binom(n,k).                         (1)

For each prime p, let p^a be its maximal power <=n. If p^a<=k, Lambda_k
already contains it. Otherwise p^(a-1)<=k, so only one additional p is
needed. Legendre's formula for v_p binom(n,k) is a sum of nonnegative
floor differences. Its level p^a is one, because k and n-k are both below
p^a, while n<2p^a. This proves (1).

If n=2m, binom(n,k)<=2^(2m)=4^m. If n=2m+1, the two equal middle
coefficients have sum at most 2^(2m+1), so binom(n,k)<=4^m. Complete
induction using (1) proves Lambda_n<=4^n in both cases. The n=1 case is
immediate. This is a classical bound, not a claimed new number-theoretic
result; see Chan and Norrish, *Proof Pearl: Bounding Least Common Multiples
with Triangles*, J. Automated Reasoning 62 (2019), 171–192, Theorem 3,
DOI 10.1007/s10817-017-9438-0.

Our unchanged cofinal horizon satisfies t=16+h^2. Therefore

    F=[2(t+1)]^t >= 34^t > 16^t >= Lambda_t^2.                     (2)

Consequently the incoming binomial prime-power selector theorem applies
with the new radius R=F, not just R=F^2.

For clarity, its arithmetic content is: if R>=Lambda_t^2 and
B=binom(R+t,t), every row i in [1,t] has a prime power p^e exactly dividing
B with p^e>t and p^e | R+i; and every prime power exactly dividing B divides
R+i for at least one row. The first statement recovers every local row;
the second handles all primes, including non-isolating primes, in reverse
CRT construction. These are precisely the two required directions.

## 2. Unchanged signed power interface

The retained squared frame, squared semantic anchor, common principal Pell
center and pooled orientation conditions canonically orient **both**
coordinates of every retained principal Pell pair at its signed requested
index. All eighteen power slots are retained. No representative subset,
orientation condition, or frame atom is dropped. The new edits affect only
the two displayed front identities. The actual bases, exponents and output
atoms retain their squared bounds by W; |A|>W^W and W>=258 remain available.

The inherited signed-power lemma says: at a nonzero integer base n, if
|n|>=2 then the requested index k is nonnegative and its output is exactly
n^k. At n=1 or n=-1 the output is respectively 1 or (-1)^k even for signed
k. Its proof uses T=2An-n^2-1, the canonical Pell congruence, and the strict
frame bound to turn a congruence into equality. If k<0 and |n|>=2, that
equality would be m n^(-k)=1, impossible over the integers. We never apply
this lemma to n=0.

In particular, independently of any radix sign, the already positive
index t and base 2(t+1) give the genuine positive F=[2(t+1)]^t>2^32.
The unchanged beta certificate

    v_beta=(2w+1)^2,          y=F v_beta

then gives y>=F>0. This is all that is needed initially; the possible y=F
boundary is addressed only after local-row recovery, not assumed away.

## 3. Acyclic signed-radix bootstrap

Throughout this section take R=F for the linear endpoints, or R=F^2 for
the controls. In either case R>0. The affine radix constraint makes q=4z+1,
so q is neither zero nor -1.

First exclude q=1. Then q+1=2, so all nine actual CRT representatives are
nonnegative by the signed-power lemma. Their sum defines H=2+sum(a_nu),
hence H>=2. In particular the actual index representative C0>=0. The
retained index row

    B mu = C0+R+1

has positive right side, so B!=0. Thus |BH|>=2. The self-radix request
at base BH gives x>=0 and 1=(BH)^x, forcing x=0. But the last beta endpoint

    x=1+[1+(t+1)y]u_t

cannot hold at x=0, since its bracket exceeds one and cannot divide -1.
This excludes q=1 without using any binomial interpretation or norm bound.

For every remaining q=4z+1, Q=|q|>=3 and |q+1|>=2. Therefore the same
nonnegative-representative argument gives H>=2 and B!=0. The derived
label, also a requested exponent at base q+1, is nonnegative; the retained
anchor excludes zero. The request at nonzero base BH gives x>=0 and
q=(BH)^x. Since x=0 would give q=1, x>=1. If the first beta quotient u0
were at most -1, its identity

    x=F+1+(y+1)u0

would imply x<=F-y<=0. Hence u0>=0 and x>=F+1. The last endpoint then
has u_t>=1 and gives

    x>=2+(t+1)y >=2+(t+1)F.

In particular x>=2, and the genuine self-radix equality yields

    Q=|BH|^x >=2^x,        Q>=4B^2,        |B|<=Q/4.              (3)

We have still made no positivity assumption about q or B.

Every power at q and q+1 now has its genuine meaning at its nonnegative
index. In particular M=q^x!=0 and each low denominator L_i is a nonzero
power of q. The four denominator exponents t,t+1,y+1,x are at most x.
For each normalization ratio L_i v_i=M, the ratio v_i is nonzero. From
v_i U_i=M Q_i+R_i one gets v_i | R_i, so r_i=R_i/v_i is an integer and

    U_i=L_i Q_i+r_i.

The unchanged common norm M^2-1-4 sum(R_i^2)=G(a,b,c), where
G=a^2+b^2+c(c+1)>=0 on integers, gives |r_i|<|L_i|/2. Signs of L_i,v_i,
and M are not used. Two congruent lifts with this bound and a prescribed
canonical lift of size <|L_i|/32 must coincide, since their difference
has absolute value <(1/2+1/32)|L_i|<|L_i|.

## 4. Recovering the binomial at a signed radix

Put n=R+t and C_j=binom(n,j). The retained numerator power is exactly
U=(q+1)^n. The standard bound

    C_j <= (R+1)^t <= (F^2+1)^t =: V       (0<=j<=t)

holds because R>=1 and R<=F^2. V is proof notation only: no new power
slot is introduced. For F>=7, F^2+1<=2^(F-1), and (3) gives

    V/Q <= 2^(-F-t-2),         V/(Q-1)<1/32.

For either sign of q the signed low polynomial

    r0=sum_(j=0)^(t-1) C_j q^j

satisfies |r0|<Q^t/32. It is congruent to U modulo q^t, so the preceding
short-lift argument identifies the restored digit remainder with r0.
Dividing the digit equation by q^t and reducing modulo q gives

    B = C_t modulo q.

Here 0<C_t<=V<Q/32 and |B|<=Q/4. Thus |B-C_t|<Q and their congruence is
an equality:

    B=binom(R+t,t)>0.

Now q=(BH)^x is positive because B,H>0. The negative-radix branch is
therefore excluded by the arithmetic, rather than a missing guard. The
power N=B^x can now be interpreted at its positive nonunit base. For our
R>=1,t>=16, B>=R+t>=2. Also B>R+1, so the raw index row excludes C0=0.

All remaining digit tails have the inherited bound <L_i/32, now with
positive q. The fixed upper indices and local majorant estimates are no
larger than in the factorial-free predecessor; only the positive binomial
radius has fallen from F^2 to F. In particular x>=2+(t+1)F still supplies
the strict local-polynomial and derived-label budgets. Every normalized
range test and local polynomial congruence therefore has its intended
meaning. Applying (2) and the inherited prime-power selector theorem
recovers every C222 row, with no unused-prime gap in its reverse CRT lemma.

## 5. Boundary y=F and exact label multiplicities

This essential inherited step remains necessary. The recovered local
beta rows give S_0,...,S_t and updates

    S_(i+1)(1+c_i F)=S_i(1+p_i F)(1+q_i F),

where all weights are positive. If y=F, the first endpoint makes S_0=0,
while the last endpoint makes S_t=1. Every update propagates zero forward,
a contradiction. Hence y>F at a complete zero. The genuine initial
remainder is F+1, the final one is 1, and every accumulator is positive.
Their product identity has exactly the same meaning as in the incoming
factorial-free proof.

For completeness of the soundness explanation, equality of the two
products first forces equal nonunit factor counts d<=t: otherwise the
larger count contributes at least (F+1)^(d+1), whereas the smaller is at
most t^d(F+1)^d, contradicting F+1>t^t. The two products are now evaluations
at F of products of at most t factors 1+jX, 1<=j<=t. Every coefficient is
less than (t+1)^t<F. A nonzero difference polynomial cannot vanish at F,
by reduction modulo F at its least nonzero degree. Thus the polynomials
are identical. Their distinct roots -1/j recover exact label
multiplicities, and the unchanged Horn-closure argument yields a finite
C222 refutation and hence a finite ZFC refutation. This proves soundness.

## 6. Constructive completeness with the smaller radius

Begin with a finite C222 refutation. Choose a sufficiently large padded
cofinal horizon t=16+h^2 and put F=[2(t+1)]^t, R=F for the linear endpoints.
By (2) the two-sided binomial prime-power CRT theorem applies. Let O be
the odd part of t!. Choose an arbitrarily large odd multiple a_beta of O,
put v_beta=a_beta^2 and y=F v_beta. Since v_2(F)>=t>v_2(t!), this y is an
even multiple of t!, and it can exceed F and every actual accumulator.
The beta CRT therefore works as before. Its moduli are odd, so choose a
sufficiently large even positive beta code x in the same CRT class.

The new binomial B=binom(F+t,t) is odd: for 1<=i<=t,
v_2(i)<t<=v_2(F), whence v_2(F+i)=v_2(i), so the product quotient has
zero 2-adic valuation. The control R=F^2 has the same property. Thus
N=B^x and N^2 are odd. The incoming all-primes CRT construction supplies
actual representatives, whose parities can be chosen by adding N^2.
Choose the dominant a odd and every other representative even, so its
required parity opposite b and the even nonzero semantic anchor are
preserved and H=2+sum(a_nu) is odd. The old dominance intervals are
unchanged. The changed front index R+t is below B^2<N^2, since B>=R+t.
All other canonical frame and principal-index bounds are therefore valid.

Now q=(BH)^x is an odd square, because BH is odd and x is even. In
particular q=1 modulo 4, and z=(q-1)/4 is an integer supplying the new
radix row. The usual normalized tails R_i=(M/L_i)r_i^0 satisfy
0<=R_i<M/32; their strict common norm gap has the standard ternary
representation G. The unchanged Pell completion and coordinate equations
supply all remaining witnesses. Hence a finite refutation gives a zero
of every new equation. No factorial authenticity is reintroduced: t!
is used only for the existence of a suitable beta parameter.

Combining Sections 2–5 and this construction proves both directions.
The mod4-only controls use the same proof with R=F^2 and the old radius
threshold; the lcm argument is required only for the new linear endpoints.

## 7. Literal edits and restoration boundary

In both pinned sources F=x3 and R=x4, and row0 is R-F^2. The prior
factoring and projection certificates retain these two coordinates; no
coordinate shear, affine projection, or row-basis operation changes or
uses row0. Their coordinate translations are zero. Replacing row0 by
R-F therefore implements exactly the semantic radius change just proved.
The independent source-interface audit verifies these bindings.

The stored pow2 coordinate has actual value q=stored_q-1. Its old guard
is stored_q-2-4z-4z^2. The semantic mod-four replacement is
stored_q-2-4z. Thus the affine restoration is stored_q=4z+2, **not**
4z+1. In the linear endpoints also restore R=F. Deleting these two
monic affine rows and substituting these expressions in every retained
row is an integer zero-set bijection between the edited source and final
endpoint, with inverse restriction. The sum-of-squares step is valid
because a sum of integer squares is zero exactly when every summand is.

`check.py` independently verifies every pulled-back residual and restored
coordinate, exact quartic collection, variable liveness, degree and all
metrics, under normal Python and Python -O. At least six deliberate corruptions
are required to fail per endpoint. The local old-root map z_new=z_old(z_old+1)
proves that the old square guard implies the new mod-four guard when
R is unchanged; it is not a reverse root extractor or a pointwise map for
the independent R=F semantic change. None of the finite checks substitutes
for the unbounded arithmetic proof above.
