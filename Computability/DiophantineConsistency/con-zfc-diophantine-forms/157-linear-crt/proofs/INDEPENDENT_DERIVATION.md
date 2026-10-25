# Independent arithmetic proof: parity bootstrap and a linear CRT radius

This note concerns the factorial-free binomial CRT source in the incoming
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip` at ProveIt commit
`7a8da414376a80b90ecf799f37ceb26fb9ac674e`. It supplies ordinary mathematical
proofs for three source changes. It does not claim a new source-to-ZFC
calibration or a new proof-assistant build. Numerical endpoint counts must
come from the complete emitted residual system.

## 1. Changes and retained interfaces

The horizon is `t=16+h^2`. Retain the exact-power request

    d=2(t+1),       F=d^t,

and the beta spacing `y=F(2v+1)^2`. Let C be the actual encoded-index CRT
representative and let A_1,...,A_8 be the other eight actual representatives.
In the source several actual representatives are stored as a coordinate
plus one; parity must be imposed on the actual value, not its stored offset.

Make these changes:

1. Replace the CRT radius R=F^2 by R=F everywhere, including the exact
   binomial digit's upper index and the raw encoded-index relation.
2. Parameterize C=2c with unrestricted c. Replace the old majorant by

       H=2+4(C+A_1+...+A_8).

3. Delete the row q=(2z+1)^2 and its private root coordinate z.

The surviving intended arithmetic equalities include

    x=F+1+(y+1)u_0,
    x=1+[1+(t+1)y]u_t,
    B h_B=C+F+1,
    N=B^x,       q=(BH)^x,       M=q^x.

The exact digit is intended to certify B=binom(F+t,t). Every variable
exponent in this note is the meaning of an unchanged polynomial Pell
certificate, not an extra operation in the delivered polynomial.

We use the inherited signed exact-power interface: after the signed Pell
frame, semantic anchor, and bounded index recovery, a request (n,k,m)
with |n|>=2 forces k>=0 and m=n^k. A request at n=1 or n=-1 has the
corresponding unit-base meaning for signed k. Its proof applies before
arithmetic signs because the common frame bounds absolute atom values.
No power meaning is assumed for base zero.

## 2. An elementary bound for the least common multiple

Write L_n=lcm(1,...,n), n>=1. Then

    L_n <= 4^(n-1).

Here is a direct proof, so that this bound need not be cited as an
unverified estimate. For n>=1,

    L_(2n) divides L_n * binom(2n,n),
    L_(2n+1) divides L_(n+1) * binom(2n+1,n).

For the even relation, a prime power p^a contributing to L_(2n) but not
L_n satisfies n<p^a<=2n. There is at most one additional p-adic level,
since p>=2. Its contribution to the Legendre valuation formula for
binom(2n,n) is 1: floor(2n/p^a)-2floor(n/p^a)=1. All other contributions
are nonnegative. For the odd relation, a newly appearing p^a satisfies
n+1<p^a<=2n+1; the contribution to binom(2n+1,n) is again 1. This proves
both divisibilities prime by prime.

Now binom(2n,n)<=4^n. Also binom(2n+1,n)<=4^n, since its two equal middle
terms together are at most the whole binomial sum 2^(2n+1)=2*4^n.
Strong induction from L_1=1 therefore proves

    L_(2n) <= 4^(n-1)*4^n=4^(2n-1),
    L_(2n+1) <= 4^n*4^n=4^(2n).

For t>=16, d=2(t+1)>=34, and consequently

    F=d^t >=34^t >16^(t-1) >= L_t^2.

Thus R=F satisfies the precise radius hypothesis of the inherited
binomial CRT compiler. Squaring F was unnecessary in this source.

## 3. The binomial CRT theorem is unchanged

The inherited compiler assumes R>=L_t^2 and sets B=binom(R+t,t).
For every row i in {1,...,t}, some full prime power p^e exactly dividing
B divides R+i and exceeds t. Conversely every full prime power of B
divides at least one R+i. The proof and both completeness directions
depend only on R>=L_t^2, not on R being a square.

For clarity, the row-selector proof uses

    t*binom(t-1,i-1) divides L_t.

If v_p(R+i)>2v_p(L_t), all other R+j have the valuations of j-i. Hence
the exponent e of p in B is

    e=v_p(R+i)-v_p(t*binom(t-1,i-1))>v_p(L_t),

and p^e>t. Such a prime exists because R+i>L_t^2. Full support follows
from Legendre's formula: v_p(B) is a sum of 0/1 contributions with at
most max_i v_p(R+i) nonzero levels. These arguments apply literally to
R=F.

## 4. Noncircular soundness of the parity bootstrap

First the positive base d and positive exponent t authenticate F=d^t.
In particular F is a positive even integer, F>2^32, and y>=F>0.

The actual index C=2c is even. The raw polynomial row

    B h_B=C+F+1

has an odd right side. Thus B is odd and nonzero, without any assumption
on C's sign and without invoking a binomial interpretation.

The expression H=2+4(C+sum A_j) is congruent to 2 modulo 4 at every
integer assignment. Hence |H|>=2 before the representatives' signs are
known. Together with B!=0 this gives |BH|>=2. The self-radix power request
therefore forces

    x>=0,       q=(BH)^x.

The case x=0 is impossible: 1+[1+(t+1)y]u_t=0 would require an integer
greater than one to divide -1. Thus x>0. If u_0<=-1 then

    x=F+1+(y+1)u_0 <=F-y<=0,

a contradiction. Therefore x>=F+1. In particular x>1, so the second
endpoint has u_t>=1 and yields

    x>=2+(t+1)y>=2+(t+1)F.

Put Q=|q|. The authenticated self-radix equality gives

    Q=|BH|^x>=2^x>=4.

Thus both |q|>=2 and |q+1|>=2. Every actual CRT representative is an
exponent in a surviving request at base q+1, so all nine are nonnegative.
The derived-label exponent is likewise nonnegative. It follows that
H>=2 and that H dominates each representative. Also M=q^x and all
denominator powers at q have their genuine meanings. This proves every
sign and nonzero premise used in subsequent digit extraction without
assuming q positive.

## 5. Recovering the first binomial digit at a signed radix

Let C_j=binom(F+t,j), 0<=j<=t. As F>=t and F>=7,

    C_j <= (F+t)^t <=(2F)^t <=2^[t(F-1)].

Since x>=2+(t+1)F and Q>=2^x,

    C_max/Q <=2^(-F-t-2),
    C_max/(Q-1)<1/32.

The exact numerator request gives U=(q+1)^(F+t). Define its signed low
polynomial

    r_0=sum_(j=0)^(t-1) C_j*q^j.

Then |r_0|<Q^t/32. This estimate is valid for either sign of q.

The retained common normalized-remainder certificate is

    M^2=1+4*sum rho_i^2+alpha^2+beta^2+gamma(gamma+1).

The final three terms are nonnegative for all integer alpha,beta,gamma,
so |rho_i|<|M|/2. For the first digit, the retained ratio is Dv=M with
D=q^t, and the scaled digit row is

    Uv=M(B+q eta)+rho.

Because Dv=M and all values are integers, this row implies rho=v*r for
the integer r=U-D(B+q eta), and therefore |r|<|D|/2. Both r and r_0 are
congruent to U modulo D. Their difference has absolute value less than
(1/2+1/32)|D|<|D|, so r=r_0.

Subtracting r_0, dividing by q^t, and reducing modulo q gives

    B=C_t modulo q.

Since |H|>=2, |B|<=|BH|/2<Q/2. Also C_t<Q/32. Hence |B-C_t|<Q, and
the congruence forces B=C_t=binom(F+t,t)>0. With H>=2 and x>0, the
self-radix equality now gives q>0. The temporary signed-radix branch
has been resolved by exact arithmetic.

All later range estimates are preserved: the new H=2+4 sum(reps) is
at least the old 2+sum(reps) once the signs are proved. Thus each ordinary
binomial coefficient is bounded by H^x, the inherited derived-label
bound by H^ell is retained, and q=B^x H^x supplies the same strict digit
separation. The local polynomial budget is unchanged because F,y,x,t
and their endpoint inequalities have not been weakened. The new radius
R=F satisfies the inherited CRT theorem by Section 2.

The y=F boundary is handled exactly as in the parent: first endpoint
remainder zero would force initial accumulator zero; all positive-weight
local updates propagate zero; the final endpoint requires accumulator
one. Thus every decoded certificate has y>F. Label multiplicity recovery
uses F>(t+1)^t, which remains true. The same single-conclusion Horn-flow
argument yields a finite calibrated refutation.

## 6. Constructive completeness and the retained semantic anchor

Begin with a finite calibrated refutation. Choose t=16+h^2 beyond its
finite proof and label data. Define F=[2(t+1)]^t. For the odd part O of
t!, choose an arbitrarily large odd multiple w of O and put y=Fw^2.
The inequality v_2(F)=t[1+v_2(t+1)]>=t>v_2(t!) shows t! divides y.
Choose w sufficiently large that y>F and all pending accumulators are
at most y. The beta moduli 1+(i+1)y are odd and pairwise coprime. Their
CRT progression contains arbitrarily large even x, so the parent's
choice of even x can be retained.

Put R=F, B=binom(F+t,t), and N=B^x. The integer B is odd. Indeed,
v_2(F)>=t>floor(log_2 t), so for every 1<=i<=t,

    v_2(F+i)=v_2(i).

The numerator and denominator valuations in binom(F+t,t) cancel.
Thus N^2 is odd, and adding N^2 to any independent CRT representative
changes its parity while preserving all required congruences.

Choose C even. The parent already chooses its dominant schema
representative a odd and the other eight representatives even, so this
is compatible with its literal completeness assignment. Take a in
[2N^2,4N^2), and the other representatives positive and at most 2N^2.
The inherited shell identity gives

    h_*=1+a+b modulo 2,       h_*>=2a^2>=8N^4.

Hence h_* is even and dominates every other index as required by the
unchanged semantic-anchor construction. For the only changed front
index, F+t<=binom(F+t,t)=B<N^2. The other front indices x,y+1,t,t+1
also lie below N^2 by the endpoint bounds and B>=2. Polynomially derived
label congruences remain valid because the representative shifts preserve
the full CRT modulus.

Now define H=2+4(C+sum A_j) and q=(BH)^x. The radix is positive (and
even); the deleted odd-square row is the only condition that would have
required q odd. The unchanged exact-power and Pell-frame existence
theorems apply at even and odd bases alike. Even in the older modular
version, its linear congruence for A explicitly handles the gcd-2 case
when q is even and q+1 odd. No odd-radix hypothesis is required by the
retained eighteen exact-power requests.

Choose genuine digit remainders and ratios. Their normalized absolute
values are less than M/32. Hence

    4*sum_(i=1)^11 rho_i^2 <44*M^2/1024<M^2.

The integer gap M^2-1-4 sum rho_i^2 is nonnegative and has the same
three-variable representation alpha^2+beta^2+gamma(gamma+1) used in the
parent. Finally choose the common Pell frame after all semantic values,
then its private anchor and power witnesses. This completes the new
source's integer solution from any finite refutation.

## 7. Audit boundaries

The algebraic implementation must substitute the actual C=2c in every
row and in the complete power/frame metadata; update every occurrence
of the radius from F^2 to F; replace the whole H formula; remove only the
private odd-square radix row and coordinate; and re-run all projection
and collected-polynomial checks. An old finite checker that assumes the
former q row or radius must be updated and independently checked. The
source maps are existence-preserving maps; the even C restriction is
not a bijection between all parent and child assignments.

The proof removes a nonlinear radix requirement and an unnecessarily
quadratic radius. Whether this lowers a particular projected endpoint's
variable count is an emitted-system question: earlier projections may
already eliminate an affine coordinate, and altered coefficients may
change support and height. No endpoint metric is asserted by this note.

## 8. Strengthening: the beta multiplier can be affine

The square on the beta multiplier can also be removed. Replace

    y=F(2v+1)^2

by the quadratic row

    y=F(2v+1)

and eliminate the private square wire if it is still retained. This does
not assume y is positive: its sign is recovered from an already existing
power request. The exact soundness order is as follows.

1. Authenticate F=d^t>2^32. Thus F is positive and even. The affine odd
   multiplier is nonzero, so |y|>=F.
2. C even and B h_B=C+F+1 give B odd and nonzero. The new H is 2 modulo
   4, so |BH|>=2. Thus x>=0 and q=(BH)^x by the exact-power interface.
3. Even with signed y,

       |1+(t+1)y| >= (t+1)F-1>1.

   Consequently x=0 is excluded by the last endpoint. Hence x>=1 and
   Q=|q|=|BH|^x>=2.
4. The existing denominator request q^(y+1) is now at a base of absolute
   value at least two. Its signed-index theorem forces y+1>=0. If y
   were negative, |y|>=F>=2 would instead give y+1<=1-F<0. Therefore
   y>=F>0.
5. The first endpoint now excludes u_0<=-1 exactly as before, so
   x>=F+1. The last endpoint then gives x>=2+(t+1)y. In particular
   Q>=2^x is enormous and |q+1|>=2. Only at this point are the requests
   at q+1 used to recover all CRT representative signs.

The rest of Sections 4 and 5 is unchanged. In particular the denominator
request at q is used *before* numerator requests at q+1. Swapping that
order would leave the exceptional radix q=-2 untreated.

For completeness, choose a positive odd multiple w of the odd part O of
t!, large enough that y=Fw exceeds F and every finite pending accumulator.
Because v_2(F)>=t>v_2(t!), the integer y is again an even multiple of t!.
Set v=(w-1)/2. The same beta CRT construction, even x, odd B, even C,
dominant odd a, even semantic anchor, and final Pell witness construction
then apply. No square multiplier is needed to obtain any congruence or
cofinality condition.

This is a semantic change, not a coordinate identity at all assignments.
Its ordinary existence equivalence follows from the ordered soundness
argument and explicit completeness construction above. It uses the
unchanged q^(y+1) request already present in the eighteen-power interface.

## 9. A sharper growth choice: F=t^t

There is an optional further simplification. Use the cofinal horizon

    t=16+4h^2

and replace the growth request F=[2(t+1)]^t by

    F=t^t.

The new horizon is the old one with its root restricted to 2h; it remains
cofinal and is divisible by four. The growth base and growth index now
coincide. This is a simpler arithmetic description; any reduction in
emitted support or coefficient height must still be measured. The former
affine base register may already have disappeared under projection, so
this does not by itself imply a smaller number of final unknowns.

### Sharpened label-injectivity lemma

Let t>=2 and F=t^t. Let L and R be products of factors 1+jF with
j in {1,...,t}, where L has at most t factors and R at most 2t+1.
If L=R, their factor multisets are equal.

To prove this, suppose the counts differ and let r be the smaller count.
Then r<=t. The side with more factors is at least (F+1)^(r+1). The side
with fewer factors is at most

    (1+tF)^r <= t^r(F+1)^r.

Equality would imply F+1<=t^r<=t^t=F, a contradiction. Hence both
counts are the same integer m<=t.

Replace F by an indeterminate Z. Each side is a product of exactly m
linear factors with labels in {1,...,t}. For every degree 0<=k<=m,
its coefficient is a positive integer and at most

    binom(m,k)*t^k <= m^(m-k)*t^k <= t^m.

The middle inequality follows from binom(m,k)=binom(m,m-k)<=m^(m-k).
It is also valid at k=m. If m=0 the claim is immediate, so no expression
0^0 is needed. Since both coefficients are in [1,t^m], the difference
at every degree has absolute value at most t^m-1<F. All higher
coefficients vanish.

If the difference polynomial were nonzero, choose its lowest nonzero
coefficient a_r. Evaluating at F, dividing by F^r, and reducing modulo
F would show F divides a_r, contradicting 0<|a_r|<F. Therefore the
polynomials agree identically. The rational roots -1/j distinguish
their linear factors, giving equality of multiplicities.

For the Horn source, first discard truth-label zero factors (which are
one) and include the target factor 1+F on the right. This has exactly
the count bounds above. Thus the original multiplicity and closure
argument remains valid. The old sufficient hypothesis F>(t+1)^t is
replaced by this proved sharper hypothesis F=t^t; it is not silently
reused when false.

### Remaining estimates and parity

At t=16+4h^2,

    F=t^t >=16^t >16^(t-1) >=L_t^2,
    F>=16^16=2^64>2^32,
    v_2(F)=t*v_2(t)>=2t.

These prove every size and parity premise used above. In particular the
linear radius R=F remains valid; B=binom(F+t,t) remains odd; y=F(2v+1)
has the same cofinal t!-divisible completeness choices; C even still
forces B odd already in raw soundness; the digit coefficient and local
amplification estimates are unchanged or strengthened. The dominant
representative and even semantic-anchor construction is unchanged.

The eighteen-request power interface must identify the first request
as (t,t,F). One may eliminate the old base slot d altogether and
recompute the common frame from distinct actual atoms. Alternatively,
one may retain the explicit affine row d=t and retain both square slots
d^2 and t^2 in the frame. This latter choice only strengthens the
absolute bound; it omits no actual request atom. The concrete source
audited below uses the latter choice. A source change still needs a
complete occurrence and power-interface audit, since stale radius or
parity offsets elsewhere would not be repaired by a correct headline
growth equation. The geometric source proofs above apply to the complete
revised source once those literal edits are checked.
