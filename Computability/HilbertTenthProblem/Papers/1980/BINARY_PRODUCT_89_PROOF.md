# Narrow binary product packing: a complete 89-operation certificate

This construction represents exactly the same sets of positive inputs as
the binary product system in `BINARY_PRODUCT_90_PROOF.md`, using the same
raw input x and the same three fixed index components H,V,Tindex. Its
complete arithmetic certificate has **89 operations: 47 multiplications
and 42 additions**, with 34 positive unknowns and 22 equations. Fixed
numerals and equality tests are free. No optimality claim is made.

The compiler is unchanged. The saving comes from arranging its four
bounded words in consecutive q-fields and allowing the product mask to
borrow one at its low end. This deletes the multiplication computing
q^8. A possible spill into the binary code mask must be excluded before
the fixed code can be decoded; Section 4 proves that exclusion without
assuming canonical coefficients. The preliminary Pell range is slightly
wider. Both positive-domain directions of that kernel are proved afresh
in `BASE_TWO_PELL_89_PROOF.md`.

## 1. Source equations and bounds before any exponent decoding

Retain every source equation and every positive supplied variable of
`BINARY_PRODUCT_90_PROOF.md`, except the definition of n and the packed
index equation. In particular, retain

    C=x+g, sigma=(e-ell)*C^2, ell+sigma+alpha=q,
    b=x+beta, theta=H+b=B-2, B=H0+1+b,
    lambda*(B-1)=q^2-1,
    S2=ell+e*q=V+t*theta.

Here C is computed, not a new supplied variable. Positive sigma and
C>=2 imply e-ell>=1. Consequently

    0<ell<q, C^2<=sigma<q, 0<e<q, 0<g<C<q,
    0<S2<q^2.                                      (1)

Replace the two source equations by

    n=q^4,
    S=g+q*sigma+q^2*S2,
    Tplus=q^2*theta*lambda+ell*(theta*q-b),
    r=S*(n^2-n)+Tplus*(n^2-1).                      (2)

S and Tplus are computed expressions, not additional supplied unknowns.
All 22 source residuals, including the unchanged main, first, second,
relaxed, and half-parameter Pell equations, are stated explicitly in
`../verification/round38_1980_binary_product_certificate.py`.

The four consecutive q-fields g,sigma,ell,e all satisfy (1), so 0<S<n.
From positive lambda and geometry, B<=q^2 and theta*lambda<q^2.
Also theta>b>0, giving theta*q-b>0. Therefore

    0<Tplus<q^4+theta*q^2<2q^4=2n,
    n^2-1<=r<3n^3.                                (3)

The fixed threshold retained below gives n>=64 and 3L<=B<=n; hence
n^2-1>=n. These estimates use only positive supplied coordinates and
the stated equations. They do not use radix powers, coefficient types,
or canonical code values. The inequality Tplus<n is deliberately not
claimed at this point.

## 2. The unchanged binary compiler and fixed index

Use exactly the effective compiler of Sections 2--3 of
`BINARY_PRODUCT_90_PROOF.md`. The actual input x is the coordinate of
weight zero and is not split or recoded. The unit delta has a separate
coordinate. Every other logical value is a sum of three disjoint
nonnegative physical coordinates; splitting at the fixed H0 bit lets
all those pieces clear that bit. The two reserved helpers V0,V1 have
their own triples. The seed/reverse pairs test

    Vi^2-x^2, 2*delta*(x-Vi), i=0,1.

Ordinary circuit rows use V0 in place of x. The normalization rows are

    X^2-V0^2, Y^2-V0^2, Z^2-V0^2,
    delta_copy^2-delta^2,
    2*V0*X-2*delta*delta_copy-2*u*delta.

Every ordinary row is tested in both signs. The two unpaired unit rows
test delta^2; the second has the preceding raw padding coefficient
2*x*X. No new compiler operation or index component is introduced.

For m non-input physical coordinates the true weights are

    v_i=8*7^i, 0<=i<m, M=8*7^(m-1), v_0=8.

The existing separated row bands, helper complements, positive resets,
and final padding construct D(T), ell0(T), e0(T)=ell0(T)+D(T). Their
proved properties, all retained without modification, are:

* ell0 and e0 have coefficients zero or one, vanish at degree zero,
  and have support below K. The least indicator position is v_0=8.
* Every negative D coefficient is -1 at an indicator start. Every
  positive D coefficient is +1 off the indicator. D has residues
  0,4,7 modulo eight, has leading coefficient +1, and D(B)>0 for B>=2.
* min(support D)>M. Thus D(B)*C^2 is divisible by B^(M+1) for every
  integer C, without any coefficient or carry assumption on C.
* Tested row starts carry three-digit windows. Their reset at offset
  -4 is a nonnegative raw polynomial containing x^2; the intermediate
  carry-clearing positions are empty. Only the last unit window has
  a nonempty position at offset -1, with exact raw value 2*x*X.
* Permitted dummy coordinates at the row-window positions affect no
  tested low coefficient or reset. Every true-coordinate position has
  zero raw product coefficient and zero incoming carry.

These are polynomial support and coefficient facts, proved by the
base-seven multiset separation in the cited compiler; none depends on
the q-field layout or on n. Let cstar count all permitted coordinates,
including x and dummies, and D1 be the sum of the absolute D coefficients.
Choose a power of two L>3K+2 and a power of two H0 with

    H0>max(2*2^(2L+1),128*max(1,D1)*cstar^2,3L,1024).

Retain the identical fixed index

    H=H0-1,
    V=ell0(2)+2^L*e0(2),
    Tindex=psi_2(L).                               (4)

These constants are chosen before x. Thus this construction improves
the complete original raw-input representation, not only a component
with an unpaid input compiler.

## 3. Decode the exponents before tightening the packed-word bound

The retained Pell quantities are

    U=w*n^2, YP=sP*n^2, a=YP*(U+1), A=a+2,
    Dpell=A^2-1, J=2r+1,
    d=U+a*c+gamma*(4a+3), kappa=Tindex+Delta*a.

Together with the unchanged norm, interval, rank, half-parameter, and
second-exponential equations, (1)--(3) meet every initial hypothesis of
`BASE_TWO_PELL_89_PROOF.md`: n=q^4, n>=64, n<=r<3n^3 and
3L<=B<=n. That proof recovers the exact Pell indices, then lower ratio
growth, then

    U=2^(2r+1), q=B^L,
    B,q,n powers of two,
    n^2 divides binom(2r,r).                       (5)

In particular it does not invoke Tplus<n or a decoded mask to obtain
(5). Its wider preliminary estimates include

    E>=n^4>r+1, a>n^4>2r+1,
    4r/a<12/n<=3/16<1/2.

Now q=B^L with L>=2, and

    theta*lambda=q^2-1-lambda,
    lambda=(q^2-1)/(B-1)>=B+1>theta.

Since ell<q,

    ell*(theta*q-b)<theta*q^2<lambda*q^2,
    Tplus<q^2*(q^2-1-lambda)+lambda*q^2<n.        (6)

Both packed words now satisfy 0<S,Tplus<n. The usual binary packed
lemma applies to (2), with no extended or overflowing version needed:

    n^2 | binom(2r,r)  iff  S & (Tplus-1)=0.       (7)

For completeness, writing t=Tplus-1, the three base-n blocks of r are
n-1-t, n-1-S, S+t. Their bit count is

    2*log2(n)-popcount(S)-popcount(t)+popcount(S+t).

The last popcount is at most the sum of the preceding two, with
equality exactly when S and t have no common bit. Kummer's identity
v2(binom(2r,r))=popcount(r) proves (7), including the case S+t>=n.
The three blocks occupy disjoint binary positions even in that case,
since S+t is the entire top block with no imposed upper width.

## 4. The spill into the binary code mask is impossible

This step must precede canonical decoding. Divide

    b*ell=k*q+rb, 0<=rb<q,
    theta*ell-k-1=j*q+u, 0<=u<q.

Because ell<q and b<theta, 0<=k<=b-1, and therefore
theta*ell-k-1>=theta-b>0. Also theta*ell-k-1<theta*q, so

    0<=j<=theta-1=B-3.

The exact normalized mask is

    Tplus-1=(q-1-rb)+q*u+q^2*(theta*lambda+j).    (8)

The top field in (8) is below q^2: (6) proves the full integer is
below q^4. Thus (7), the three fields g,sigma,S2 of S, and their
bounds imply

    S2 & (theta*lambda+j)=0.                     (9)

Here theta*lambda has 2L base-B digits, all B-2. Analyze the possible
addition j to its unit digit:

* If j=0, all its digits remain B-2.
* If j=1, its unit digit becomes B-1 and every other digit remains
  B-2. Consequently ell has unit digit zero and all other digits
  zero or one. Hence ell<q/(B-1), so theta*ell<q, contradicting j=1.
* If j>=2, its unit digit is j-2, its next digit is B-1, and every
  higher digit is B-2. Consequently ell has digit 1 equal to zero,
  digits at positions >=2 in {0,1}, and unit digit at most B-1.
  Thus, for every L>=2,

      ell <= B-1 + sum_(i=2)^(L-1) B^i
           = (q-2B+1)/(B-1) < q/(B-1).

  Again theta*ell<q, contradicting j>=2.

Therefore j=0. The unperturbed middle mask now proves that every
base-B digit of the whole S2 is zero or one. This conclusion uses no
property of the fixed code other than L>=2, and no value of F(2).

Write S2=F(B), where F has binary coefficients and degree below 2L.
The retained congruence gives F(2)=V modulo B-2. Both values are below
2^(2L), while the fixed threshold makes B-2 larger than their possible
difference. Hence F(2)=V as integers. Binary uniqueness gives

    F(T)=ell0(T)+T^L*e0(T),
    ell=ell0(B), e=e0(B).                        (10)

The fixed supports now give b*ell<q and theta*ell<q. For example,
ell< B^K and b,theta<B, while K+1<L. Thus k=0, and (8) becomes

    Tplus-1=(q-1-b*ell)+q*(theta*ell-1)
                           +q^2*theta*lambda.   (11)

## 5. The borrowed product mask has exactly the required meaning

The three independent tests furnished by (7) and (11) are

    g & (q-1-b*ell)=0,
    sigma & (theta*ell-1)=0,
    S2 & (theta*lambda)=0.                      (12)

The first mask has digit H0=B-1-b at each indicator, and B-1
elsewhere. It forces g to have only permitted digits, each clearing
the H0 bit. In particular its unit digit is zero. Since x<b<B,
C=x+g is exactly the physical coordinate polynomial evaluated at B,
with raw input x at its unit coordinate and no addition carry.
The narrower width q loses no allowed coordinate, since all indicator
positions lie below K<L and g<q was established before decoding.

The second mask differs from the former theta*ell mask only at and
below the least indicator v_0=8. Subtracting one changes every lower
zero digit to B-1, and changes the digit at v_0 from B-2 to B-3.
All higher digits are unchanged. But (10) and the retained product
equation give

    sigma=D(B)*C^2,
    B^(M+1) divides sigma, M>=v_0.

Thus every affected sigma digit is identically zero, for every integer
C, independently of the high signed-carry analysis. Consequently

    sigma & (theta*ell-1)=0
        iff sigma & (theta*ell)=0.              (13)

At every indicator the product digit is therefore zero or one, exactly
as in the previous compiler. The change does not weaken a row test or
require an additional zero-coordinate predicate.

## 6. Recover the represented equations in the original order

After (10)--(13), all physical code and product-mask hypotheses are
identical to Sections 5--6 of `BINARY_PRODUCT_90_PROOF.md`. To state
their use explicitly, B is a power of two strictly exceeding H0,
so B>=2H0. The raw coefficients of D(T)*C(T)^2 have
absolute value less than D1*cstar^2*B^2<B^3/256. Signed incoming
carries are bounded by B^2/128. The two empty places before each
positive reset reduce its incoming carry to -1 or zero. The reset
contains x^2 and is nonnegative; the next two empty places clear its
outgoing carry. Each ordinary three-digit window therefore tests its
exact raw value modulo B^3, and a negative raw value in the bound
has a top digit exceeding one and fails.

Apply the resulting tests in this noncircular order:

1. The seed inequalities give Vi>=x>0.
2. Both signs of each ordinary row make it zero. Normalization gives
   X=Y=Z=V0, delta_copy=delta, and V0^2=delta^2+u*delta, hence delta>0.
3. Reverse rows 2*delta*(x-Vi)>=0 give Vi<=x. Therefore V0=V1=x,
   all extra helper targets vanish, and 0<delta<=x<B with X=x.
4. The two remaining three-digit binary tests are delta^2 and
   delta^2+floor(2*x^2/B). The first allows only delta=1 or
   delta^2=B. In the latter case the second has the form B+h with
   2<=h<2B; its middle and low binary digits cannot both be in {0,1}.
   Thus delta=1, and the homogeneous circuit yields the represented
   equations at the actual input x.

For the first unit test, if delta^2=kB+s with k,s in {0,1} and s=1,
then delta^2<=B+1<B^2/16. The four square roots of one modulo the
large power of two B leave only delta=1 in this range. If s=0, the
only positive alternative is delta^2=B. This is the same unit proof,
with no new assumption on the unknown physical coordinates.

## 7. Positive completeness, with fresh Pell witnesses

Given a represented solution, take the identical canonical physical
assignment: V0=V1=X=Y=Z=x, delta=delta_copy=1, u=x^2-1, the circuit
values and copies, their H0-bit splits, and zero dummies. Choose B an
arbitrarily large power of two with B>H0+1+x, all absolute raw
coefficients below B/4, and 2*x^2<B/4. Set

    b=B-H0-1, beta=b-x,
    ell=ell0(B), e=e0(B), C=C(B), g=C-x,
    q=B^L, n=q^4, sigma=D(B)*C^2,
    alpha=q-ell-sigma,
    lambda=(q^2-1)/(B-1), t=(ell+e*q-V)/(B-2).

All these supplied coordinates are positive: the unit coordinate
gives g>0; D(B)>0 gives sigma>0; the degree bound
deg(D*C^2)<3K<L and sufficiently large B give alpha>0; the fixed
binary polynomial is nonconstant and larger at B than at two, giving
positive integral t. The original compiler shows every window is
(0,0,0) or (1,0,0), and the first-mask bits clear. The new mask passes
by (13). All fields fit within their q widths. Define S,Tplus,r by
(2); (3), (6), and (7) give the required positive range and central
binomial divisibility.

Both g and ell are divisible by B. Since B and q are even, (2)
gives S and Tplus even and therefore r even. This is the retained
half-parameter sign condition J=2r+1 equal to one modulo four.
Construct the Pell coordinates afresh for this new n and r, using
Section 6 of `BASE_TWO_PELL_89_PROOF.md`. In particular use
U=2^(2r+1), the new binomial integer YP, the new main and first indices,
and the new relaxed/half-parameter and second-index witnesses. That
proof verifies the positivity and integrality of every quotient and
gap. No old n=q^8 Pell tuple is reused. This supplies all 34 positive
unknowns and proves completeness with the unchanged fixed index (4).

## 8. Exact operation count and reproducible evidence

The previous graph already computes q2=q*q and q4=q2*q2. Delete
q8=q4*q4 and compare the supplied n directly with q4. Arrange the
source word in four operations, using the existing S2 and product:

    s2q=S2*q, inner=sigma+s2q, innerq=inner*q, S=g+innerq.

The old source word also cost four. For the mask, use

    top=(theta*lambda)*q2,
    thetaq=theta*q, gap=thetaq-b,
    low=ell*gap, Tplus=top+low.

These are the same five operations as before. The graph still computes
1+theta*lambda for the unchanged q2=(1+theta*lambda)+lambda geometry,
but the mask now uses the already available theta*lambda directly.
No other operation is removed or added. Thus the complete count is
47 multiplications and 42 additions, including the nine subtractions
represented as addition primitives.

The full source checker verifies all 22 expanded polynomial residuals,
all 89 primitive instructions, participation of all positive supplied
inputs, and the fact that only source residuals 5 and 6 change (zero
based). The inherited acyclic corrections are exactly

    correction2=-lambda*F3,
    correction16=F15*(u_aux^2-y_aux^2),
    correction17=F3*(kappa+rho*(F3-2*(A-B))).

F3 and F15 are independently exact. The source and receipt are
`round38_1980_binary_product_certificate.py/.json`. The companion
`round38_1980_binary_product_encoding.py/.json` reruns the existing
sample compiler's symbolic and sparse-carry checks, checks the shifted
mask on that sparse support, and exercises the new bounds, spill
exclusion, mask normalization, and packed-popcount equivalence in
explicit finite families. Those regressions supplement the general
proof above; they are not exhaustive over circuits, indices, or
positive witnesses, and do not materialize a giant full Pell tuple.

Review status: author and independent complete proof/source reviews pass.
Fresh independent calls to both verification functions exactly match the
saved JSON after serialization, with source and receipt hashes unchanged.
