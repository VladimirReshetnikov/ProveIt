# Binary coefficient codes and a matching Pell shift: 90 operations

This construction gives **90 operations: 48 multiplications and 42
additions**, with 34 positive unknowns and 22 equations. There are three
fixed index components besides the queried positive input x. Fixed
numerals and equality tests are free.

The product bound and half-parameter auxiliary block of the published
91-operation system are retained. A different helper reverse row makes
both fixed code polynomials binary. The main Pell base is shifted from
a+4 to a+2 to match this alphabet. Geometry then uses lambda directly,
deleting the multiplication 3*lambda. The complete matching Pell proof
is `BASE_TWO_PELL_90_PROOF.md`; all its hypotheses are verified here
in the required order. Its witnesses are constructed afresh.

## 1. Source and preliminary bounds

Retain positive supplied sigma,alpha and the exact equations

    C=x+g, sigma=(e-ell)*C^2, ell+sigma+alpha=q.

There is no supplied Omega. Since C>=2 and sigma>0, the computed
integer Omega=e-ell is positive, and

    ell<q, C^2<=sigma<q,
    e=ell+Omega<=ell+sigma<q, g<C<q.             (1)

Use the new radix and geometry

    H=H0-1, theta=H+b=B-2,
    B=H0+1+b, b=x+beta,
    lambda*(B-1)=q^2-1.

Here H0 is a large fixed power of two chosen below. Packing remains

    S2=ell+e*q=V+t*theta, n=q^8,
    S=g+q^2*(S2+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b),
    r=S*(n^2-n)+Tplus*(n^2-1).                 (2)

Before exponent decoding, (1) gives S2<q^2. Geometry gives B<=q^2,
theta*lambda>b, and 1+theta*lambda=q^2-lambda<q^2. Thus

    Tplus>b*q^2-b*q>0,
    Tplus<q^4*(1+theta*ell)<B*q^5<=q^7,
    0<S<q^7<n, n^2-1<=r<2n^3.                 (3)

The fixed threshold gives 3L<=B<=n and n>=64. No decoded coefficient,
canonical code, or exponential identity has been assumed.

## 2. Physical values, helpers, and reverse rows

Use the representation from `PRODUCT_BOUND_91_PROOF.md`. The actual
input x has weight zero and is not split. The unit delta is one physical
coordinate. Every other logical value is a sum of three distinct
nonnegative physical coordinates, and logical groups are disjoint.
A value z is represented by (z,0,0) if its H0 bit is zero, otherwise
by (z-H0,H0/2,H0/2). These pieces are nonnegative and clear the fixed bit.

Introduce two reserved helpers V0,V1 with separate triples. Every
ordinary circuit row uses V0 as input and mentions neither x nor V1.
Fresh square-difference copies eliminate repeated gate operands and
repeated unit factors. Expanded square coefficients are +/-1, cross
coefficients are +/-2, and divided coefficients are therefore +/-1.

For each i=0,1 retain the seed base row -x^2, whose augmentation will
give Vi^2-x^2. Replace the reverse row by

    2x*delta-2Vi*delta.                       (4)

Its positive monomial has one non-input factor; its negative monomials
have two. The augmenting helper is V(1-i), disjoint from those negative
factors. Do not infer Vi=x from (4) before proving delta>0.

Every ordinary zero equation has both signs. Retain the normalization
rows with disjoint logical groups,

    X^2-V0^2, Y^2-V0^2, Z^2-V0^2,
    delta_copy^2-delta^2,
    2V0*X-2delta*delta_copy-2u*delta.           (5)

The extra copies Y,Z may be retained without changing the final
operation count. Finish with two unpaired delta^2 rows. The last
one receives a preceding raw coefficient 2xX. There is no constant
padding term and no fivefold or sevenfold padding.

## 3. Support and the binary coefficient property

For m true non-input physical coordinates, assign

    v_i=8*7^i, 0<=i<m, M=8*7^(m-1).

Sums of at most six true weights have unique multisets, by base-seven
digits after division by eight. Let s count the main rows, including
four helper rows and the two unit rows. Define

    d0=12M+8,
    t_j=(s+2)d0+8M+j*d0, 0<=j<s,
    t_last=(2s+1)d0+8M, K=t_last+3.            (6)

Place each divided base coefficient a of monomial weight w at
t_j-w in D(T). For every negative base coefficient -1 at r=t_j-w,
add the six positive helper complements

    sum_(h<=h' in helper group) T^(r-v_h-v_h').

Use its own helper for a seed, the other helper for a reverse, and V1
for ordinary rows. Let Rset contain every main target and negative base
exponent. A seed target is its negative base exponent. Add exactly one
positive reset T^(r-4) for each distinct r in Rset. Finally add

    Dpad(T)=sum_(h in P(X)) T^(t_last-1-v_h).  (7)

The resulting D has only residues 0,4,7 modulo eight.

The exact coefficient arguments of the 91-operation compiler apply,
with one additional degree case. At a non-seed main target, helper
complements have degree four and cannot be completed by a C^2 monomial.
At a negative position, its base term gives -x^2. A different base
contribution would require w_base=w_negative+w_C. Ordinary monomials
have degree two. The positive reverse monomial has degree one and
cannot satisfy this equation, since w_negative has degree two.

A helper complement contributes at an extra negative-position target
only when

    w_negative_1+w_helper=w_negative_2+w_C.

Disjointness of the negative factors from the helper group forces the
same negative pair and helper pair. The tested value is exactly
Vhelper^2-x^2. In a seed, its degree-two complements give Vi^2-x^2
at the coincident target. A reverse main target remains exactly (4).

These multiset facts also exclude coefficient accumulation. Within
an augmentation the group partition is unique. Seed helper pairs
are distinct. Base and helper complements have different degrees in
non-seed rows. Different row bands are separated by more than 12M;
resets and padding occupy other residue classes. Thus every nonzero
D coefficient is still plus or minus one.

Put

    ell0(T)=sum_i T^v_i
             +sum_(r in Rset)(T^r+T^(r+1)+T^(r+2)),
    e0(T)=ell0(T)+D(T).                       (8)

Every negative D coefficient is at an indicator start. The crucial
new fact is that every positive D coefficient is OFF the indicator:

* Ordinary positive base complements have degree two, distinct from
  the row's negative monomials and its degree-zero main target.
* A reverse positive complement has degree one, distinct from both
  negative degree-two complements and the main target.
* Non-seed helper complements have degree four. A seed has only its
  main start, and its positive complements have degree two.
* Reset and padding exponents have residues four and seven, while
  tested windows have residues zero, one, and two.
* Other row bands and the low true-coordinate region are disjoint.

The old reverse +x^2 was the only positive coefficient at a main
indicator target. Replacing it by 2x*delta removes that collision.
Every e0 and ell0 coefficient is consequently zero or one. Their
constant coefficients vanish and their supports lie below K.
The leading D term is the last reset T^(t_last-4), with coefficient
+1: all other terms of the last positive-only row have smaller degree.
Hence D(B)>0 for every integer B>=2.

Permit arbitrary dummy C digits at all window positions. Their least
weight is at least t_0-2M and the least D exponent is at least t_0-4M,
so their sum exceeds t_last+2. No dummy affects a low test or reset.
The least D exponent also exceeds M; every true-coordinate indicator
has raw coefficient and incoming carry zero.

## 4. Fixed index, Pell conclusions, and canonical decoding

Let cstar count x, all true coordinates, and all permitted dummies;
let D1 be the sum of absolute D coefficients. Choose a power of two
L>3K+2 and then a power of two H0 such that

    H0>max(2*2^(2L+1),128*max(1,D1)*cstar^2,3L,1024).

The fixed index is

    H=H0-1, V=ell0(2)+2^L*e0(2), Tindex=psi_2(L). (9)

It is chosen before x. The actual radix B=H0+1+b satisfies (1)--(3),
including 3L<=B<=n and n>=64.

The Pell source is precisely that of `BASE_TWO_PELL_90_PROOF.md`:

    U=w*n^2, YP=sP*n^2, a=YP*(U+1), A=a+2, Dpell=A^2-1,
    d=U+a*c+gamma*(4a+3), kappa=Tindex+Delta*a,

with all other first, main, second, relaxed, and half-parameter norms
retained. Equations (1)--(3) supply every initial hypothesis of that
proof, independently of coefficient decoding. Its proof first fixes
the Pell indices, then obtains lower ratio growth, then decodes
U=2^(2r+1) and q=B^L. The exact binomial symmetry estimate bounds the
fractional tail by 1/4; rounding supplies central-binomial divisibility.
It also proves that B,q,n are powers of two.

Now b<B<q and ell<q give b*ell<q^2. The exact normalized mask is

    Tplus-1=(q^2-1-b*ell)+q^2*theta*lambda+q^4*theta*ell.

Its blocks fit widths q^2,q^2,q^4. The packed binary lemma gives the
three independent masks. The middle mask is

    theta*lambda=(B-2)*sum_(j<2L)B^j,

so every base-B digit of S2 is zero or one. Write its digit polynomial
as F(T), of degree below 2L. The fixed congruence gives F(2)=V modulo
B-2. Both integers are below 2^(2L), and the threshold makes their
difference smaller than B-2. Hence F(2)=V. Binary uniqueness recovers

    F(T)=ell0(T)+T^L e0(T), ell=ell0(B), e=e0(B).

The first mask has digit H0=B-1-b at indicator positions and B-1
elsewhere. It forces g to have only permitted digits, all clearing
the H0 bit. Its unit digit is zero. Since x<B, C=x+g is exactly
the physical coordinate polynomial evaluated at B. The third mask
has digit B-2 at each indicator, so every corresponding digit of
sigma=D(B)C(B)^2 is zero or one.

## 5. Carry clearing and the noncircular helper order

Since B>=2H0, every raw coefficient of D(T)C(T)^2 is in absolute
value below D1*cstar^2*B^2<B^3/256. The signed carry recurrence bounds
all incoming carries in absolute value by B^2/128. Dummy exclusion
makes the only low raw residues 0,4,7 modulo eight.

At a start r, the empty positions r-6,r-5 reduce the carry entering
r-4 to -1 or zero. Its reset polynomial is nonnegative and contains
x^2, so its outgoing carry is nonnegative and below B^2. The empty
positions r-3,r-2 reduce it to zero. Every r-1 is empty except the
last unit pad, whose raw value is exactly 2xX. The following positions
r+1,r+2 are always empty.

Every ordinary/helper/extra target thus receives zero incoming carry
and tests its exact raw value modulo B^3. A negative nonzero value
in the proved range has top digit greater than one and fails. Apply
this fact in the following order:

1. Seeds give Vi^2>=x^2, so Vi>=x>0.
2. Both signs of every ordinary row force that row to vanish,
   independently of the helper values. Equations (5) yield
   X=Y=Z=V0, delta_copy=delta, and V0^2=delta^2+u*delta.
   Since V0>0, this proves delta>0.
3. The reverse value is 2delta(x-Vi). It cannot be negative, so
   Vi<=x. Combined with the seeds, this proves V0=V1=x.
4. All extra target differences vanish, and (5) now yields
   0<delta<=x<B and X=x.

Thus neither unit one nor correct helpers were assumed in the guard
bootstrap. The final unit padding carry is floor(2x^2/B).

## 6. Two binary unit tests

The two tested integers, each followed by two empty raw positions, are

    delta^2, delta^2+floor(2x^2/B).             (10)

Because delta<B, the first binary test gives delta^2=kB+s with
k,s in {0,1}. If s=1, then delta^2<=B+1<B^2/16 for the available
large B. Hence delta<B/4, and the four square roots of one modulo a
power of two leave only delta=1 in this range.

Otherwise a nonunit solution has delta^2=B and x^2>=B. Let
h=floor(2x^2/B). Then 2<=h<2B and B+h<3B<B^2. Binary digits of
the second tested integer B+h would force its middle digit
1+floor(h/B)<=1, hence h<B, and then its low digit would force
h<=1. This is a contradiction. Therefore delta=1 and the homogeneous
circuit recovers the represented system at its actual input x.

## 7. Positive necessity

Given a represented solution, choose V0=V1=x, delta=delta_copy=1,
X=Y=Z=x, u=x^2-1, all circuit values and copies, and their fixed
forbidden-bit splits. Set dummies to zero. Every ordinary, seed,
reverse, and extra target is zero; both unit targets are one.

Choose B an arbitrarily large power of two after these values are
fixed. Require B>H0+1+x, all raw coefficients in absolute value below
B/4, and 2x^2<B/4. Put b=B-H0-1, beta=b-x, and

    ell=ell0(B), e=e0(B), C=C(B), g=C-x,
    q=B^L, n=q^8, sigma=D(B)C^2, alpha=q-ell-sigma.

D(B)>0 and the unit coordinate give sigma,g>0. The support bound
deg(D*C^2)<3K<L lets B be chosen so alpha>0. All first-mask bits
clear, all middle digits are binary, and every third window is
(0,0,0) or (1,0,0), since the last padding carry is zero. The fixed
congruence quotient (ell+eq-V)/(B-2) is positive integral: the
nonconstant polynomial ell0(T)+T^L e0(T) has nonnegative coefficients
and is larger at B than at two. Geometry gives a positive lambda.

The masks give central-binomial divisibility for the resulting r,
with bounds (3). Both ell and g have zero unit digit, so B divides
them; (2), with even B,q, makes S,Tplus,r even. These are exactly
the necessity hypotheses of `BASE_TWO_PELL_90_PROOF.md`. Its Section
6 supplies all Pell witnesses at A=a+2, U=2^(2r+1), including the
positive exponent/index quotients and half-parameter auxiliaries
using J=2r+1 equal to one modulo four. No base-four witness is
silently reused. This proves positivity of all 34 supplied unknowns.

## 8. Complete arithmetic certificate and evidence boundary

`round37_1980_binary_product_certificate.py` states all 22 source
residuals afresh. Geometry now reads

    q^2=(1+theta*lambda)+lambda.

It deletes three_lambda=3*lambda and uses lambda in the final
addition. The shared Pell modulus/discriminant become 4a+3 and
a^2+(4a+3), with the same operation count as their predecessors.
Also A-B=a-theta still uses the same subtraction. Thus exactly one
multiplication disappears: 48 multiplications and 42 additions.

For exact source comparison, let E=4a+12 be the old discriminant
minus the new one, and u_aux=2r+1+jc. The only residual changes,
in zero-based order, are

    2: +2lambda,
    13: +gamma*E,
    14: +c^2*E,
    15: +(f^2-1)*E,
    16: -(f^2-1)*(u_aux^2-y_aux^2)*E,
    17: +rho*E,
    18: -kappa^2*E.

The three inherited certificate corrections remain

    correction2=-lambda*F3,
    correction16=F15*(u_aux^2-y_aux^2),
    correction17=F3*(kappa+rho*(F3-2*(A-B))).

F3 and F15 are independently exact, so these are acyclic. The checker
verifies all primitive instructions, source equalities, difference
formulas, the exact histogram, and every supplied positive input.

`round37_1980_binary_product_encoding.py` independently checks a sample
layout symbolically, including every target, all positive coefficients
off the indicator, binary e0, positive resets, the exact 2xX pad, and
dummy exclusion. It exercises six canonical full-code assignments,
four wide signed-carry assignments, and a finite exhaustive local
binary-unit family. These finite checks are not exhaustive over
circuits or witnesses and do not replace the general compiler and
Pell proofs. No optimality claim is made.
