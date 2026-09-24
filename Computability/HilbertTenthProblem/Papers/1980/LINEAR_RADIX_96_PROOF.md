# Linear radix scaling and reset padding: 96 operations

This note proves the positive-domain system checked by
`../verification/round30_1980_linear_radix_certificate.py`. Starting
from `COMPOSED_97_PROOF.md`, replace the quadratic radix scale and the
third packed block by

    B=H*b,
    Omega=lambda-e>0,
    sigma=Omega*(q-(x+g)^2)>0.                 (1)

Add the positive gap equation

    ell+alpha2=q.                             (2)

Every other Pell equation is retained, with B=Hb wherever the radix
occurs. The coefficient index is rebuilt below. The resulting system
has 35 positive unknowns and 23 equations. Its complete certificate
has 96 operations: 52 multiplications and 44 additions. Fixed
numerals and equality tests are free. The three fixed index
components are again (V,H,Tindex), with Tindex=psi_4(L).

The two important changes in decoding are separate. Equation (2)
removes the quotient alias directly. This makes the old high-mask
estimate unnecessary. Linear radix scaling permits quadratic raw
coefficients to occupy two base-B digits; paired zero tests, reset
padding and a new unit construction make those two-digit tests exact.

## 1. The homogeneous circuit and its normalization rows

Compile the represented finite Diophantine system into an arithmetic
circuit over nonnegative integers, using the actual positive input x,
addition, multiplication, zero and one. Introduce a homogeneous
coordinate delta. Repeated operands are replaced by fresh copies and
every gate output is fresh. All circuit coordinates other than x
have positive weights in the code.

For a multiplication, addition or zero equation use, respectively,

    2XY-2W*delta=0,
    2(X+Y-W)*delta=0,
    2X*delta=0.                               (3)

All products in (3) are products of distinct coordinates. A copy
X'=X may instead be imposed by

    X'^2-X^2=0.                               (4)

Nonnegativity makes (4) an exact copy equation. It also supplies
arbitrarily many distinct copies of delta without introducing a
diagonal coefficient of magnitude two. A circuit occurrence of the
constant one is represented by delta, or by a copy (4) of delta.
Whenever using delta directly would create delta*delta in (3), use
a fresh square-difference copy instead. Likewise give repeated gate
operands distinct copies. Thus every product displayed in (3) has
distinct factors, including when a gate operand is the constant one.
Final equalities can use either distinct-coordinate products with
delta or square differences. We include both F and -F for every
zero equation F=0 in this construction.

For normalization, introduce distinct coordinates X,Y,delta',u and
include the following equations and their negatives:

    X^2-x^2=0,       Y^2-x^2=0,
    delta'^2-delta^2=0,
    2xX-2delta*delta'-2u*delta=0.              (5)

When their zero tests have been decoded, (5) gives

    X=Y=x, delta'=delta,
    x^2=delta^2+u*delta.                       (6)

Thus delta>0 because x>0, and delta<=x. Conversely, delta=delta'=1,
X=Y=x and u=x^2-1 are nonnegative witnesses to (5) for every positive
x, including x=1.

Finally include two unpaired targets, each with raw polynomial
delta^2. The second will receive extra positive padding. These two
tests, rather than a first special target with a presumed incoming
carry, force delta=1 in Section 6.

For every listed target polynomial, divide a square coefficient by
one and a distinct-coordinate product coefficient by two. Every
result lies in {-1,0,1}. This includes (3), (4), both signs of (5),
and the two delta-squared targets. The row count and the number of
encoded coordinates can depend on the represented system; they are
digits of the integer codes, not additional unknowns in the final
23-equation system.

## 2. A support layout with two-digit targets and reset positions

Let m count all non-input circuit and normalization coordinates.
Give them weights

    v_i=4*3^i, 0<=i<m,
    M=4*3^(m-1).

The input x has weight zero. Quadratic monomial weights determine
their unordered coordinate pair, including squares and products
with x: divide by four and use the base-three digits. In particular,
all these weights are multiples of four and are at most 2M.

Let s be the number of targets, counting both signs of each zero
equation and the two final unit tests. Put the two unit tests last,
and distinguish the last target t_* as the additional-carry test.
Define

    d=4M+4,
    t_j=(s+1)d+2M+j*d, 0<=j<s,
    t_last=2s*d+2M,
    K=t_last+2.                               (7)

All t_j are multiples of four. For a target G_j and a monomial of
weight w with divided coefficient a, put a*T^(t_j-w) in D_main(T).
The intervals [t_j-2M,t_j] are disjoint, so these instructions do not
collide. Add the reset polynomial and the last-target padding:

    D_reset(T)=sum_j T^(t_j-2),
    D_extra(T)=T^(t_*-1)+T^(t_*-1-v_X)
                            +T^(t_*-1-v_Y),
    D(T)=D_main(T)+D_reset(T)+D_extra(T).       (8)

The three parts have exponents congruent to 0, 2 and 3 modulo four,
respectively. The three extra exponents are distinct. Thus all D
coefficients still lie in {-1,0,1}. All exponents are positive,
greater than M, and less than K.

Include a dummy coordinate at each t_j and t_j+1. Set

    ell_0(T)=sum_i T^v_i+sum_j(T^t_j+T^(t_j+1)),
    e_0(T)=sum_(0<=h<K) T^h+D(T).              (9)

The digits of ell_0 are zero or one and those of e_0 are zero, one
or two. The unit digit of e_0 is one. Let c_* count the input, all
m true coordinates, and the 2s dummies. Let

    D1=sum_h |[T^h]D(T)|.

Choose a power of two L>3K+2 and a power of two H satisfying

    H>max(2*4^(2L+1), 64*max(1,D1)*c_*^2, 3L, 64).
                                                        (10)
    V=ell_0(4)+e_0(4)*4^L,
    Tindex=psi_4(L).                           (11)

All these choices depend only on the represented system and are
made before the queried input x is supplied.

For arbitrary decoded dummy values, no dummy contributes to any
coefficient of D(T)C(T)^2 through t_last+1. Indeed, the least D
exponent is at least t_0-2M, the least dummy weight is t_0, and

    2t_0-2M>t_last+1.                         (12)

This observation is needed: dummies at t_j+1 are not in the zero
residue class modulo four. Up to the last tested digit, however,
they have no effect on the product at all.

## 3. Preliminary packing bounds and the unchanged Pell block

Retain the following coding equations and definitions in addition
to (1) and (2):

    C=x+g, b=x+beta, B=Hb, theta=B-4,
    lambda*(B-1)=q^2-1,
    S2=ell+e*q=V+t*theta, S2+alpha=q^2,
    n=q^8,
    S=g+q^2*(S2+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell
                                      +theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).                (13)

All supplied unknowns, including alpha, alpha2, Omega and sigma,
are positive integers. Before any internal circuit row or Pell
conclusion is used, positivity gives

    ell<q, e<q, S2<q^2,
    C^2<q, g<q,
    0<sigma<lambda*q<q^3.                    (14)

The last inequality uses lambda=(q^2-1)/(B-1)<q^2. Geometry gives
B<=q^2. Also b>=2 and (10) imply q>=6, b<B<n and 3L<=B<=n.
The old estimate q>4b is not used or asserted for the linear radix.
We have

    theta*lambda> b,

because theta*lambda>=B-4=Hb-4>b. Now (14) gives 0<S<q^7<n.
For the second packed number,

    Tplus>q^2*theta*lambda-b*ell
          >b*q^2-b*q>0,
    Tplus<q^4*(1+theta*ell)<B*q^5<=q^7<n.     (15)

For its upper bound, use 1+theta*lambda<q^2 and
1+theta*ell<=1+(B-4)(q-1)<Bq. Consequently

    n<=n^2-1<=r<2n^3.                        (16)

These are all the packing-size inputs to the main Pell and binomial
arguments. In particular, put

    U=w*n^2, Y_pell=s_pell*n^2,
    a=Y_pell*(U+1), A=a+4,
    D_pell=A^2-1, P=2U*Y_pell^2+1,
    J=2r+1.

Here Y_pell and s_pell denote the former Y and s of the Pell proof,
not the new encoded copy Y in (5). From (16), U,Y_pell>=n^2,
U*Y_pell>=n^4>r+1, and a>n^4>J. The first index equation and the
positive interval imply c>J. The norm classifications and P>A imply
that the preliminary main index is at least r+2. Hence
c>A*D_pell^2, exactly as in `COMPOSED_97_PROOF.md`.

The relaxed auxiliary norm

    (i*c^2)^2=D_pell*(f^2-1)

therefore has the same fundamental-unit and strong-divisibility
hypotheses as before. It recovers its required multiple of c. The
doubled signed-index argument then identifies c=psi_A(J),
d=chi_A(J). The first-index and ratio argument gives
Y_pell>=U^r and a>U^(r+1), before either exponent relation is used.
The common-witness exponent equation gives U=4^J. The unchanged
fixed congruence kappa=Tindex+Delta*a determines the second index
as L; the second exponent equation then gives q=B^L.

Every exponent-size hypothesis follows from (16) and
3L<=B<=n<=r as in that proof. None uses B=Hb^2. Since n^2 divides
U=4^J, q is a power of two; q=B^L makes B a power of two; and the
fixed power of two H divides B=Hb, so b is a power of two. Finally
the unchanged upper ratio and binomial fractional-part estimates
give

    n^2 divides binom(2r,r).                  (17)

This applies the full Pell argument before any coefficient equation
or unit value is assumed. Its necessity construction will be used
only after the new coding witnesses have been chosen in Section 7.

## 4. Both integer codes are canonical, without a high-mask bound

After the Pell conclusions, b<B<q and ell<q. Hence the raw first
mask is nonnegative:

    q^2-1-(b-1)*ell>0.                        (18)

Thus T=Tplus-1 has the exact three-block expansion

    T=(q^2-1-(b-1)*ell)+q^2*theta*lambda
                                      +q^4*theta*ell.

All three blocks have their indicated widths (2,2,4) in radix q.
The binary no-carry packing lemma applied to (13), (16) and (17)
gives the three ordinary masks

    g & (q^2-1-(b-1)*ell)=0,
    S2 & theta*lambda=0,
    sigma & theta*ell=0.                      (19)

Here '&' is bitwise intersection, used only in the proof of the
polynomial system's meaning.

Because q=B^L and theta=B-4, the middle mask says that the base-B
digits of S2 are in {0,1,2,3}, with fewer than 2L positions. If F(T)
is that digit polynomial, F(B)=S2 and the congruence in (13) gives
F(4)=V modulo B-4. Both F(4) and V are less than 4^(2L), whereas
(10) makes B-4 larger than their possible difference. Thus F(4)=V.
Uniqueness of the base-four expansion now gives

    S2=ell_0(B)+e_0(B)*q.

Since both ell and e are less than q, as are ell_0(B) and e_0(B),
uniqueness of the quotient and remainder in division by q gives

    ell=ell_0(B), e=e_0(B).                    (20)

No high-mask estimate proportional to the square of the digit bound
is needed. In particular, no quadratic scale is being inferred from
the new linear choice B=Hb.

The first mask in (19), together with b and B being powers of two,
now bounds every coordinate digit of g by b-1 and permits nonzero
digits only at the indicator positions. The unit digit of g is
zero, so the unit coordinate of C is exactly the queried x. Write

    C(T)=x+sum_i z_i*T^v_i
                   +sum_j(d_j*T^t_j+d'_j*T^(t_j+1)).

All these decoded coordinates are nonnegative and below b. Let
A_C=C(1)^2. Then

    A_C<(c_*b)^2<B^2/64.                     (21)

Also e,C<B^K, and L>3K+2 implies e*C^2<q. Through position K-1,
the raw signed coefficients of sigma are exactly those of
D(T)C(T)^2: the q terms in (1) start at L, and the difference between
the finite coefficient baseline in (9) and lambda starts at K.
Each such raw coefficient has absolute value at most A_C, since D
has coefficients of absolute value at most one.

## 5. Reset padding gives exact paired zero tests

Consider the ordinary signed base-B carry recursion

    h_0=0,
    digit_j=a_j+h_j-B*h_(j+1),
    h_(j+1)=floor((a_j+h_j)/B),                (22)

where a_j=[T^j]D(T)C(T)^2. It computes the actual low base-B digits
of the positive integer sigma. From (21), induction gives
|h_j|<B/8 throughout the tested range. For example,
|a_j|<B^2/64 and |h_j|<B/8 imply
|floor((a_j+h_j)/B)|<=B/64+1/8+1<B/8;
the last inequality follows from B>64.

By (12), dummies do not affect this range. Every non-input true
coordinate weight is zero modulo four. Consequently a_j can be
nonzero only in residue classes 0, 2 and 3 modulo four. Class 1 is
empty. In particular the carry into t_j-2, immediately following
an empty class-1 position, is either -1 or zero.

At t_j-2 the raw coefficient is nonnegative and at least x^2: the
row's own reset term contributes x^2 and every other reset
contribution is nonnegative. It is less than B^2/64. Therefore the
carry into t_j-1 is a nonnegative integer alpha_j<B/64.

At any target other than t_*, the raw coefficient at t_j-1 is zero.
Indeed, only D_extra can contribute in this residue class, and
its possible contributions lie within distance 2M of t_*-1;
different targets are separated by d=4M+4. Dividing the carry
alpha_j<B by B at this empty position leaves exactly zero carry
into t_j.

There is also no raw coefficient at t_j+1. Thus the two tested
digits at t_j and t_j+1 are the residue modulo B^2 of the target's
raw polynomial value G_j. The third mask in (19) permits each of
these digits to lie only in {0,1,2,3}.

For a paired zero equation, |G_j|<B^2/64. A negative nonzero value
has residue modulo B^2 with a high digit greater than three, so it
fails the mask. Both G_j and -G_j have their own reset padding and
zero incoming carry. They can both pass only when G_j=0; conversely
zero passes both masks. This proves every equation (3)--(5) exactly,
without yet knowing delta=1. In particular (6) holds.

The same argument gives zero incoming carry at the first unpaired
delta-squared target. Its consequences are used next. The only
exception to the zero incoming carry rule is the deliberately
modified last target t_*.

## 6. The last carry forces delta=1

The first unit test has raw value delta^2 and zero incoming carry.
Using (21), its two allowed digits give

    delta^2=kB+s, k,s in {0,1,2,3}.            (23)

Equation (6) gives 0<delta<=x, and coordinate bounds give
delta<b=B/H<B/4. Since B is a sufficiently large power of two,
s=2 or 3 is impossible modulo four. If s=1, the positive square
roots of one modulo B are congruent to 1, B/2-1, B/2+1 or B-1.
The bound delta<B/4 therefore forces delta=1. The only remaining
possibility for delta>1 is s=0, so

    delta^2>=B and x^2>=B.                   (24)

At t_*-1, monomial uniqueness and the input-copy equations in (5)
make the raw extra-padding coefficient exactly

    x^2+2xX+2xY=5x^2.

The reset at t_*-2 remains present. As in Section 5, it supplies a
nonnegative carry alpha_*<B/64 into this position. Thus the incoming
carry at the last target is

    k_pad=floor((5x^2+alpha_*)/B)>=0.          (25)

The global coefficient bound also gives k_pad<B/8<B. If (24) held,
(25) would give k_pad>=5. At t_* the raw coefficient is delta^2,
and delta^2 is a multiple of B by (23). Its low digit would therefore
be k_pad, between five and B-1, contradicting the last mask.
Hence (24) is impossible and delta=1.

At delta=1, (3), (4), and all circuit rows decode the represented
system at the actual input x. This proves sufficiency.

## 7. Necessity and every positive supplied witness

Given a solution of the represented system, take its circuit values,
delta=delta'=1, X=Y=x, u=x^2-1, and zero dummy coordinates. Supply
all fresh copies by equality. Every paired row has value zero, and
both unpaired unit targets have value one.

The fixed index has already been chosen by (7)--(11). Now choose a
power of two b arbitrarily large relative to these finitely many
coordinate values. In addition to exceeding every coordinate,
choose it large enough that every raw coefficient of D(T)C(T)^2
has absolute value less than B/4 for B=Hb, and that 5x^2<B/4.
This is possible: the coordinates, D and their raw coefficients
are fixed before b is chosen, while Hb grows without bound.

Take the canonical codes (20), q=B^L and n=q^8. The support margin
gives C^2<q, and lambda=(q^2-1)/(B-1)>e. Thus both Omega and sigma
in (1) are positive. The values

    alpha2=q-ell, alpha=q^2-(ell+e*q),
    beta=b-x, t=(ell+e*q-V)/(B-4)

are positive integers. For t, use evaluation of the nonconstant
nonnegative polynomial ell_0(T)+e_0(T)T^L at B>4. The coordinate
delta=1 gives g>0.

The first two masks in (19) hold by the coordinate and digit bounds.
For the third, all variable positions and their preceding positions
lie below the least D exponent, so they have zero raw coefficient
and zero carry. Every paired target receives the zero carry from
its reset and has raw value zero. The first unit target has value
one. At the last target, the chosen small-coefficient bounds give
alpha_*=0 and k_pad=0, so its two tested digits are also one and zero.
Thus all three masks hold. The packing lemma supplies (17) for the
newly determined r, and (14)--(16) give its required size bounds.

Construct the positive Pell witnesses at this new r exactly as in
`COMPOSED_97_PROOF.md`: choose U=4^J,
Y_pell=floor((U+1)^(2r)/U^r), then w=U/n^2,
s_pell=Y_pell/n^2 and a=Y_pell(U+1). Take the main and first Pell
coordinates at J and r+1, their positive interval and first-index
quotients, and the second coordinates at L. The second index uses
the newly fixed Tindex=psi_4(L). The exponent and rounding bounds
give all the required positive quotients as in that proof.

For completeness, choose the doubled-index auxiliary exponent last
as m_aux=2cJ. Set f=chi_A(m_aux) and
i_old=psi_A(m_aux)/c^2>0; the doubled-index construction supplies
positive o and j. Use i=D_pell*i_old. This gives the relaxed norm
(i*c^2)^2=D_pell*(f^2-1) and leaves the signed auxiliary value
unchanged. No coding witness needs to be changed. Together with
the new positive alpha2, all 35 supplied unknowns are now positive
integers. This proves necessity.

## 8. Arithmetic count and the scope of verification

Relative to the 97-operation certificate, replacing B=Hb^2 by Hb
removes one multiplication. Replacing

    sigma=theta*lambda*q-(lambda-e)*C^2

by (1) replaces two multiplications and one subtraction by one
multiplication and one subtraction. It therefore removes another
multiplication. Adding (2) costs one addition. All normalization,
padding and two-digit support changes are changes to the fixed
coefficient index, not additional arithmetic in the final system.
Thus

    97-1-1+1=96,
    (54 multiplications,43 additions)
           ->(52 multiplications,44 additions).

The standalone checker verifies all 96 primitive instructions,
the complete 23 source residuals, and their acyclic corrections.
The geometric and second-exponent corrections still depend only
on the exact theta+4=B equality; the signed auxiliary correction
still depends only on the exact relaxed auxiliary norm. Fixed
numerals have no construction cost. The sparse coefficient/carry
regression is additional finite evidence; it does not replace the
universal support, carry, index, or positive-witness arguments above.
No optimality claim is made.
