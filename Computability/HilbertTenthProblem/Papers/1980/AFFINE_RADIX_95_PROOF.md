# Affine radix and two independent padding carries: 95 operations

This note gives the full coefficient construction and equivalence proof
for a system with 95 operations: 51 multiplications and 44 additions.
It starts from the 34-positive-unknown, 22-equation system in
`COMBINED_BOUND_96_PROOF.md`, retaining its combined positive gap

    ell+e+alpha=q.

Replace the radix definition and the first packed mask by

    H=H0+1, B=H+b,                            (1)
    q^2-1-b*ell,

where H0 is a sufficiently large fixed power of two. The supplied
fixed index still has three components (V,H,Tindex), chosen below.
H0 is not an additional supplied parameter: it is the fixed integer
H-1. The other positive unknowns and the Pell equations are unchanged.
Fixed numerals and equality tests have no cost.

The exact arithmetic change is small, but its interpretation requires
a new coefficient construction. After B has been proved a power of
two, the first mask forbids one fixed bit in every coordinate digit.
Three nonnegative coordinates with that bit clear represent an
arbitrary nonnegative circuit value. Three-digit target windows and
reset positions make paired zero equations exact. Two deliberately
different padding carries then rule out all nonunit homogeneous
scalings. Independent reviews of the complete proof and the full
source-equation certificate pass.

## 1. Logical values, physical coordinates, and the homogeneous unit

Compile the represented finite Diophantine system into a circuit over
nonnegative integers, with actual positive input x, addition,
multiplication, zero, and one. As usual, signed integer witnesses can
first be represented by differences of nonnegative witnesses. Use a
homogeneous coordinate delta, retained as one physical coordinate.
Every other logical non-input circuit coordinate is a sum of three
distinct nonnegative physical coordinates. Different logical
coordinates use disjoint groups of physical coordinates. The input x
is not split and has weight zero.

This splitting preserves arbitrary witnesses. Given a nonnegative
integer z, if its H0 bit is zero, use the triple (z,0,0). If its H0 bit
is one, use

    (z-H0, H0/2, H0/2).                       (2)

All three entries are nonnegative and have the H0 bit zero. Once B
is larger than these finitely many entries, they are base-B digits.
The chosen entries depend on z and H0, not on how much larger B is
subsequently chosen. In the reverse direction, the sum of three
decoded physical digits is simply a nonnegative logical value; no
additional bound on that sum is required.

Use fresh outputs and fresh square-difference copies whenever a
product would have repeated logical factors. For multiplication,
addition, and zero equations use respectively

    2XY-2W*delta=0,
    2(X+Y-W)*delta=0,
    2X*delta=0.                               (3)

A copy X'=X is imposed by

    X'^2-X^2=0.                               (4)

Nonnegativity makes (4) exact. A constant-one occurrence can use
delta or a fresh logical copy of delta. Whenever its use in (3)
would produce delta*delta, use a fresh copy (4) instead. Repeated
gate operands are copied as well. Thus every product in (3) has
distinct logical factors, and every such pair expands into distinct
physical factors. Final equalities may use square differences or
distinct-factor products with delta. Include both F and -F for every
zero equation F=0.

Introduce logical coordinates X,Y,Z,delta',u with disjoint physical
groups, distinct from all other circuit coordinates. Include both
signs of the five normalization rows

    X^2-x^2=0, Y^2-x^2=0, Z^2-x^2=0,
    delta'^2-delta^2=0,
    2xX-2delta*delta'-2u*delta=0.              (5)

Once their exact zero tests are decoded, these equations give

    X=Y=Z=x, delta'=delta,
    x^2=delta^2+u*delta.                       (6)

Since x>0, (6) implies delta>0 and delta<=x. Conversely, every
positive x admits the nonnegative assignment

    delta=delta'=1, X=Y=Z=x, u=x^2-1.          (7)

Finally add three unpaired targets whose raw polynomial is delta^2.
The first is an ordinary unit test. The second and third receive
different padding in their preceding positions. Put these three
targets last, in that order.

Expand every logical row as a quadratic polynomial in the physical
coordinates and x. Divide a square coefficient by one and a
distinct-coordinate product coefficient by two. Every divided
coefficient belongs to {-1,0,1}. In particular, a square of a
three-coordinate sum has diagonal coefficients one and cross
coefficients two. Disjoint groups and the fresh-copy convention
prevent coefficients from adding at the same physical monomial in
(3)--(5). The three unpaired squares have divided coefficient one.
The number of logical rows and physical coordinates affects the
fixed integer index, not the number of unknowns in the final system.

## 2. Support layout, three-digit windows, and fixed constants

Let m be the number of true non-input physical coordinates, including
the unsplit delta. Assign distinct weights

    v_i=6*3^i, 0<=i<m,
    M=6*3^(m-1).

The input has weight zero. Every quadratic monomial weight is a
multiple of six, at most 2M, and determines its unordered pair of
physical coordinates, including products with x and squares. This
follows from the base-three digits after division by six.

Let s count all targets, including both signs of every zero equation
and the three final unit tests. Define

    d0=4M+6,
    t_j=(s+1)d0+2M+j*d0, 0<=j<s,
    t_last=2s*d0+2M, K=t_last+3.              (8)

All target positions are multiples of six. Write t5=t_(s-2) and
t7=t_(s-1) for the second and third unit targets. For each target
polynomial G_j, put its divided coefficient a for monomial weight
w at exponent t_j-w in D_main(T). The intervals [t_j-2M,t_j] are
disjoint. At any target t_j, multiplying by the physical coordinate
polynomial squared therefore recovers exactly G_j.

Add one reset term for every target:

    D_reset(T)=sum_j T^(t_j-3).               (9)

If P(X) denotes the three physical-coordinate indices belonging to
logical X, define

    D5(T)=T^(t5-1)
          +sum_(p in P(X) union P(Y)) T^(t5-1-v_p),
    D7(T)=T^(t7-1)
          +sum_(p in P(X) union P(Y) union P(Z))
                                               T^(t7-1-v_p),
    D(T)=D_main(T)+D_reset(T)+D5(T)+D7(T).     (10)

The exponents in the three types of terms are congruent to zero,
three, and five modulo six. Within either extra padding polynomial
they are distinct. The two padding intervals are disjoint because
t7-t5=d0>M. Thus every coefficient of D still lies in {-1,0,1}.
Every D exponent is positive, greater than M, and below K.

Permit a dummy physical digit at each of the three tested positions
t_j,t_j+1,t_j+2. Set

    ell_0(T)=sum_i T^v_i
                     +sum_j(T^t_j+T^(t_j+1)+T^(t_j+2)),
    e_0(T)=sum_(0<=h<K) T^h+D(T).             (11)

The digits of ell_0 belong to {0,1}, those of e_0 belong to {0,1,2},
and the unit digit of e_0 is one. Let c_*=1+m+3s count the input,
the true physical coordinates, and the dummies. Let

    D1=sum_h |[T^h]D(T)|.

Choose a power of two L>3K+2. Only after this complete layout has
been fixed, choose a power of two H0 such that

    H0>max(2*4^(2L+1), 128*max(1,D1)*c_*^2, 3L, 1024).
                                                        (12)
    H=H0+1,
    V=ell_0(4)+e_0(4)*4^L,
    Tindex=psi_4(L).                          (13)

All these choices are independent of the queried input x. In
particular, H need not itself be a power of two.

For arbitrary decoded dummy values, no dummy contributes to
D(T)C(T)^2 through the last tested digit t_last+2. The least D
exponent is at least t_0-2M, the least dummy weight is t_0, and

    2t_0-2M>t_last+2.                         (14)

Consequently the residue-class analysis below concerns only the
true coordinate weights, which are all zero modulo six. This
exclusion is essential because some dummy weights are not zero
modulo six.

The same spacing gives several exact isolation facts. At t_j-3,
the reset term belonging to j contributes x^2, and no other reset
can contribute: any other required monomial weight would have
absolute value at least d0>2M. At t5-1 the extra terms contribute
exactly x^2+2xX+2xY; at t7-1 they contribute exactly
x^2+2xX+2xY+2xZ. At every other target's preceding position the
extra contribution is zero. Here monomial uniqueness identifies
each contribution, and distinct target bands are separated by
more than 4M. Other parts of D are excluded by their residue classes.

## 3. Preliminary bounds and the unchanged Pell argument

The relevant source definitions and equations are

    C=x+g, b=x+beta, B=H+b, theta=B-4,
    lambda*(B-1)=q^2-1,
    S2=ell+e*q=V+t*theta, ell+e+alpha=q,
    Omega=lambda-e>0, sigma=Omega*(q-C^2)>0,
    n=q^8,
    S=g+q^2*(S2+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-b*ell
                                      +theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).                (15)

All supplied unknowns, including alpha, beta, Omega, and sigma, are
positive integers. Before using any Pell conclusion or any decoded
coefficient row, their positivity gives

    ell,e<q, S2<q^2, C^2<q, g<q,
    0<sigma<lambda*q<q^3.                    (16)

For S2, the combined bound gives the explicit estimate
S2<=(q-1)^2. Geometry gives B<=q^2. Since b>=2 and H>1024,
we have q>=6, b<B<n, and 3L<=B<=n. Moreover

    theta*lambda>=B-4=H+b-4>b.

Using integer gaps in (16) gives 0<S<q^7<n. For example,
S<=q-1+q^2(q^2-1)+q^4(q^3-1)<q^7. The other packed number satisfies

    Tplus>q^2*theta*lambda-b*ell
          >b*q^2-b*q>0,
    Tplus<q^4*(1+theta*ell)<B*q^5<=q^7<n.     (17)

The upper bound uses 1+theta*lambda<q^2 and
1+theta*ell<=1+(B-4)(q-1)<Bq. Consequently

    n<=n^2-1<=r<2n^3.                        (18)

These are precisely the packing and growth hypotheses needed in
the unchanged Pell block. To make the proof order explicit, put

    U=w*n^2, Y_pell=s_pell*n^2,
    a=Y_pell*(U+1), A=a+4, D_pell=A^2-1,
    P=2U*Y_pell^2+1, J=2r+1.

The subscripts distinguish Pell coordinates from encoded logical
coordinates. Equations (18) give U,Y_pell>=n^2,
U*Y_pell>=n^4>r+1, and a>n^4>J. The positive interval and first
index equation imply c>J. Classification of the main and first
norms, together with P>A, gives preliminary main index at least
r+2. Hence c>A*D_pell^2, exactly as in
`COMPOSED_97_PROOF.md` and `PELL_RELAXED_AUXILIARY_PROOF.md`.

The retained relaxed norm

    (i*c^2)^2=D_pell*(f^2-1)

therefore has the required fundamental-unit and divisibility
hypotheses. The doubled signed-index argument fixes
c=psi_A(J), d=chi_A(J). The first-index and ratio argument then
gives Y_pell>=U^r and a>U^(r+1), before either exponent relation
is used. The common-witness exponent equation gives U=4^J.
The unchanged fixed congruence kappa=Tindex+Delta*a determines
the second index as L, and its exponent equation gives q=B^L.
All exponent-size inequalities follow from (18) and
3L<=B<=n<=r, as in the cited proofs.

Since n^2 divides U=4^J, q is a power of two; q=B^L makes B a
power of two. It follows from B>H0+1 that B>=2H0. There is no
claim that b or H is a power of two. No Pell step needs that claim.
The retained upper ratio and binomial fractional-part argument gives

    n^2 divides binom(2r,r).                  (19)

This entire deduction precedes canonical decoding, the internal
equations, and the conclusion delta=1.

## 4. Canonical decoding and the single forbidden bit

After the Pell conclusions, b<B<q and ell<q. Hence

    q^2-1-b*ell>0.                           (20)

Thus T=Tplus-1 has the exact block expansion

    T=(q^2-1-b*ell)+q^2*theta*lambda
                                  +q^4*theta*ell.

The three blocks have widths (2,2,4) in radix q. Apply the binary
no-carry packing lemma to (15), (18), and (19). It gives

    g & (q^2-1-b*ell)=0,
    S2 & theta*lambda=0,
    sigma & theta*ell=0.                     (21)

The ampersand denotes bitwise intersection, used only in the
interpretation proof of the polynomial system.

Because q=B^L and theta=B-4, the middle mask bounds each base-B
digit of S2 by three. If F(T) is its digit polynomial, then
F(B)=S2 and deg F<2L. The congruence in (15) gives
F(4)=V modulo B-4. Both F(4) and V are below 4^(2L), and (12)
makes B-4 larger than their possible difference. Thus F(4)=V.
Uniqueness of base-four expansion gives

    S2=ell_0(B)+e_0(B)*q.

Both ell and e are below q by (16), and both fixed codes are below
B^K<q. Quotient and remainder uniqueness therefore gives

    ell=ell_0(B), e=e_0(B).                   (22)

This eliminates the quotient alias without any quadratic digit
bound. In particular, no bound of the form physical digit<b is
being inferred from the changed first mask.

In base B, the integer q^2-1 has every digit B-1. Subtracting
b*ell_0(B) causes no borrow because ell_0 has digits zero or one
and b<B. At indicator positions the first mask has digit

    B-1-b=H-1=H0,

and at all other positions it has digit B-1. Because B and H0 are
powers of two with H0<B, the first mask in (21) says exactly that
each physical digit of g has its H0 bit zero, and that digits away
from the indicator support vanish. All digits are nonnegative and
less than B. The unit position is outside that support, so g has
unit digit zero. Since x<b<B, the unit coordinate of C=x+g is
exactly the queried x. Write

    C(T)=x+sum_i z_i*T^v_i
             +sum_j(d_j*T^t_j+d'_j*T^(t_j+1)+d''_j*T^(t_j+2)).

Every physical digit, including delta, is below B. The actual
input x is below B as well. Hence, for A_C=C(1)^2,

    A_C<(c_*B)^2<B^3/64.                    (23)

The last inequality follows from (12) and B>=2H0. Every raw
coefficient of D(T)C(T)^2 has absolute value at most A_C: each
exponent of D selects a distinct nonnegative coefficient of C(T)^2,
and every D coefficient has absolute value at most one.

Also e,C<B^K, so L>3K+2 gives e*C^2<q. Through position K-1,
the raw signed coefficients of sigma are exactly those of
D(T)C(T)^2. Indeed,

    sigma=(lambda-e)*q+(e-lambda)*C^2,

and the first summand starts at L, whereas e_0(T)-lambda's
base-B coefficient polynomial agrees with D(T) below K. Terms
starting at K or L cannot affect lower digits. These facts identify
the actual low digits even though individual raw coefficients can
be negative.

## 5. Reset padding and exact three-digit zero tests

Use the signed carry recursion

    h_0=0,
    h_(j+1)=floor((a_j+h_j)/B),
    digit_j=a_j+h_j-B*h_(j+1),               (24)

where a_j=[T^j]D(T)C(T)^2. It computes the low base-B digits of
the positive integer sigma. From (23), induction gives

    |h_j|<B^2/8

throughout the tested range. In fact, the induction step is bounded
by B^2/64+B/8+1<B^2/8 for B>64.

By (14), dummies do not contribute in this range. The only possible
nonzero raw residue classes are zero, three, and five modulo six.
Classes one, two, and four are empty. Two consecutive empty
positions in classes one and two reduce a carry with magnitude
less than B^2/8 to either -1 or zero: the combined operation is
division by B^2 followed by the floor. Therefore the incoming
carry at every reset position t_j-3 belongs to {-1,0}.

By the isolation facts after (14), the raw reset coefficient is
exactly x^2. Since 1<=x<B, adding its incoming carry gives a
nonnegative number strictly below B^2. The carry to position
t_j-2 is consequently a nonnegative integer below B. That
position is empty, so the carry to position t_j-1 is exactly zero.

For every target other than t5 and t7, the raw coefficient at
t_j-1 is zero as well. It follows that its target receives zero
incoming carry. Its next two raw coefficients, at t_j+1 and
t_j+2, are zero. The three tested digits are therefore exactly
the residue of its target value G_j modulo B^3. The third mask
in (21) requires all three digits to belong to {0,1,2,3}.

For each paired zero row, |G_j|<B^3/64. A negative nonzero value
has residue modulo B^3 greater than 63B^3/64, whose top base-B
digit is greater than three. Thus it fails the mask. Both signs
have separate resets and receive zero incoming carry. They can
both pass only when G_j=0; zero passes both. Every circuit row
and every normalization row (5) is now exact, without any
assumption about delta. In particular (6) holds.

The first unpaired delta-squared target also receives zero carry.
At t5-1 and t7-1, (6) and the isolation formulas give the exact
raw coefficients 5x^2 and 7x^2, respectively. Their incoming
carries are zero. Hence their target carries are exactly

    h5=floor(5x^2/B), h7=floor(7x^2/B).       (25)

Both special targets still have raw value delta^2 and two empty
following raw positions. The three tested digits are the residues
of delta^2+h5 and delta^2+h7 modulo B^3.

## 6. The three unit tests force delta=1

The guard gives 0<delta<=x<B. Since delta is unsplit, its physical
digit bound also directly gives delta<B. Thus delta^2<B^2. The
first unit test, with zero incoming carry, implies

    delta^2=kB+s, k,s in {0,1,2,3}.           (26)

Since B is divisible by four, a square cannot have s=2 or s=3.
If s=1, (26) gives delta^2<=3B+3<B^2/16 for B>=64. Therefore
delta<B/4. The square roots of one modulo a power of two B>=8
are congruent to 1, B/2-1, B/2+1, or B-1. Only the first can
lie in (0,B/4), so delta=1.

If delta>1, the only remaining case is

    delta^2=kB, 1<=k<=3, x^2>=kB.            (27)

For c=5,7 put h_c=floor(cx^2/B). Because x<B, h_c<cB. Write

    h_c=m_c B+r_c, 0<=r_c<B.

The corresponding tested integer is
(k+m_c)B+r_c. Its value is less than (3+c)B<B^2, so there is
no reduction modulo B^3 or overflow into the third tested digit.
Acceptance therefore forces

    0<=r5,r7<=3,
    0<=m5,m7<=3-k<=2.                        (28)

The floors in (25) are not independent. With z=x^2/B,

    7h5-5h7=5*{7z}-7*{5z},
    -7<7h5-5h7<5,                           (29)

where braces denote fractional part. In particular its absolute
value is less than seven. Substituting (28), and using
|7r5-5r7|<=21, gives

    |B*(7m5-5m7)|<28.

Since B>32, the integer 7m5-5m7 is zero. Equation (28) then
forces m5=m7=0: the nonnegative solutions to 7m5=5m7 are
(m5,m7)=(5h,7h), and neither coordinate can exceed two. Thus
h5=r5<=3. But (27) gives h5=floor(5x^2/B)>=5k>=5, a
contradiction. This excludes (27), and proves delta=1.

The paired circuit equations (3)--(4), now with unit one, decode
the represented system at its actual positive input x. This proves
sufficiency for the affine-radix source system.

## 7. Necessity and all positive supplied witnesses

Given a solution of the represented system, assign its logical
circuit values and fresh copies. Use (7) for the normalization
coordinates. Split every non-input logical coordinate other than
delta into three physical coordinates by (2); keep delta=1 as
one physical coordinate. All those physical values have their H0
bit zero, including delta because H0>1. Set every dummy to zero.
Every paired target has raw value zero and all three unit targets
have raw value one.

The fixed constants (8)--(13) were chosen before this input. With
the physical assignment now fixed, choose B an arbitrarily large
power of two. Require B>H+x and B larger than every physical
coordinate. Also require every raw coefficient of D(T)C(T)^2
to have absolute value below B/4 and require 7x^2<B/4. This is
possible because those finitely many coefficients and values
are fixed while B grows without bound. Put

    b=B-H, beta=b-x>0,
    ell=ell_0(B), e=e_0(B), q=B^L, n=q^8.

The combined-code digits are at most three, so ell+e<B^K<q.
The support margin gives C^2<q, and
lambda=(q^2-1)/(B-1)>e. Thus

    alpha=q-ell-e,
    Omega=lambda-e,
    sigma=Omega*(q-C^2),
    t=(ell+e*q-V)/(B-4)

are positive integers. For t, evaluate the nonconstant polynomial
ell_0(T)+e_0(T)T^L, which has nonnegative coefficients, at B>4;
its difference from its value at four is positive and divisible
by B-4. The encoded delta=1 guarantees g>0.

The first mask in (21) holds because all physical digits have
their H0 bit zero; the second holds because the combined code
has digits at most three. For the third mask, every true variable
position lies below the least D exponent and has zero raw
coefficient and zero carry. Every paired target receives the
zero carry supplied by its reset and has raw value zero. The
plain unit target has value one. Since 7x^2<B/4, both h5 and
h7 vanish, so both special targets also have digits (1,0,0).
All three masks therefore hold. The binary packing lemma supplies
(19) for the newly determined r. Equations (16)--(18) give its
required size bounds.

Construct all positive Pell witnesses for this r exactly as in
`COMPOSED_97_PROOF.md`. In detail, choose U=4^J,
Y_pell=floor((U+1)^(2r)/U^r), then w=U/n^2,
s_pell=Y_pell/n^2, and a=Y_pell(U+1). Take the main and first
Pell coordinates at indices J and r+1, their positive interval
and first-index quotients, and the second Pell coordinates at L.
The second index uses the new fixed Tindex=psi_4(L). The retained
exponent and rounding bounds supply the positive exponential
quotients. They require B and q to be powers of two, which they
are; they do not require b or H to be powers of two.

Choose the doubled-index auxiliary exponent last as m_aux=2cJ.
Set f=chi_A(m_aux), i_old=psi_A(m_aux)/c^2>0, and
i=D_pell*i_old. The doubled-index construction gives positive
o and j. The relaxed auxiliary norm then holds and its signed
auxiliary value is unchanged. The new beta and combined-bound
alpha are positive as checked above. All 34 supplied unknowns
are positive integers, proving necessity.

## 8. Exact arithmetic change and evidence boundary

The combined-bound 96-operation schedule contains the multiplication
B=H*b and the subtraction bm1=b-1. In this system B=H+b is one
addition instead of one multiplication. Replacing bm1*ell by
b*ell preserves that multiplication and removes the subtraction
bm1=b-1. Thus the net count is

    52 multiplications +44 additions
      ->51 multiplications +44 additions =95 operations.

The number of positive unknowns and source equations remains
34 and 22. The fresh logical coordinates, their three-way splits,
three-digit windows, resets, and both extra padding patterns change
only the fixed integer index. No numeral construction is charged.
As in the preceding certificates, subtractions can each be realized
by one reversed addition equation with a free integer intermediate.

The complete arithmetic checker
`../verification/round32_1980_affine_radix_certificate.py` verifies
the new radix and first packed-mask expressions against every source residual, including
the unchanged acyclic corrections for geometry, the second exponent,
and the relaxed signed norm. All 95 instructions and 22 residuals pass.
A sparse encoding regression is useful
additional evidence for coefficient isolation and finite carries;
it does not replace the universal support, unit, Pell, or positive
witness arguments above. This is an upper-bound construction, with
no assertion that 95 is optimal.
