# A unit coefficient baseline gives 98 operations

This note proves the system checked by
`../verification/round27_1980_unit_center_certificate.py`. It starts
from the 99-operation composition in `COMPOSED_99_PROOF.md` and changes
only the coefficient code, its positive coefficient, and the resulting
packed index. Replace

    Omega=2lambda-e

by

    Omega=lambda-e>0,
    sigma=theta*lambda*q-Omega*C^2>0.          (1)

The offset, geometric equation, packed upper bound, and every Pell
equation are retained. The fixed index is rebuilt with coefficient
digits centered at one. The result has 98 operations: 55
multiplications and 43 additions, with 34 positive unknowns and 22
equations. Fixed numerals are free, and the three fixed index
parameters remain `(V,H,Tindex)`, where `Tindex=psi_4(L)`.

## Remove negative square coefficients without weakening the guard

Keep the paired primitive multiplication, addition, copy, final
equality, and zero rows of `HALF_CENTER_ENCODING_PROOF.md`. Operands
in a multiplication or addition are distinct, outputs are fresh, and
all circuit coordinates are distinct from delta. Each such row F
and its negative have targets `2F+delta^2`.

For a unit gate X=1, introduce a fresh nonnegative coordinate X'.
Include the paired copy rows

    (X-X')delta,       (X'-X)delta,

and the two unpaired rows

    F_unit,1=X*delta-delta^2,
    F_unit,2=X*delta-X*X'.                     (2)

All four use targets `2F+delta^2`. The product XX' is a product of
distinct coordinates, so its divided target coefficient is -1,
rather than the -2 produced by the square X^2 in the predecessor.

Use a fresh guard coordinate u, but give it the direct target

    G_guard=2u*delta-x^2+delta^2.               (3)

This target is not asserted to be `2F+delta^2` for an integer
polynomial F. Its role is solely to exclude delta=0. In particular,
do not replace x^2 by a copied product: a copy equation homogenized
by delta would not constrain that copy when delta=0.

Keep the special target `G_special=delta^2` FIRST in the target list.
Every target coefficient, divided by its monomial coefficient in
C(T)^2, now lies in

    {-1,0,1}.                                 (4)

Paired primitive rows have cross-term quotients plus or minus one
and a delta^2 coefficient one. The first unit target has quotients
one and minus one. The second has cross-term quotients one and
minus one and delta^2 coefficient one. The direct guard has
cross-term quotient one, x^2 coefficient minus one, and delta^2
coefficient one. Thus every indicated division is integral.

## Rebuild the admissible index

Apply the full dynamic support construction of
`HALF_CENTER_ENCODING_PROOF.md` to this new finite list, including
all added unit-copy coordinates and rows. With m positive-weight
coordinates, s targets, and input x at weight zero, use

    v_i=3^i (0<=i<m), delta at v_0=1,
    M=3^(m-1), d_0=4M+1,
    t_j=(s+1)d_0+2M+j*d_0 (0<=j<s),
    t_last=2s*d_0+2M, K=t_last+1,
    L a power of two with L>3K+2.

The special target is at t_0. Include dummy coordinates at all
target positions. The complementary coefficient polynomial D(T)
satisfies the exact target identities

    [T^t_j]D(T)C(T)^2=G_j.

Monomial uniqueness, row separation, and the dummy-coordinate bound
are unchanged. In particular, (4) is also the coefficient alphabet
of D, its support is above every low variable position and below K,
and its sole contribution through t_0 is +T^(t_0-2).

Define the new code by

    ell_0(T)=sum_i T^v_i+sum_j T^t_j,
    e_0(T)=sum_(0<=j<K) T^j+D(T),
    V=ell_0(4)+e_0(4)*4^L.                     (5)

Every e_0 digit lies in {0,1,2}, hence below four. Its unit digit is
one, so it is positive. Put c_*=m+s+1 and choose a power of two

    H>max(2*4^(2L+1),4^(t_last+3)*4*c_*^2,3L,16). (6)

Finally supply `Tindex=psi_4(L)`. These rules define the admissible
triple `(V,H,Tindex)` from the represented system independently of
the queried positive input. The underlying L is not an additional
system input. Both V and H are rebuilt from the new coordinates,
target list, and baseline; they are not retained from the old index.

## Preliminary bounds and the unchanged Pell proof

Retain B=Hb^2, C=x+g, n=q^8 and all the equations

    b=x+beta, lambda*(B-1)=q^2-1, theta+4=B,
    S2=ell+e*q=V+t*theta, S2+alpha=q^2,
    S=g+q^2*(S2+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).

All supplied unknowns, including Omega and sigma in (1), remain
positive. The packed upper bound gives e<q and ell<q^2. Geometry
and (6) give B<=q^2, q>4b>=8, and 3L<=B<=n. Since Omega>=1,

    C^2<theta*lambda*q<B*lambda*q<3q^3<q^4.

Therefore g<C<q^2 and 0<sigma<q^4. The offset and every packed mask
have the same preliminary bounds as before; in particular the
possible first-block borrow is fewer than b while theta*lambda>b.
It follows that

    0<S<n, 0<Tplus<=n,
    n<=r<=2n^3-2n^2<2n^3.                      (7)

These conclusions are direct consequences of positivity and the
retained bounds; they do not compare the new sigma with an old
witness value. Thus n,r>=64, U=w*n^2 and Y=s*n^2 are at least n^2,
UY>=n^4>r+1, and a=Y(U+1)>n^4>2r+1. The positive interval and first
index equation give c>2r+1. Also L>=2 and 3L<=B<=n<=r.

Every preliminary hypothesis of the doubled-index and common-witness
Pell arguments in `COMPOSED_99_PROOF.md` has therefore been checked.
Their source equations are unchanged. In their original order they
recover the exact main indices, then U=4^(2r+1), the underlying L
from Tindex=psi_4(L), and finally

    q=B^L, b,B,q powers of two,
    n^2 | binom(2r,r).                         (8)

The binomial rounding and second exponent bounds depend on (7),
U,Y and the displayed L bound; they do not use any internal target
coefficient. Thus this application precedes code decoding.

The new post-Pell estimate needs one additional observation. Since
L>=2 and B>16,

    lambda>=B^(2L-1)>=Bq>2q,
    q=B^L>=B^2>2B.

Consequently e<q gives Omega=lambda-e>lambda/2. Positivity in (1)
therefore yields

    C^2<2theta*q<2Bq<q^2, hence g<C<q.         (9)

This supplies exactly the code range needed by the first mask.

## Canonical codes and the smaller high plateau

The first two masks and their geometry, congruence, and upper bound
are unchanged. The base-four evaluation lemma permits all digits
in {0,1,2}; it does not require the digit three or positive digits
at every position. The borrow removal and canonical split therefore
give

    S2=ell_0(B)+e_0(B)q,
    ell=ell_0(B)+a_alias*q, e=e_0(B)-a_alias,
    0<=a_alias<e_0(B).

Using (9), the first mask decodes every coordinate below b, with
input x in the unit position and dummy coordinates only at row
positions. In particular

    e,C<B^K, e*C^2<q,
    A_C=C(1)^2<(c_*b)^2.

As before, g>0 and x>0 imply C(1)>=2 and A_C>=4 before delta is
identified. Set J_C=A_C and divide

    lambda*C^2=qV_1+V_0, 0<=V_0<q.

All its polynomial coefficients are at most J_C<B/4, so they are
actual base-B digits. The digits at L through L+K form the constant
plateau J_C. Equation (1) gives

    floor(sigma/q)=theta*lambda-V_1+epsilon,
    epsilon=floor((e*C^2-V_0)/q) in {-1,0}.

Because theta*lambda has all digits B-4 in this window, there is no
borrow. The sigma digit at L is B-4-J_C+epsilon; the digits at
L+1 through L+K are B-4-J_C. Thus the high part of the third mask,
X=(B-4)*a_alias, has every digit bounded by

    J_C+4=A_C+4<=4A_C.

For its digit polynomial F_X, evaluation at four gives

    B-4 | F_X(4),
    0<=F_X(4)<=4A_C*(4^(K+1)-1)/3<B/12<B-4.

Bound (6) supplies the strict inequality, with no enlargement from
the previous construction. Thus X=0 and a_alias=0. Both codes are
canonical before any circuit equation is tested.

## Recover the special coordinate before enforcing copies

From (5), the raw coefficients of sigma below K are those of
D(T)C(T)^2. Each has absolute value at most A_C<B/4; hence all
incoming carries are zero or minus one. For a target raw value v,
the mask B-4 is equivalent to

    0<=v+epsilon<=3, epsilon in {-1,0}.         (10)

The special-first argument is unchanged: its single positive D
term precedes all other row intervals, all raw coefficients through
its target are nonnegative and below B, and its incoming carry is
zero. Its raw value delta^2 therefore forces delta in {0,1}.

At delta=0, the direct guard (3) has raw value -x^2<0. Neither
incoming carry can make it pass (10). Therefore delta=1, without
using any copy equation or assuming another decoded coordinate
positive.

Now every ordinary target `2F+delta^2` passes exactly when F is
zero or one. Paired rows F,-F force F=0. In particular the paired
unit-copy rows give X'=X. Substitution into (2) gives

    X-1 in {0,1}, X-X^2 in {0,1},

so X=1. All original circuit gates, constants and final equalities
are recovered exactly. The direct guard is not treated as an
original equation; its coordinate u is auxiliary and its only
sufficiency role was to exclude delta=0. This proves the represented
system at the actual queried input x.

## Necessity and every positive final witness

Given a solution of the original system, take its circuit values,
delta=1, every unit copy X'=X=1, and zero dummy coordinates. Set

    u=ceil(x^2/2).

The direct guard then has raw target value

    2u-x^2+1=1+(x^2 mod2),

which is one or two. Either value remains allowed after an incoming
carry of zero or minus one. All ordinary F values are zero, giving
raw value one, and the first special target has value one with
incoming carry zero. The low variable tests vanish by support.

Choose a power-of-two b larger than every coordinate, and take the
canonical codes, B=Hb^2, q=B^L, and n=q^8. The unit digit of e_0 is
one and the delta digit makes g>0. The canonical packed bound and
congruence supply positive alpha and t, as before: the polynomial
ell_0(T)+e_0(T)T^L is nonconstant with nonnegative coefficients, so
its value at B is strictly larger than its value at four. Also
Omega=lambda-e>0. Finally C^2<q<=theta*q implies

    sigma=lambda*(theta*q-C^2)+e*C^2>0.

All three masks hold. The newly determined packed r has (7), and
their Kummer argument gives (8). The complete positive Pell witness
construction of `COMPOSED_99_PROOF.md` applies: choose
U=4^(2r+1), then Y=floor((U+1)^(2r)/U^r), the main and first Pell
coordinates and positive interval witnesses, the second coordinates
at L, and the positive exponent quotients. Choose the doubled-index
auxiliary witnesses last at the new main parameter. Its positive
Delta uses the new fixed Tindex=psi_4(L), and its auxiliary f,i,o,j
construction changes no coding value. No Pell source equation or
required bound has changed. Thus all 34 final unknowns receive
positive integer values.

## Six shared instructions instead of seven

The preceding seven-instruction block was

    tl=theta*lambda, twice_lambda=2*lambda,
    Tcoef=tl+1, three_lambda=twice_lambda+lambda,
    R2=Tcoef+three_lambda,
    t2=twice_lambda-e, P2=tl*q.

Replace it by

    tl=theta*lambda, Tcoef=tl+1,
    three_lambda=3*lambda, R2=Tcoef+three_lambda,
    t2=lambda-e, P2=tl*q.

Both blocks have three multiplications. The new block has three
additions, rather than four. The tests q^2=R2 and theta+4=B still
give exactly lambda*(B-1)=q^2-1. The remaining coding and Pell
instructions are retained. Therefore 99 decreases to 98 by one
addition, without increasing the unknown or equation count.

The checker verifies all 98 primitive instructions, the complete
source polynomials, and the same three exact corrections as the
99-operation certificate. Only the packed r equation and the sigma
and Omega equations change. Its finite target and guard regressions
are explicitly separate from the universal support, admissibility,
carry, and positive-witness proof given here. No optimality claim is
made.
