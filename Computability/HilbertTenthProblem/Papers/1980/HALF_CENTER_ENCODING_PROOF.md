# A shared geometric factor gives a 100-operation certificate

This note proves the system checked by
`../verification/round25_1980_half_center_certificate.py`. Starting with
the 101-operation construction in `FIXED_FOUR_ENCODING_PROOF.md`, replace

    Omega=4*lambda-2*e,
    sigma=B*lambda*q-Omega*C^2

by

    Omega=2*lambda-e,
    sigma=theta*lambda*q-Omega*C^2,             (1)
    theta=B-4, C=x+g.

Both Omega and sigma remain positive supplied unknowns with equality
tests. The admissible coefficient index is rebuilt below. No packed
bound is removed. The result has 100 operations: 55 multiplications
and 45 additions, with 34 positive unknowns and 22 equations. Fixed
numerals are free; the three set-dependent parameters remain V,H,L.

The new coefficient produces a smaller target value. Pairing ordinary
equations recovers the exact zero test, and putting the special target
first ensures its incoming carry is zero. The arithmetic saving comes
from using theta*lambda in both the geometric equation and the offset
in (1). These changes are proved together, rather than asserting that
arbitrary witnesses for the previous index remain valid.

## Primitive rows and the new ordering of targets

Compile the represented polynomial system into the primitive circuits
of `FIXED_FOUR_ENCODING_PROOF.md`. Repeated operands are given distinct
copies; outputs are fresh coordinates, distinct from delta. For each
primitive multiplication, addition, copy, final equality, or zero row

    F=XY-W*delta,
    F=(X+Y-W)*delta,
    F=(X-Y)*delta,
    F=X*delta,

include both F and -F among the ordinary rows. Omit trivial identical
equalities as before. Replace each unit gate X=1 by the two rows

    F_unit,1=X*delta-delta^2,
    F_unit,2=X*delta-X^2.                       (2)

These two rows are not paired with their negatives. Include the
unpaired guard F_guard=u*delta-x^2 with a fresh coordinate u.
For every ordinary row use the target

    G=2F+delta^2.                              (3)

Put the special target G_special=delta^2 FIRST in the list of targets.
At delta=1 and a genuine circuit solution, every F in this list is
zero, including both rows (2). Choose u=x^2 for the guard.

After division by the coefficient of the corresponding monomial in
C(T)^2, all target coefficients lie in {-2,-1,0,1}. The paired rows
have only distinct-coordinate cross terms, with divided coefficients
plus or minus one, and their added delta^2 has coefficient one. The
first unit target is 2X*delta-delta^2. The second is
2X*delta-2X^2+delta^2. The guard has the same coefficient pattern.
Thus no target needs a coefficient outside this alphabet, and the
special target has coefficient one.

## Fixed index and support

Use the dynamic support of `FIXED_FOUR_ENCODING_PROOF.md`, now for
this finite list of circuit coordinates and targets. In its notation,

    v_i=3^i, 0<=i<m, with delta at v_0=1,
    M=3^(m-1), d=4M+1,
    t_j=(s+1)d+2M+j*d, 0<=j<s,
    t_last=2s*d+2M, K=t_last+1,
    L a power of two with L>3K+2.

The input x has weight zero. The special target is at t_0, and
ordinary targets follow it. Include dummy coordinate positions t_j
in the indicator polynomial as before. Distinct monomial weights,
disjoint row intervals, and 2t_0-2M>t_last give the same exact target
identity and exclude every dummy contribution:

    [T^t_j]D(T)C(T)^2=G_j.                     (4)

Define

    ell_0(T)=sum_i T^v_i+sum_j T^t_j,
    e_0(T)=2*sum_(0<=j<K) T^j+D(T),
    V=ell_0(4)+e_0(4)*4^L.

The digits of e_0 are in {0,1,2,3}, with unit digit two. Let
c_*=m+s+1 count all available code coordinates, including the input,
and choose a power of two H with the unchanged sufficient bound

    H>max(2*4^(2L+1),4^(t_last+3)*4*c_*^2,3L,16). (5)

All these choices depend only on the represented system, not on its
queried input. They define the admissible triple (V,H,L).

The special-first ordering has a useful stronger property. Its only
D coefficient is +1 at t_0-2. Every later row has all its D support
above t_0, since t_1-2M=t_0+d-2M>t_0. Therefore every coefficient of
D(T)C(T)^2 up to and including t_0 is nonnegative. After coordinate
decoding, its coefficients in this region are smaller than B. It
follows that there is no incoming carry at the first target t_0.
This property does not assume delta=1 or any ordinary equation.

## Preliminary bounds and the unchanged Pell bootstrap

Write Y_code=ell+e*q, B=H*b^2, and n=q^8. Retain all the geometric,
packed-congruence, and bound equations

    b=x+beta, lambda*(B-1)=q^2-1, theta+4=B,
    Y_code=V+t*theta, Y_code+alpha=q^2,

and the unchanged packing

    S=g+q^2*(Y_code+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).                  (6)

The bound still gives e<q and ell<q^2. Geometry and (5) give
q>4b>=8 and 3L<=B<=n. Since Omega is a positive integer, (1) gives

    C^2<theta*lambda*q<B*lambda*q<3q^3<q^4.

Hence g<C<q^2 and 0<sigma<q^4. The mask Tplus and all its preliminary
borrow estimates are unchanged. Thus

    0<S<n, 0<Tplus<=n,
    n<=r<=2n^3-2n^2.

These are exactly the hypotheses used by the common-witness Pell
proof. No internal coefficient test has been used. That proof yields
the powers of two b,B,q, the identity q=B^L, and
n^2 dividing binom(2r,r). It applies to the present index because
L>=2 and 3L<=B<=n<=r, as required there.

Now lambda>q and e<q imply Omega=2lambda-e>lambda. Positivity in
(1) strengthens the bound to

    C^2<theta*q<Bq<q^2,                        (7)

so g<C<q before either code is decoded. The prior argument required
only C<q at this point; its stronger numerical factor one-half was
not needed for either mask decoding or coefficient bounds.

## Canonical codes and the modified high window

The first two masks, Y_code, its congruence, and its upper bound are
unchanged. Applying the borrow removal and base-four evaluation proof
gives

    Y_code=ell_0(B)+e_0(B)*q,
    ell=ell_0(B)+a_alias*q, e=e_0(B)-a_alias,
    0<=a_alias<e_0(B).                         (8)

By (7) the first mask decodes g using the low indicator ell_0.
The unit digit of g is zero, the unit digit of C is x, and every
decoded coordinate is nonnegative and smaller than b. Dummy digits
are still allowed only at row positions. In particular

    e,C<B^K, e*C^2<q,
    A_C=C(1)^2<(c_*b)^2.

Moreover g>0 and x>0 imply C(1)>=2, so A_C>=4. This observation
precedes the recovery of delta and holds even if the nonzero digit
of g is a dummy coordinate.

Let J_C=2A_C and write

    2lambda*C^2=qV_1+V_0, 0<=V_0<q.

Its displayed polynomial coefficients are at most J_C<B/4, so they
are its base-B digits. At positions L through L+K they all equal
J_C, by L>3K+2. Dividing (1) exactly by q gives

    floor(sigma/q)=theta*lambda-V_1+epsilon,
    epsilon=floor((e*C^2-V_0)/q) in {-1,0}.

Every digit of theta*lambda is B-4 through position 2L-1. In the
window at issue, subtracting V_1 and adding epsilon creates no
borrow: the unit result B-4-J_C+epsilon is positive, as are all
subsequent digits. Thus the digit of sigma at L is
B-4-J_C+epsilon, and at L+1 through L+K it is B-4-J_C.

The high part of the third mask is X=(B-4)*a_alias<B^(K+1).
No binary overlap bounds every digit of X by

    J_C+4=2A_C+4<=4A_C.

If F_X is its digit polynomial, F_X(4) is divisible by B-4. Bound
(5), exactly as in the predecessor, gives

    0<=F_X(4)<=4A_C*(4^(K+1)-1)/3<B/12<B-4.

Consequently F_X(4)=0, then X=0 and a_alias=0. Both supplied codes
are canonical. The unchanged bound (5) is sufficient; no larger H
is required for the new high window.

## Low carries and exact circuit recovery

After (8) has been made canonical, the raw coefficients of sigma
below K are those of D(T)C(T)^2. The offset theta*lambda*q begins
at L>K; the omitted baseline tail begins at K. Every such raw
coefficient has absolute value at most 2A_C<B/4. All incoming
carries are therefore zero or minus one.

At an ordinary target, let v=2F+delta^2 and let epsilon be its
incoming carry. The binary mask B-4 permits exactly the digits
0,1,2,3. Because |v|<B/4, that mask is equivalent to

    0<=v+epsilon<=3.                           (9)

A negative value would normalize to a digit greater than three.
There is no incoming carry at the first, special target, by the
support argument above. It therefore gives 0<=delta^2<=3 and hence
delta in {0,1}. If delta=0, the guard has v=-2x^2<0, which cannot
pass (9). Since x is positive, delta=1.

At delta=1, condition (9) for an ordinary row is
0<=2F+1+epsilon<=3. For either epsilon in {-1,0}, this holds exactly
when the integer F lies in {0,1}. Paired rows F and -F therefore
force F=0. For a unit coordinate X, rows (2) give

    X-1 in {0,1}, X-X^2 in {0,1}.

The first permits X=1 or 2, while the second permits X=0 or 1;
thus X=1. The unpaired guard need not force u=x^2 for sufficiency:
its only purpose is to exclude delta=0, and u is absent from the
original circuit. All circuit gates and final equalities have now
been recovered exactly at the queried input x. The low coordinate
tests are automatic because D starts above their positions.

## Necessity and all positive witnesses

Given a solution of the original system, take its circuit values,
delta=1, and u=x^2, with zero dummy coordinates. Every ordinary F,
including both unit rows, is zero. Choose a power-of-two b larger
than every coordinate and take the canonical codes and q=B^L.
The first two masks and their positive witnesses are unchanged;
e_0 has unit digit two and the positive delta digit makes g>0.

One has Omega=2lambda-e>lambda>0. Also 2C^2<q<=theta*q from
C<B^K, L>3K+2, and B>16. Since Omega<2lambda,

    sigma=lambda*(theta*q-2C^2)+e*C^2>0.

The special target has raw coefficient one and incoming carry zero.
Every ordinary target also has raw coefficient one; its actual digit
is zero or one, both allowed by B-4. The low coordinate positions
have digit zero. Thus all three masks hold and the packed Kummer
argument supplies n^2 dividing binom(2r,r), with the preliminary
ranges proved above. The complete positive Pell witness construction
of `PELL_COMMON_WITNESS_PROOF.md` then applies to this newly chosen r.
Every final unknown has the required positive integer value.

## Exact arithmetic saving and source equations

The predecessor uses eight instructions for the relevant shared
quantities:

    L2=lambda+q^2, Lam=B*lambda, R2=Lam+1,
    zl=4*lambda, twice_e=2*e, t2=zl-twice_e,
    Tcoef=L2-zl, P2=Lam*q.

The new certificate uses seven:

    theta_lambda=theta*lambda,
    twice_lambda=2*lambda,
    Tcoef=theta_lambda+1,
    three_lambda=twice_lambda+lambda,
    R2=Tcoef+three_lambda,
    t2=twice_lambda-e,
    P2=theta_lambda*q.

Test q^2=R2 and t2=Omega. With theta+4=B, the former is precisely
lambda*(B-1)=q^2-1. All other arithmetic instructions are retained,
including S3=P2-t2*C^2 and the original packed bound. The replacement
has three multiplications and four additions, compared with four
multiplications and four additions. It saves exactly one operation.

The checker verifies all 100 primitive instructions and all 22 source
residuals. It retains the usual geometric source equation; its new
test differs by minus lambda times the theta+4=B residual. The packed
formula and positive-sigma source equation use theta explicitly, so
their residuals need no geometric correction. The signed Pell and
second-exponent corrections are checked exactly as before. No source
Pell equation changes, and no arithmetic saving is inferred merely
from a macro notation or an unchecked equality.
