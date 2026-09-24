# Removing the added low offset: the 103-operation encoding

This note proves the encoding used by
`../verification/round20_1980_borrow_mask_certificate.py`. Starting from
the 104-operation system in `PELL_SHARED_RATIO_PRODUCT_PROOF.md`, replace

    S3=B lambda (1+q)-(Z lambda-2e) C^2

by

    S3=B lambda q-(Z lambda-2e) C^2.              (1)

The positive witness equality `sigma=S3` is retained. The formula
continues to have exactly the same positive-domain interpretation after
the fixed coefficient code is changed as specified below. The operation
computing `q+1` disappears, giving 103 operations: 57 multiplications
and 46 additions, with 34 positive unknowns and 22 equality tests.
All fixed numerals are supplied free.

This change requires a new fixed admissible index. It is not a claim
that arbitrary old coding witnesses remain solutions of the new system.
The construction and proof are uniform in the represented set; none of
the fixed indices depends on the queried positive input x.

## New coefficient targets, with unchanged support positions

Keep the modular Sidon coordinates and row positions of
`MODULAR_SIDON_PROOF.md`. The input x has weight zero, delta has weight
`v_0=1`, the original 58 coordinates have weights `v_1,...,v_58`, and
the additional guard coordinate u has weight `v_59`. Thus

    v_i=1+3(122i+(i^2 mod 61)), 0<=i<=59,
    v_*=21607, D_step=86429,
    t_r=158467571+r D_step, 0<=r<1832,
    t_*=316719070, K=t_*+1=316719071,
    L=2^32, 3K+2<L.

There are 1830 original homogeneous quadratic rows `F_i^h`, obtained
from the same integer row basis and padding as before. Include the
guard `u delta-x^2` as the 1831st ordinary row. For every ordinary row,
replace the former coefficient target by

    G_i=4F_i^h+delta^2.                          (2)

For the guard this means `G_guard=4(u delta-x^2)+delta^2`.
The last, special target remains `G_special=delta^2`.

For a homogeneous quadratic monomial I, let `c_I` be its coefficient
in the square of the coordinate code: it is 1 for a square and 2 for
a product of distinct coordinates. Put its coefficient in D at
position `t_i-weight(I)`, divided by `c_I`, so that

    [T^(t_i)] D(T) C(T)^2=G_i.                  (3)

These coefficients are integers. The contribution from `4F_i^h` is
divisible by both possible denominators; the added `delta^2` is a
square and has denominator 1. The special row has coefficient 1 at
position `t_special-2`.

The old support separation proves (3) exactly. Distinct quadratic
monomials have distinct weights, row intervals are disjoint, and
products involving dummy row coordinates cannot reach any row target.
The least position of D exceeds `v_*`, so all low coordinate tests
remain automatic. There are still 1893 coordinates including the
input, giving the same strict coefficient-sum bound `1900b`.

Choose a power of two `z>=2` strictly above the absolute values of
the new coefficients of D, and put `Z=2z`. Define

    ell_0(B)=sum_(i=0)^59 B^(v_i)+sum_(r=0)^1831 B^(t_r),
    e_0(B)=z sum_(j=0)^(K-1) B^j+D(B),
    V=ell_0(Z)+e_0(Z) Z^L.

Every digit of `e_0` below K lies between 1 and `Z-1`; its higher
digits vanish. Choose a power of two H satisfying the same bound
as before:

    H>max(2Z^(2L+1),4^(t_*+3) Z 1900^2,3L,16).   (4)

No enlargement of this bound is needed for the new carry argument.
The parameters Z,V,H are rebuilt from the new D and these formulas.

## The Pell bootstrap still applies

Retain the equations and positivity conditions

    B=Hb^2, lambda(B-1)=q^2-1, theta=B-Z,
    S2=ell+e q=V+t theta, S2+alpha=q^2,
    Omega=Z lambda-2e>0, sigma=S3>0,
    C=x+g, N=q^8,
    S=g+q^2(S2+q^2 S3),
    Tplus=q^2(1+theta lambda)-(b-1)ell+(B-4)ell q^4,
    R=S(N^2-N)+Tplus(N^2-1).

Here `S2` is the packed code register; the Pell interval scale
`Y=sN^2` is a different quantity.

Every pre-Pell upper bound in `POSITIVE_COEFFICIENT_BOUND_PROOF.md`
and `PELL_UNIT_SCALE_PROOF.md` remains valid, because the new positive
offset is smaller than the previous one:

    0<B lambda q<B lambda(1+q).

In particular, `S2<q^2` gives `ell<q^2` and `e<q`;
the geometric equation gives `B<=q^2`; and Omega and sigma positivity
give `C^2<B lambda q<3q^3<q^4`. Hence `g<C<q^2` and
`0<S3<q^4`. The same normalized packed masks give

    0<S<N, 0<Tplus<=N,
    N<=R<=2N^3-2N^2<2N^3.

The 104-operation Pell argument uses exactly these preliminary bounds,
not the internal coefficients of the encoding. It therefore still
recovers b as a power of two, `q=B^L`, and

    N^2 divides binom(2R,R).

Once `q=B^L` is known, `lambda>q` and `e<q` imply
`Omega>Z lambda/2`. Positivity in (1) then gives the stronger bound

    C^2 < 2Bq/Z <= Bq/2 < q^2.                 (5)

Thus `g<C<q` is available before either the input digits or the
coefficient quotient is decoded.

## Canonical packing and the possible quotient alias

The first two masks and the congruence `S2=V+t theta` are unchanged.
Their proofs in `REVERSED_PACKING_PROOF.md`, `INPUT_UNIT_PROOF.md`,
and `MODULAR_SIDON_PROOF.md` depend only on the following properties:
the displayed bounds for S2 and g, the fixed support of `ell_0`, the
digits `0<e_(0,j)<Z`, and the size bound (4). All remain true.
The same borrow-removal and base-Z uniqueness arguments give

    S2=ell_0(B)+e_0(B)q,
    ell=ell_0(B)+m q, e=e_0(B)-m,
    0<=m<e_0(B).                               (6)

Using (5), the first mask decodes the low coordinate code. Its unit
digit is exactly x, delta and all other decoded coordinates are
nonnegative integers smaller than b, and dummy coordinates may be
present only at row positions. In particular

    C<B^K,
    A_C=C(1)^2<(1900b)^2,
    0<e<B^K,
    2eC^2<q.                                  (7)

The last inequality follows from `L>3K+2`. These conclusions precede
the elimination of m; the first mask only needs the low part
`ell_0` because `g<q`.

For completeness, the modified high-window argument is given in full
in `HIGH_MASK_SINGLE_OFFSET_PROOF.md`. Its key steps are particularly
simple. Let

    J_C=Z A_C<B/4,
    V_C=Z lambda C^2=q V_1+V_0, 0<=V_0<q.

Every coefficient of the polynomial `Z lambda C^2` is at most J_C,
so its displayed coefficients are already its base-B digits. Its
digits at positions `L,...,L+K` are all J_C: this interval lies inside
the stable convolution region because `L>3K+2`. By (7), exact division
of (1) by q therefore gives

    floor(S3/q)=B lambda-V_1+epsilon,
    epsilon=floor((2eC^2-V_0)/q) in {-1,0}.

The high digit of S3 at position L is `B-J_C-1` or `B-J_C`.
At positions `L+1,...,L+K` it is exactly `B-J_C`.
Thus all these digits are at least `B-J_C-1`.

The high part of the third mask is

    X=(B-4)m<B^(K+1).

Binary nonoverlap makes each of its digits at most J_C. If F is its
digit polynomial, then `F(B)=X` is divisible by `B-4`; hence `F(4)`
is divisible by `B-4` as well. But (4) gives

    0<=F(4)<=J_C (4^(K+1)-1)/3 < B/12 < B-4.

Therefore `F(4)=0`; its coefficients are nonnegative, so `X=0` and
`m=0`. This proves the exact canonical identities

    ell=ell_0(B), e=e_0(B).                     (8)

## The low carries encode every quadratic equation

After (8), positions below K in S3 receive no contribution from the
offset `qB lambda`, nor from the negative tail of `e_0-z lambda`
beginning at K. At these positions the raw coefficients are precisely
those of

    2D(B) C(B)^2.

Each has absolute value strictly smaller than
`2z A_C=J_C<B/4`. Normalize these signed coefficients from the unit
position upward. The incoming carry starts at zero, and induction
shows that each following carry is either -1 or 0: a coefficient of
absolute value less than `B/4`, plus such a carry, lies strictly
between -B and B. Thus its Euclidean quotient by B is -1 or 0.

At a target position, write this incoming carry as kappa. Its digit
is the residue modulo B of `v+kappa`, with `kappa in {-1,0}` and
`|v|<B/4`. The mask digit `B-4` permits exactly the four values
`0,1,2,3`. A negative `v+kappa` would normalize to a digit greater
than 3, while a nonnegative one cannot wrap around B. Consequently
the no-carry test at this position is exactly

    0<=v+kappa<=3.                              (9)

At the special row, (3) gives `v=2delta^2`. Equation (9) implies
`2delta^2<=4`, and delta is a nonnegative integer. Hence
`delta in {0,1}`.

At the guard, `v=8(u delta-x^2)+2delta^2`. If delta were zero,
this would be `-8x^2<0`, and an incoming carry of -1 or 0 could
not satisfy (9). Since the queried input x is positive, delta must
equal one.

At every ordinary row, we therefore have `v=8F_i^h+2`, so (9) reads

    0<=8F_i^h+1<=3

or

    0<=8F_i^h+2<=3.

In either case integrality forces `F_i^h=0`. With delta equal to
one, the original homogeneous rows recover the represented system.
This proves sufficiency. The low coordinate positions impose no
additional equations: D starts above all of them, so both their
coefficients and incoming carries are exactly zero.

## Necessity and positivity

Given a solution of the represented system, use delta equal to one,
`u=x^2`, the same original witness coordinates, and zero dummy
coordinates. Choose a sufficiently large power of two b as in the
preceding coding construction, and set

    B=Hb^2, q=B^L, lambda=(q^2-1)/(B-1),
    ell=ell_0(B), e=e_0(B),
    C=x+g.

The delta digit at weight one makes g positive. All fixed-index,
packed-congruence, bound, and Omega witnesses are positive by their
previous arguments, since the support conditions and digit bounds
are unchanged.

The changed sigma is also positive. From `C<B^K`, `Z<B`, and
`L>2K`, one has

    ZC^2<B^(2K+1)<qB.

Thus (1) gives

    S3=lambda(qB-ZC^2)+2eC^2>0.

At each ordinary row and at the special row, the raw coefficient is
now exactly 2. The carry argument above shows that its actual digit
is 1 or 2, both permitted by `B-4`. The low coordinate tests have
digit zero, and there are no other third-mask targets because
`ell=ell_0`. The first two masks work as before. Hence the packed
integers have no binary overlap, so the usual Kummer argument gives
`N^2` dividing `binom(2R,R)` for their newly calculated R.

The positive Pell witnesses are then chosen by the constructions of
`PELL_UNIT_SCALE_PROOF.md` and `PELL_SHARED_RATIO_PRODUCT_PROOF.md`,
using this R. Those constructions require only the packed ranges,
the central-binomial divisibility, and the fixed exponent bounds,
all of which were just proved. Every positive witness is therefore
available, completing necessity.

Only one arithmetic instruction is removed: `P2=Lam*qp1` becomes
`P2=Lam*q`, and `qp1=q+1` is deleted. The factor `Lam=B lambda`
was already computed for the geometric equation. The new coefficient
index affects only supplied constants; it introduces no arithmetic
instruction or additional unknown into the final system.
