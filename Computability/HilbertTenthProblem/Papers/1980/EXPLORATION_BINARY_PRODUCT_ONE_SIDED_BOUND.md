# The binary product system also needs more than the one-sided sigma bound

The 90-operation binary product construction uses

    sigma=(e-ell)C^2>0, ell+sigma+alpha=q.

Replacing its bound by `sigma+alpha=q` would delete one addition. This
note gives a full positive-domain counterexample to that replacement
with the current binary compiler, fixed-index congruence, and packing.
It does not change the 90-operation system or its proof, and it does
not rule out a different 89-operation construction.

The alphabet-four counterexample in
`EXPLORATION_PRODUCT_ONE_SIDED_BOUND.md` does not transfer unchanged:
its positive false row has value 2, which the binary mask rejects.
The repair below changes both false rows and preserves every binary
mask. The matched Pell extension uses `BASE_TWO_PELL_90_PROOF.md`.

## 1. A fixed index representing the empty set

Use the compiler of `BINARY_PRODUCT_90_PROOF.md` for an inconsistent
finite system, namely the final zero constraint

    2 delta delta_copy = 0,

where delta_copy is a fresh square-difference copy of delta. The
compiler's ordinary guard and unit tests force delta=delta_copy=1
in every canonical solution, so this circuit has no solution for any
positive queried input x. Include both signs of this final constraint
as usual. Write t_plus and t_minus for those two main targets.

For any positive x, assign the helpers, guard, copies, and unit their
usual necessity values, including V0=V1=X=Y=Z=x,
delta=delta_copy=1, and u=x^2-1. All ordinary rows except the final
pair are true. Their physical forbidden-bit decomposition is exactly
the published binary decomposition, fixed before choosing the radix.
The two false main raw coefficients are +2 and -2. Every extra
negative-coefficient target is still Vhelper^2-x^2=0.

Keep the exact finite compiler polynomials ell0(T), e0(T), and
D(T)=e0(T)-ell0(T). Both codes are binary. Their indicator includes
all three positions at t_plus and t_minus. Their supports lie below
K, and their row bands are separated as in the compiler. Let L be its
fixed power of two greater than 3K+2, and choose the admissible fixed
power of two H0 with every threshold in that proof. Thus

    H=H0-1, V=ell0(2)+2^L e0(2), Tindex=psi_2(L)

is the actual fixed index of this inconsistent circuit.

After assigning the finitely many physical values, choose an
arbitrarily large power of two B with B>=4H0, B>H0+1+x, every raw
coefficient smaller in absolute value than B/4, and 2x^2<B/4. Define

    b=B-H0-1, beta=b-x, theta=B-2,
    q=B^L, n=q^8, lambda=(q^2-1)/(B-1),
    C=C(B), g=C-x, ell_c=ell0(B), e_c=e0(B),
    Omega=D(B)=e_c-ell_c, sigma=Omega*C^2.

The leading positive reset in D gives Omega>0. The encoded unit gives
g>0. Degree bounds, followed by enlarging B, give

    ell_c,e_c<B^K, deg(D C^2)<3K<L, 0<sigma<q.

Set alpha=q-sigma>0. The weakened bound is now satisfied. The first
and middle canonical masks pass. Exactly the two false main windows
fail the third binary mask; every other window passes by the same
reset and small-coefficient necessity argument as in the full proof.

## 2. Two corrections and the fixed-index congruence

Put

    m0=(B^2-2)B^t_plus + (B+2)B^t_minus.       (1)

Its positive-row contribution changes the raw value +2 into B^2,
with three binary digits (0,0,1). Its negative-row contribution
changes -2 into B, with digits (0,1,0). Both additions are positive
integers. Equivalently, their signed polynomial forms cancel the two
false raw coefficients exactly and add +1 at t_plus+2 and
t_minus+1. These are already tested positions. The three-digit
windows and row spacing ensure that no other tested window changes.

Write theta=2r0 with r0=B/2-1 odd. Since gcd(B,r0)=1, choose
0<=k<r0 so that

    m=m0+k B^(K+1) == 0 mod r0.               (2)

This high adjustment begins above the support of the codes and all
tested windows. As 2 divides q^2, it implies

    theta divides m q^2(q+1).                (3)

The spacing and degree bounds imply

    0<m<B^(K+3), mb<B^(K+4)<q, theta*m<q.     (4)

Now supply the noncanonical positive codes

    ell=ell_c+m q^2, e=e_c+m q^2.             (5)

Their difference is still Omega, so the exact product and the weakened
bound are unchanged. Their middle source value is

    S2=ell+eq=(ell_c+e_c q)+m q^2(q+1).

The canonical first summand is V modulo theta. Equation (3) preserves
that congruence, and its quotient is strictly larger than the already
positive canonical quotient. Thus the fixed-index equation has a
positive witness as well. Both supplied codes exceed q; they violate
the original stronger bound, as they should.

## 3. All three normalized packed masks pass

Let S2_c=ell_c+e_c q. The packed S has the exact expansion

    S=g+q^2 S2_c+q^4(sigma+m(q+1)).           (6)

The first two coordinates are below q^2. By (4), the last one is
also below q^2, and hence fits its allocated width q^4. For example,
m<q/B^2 and sigma<q give sigma+m(q+1)<q^2 for B>=4, q>B.

The corresponding normalized mask T=Tplus-1 is exactly

    T=(q^2-1-b ell_c)
       +q^2(theta lambda-mb)
       +q^4(theta ell_c+q^2 theta m).         (7)

The first block is positive and below q^2: ell_c is a binary
indicator code, b<B, and b ell_c<B^(K+1)<q. The middle block is
positive and below q^2, because mb<q and theta lambda>q for these
large powers. The last block is below q^4, since theta ell_c<q and
theta m<q. These are genuine block decompositions; no borrow crosses
their displayed boundaries.

The first mask in (7) is unchanged and therefore passes. For the
middle mask, the exact base-B digits of the two low products are

    (B^2-2)b = (2H0+2) + (B-2)B + (B-H0-2)B^2,
    (B+2)b   = (B-2H0-2) + (B-H0)B.          (8)

All digits are between zero and B-2. Subtracting these from the
uniform mask digit theta=B-2 causes no borrow. At the positive
target its three changed mask digits are

    (B-2H0-4, 0, H0),                        (9)

and at the negative target the two changed digits are

    (2H0, H0-2).                            (10)

They are nonnegative even integers below B. Each corresponding
canonical ell digit is one, so every binary intersection is zero.
The separated bands make the two products disjoint. All other low
nonzero ell digits see their unchanged mask B-2.

The remaining subtraction is kb B^(K+1). Since k<B/2, its product
kb has two digits, with upper digit below B/2. Its low subtraction
can borrow only one; the next mask digit B-2 absorbs that borrow and
the upper product digit, ending the borrow there. Thus it modifies
only positions K+1 and K+2, where the ell_c coordinate is zero.
Both positions are below L, so the e_c block beginning at L also
sees its unchanged mask. This proves that the entire middle
coordinate S2_c has zero binary intersection with its mask.

For the third mask, q^2 theta m begins at position 2L. The effective
third coordinate sigma+m(q+1) is below q^2, so it cannot intersect
that term. The other term theta ell_c is supported below K. In that
region the effective coordinate agrees with sigma+m0: the m*q
summand begins at L, and the adjustment from (2) begins above K.
By (1), all these low indicator windows now pass, with the repaired
windows (0,0,1) and (0,1,0). Thus every third-mask bit also passes.

## 4. Bounded packing and the full positive Pell extension

Equations (6)--(7) give

    0<S,Tplus<n=q^8,
    n^2-1<=r=S(n^2-n)+Tplus(n^2-1)<2n^3.

The retained binary packing lemma applies and gives n^2 dividing
the central binomial coefficient binom(2r,r). This is a bounded
counterexample; it does not rely on dropping the size hypotheses
of that packing lemma.

All powers are already canonical: B is a power of two, q=B^L,
and n=q^8. Also B divides g and ell_c because their unit digits
vanish. It divides the added shift in (5), so B divides ell.
The definitions of S and Tplus consequently make r even.

The positive necessity construction in
`BASE_TWO_PELL_90_PROOF.md`, Section 6, now applies to this newly
determined r. Its actual hypotheses are the powers, 3L<=B<=n,
the displayed r bounds, central-binomial divisibility, and even r.
These have all been established independently of the truth of the
compiled circuit and of canonicality of the supplied ell,e. It
constructs U=2^(2r+1), all first/main/second Pell coordinates and
their positive index and exponent quotients, and the relaxed and
half-parameter auxiliary witnesses. Even r gives the required
J=2r+1 equal to one modulo four. It uses A=a+2 and psi_2(L), so
no obsolete base-four witness is being reused.

The coding witnesses were supplied above: positive b,beta,g,ell,e,
sigma,alpha,lambda and the fixed-congruence quotient. The product
equation holds because the common shift does not change e-ell.
There is no additional supplied Omega witness to restore. Therefore
every one of the weakened system's 34 positive unknowns can be
supplied, with the same fixed index of the inconsistent circuit.
That index now admits every positive x although the represented
set is empty. The proposed one-addition bound is unsound for this
compiler and packing.

## 5. Exact finite corroboration and its limits

`../verification/explore_binary_product_one_sided_bound.py` imports
the actual round37 binary helper compiler. Its sample circuit is
assigned a value making exactly one ordinary pair false with raw
values +2,-2. In four cases it checks both original rejections,
all 397 repaired indicator digits, the exact middle-mask formulas
(8)--(10), the bounded high subtraction, and the fixed-congruence
adjustment using the actual large support exponents modulo theta.
The receipt is `explore_binary_product_one_sided_bound.json`.

These finite checks demonstrate acceptance of a false assignment;
they do not assert nonmembership in that sample's represented set.
The inconsistent circuit in Section 1 supplies the general
nonmembership argument. The sample thresholds are small to make
local calculations convenient, and no full admissible astronomical
index or universal Pell witness is instantiated. Sections 1--4
prove the general construction and its complete positive extension.

## 6. A variable packing bound does not remove this alias

A separate proposed saving replaces both n=q^8 and the combined
code bound by n=q^4(S+alpha), retaining the same S,Tplus definitions
and product equation. The same inconsistent-circuit alias defeats
this proposal. Keep the constructed coding values, so S,Tplus and
their binary nonintersection are fixed independently of n. Choose
a power of two W>max(S,Tplus), and set alpha=W-S>0 and n=q^4 W.

The new equation is exact. The new n is a power of two, both S and
Tplus lie below n, and recomputing r preserves the packing lemma's
binomial divisibility and even parity. Also 3L<=B<=n and
n^2-1<=r<2n^3 still hold. The same base-two positive Pell necessity
construction therefore applies to this larger n,r with the same
fixed L and admissible index. Every changed unknown is positive.

This extension was independently audited against the packing and
Pell hypotheses. It concerns the current compiler and is not a
prohibition on variable packing parameters in a different encoding.
