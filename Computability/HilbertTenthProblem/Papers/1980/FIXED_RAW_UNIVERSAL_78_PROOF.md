# A 78-operation fixed-index universal certificate

For every recursively enumerable set of positive integers, fixed positive
compiler numerals can be computed so that the system below has positive
integer witnesses exactly for its members. The complete straight-line
certificate uses **78=42M+36A**, with **32 positive existential coordinates
and 20 equations**. Numerals and equality comparisons are free; multiplication
by a numeral is charged.

This changes the native compiler of the
[80-operation construction](FIXED_RAW_UNIVERSAL_80_PROOF.md), allowing the
equation `(B-1)align=P-1` to be removed. Its two operations and the coordinate
align disappear. The divisor equation **P*v=q remains**. Two duplicate center
clause bands and four synchronization bits force P to be a whole-cell shift
before the local computation is interpreted. All of these additions are
inside fixed compiler numerals and the same two paid masks.

The fixed machine, exact helical semantics, two markers, 14-operation
raw-input bridge and 43-operation fixed-minus Pell kernel are retained.
The [complete checker](../verification/explore_fixed_raw_universal_78.py)
and [receipt](../verification/explore_fixed_raw_universal_78.json) give the
full source and operation ledger. This is a mathematical proof supported
by symbolic and finite checks, not a proof-assistant formalization.

## 1. The fixed window relation and center clauses

Use precisely the fixed stay-step machine and marked windows of the
[81-operation proof](FIXED_RAW_UNIVERSAL_81_PROOF.md). Enumerate its full
finite alphabet of allowed three-by-three windows as w0,...,w_(k-1), with
End as state0 and Start as state1. The underlying tile alphabet has size a;
this a is distinct from the later Pell parameter. We have k>=2. The exact
local relation is

    center[r,c+1]=right[r,c], r=0,1,2; c=0,1,
    center[r+1,c]=next[r,c], r=0,1; c=0,1,2.             (1)

All three windows must be in the allowed alphabet. The retained semantic
theorem identifies its cyclic words at offsets0,-1,-h, with unique Start
at0 and End at raw distance x<N, exactly with halting runs on input x.
It includes x=1, intervening one-I strips, and arbitrary h not dividing N.

As in the 80 compiler, use k Boolean selector bits and9a Boolean tile-copy
bits. Add four Boolean synchronization bits. In a power-of-two clause
radix A>k+1, A>=4, concatenate:

* selector occupancy e=sum_i z_i, tested by mask A-2;
* for each tile-copy bit, that bit plus the sum of selectors whose window
  has the corresponding tile, tested by mask1;
* for each of the four synchronization bits, that bit plus e, tested by
  mask1.

The raw clause values are at most k+1<A. The occupancy test therefore
forces e to be0 or1; the parity tests force all copies to match the
selector and all four synchronization bits to equal e. Write the resulting
homogeneous expression as sum_e c_e*bit_e and its mask as mu. Position
exponents e will be specified next. Each genuine selector, copy and
synchronization variable has a positive coefficient. Ignored dummy bits
have coefficient zero. Zero-expression mask1 clauses may be appended.

## 2. Four separated anchors and two clause bands

Selectors occupy inner-radix exponents0,...,k-1. Tile-copy exponents are

    e(r,c,s)=T0+(2-r)3a+(2-c)a+s, T0=k+3a.               (2)

Thus multiplication by R^(3a) shifts the bottom two rows onto the top two,
and multiplication by R^a shifts right columns onto left columns. A left
column that wraps across a row lands in an untested rightmost column.

Let

    m=2*popcount(mu)+12a+2.

Append zero-expression clauses until m+2>=k+9a+4. Each such clause raises
m by2. Add exactly m+2-(k+9a+4) ignored dummy positions consecutively
above the tile-copy positions. Let E0 be the largest selector, tile-copy
or dummy exponent, and put

    M0=E0+3a+1,
    u1=M0, u2=3M0, v1=9M0, v2=27M0.                   (3)

Place the four synchronization bits at these four exponents. Let E be
the full set of native exponents, K=|E|=m+2, and Emax=27M0. All dummies
are below the anchors. The difference18M0 occurs in E-E exactly once:
v2-v1. Indeed every pair not ending at v2 has difference at most9M0;
subtracting any other member of E from v2 gives a different difference.

Choose the following fixed layout:

    H=Emax+24M0+3a+1,
    T1=H+2Emax+a+1,
    T2=T1+2Emax+1,
    L=T2+Emax+2.                                       (4)

Choose a power of two R=2^b satisfying

    R >= max(2K*(2*sum_e c_e+5), 2mu)+4,
    B=R^L=2^d, d=bL.                                  (5)

Thus mu<R/2, and K*(2*sum c_e+5)<=R/2-2. All these quantities are fixed
numerals computed from the fixed machine alone. Define

    DC=R^(3a)+R^(H+a)+R^(8M0)+R^(24M0)
       +sum_e c_e*(R^(T1-e)+R^(T2-e)),
    DR=R^H, DY=1.                                     (6)

The sum includes selectors, tile copies and synchronization bits. Define

    MF=mu*(R^T1+R^T2)
       +sum_{r=0,1; c=0,1,2; s<a}R^e(r,c,s)
       +sum_{r=0,1,2; c=0,1; s<a}R^(H+e(r,c,s))
       +R^v1+R^v2,
    MC=B-1-sum_{e in E\{0,1}}R^e,
    CS=R.                                             (7)

All tested bands and positions are disjoint. Hence popcount(MF)=m,
popcount(MC)=d-m, MC is odd and MF is even. Also

    0<DC,DR<B, 0<MC,MF<=B-2.                           (8)

CS is only the Start selector contribution; End's selector contribution
is1. Their tile-copy and synchronization bits remain in Z.

## 3. Exact coefficient bounds before period alignment

First consider arbitrary native typed cells: every permitted position
contains either0 or1, with no assumed selector or copy consistency. In
the expression DC*Ccell+DR*Rcell, the total raw coefficient mass is at most

    K*(2*sum c_e+5)<=R/2-2.                            (9)

The5 counts the four explicit DC monomials and DR. Every exponent is at
most T2+Emax<L. There are no inner-radix or cell carries.

Now suppose q=B^N and P is any power of two dividing q; no whole-cell
alignment is assumed. Write

    P=2^p, p=b*t+ell, 0<=ell<b.

The cyclic binary rotation Yword=P*C modulo q-1 has at most one bit in
each R-digit, always at the same residue ell. Its R-digit values therefore
belong to {0,2^ell}, and its possible positions within a cell are

    E+t modulo L.                                     (10)

This statement holds uniformly across every cell, including rotation
through the end of the full word. It follows directly by translating
native bit positions b(iL+e) modulo bLN.

Since 2^ell<=R/2, adding this arbitrary rotated word to the unshifted
expression in (9) leaves every R-digit at most R-2. Thus the actual field

    Factual=DC*C+DR*Rword+Yword                         (11)

has every B-cell at most B-2, even before the rotation is aligned or the
center clauses are decoded. Here Rword is the exact one-cell cyclic
rotation of C. This is the bound needed to identify a supplied F with
its actual local field without circular typing assumptions.

The tested coefficients from the unshifted part of (11) are exactly:

* at T1 and T2, the same center clause expression sum_e c_e*bit_e;
* at e(r,c,s), r=0,1, the center's(r+1,c,s) copy;
* at H+e(r,c,s), c=0,1, the sum of center's(r,c+1,s) and right's(r,c,s);
* at v1 and v2, respectively the center bits at u1 and u2.

The four-anchor repair is essential: adding a constant1 to DC would also
add the center's top-row copy at every vertical target and change (1).
Instead the shifts8M0 and24M0 cannot reach any low tile-copy target.
At v1 they receive exactly u1, and at v2 exactly u2. No other native
position can contribute there. The old3a shift cannot hit either target
because the anchor gaps exceed3a. All these low shifted terms end below H.

The horizontal band ends at H+Emax+a, while the first clause-convolution
band begins at T1-Emax above that. The two clause bands have separation
greater than2Emax. At the center Tj of either band, a convolution term
Tj-e+f contributes precisely when e=f; the other band cannot reach it.
These bounds include all dummy and synchronization positions.

## 4. Decoding first, then forcing exact period alignment

The possible rotated support (10) cannot contain both T1 and T2. If it
did, their difference modulo L would lie in E-E. But

    T2-T1>2Emax, L-(T2-T1)>Emax,

whereas every member of E-E lies between -Emax and Emax. Thus at least
one complete unary clause band receives no contribution from Yword,
uniformly at every cell. This is true for every bit residue ell.

If the supplied field passes MF, the clean band forces every center
cell to have either no selector and zero copies/anchors, or one actual
allowed window with all its copies and four anchors correct. At Start,
the inserted selector is present, so its four anchor bits are1.

The tests at v1 and v2 now have the form

    1+Ydigit(v_i) is even, i=1,2.                       (12)

With Ydigit in {0,2^ell}, evenness of (12) forces ell=0 and both target
positions populated. Therefore v1-t and v2-t, taken modulo L, both lie
in E. Because L>2Emax, their difference is the ordinary difference18M0,
not a wrapped alternative. Its unique representation in E-E is v2-v1,
so t=0 modulo L. Consequently

    P=B^h, 0<=h<=N.                                    (13)

Both endpoints h=0 and h=N give Yword=C. They are impossible: Start's
top row consists of horizontal boundary tiles, and its middle row has
interior initialization tiles. The vertical parity tests would require
these different one-hot tile indicators to be equal. Thus 0<h<N.

After (13), Yword is a whole-cell rotation. It has no bits in either
unary or horizontal band, and the vertical parity tests are exactly the
second overlap relation in (1). Horizontal tests give the first relation.
Horizontal overlap propagates occupancy under cyclic shift1: an occupied
window has one tile indicator at every physical position, while an empty
cell has none. Adjacent occupancies must therefore agree. Start is occupied,
so every cell selects one genuine allowed window. The extra anchor tests
then hold automatically for every aligned genuine word.

## 5. Full source and noncircular arithmetic soundness

Remove only align from the positive witness list of the 80 proof. The six
outer equations are

    (B-1)J=q-1,                    P*v=q,
    C+alpha+d*x=q,
    (DC+B*DR+P)C=F+z(q-1),
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
    C=CS+Z+W.                                          (14)

The ten fixed-minus Pell equations and four fixed-base input equations
are literally those in Sections3--4 of the 81 proof, with scale D0=q^3.
They are included in the complete source expanded by the checker.
There is no uncounted alignment, digit or power predicate.

For clarity, dropping align changes the preliminary bound: we initially
know only 1<=P<=q. The positive repunit equation independently gives
q>=B>=16. Marker decomposition and the raw bound give

    0<Z<C<q, 0<W<C<q, 0<d*x<q.

The fixed mask ranges give 0<(MC+q*MF)J<q^2-1. Positivity of r forces
Z+qF<=q^2, hence F<q; since Z<q the packed word is strictly below q^2.
Therefore q^2<=r<q^4. The retained kernel applies in this order, without
assuming P>=B, and yields q=B^N. The divisor equation implies P=2^p with
0<=p<=dN. The unchanged input bridge gives W=B^x and 0<x<N. The inverse
packed-mask argument recovers

    Z AND(MC*J)=0, F AND(MF*J)=0.                        (15)

The disjoint insertion C=CS+Z+W now types every native bit and inserts
exactly Start at0 and End at x. It does not yet prove copy consistency.
Construct Rword and Yword as actual cyclic binary rotations of this typed C.
The bound (9)--(11) gives 0<Factual<q-1. Equation (14) makes F congruent
to Factual modulo q-1; because 0<F<q, we obtain F=Factual.

Only now apply Section4: one clean band decodes all centers, Start's
anchors force P=B^h with0<h<N, and the exact overlaps and occupancy follow.
The two marker selectors are unique. The unchanged helical semantic theorem
then gives a genuine halting computation at exactly the raw input x.

## 6. Strictly positive completeness at the new constants

For an accepted x, take the padded helical word provided by the 81 proof,
with N>=4, 0<x<N and0<h<N. Encode each genuine window by its selector,
its nine nonzero tile copies and four synchronization bits1, with dummy
bits0. Set q=B^N, P=B^h, v=B^(N-h), W=B^x and J=(q-1)/(B-1).

Let Z=C-CS-W. Removing the two marker selector bits leaves their copies
and anchors, so Z>0. Its low mask vanishes and it is even. Both unary bands
are uncontaminated because the successor is aligned; the copy-overlap and
anchor tests pass. The field F of (11) is positive and at most (B-2)J.

Every genuine cell has a selector, so C>=J and C<=(B-2)J. Thus

    q-C>=J+1, J>=B^(N-1)>=B^x=2^(d*x)>d*x,
    alpha=q-C-d*x>0.

The cyclic wrap quotients kR and kY are positive. The ghost quantity
(P-1)/(B-1)>=1 can still be used to bound kY; it is not supplied or
computed by the certificate. Set z=DR*kR+kY>0. All six outer equations
hold, and the actual packed r is odd because Z is even and MC*J is odd.
The mask population identity gives popcount(r)=3dN exactly.

The retained positive kernel converse supplies all seventeen fresh kernel
coordinates at this actual r and scale q^3. With u=d*x>=4 and u<q, the
unchanged input bridge supplies its five fresh positive Pell coordinates,
as in Section5 of the 80 proof. Every one of the 32 supplied coordinates
is strictly positive, including for x=1. No previous numerical kernel
tuple is reused, and no operation computes the removed align witness.

## 7. Exact ledger and finite evidence

Delete `Pm1=P-1` and `alignment=(B-1)*align` from the 80-operation schedule,
and delete their equality and the coordinate align. Retain the multiplication
P*v and its comparison with q. All other variable operations are unchanged.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry, transport, masks, raw bound and markers |10|11|21|
| Fixed-minus kernel |25|18|43|
| Fixed-base raw-input bridge |7|7|14|
| **Complete certificate** |**42**|**36**|**78**|

Larger compiler numerals encode the duplicate bands and synchronization
bits. Their size is outside the chosen complexity measure. Variable powers
and every multiplication by a fixed numeral keep their counted costs.

The checker audits all20 source residuals, including the inherited acyclic
norm correction. Exact sparse-polynomial basis checks cover every native
bit, including dummies and anchors, against every tested coefficient. For
each tested compiler it exhausts all inner-cell rotation offsets, proving
the clean-band and unique-anchor support claims numerically, and checks
every possible bit residue's parity implication. Raw malformed triples,
canonical or empty triples, and copy/anchor defects provide further checks.
The receipt distinguishes sampled larger-alphabet cases from the small
exhaustive ones. A large alphabet exercises zero-expression padding.

Selected complete packed outer examples use the actual generated constants,
positive geometry and transport witnesses, the exact raw x, both masks and
the full odd-index population threshold. Their small window alphabets test
the compiler and arithmetic interface; they do not purport to enumerate the
universal machine alphabet. That effective full alphabet and the retained
helical theorem supply the universal statement mathematically. Astronomical
full Pell witnesses are proved to exist, not numerically materialized.

The default checker command compares its fresh result against the saved
receipt without writing. Receipt regeneration requires `--write`.

Review status: author and independent complete proof/source reviews pass.
Independent checks include additional layout, support-difference and
whole-word rotation audits, and rejection of the former initial-slab
alignment attack by the new anchor tests. Fresh default verification
matches the saved receipt. These are mathematical and exact-computation
checks, not a proof-assistant formalization.
