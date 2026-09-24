# A 77-operation fixed-index universal certificate

For every recursively enumerable set of positive integers, one can effectively
choose fixed positive compiler numerals such that the system below has positive
integer witnesses exactly for its members. The complete straight-line
certificate uses **77=42M+35A**, with **32 positive existential coordinates
and 20 equations**. Numerals and equality comparisons are free; multiplication
by a numeral is charged.

This saves one marker addition from the
[78-operation certificate](FIXED_RAW_UNIVERSAL_78_PROOF.md). Start becomes the
native unit selector and is forced at the origin by a necessary parity property
of the unchanged fixed-minus kernel. Only End is inserted explicitly. A new
odd-index input congruence uses the already computed discriminant, paying for
End's fixed bit offset without increasing the 14-operation input bridge.

Two separately proved dependencies are essential:

* [Every positive fixed-minus kernel solution has odd packed index](EXPLORATION_FIXED_MINUS_INDEX_PARITY.md).
* [Unique End implies unique Start for the actual helical relation](EXPLORATION_CYCLIC_MARKER_BIJECTION.md).

Neither statement is inferred merely from canonical examples. The
[complete checker](../verification/explore_fixed_raw_universal_77.py) and
[receipt](../verification/explore_fixed_raw_universal_77.json) provide the
expanded source and arithmetic ledger. This is a mathematical proof with
symbolic and finite checks, not a proof-assistant formalization.

## 1. The synchronized compiler with one reserved marker

Use the same fixed stay-step machine, allowed three-by-three windows,
two overlap relations, duplicated center clauses and four synchronization
anchors as in the 78 proof. Enumerate **Start as selector0** and **End as
selector1**. Start's native selector contribution is therefore1; End's is R.
Both are fixed windows of the actual universal machine construction.

Let mu be the center-clause mask, a_tiles the original tile alphabet size,
and

    m=2*popcount(mu)+12*a_tiles+2.

The only population change is to choose **K=m+1** native Boolean positions,
rather than m+2. Append zero-expression mask1 clauses until enough positions
exist for all selectors, tile copies and four synchronization bits, then
place the remaining ignored dummies below the four anchors exactly as in
the 78 construction. All gap and band inequalities there remain valid.

Keep its DC, DR, DY=1 and MF formulas. Choose the inner radix R=2^b above
the same strong no-carry bound, but choose **b odd**. Pad the fixed inner
cell length L upward if necessary so that **L is even**. Then

    B=R^L=2^d, d=bL is even.

These choices only increase fixed numerals. The new remainder mask is

    MC=B-1-sum_{e in E\{1}}R^e,                         (1)

where E is the full set of K native position exponents. It permits every
native bit except the End selector. Exactly K-1=m bits are permitted, so

    popcount(MC)+popcount(MF)=d,
    MC even, MF even, 0<MC,MF<=B-2.                      (2)

The unit Start bit is permitted in Z. Only the End selector is excluded
at every cell and supplied by the marker word W. The four anchor positions,
duplicate-band separation, arbitrary-shift coefficient bound and uniqueness
of the anchor difference are exactly those of the 78 proof. Reducing K by1,
rounding b to odd and rounding L to even preserve all their inequalities.

## 2. The complete source and its preliminary bounds

Use the same 32 positive coordinates as in the 78 proof:

    q,P,C,v,J,F,alpha,z,Z,
    aP,c,dmain,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,muP,delta,phiP,rho.

Here aP is the main Pell parameter, distinct from a_tiles. The six outer
equations are

    (B-1)J=q-1,                    P*v=q,
    C+alpha+d*x=q,
    (DC+B*DR+P)C=F+z(q-1),
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
    C=Z+W.                                             (3)

The ten retained fixed-minus kernel equations are unchanged from the 78
proof, with scale D0=q^3. Write

    A0=aP+2, Delta=A0^2-1, Hpell=4aP+3,
    J0=2r+1, u=d*x+b.

Replace the four input equations by

    kappa=u+delta*Delta,
    c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+aP*kappa+rho*Hpell.                           (4)

These are all 20 equations. There is no supplied parity, marker, digit or
period-alignment predicate. The registers Delta and Hpell are already
computed in the retained kernel.

Before any power or computation is interpreted, positivity gives q>=B,
1<=P<=q, 0<Z<C<q, 0<W<C<q and0<d*x<q. The mask ranges imply the same
preliminary bounds as before:

    0<F<q, q^2<=r<q^4.                                 (5)

The unchanged kernel therefore recovers q=B^N, P a power of two dividing q,
X=2^J0, aP>X, and c=psi_A0(J0), in the same noncircular order as before.
The inverse packing recovers the two paid masks. No fact about Start is
needed to obtain these conclusions.

Since b<B<=q, the unchanged raw bound is enough for the new input index:

    0<u=d*x+b<q+b<2q<J0<aP+1.                           (6)

The raw bound uses d*x, not u. No additional bound operation has been hidden.

## 3. The odd-index discriminant bridge

Every positive solution of the input norm in (4) has

    kappa=psi_A0(v), muP=chi_A0(v), v>0.

The retained gap c=kappa+phiP gives v<J0. The Pell recurrence, or its
integer binomial expansion, gives the exact congruence

    psi_A0(v)=v*A0^(v-1) modulo Delta.

Because A0^2=1 modulo Delta, this is

    psi_A0(v)=v modulo Delta                 if v is odd,
    psi_A0(v)=v*A0 modulo Delta              if v is even. (7)

Both displayed representatives lie strictly between0 and Delta. Indeed
v<J0<aP+1 gives v<=aP, and aP*A0<Delta. The first equation of (4) says
that the representative is u, which by (6) is below2q. If v were even,
then v>=2 and v*A0>=2A0>2q>u, a contradiction. Hence v is odd and v=u.
The chosen b odd and d even make this parity consistent for every positive x.

The retained base-two identity is

    chi_A0(u)-aP*psi_A0(u)=2^u modulo Hpell.

Equation (4) therefore gives W=2^u modulo Hpell. By (6),

    2^u<2^(2q)<2^J0=X<aP<Hpell, 0<W<q<Hpell.

Thus the congruence is an equality:

    W=2^u=R*B^x.                                      (8)

Since R>1 and W<q=B^N, this implies x<N. End is inserted at precisely the
raw distance x, in native selector position1. No input recoding changes x.

## 4. Why the origin must be Start

The [necessary kernel-parity theorem](EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
applies to every positive solution under (5), before the represented word
has been decoded. It yields r odd. To recall why this is stronger than a
canonical-converse observation, the normalized auxiliary Pell root has
an odd index s=epsilon*J0+2*maux*t. Keeping both fixed-minus congruence
signs forces

    r+maux*t odd, r+(maux+1)*t odd.

Their difference forces t even and then r odd. The theorem proves these
facts for all permitted auxiliary choices, using strict bounds c>2J0 and
f>2c; it does not assume s=J0 or a canonical maux.

Reduce the packed equation (3) modulo2. Since q is even and MC is even,

    r=Z modulo2.

Consequently Z is odd. The mask Z AND(MC*J)=0 permits only native bits,
and the End selector is absent from every Z cell. Equation (8) inserts
exactly that missing bit at cell x, with no carries. Therefore C=Z+W is
native typed at every cell, and its unit bit at the origin is1: selector0,
the Start selector, is present.

This does not yet assert that the cell's copies are consistent. As in the
78 proof, form its actual one-cell rotation Rword and its arbitrary binary
P-rotation Yword. The native coefficient bounds, valid before alignment,
give 0<Factual<q-1 for

    Factual=DC*C+DR*Rword+Yword.

Transport gives equality with the supplied F. At least one duplicated
clause band is uniformly clean, so all center selectors, tile copies and
four anchors decode. The origin therefore is the full genuine Start window.
Its anchor bits force P=B^h, and Start's boundary/interior mismatch excludes
h=0 and h=N. Horizontal overlap propagates occupancy from Start to every
cell. All cells select genuine allowed windows and satisfy the exact two
overlap relations. These are precisely the 78 synchronization and transport
arguments; they require a Start at the origin, not its prior uniqueness.

## 5. Unique End supplies the remaining marker uniqueness

The mask and (8) give exactly one End, at index x. The
[cyclic marker-bijection theorem](EXPLORATION_CYCLIC_MARKER_BIJECTION.md)
now applies to the decoded genuine word. Every Start is the last I in a
proper maximal initialization I-run of length at least2, and the first I
of that run is End. Conversely every End identifies such a run and its
last I is Start. The normalized first step stays at Q, so these are the
exact fixed three-by-three windows, including their next-row contents.

The maps are inverse on the finite cyclic residues themselves. A run
cannot meet a vertical boundary at an I cell; its bounding phases are L
and Q. The scans terminate before N steps. Covering-plane aliases and
h not dividing N therefore cannot merge two distinct Starts into one End.
Short one-I runs and all-I cycles have neither marker.

Thus unique End implies unique Start. Its location is the already proved
origin. The unique End at x belongs to that same I-run, whose length is x+1.
The initial unary input has length x+2, exactly as in the retained machine
normalization. The finite-rectangle halting argument of the 81 proof gives
acceptance of the raw input x. This completes universal soundness.

## 6. Strictly positive completeness

For an accepted x, use the padded genuine helical word of the 81 proof,
with N>=4, 0<h<N and unique Start at0 and End at x<N. Encode Start as0,
End as1, all genuine copies and synchronization bits, and dummy bits0.
Set q=B^N, P=B^h, v=B^(N-h), W=R*B^x, and Z=C-W.

Z is positive, including the origin Start selector and all marked-window
copies and anchors. Its native mask vanishes and it is odd. Both field
masks vanish. The same cell bounds give C<=(B-2)J and

    q-C>=J+1, J>=B^(N-1)>=B^x=2^(d*x)>d*x.

Hence alpha=q-C-d*x>0. The positive wrap quotients give
z=DR*kR+kY>0. All six outer equations hold. The actual packed index is
odd because r=Z modulo2, and its population is exactly3dN. The retained
positive converse supplies all seventeen fresh kernel coordinates at
this actual r and scale q^3.

For the input bridge choose

    kappa=psi_A0(u), muP=chi_A0(u),
    delta=(kappa-u)/Delta, phiP=c-kappa,
    rho=(muP-aP*kappa-W)/Hpell.

Here u=d*x+b is odd and at least3. Congruence (7) gives integral delta;
psi_A0(u)>u gives delta>0. In particular psi_A0(3)=4A0^2-1=4Delta+3,
and growth is strict thereafter. Bound (6) gives u<J0 and therefore
phiP>0. The exponent congruence gives integral rho, while

    muP-aP*kappa=2*kappa-psi_A0(u-1)>kappa>=2A0>W

gives rho>0. Thus all five input Pell coordinates are positive, and all
32 supplied coordinates are strictly positive for every accepted x,
including x=1. Astronomical kernel witnesses are established by the fresh
positive construction, not by reusing a numerical tuple.

## 7. Exact cost and verification boundary

The marker instruction pair `marker_partial=CS+Z`, `marked_rhs=marker_partial+W`
becomes the single addition `marked_rhs=Z+W`. In the input adapter, replace
`ap1=aP+1` by `odd_index=d*x+b`, and replace `delta*ap1` by `delta*Delta`.
The addition of the fixed exponent offset is exactly paid by removing the
old modulus addition. The raw bound continues to use the already computed
scaled input d*x. The gap is retained.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry, transport, masks, raw bound and marker |10|10|20|
| Fixed-minus kernel |25|18|43|
| Odd-index discriminant input bridge |7|7|14|
| **Complete certificate** |**42**|**35**|**77**|

The checker verifies all20 source residuals and the inherited acyclic norm
correction. Only the marker and input-index residuals change from78. Sparse
native-basis and exhaustive inner-rotation checks cover the adjusted compiler,
including its large-alphabet zero-clause branch. Separate checks verify the
discriminant congruence and positive input coordinates, and the inverse marker
maps on closed phase words. The dependency notes additionally check noncanonical
auxiliary parity witnesses and actual valid helical presentations.

Two materialized packed outer tuples use the actual new compiler constants,
mask populations, odd indices, shifted End bit and raw x. Their small alphabets
are compiler/interface tests, not enumerations of the universal machine's
alphabet. The full fixed-machine semantics and the positive kernel construction
are proved mathematically above. The default CLI checks the saved receipt
without writing; regeneration requires `--write`.

Review status: author and independent complete proof/source reviews pass.
Fresh default verification matches the saved receipt. Additional independent
checks cover compiler layouts and support pairs, discriminant residues and
positive input bridges. The two supporting lemmas also have independent
proof/source review and exact receipt checks. These establish mathematical
and exact-computation evidence, not a proof-assistant formalization.
