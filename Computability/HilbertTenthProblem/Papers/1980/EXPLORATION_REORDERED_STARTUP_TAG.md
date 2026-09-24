# Reordered startup fields give a 93-operation tag certificate

For the positive-startup tag interface, a known zero first symbol permits
using S0 as the unit field. Replacing Gstar by the original projector guard
G=Q+AH and reusing AH saves two additions in the low packing. The complete
source has **93 operations = 51 multiplications + 42 additions/subtractions**,
with **29 positive unknowns and18 equality comparisons**. All nine masks,
both transports, the input bound, true radix geometry, and the fixed-plus43
kernel remain. The specified encoded input is unchanged.

Soundness is actual eventual halting on every valid encoded input. The
completeness domain uses the startup promises from
[the positive-startup95 theorem](EXPLORATION_POSITIVE_STARTUP_TAG.md), with
an additional zero initial symbol and without its even-beta restriction:
beta>=2, a genuine
halt at the single-symbol word0, a nonzero bit beyond the head in the initial
deleted prefix, and at least one genuine selector-one event. Neary's
normalized encoded instances satisfy these conditions. This is not a
fixed-appendant universal bound for ordinary numerical input.

Author and two independent complete proof/source reviews and fresh
verification runs pass. The [checker](../verification/explore_reordered_startup_tag.py)
and [receipt](../verification/explore_reordered_startup_tag.json) contain
both full fixed-leading-symbol sources and the fresh-index history checks.
The published95,99 and104 sources are unchanged.

## 1. Exact source and two-operation saving

Use the constants and positive coordinates of95. In particular,

    K=3^beta, k=K/3, B=3^(a-1), U=value(appendant),
    cc=(k-1)/2, C>max(K^3,K*3^a,2KU+3),
    j=(C-C/K)/2,

where C is a fixed power of three, and the fixed appendant has length
a>=2. Supply Q,S1,T,E as strictly positive integers. The checker calls
T the coordinate Tcontent. Retain

    M1=2Q+S1,
    N=3T+S1          if the appendant starts with0,
    N=3T-2Q          if it starts with1,
    D=(C/k)A,
    GN=N+jAH.

The eight outer comparisons remain

    kD=R,
    D(T-E+Ut*M1)=N-Ninit,
    D[L+(B-1)M1]=L-Linit+3q,
    Linit+alphaI=A,
    H(R-1)=q-1, Rv=q,
    2r+1=q^9+2P, r+betaP=q^9.                        (1)

Here Ut=(U-epsilon)/3 for the fixed leading bit epsilon. The sixteen
positive kernel auxiliaries and ten kernel comparisons are unchanged.

Replace the low four fields by S0,S1,Q,G and retain the five upper fields:

    S0=H-S1, S1, Q, G=Q+AH,
    M0=L-M1, M1, Ebar=ccH-E, E, GN.                 (2)

Let

    TE=ccH+(q-1)E,
    Rest=L+(q-1)M1+q^2[TE+q^2 GN].

The exact packing is

    P=H+(q-1)S1+q^2[Q+q(Q+AH)]+q^4 Rest.           (3)

Expanding(3) gives the q-Horner word of(2), even for arbitrary signed
conceptual fields. The old products j*A and(j*A)*H are replaced by
AH=A*H and j*AH, preserving their two-operation cost while making AH
available to the low packing.

With the already paid q-1,q^2,q^4 and the unchanged Rest, compute

    G=Q+AH; qG=q*G; QG=Q+qG; q2QG=q^2*QG;
    flag=(q-1)*S1; headpair=H+flag;
    low=headpair+q2QG; upper=q^4*Rest; P=low+upper.

These are4M+5A, replacing95's4M+7A low group. No new coordinate or
comparison is introduced, so the result is93=51M+42A. The checker verifies
all18 source polynomials in both leading branches. Every comparison other
than the index comparison retains exactly the95 expression. The index
uses the new P. The computed-u kernel norm correction remains at zero-based
comparison16, with u=jc+2r+1 in kernel notation.

The new index is generally different. This is not a same-index mapping of
Pell witnesses; the converse below rebuilds the kernel at the chosen new
even index.

## 2. Bounds before power or Boolean decoding

The source geometry first gives R=CA, q>=R and H=(q-1)/(R-1).
The valid input satisfies Linit=3^ell with ell>=beta and
0<=Ninit<Linit/2. The positive input slack gives A>Linit>=K,
so the fixed choice C>K^3 yields R>K^4.

The length comparison gives

    (R-k)L+R(B-1)M1=k(3q-Linit)<kKq.

Exactly as in the complete104 bound proof, positivity and B>=3 imply

    0<L<q/2, 0<M1<q/6,
    0<Q<q/12, 0<S1<q/6, N>-q/6.                   (4)

The last inequality holds in both fixed leading branches. Also

    jAH=(R-R/K)H/2 >=(q-1)/3,
    GN>q/6-1/3>0.                                  (5)

The large fixed radix threshold makes the last expression positive.
All terms in the factored low part of(3) are positive. TE is nonnegative,
and Rest is positive because L,GN>0. Therefore P>0 before any field is
known Boolean. The index and positive packed slack imply, for D0=q^9,

    (D0-1)/2<r<D0, D0>=81, r>=27, D0<r^2.          (6)

These are the scale hypotheses of the established fixed-plus43 kernel.
Only now invoke its soundness theorem. Its soundness needs no assumption
about the parity of r. It gives D0 a power of three and the required
central-binomial divisibility. Since D0=q^9, q is a power of three. The
unit-two mask theorem with0<r<D0 makes r native1/2 with unit2. Thus

    P is Boolean, P mod3=1, and P<D0/2.              (7)

Because all terms below the last term q^8 GN in(3) are positive,

    0<GN<q/2, GN<=J=(q-1)/2, N=GN-jAH<=J.          (8)

This is a scalar bound on GN, not yet a claim about its q-block.

The unchanged content comparison is equivalent to

    R(N-3E-S1+UM1)=K(N-Ninit).

Consequently

    3E=(1-K/R)N-S1+UM1+K*Ninit/R.

The valid input gives K*Ninit/R<1/2, the length bound gives
UM1<3q/4, and(8) bounds the first term by J even when N is negative.
Therefore

    E<5q/12+1/6<q/2.                                (9)

No content Booleanity or field recovery was used in this deduction.

## 3. Recovering the reordered fields and the original projector

The bounds just obtained give, in the order of(2),

    -q/2<S0<q, 0<S1<q, 0<Q<q,
    0<G=Q+AH<q/12+q/3<q,
    -q/2<M0<q, 0<M1<q,
    -q/2<Ebar<q, 0<E<q,
    0<GN<q/2.                                      (10)

For G use A/(R-1)<1/3. For Ebar use0<=ccH<q/2 and(9).
Recover successive q-blocks of the Boolean word P with zero incoming
carry. A negative field w in(-q/2,0) has remainder q+w>J, which cannot
be Boolean. Every field is therefore nonnegative; its upper bound<q
prevents an outgoing carry. This induction proves all nine individual
masks in(2). Since S0 is first, its unit trit is1.

The paid equation q=Rv now makes R a power of three. The head comparison
then forces q=R^t for a positive integer t. A=R/C is also a power of three.
Hence S0+S1=H partitions actual row heads.

The original projector guard is sufficient. At an inactive head, the
equation2Q+S1=M1 starts with no incoming carry and forces Q=0 throughout
that row. At an active head it either terminates immediately or follows
a run of Q-ones until its first zero, producing exactly one M1 marker.
Boolean G=Q+AH forces Q's A-position to be zero, so that run terminates
at or before A. There is no carry into the next row. Induction proves
the complete row projector.

In particular, at each inactive head G has a zero head trit: Q=0 there
and A>1. The word S0 consists precisely of those head positions. Thus

    Gstar=G+S0

is Boolean, belowq, and exactly the old guard. This is a disjoint addition,
established after decoding; it was not assumed in the pre-mask bounds.
All nine conceptual fields of the old104 interface are now recovered.

The length-flow and signed-content arguments in Sections4-5 of
[the complete104 proof](EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md) apply with
this restored Gstar and the unchanged transports. They prove that the
specified actual input eventually halts. This uses the established
post-typing semantic proof, not an assertion that the changed packing
already satisfies95's old index equation.

## 4. Fresh-index completeness and wrapped parity

Take a genuine trace in the stated completeness domain. The positive
startup argument for95 gives Q,S1,T,E>0; that positivity argument uses
only beta>=2, not even beta. Since the first actual symbol is0,
S0 has unit1. The canonical G=Q+AH is Boolean, and all other new fields
are the old ones. Choose an arbitrarily wide odd exponent m with
R=3^m and m>2(beta-1), meeting all the existing width and input bounds.
The canonical outer tuple has the new packing(3).

Write h=beta-1 and suppose the genuine trace has t rows. Its terminal
marker is3 and its terminal content is0. The unchanged wrapped-zero-edge
construction adds

    delta=R^t*3*sum((R/k)^i, i=0,...,m-1)

to M0 and L, increases the height to t+m-h, and replaces q,H by the
corresponding larger power and row-head word. Its identity

    ((R/k)-1)delta=R^t*3[((R/k)^m)-1],
    (R/k)^m=R^(m-h)

preserves the length comparison and the terminal marker3. The content
comparison is unchanged because Nfinal=0. Q,S1,E,N,T and the input
remain unchanged. The added M0 bits are distinct and lie entirely in
the added rows; multiple markers in one artificial row are allowed.
The remaining fields extend by their fixed head or guard patterns.
All nine new masks and strict positivity therefore hold on both tuples.

The sum of the new fields gives the useful parity identity

    P=N+L+H mod2.                                   (11)

Indeed q and A are odd, cc=beta-1 mod2 and j=beta mod2; the other terms
in the field sum are even. If d=m-h is the added number of rows,
the m new M0 bits change L's parity by m, while H's parity changes by d.
The native offset (q^9-1)/2 has parity m times the height. Thus

    delta(r)=m+d+md=m+(m+1)d=1 mod2,                 (12)

because m is odd. This holds for odd beta as well as even beta; there is
no appeal to the narrower even-beta converse of99. The canonical and
padded indices have opposite parity.
Select the even one. Its fields are Boolean with first unit1, so the
new index has the required exact valuation and satisfies(6). The
fixed-plus43 converse supplies sixteen fresh positive auxiliary values,
completing the93 source. Neither the input nor the operation count
changes when choosing this witness.

Neary's Table2 startup begins b,b,c under b=0,c=1; its normalized halt is
a single b. The primary-source verification and the positive-startup
argument are recorded in the95 note. Hence its encoded-instance family
satisfies the additional first-zero promise as well as the other
completeness hypotheses. No ordinary numerical input conversion is hidden.

## 5. Exact evidence and scope

The checker verifies both complete93 sources, the shared-AH identity,
the full reordered packing, and every unchanged non-index comparison.
It separately checks signed first-block rejection, pre-power guard bounds,
constant parity, and the original projector with restoration of Gstar.

Fresh history verification covers123 genuine positive-startup first-zero
traces and382 actual source rows. It builds246 complete canonical and
padded outer tuples across both leading branches. Every tuple checks all
eight new outer comparisons, all nine individual masks, restored Gstar,
the six unchanged non-index95 outer comparisons, and its new exact
valuation and kernel scale hypotheses. All246 indices differ from the95
packing. The canonical indices split60 even and63 odd, so63 selected
witnesses require the wrapped padding. A separate odd-beta regression has
beta=3, appendant10 and the genuine trace001100->1000->010->0. Both complete
canonical and padded outer tuples pass with opposite index parities. This
directly exercises the strengthened odd-beta converse. The positive43 extension is proved
by its converse; enormous auxiliary values are not materialized.

The projector regression covers88 complete candidates with16 accepted
row projectors. There are176 constant/padding parity cases,178 signed
first-field cases including58 negative rejections, and36 scalar guard
bound cases. Excluded terminal types, missing startup properties and14
simulation cutoffs remain explicitly outside the finite accepted set.
These are bounded implementation checks of the general proof, not
materialized Neary simulations or an assertion about a raw-input bound.
