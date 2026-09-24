# State-top doubled grid packing in 100 operations

Swapping the last two complement pairs of the formal 100 construction closes
its missing joint-recovery argument. The result has **100 operations:
55 multiplications and 45 additions/subtractions**, with 34 positive unknowns
and 22 equations. It retains all twelve mask fields. The positive supplied
zero-request word is removed and is reconstructed from the decoded fixed
controller, including its mandatory true-zero prefix.

This improves the complete alternate 101 architecture. The established
universal frontier remains 90. The earlier unreordered attempt remains open; the new theorem depends
only on the published 101 construction.
The verified 101 predecessor is also unchanged.

The new source/checker and receipt are
`../verification/explore_state_top_doubled_grid.py/.json`. The checker
depends directly on the published 101 checker; the small Z-elimination
adapter is restated locally, without importing the earlier open exploration.

## 1. Exact source and the fixed program conventions

Use the constants, supplied variables and ten retained 43-operation Pell
equations of `EXPLORATION_DOUBLED_GRID_COMPLEMENTS.md`, except that Z is no
longer supplied and its equation Z+D=H is omitted. Write D for Dzero, t for
Tgap, C,V for PC,PV, and z for zgrid. The conceptual fields, in increasing
base-q positions, are now

    Kplus,Kminus,H-D,D,t-A0,A0,t-A1,A1,zH-V,V,SH-C,C.             (1)

Let

    X=Kminus+q²[D+q²(A0+q²(A1+q²(V+q²C)))],
    P=(q-1)X+(1+q²)(H+q^4t)+q^8H(z+q²S).                      (2)

Their literal concatenation equals (2) when the sign equation holds. The
twelve outer equations are

    q=J+1, q=R³v, W=R³, H(R-1)=2J,
    Kplus+Kminus=H,
    (B0-1)(Zon+z)=R-1,
    6t=(R-3)D,
    W(A0+A1+Kplus-Kminus)=A0+A1-4x,
    4x+alphaI=R,
    2r+1=q^12+P, r+beta=q^12,
    (RK-g)C=2gIJ+R(V+hs*Kplus+hz*D).                           (3)

In the actual source the second equation is q=Wv; the separately computed
W=R³ supplies the displayed interpretation. Every unknown in (3) is
positive, as is the external input x. Conceptual complements in (1) may
initially be negative or zero. The Pell scale is D0=q^12.

The two program pairs of 101 are interchanged at equal cost. In its
factored schedule, exchange C,V in the highest Horner step and exchange
the fixed S and variable z in the high base coefficient. Delete only the
addition Z+D and its equation/positive variable. The resulting count is
100 = 55M + 45A, with the same power chain and kernel.

For G=q-J-1 and Fsign=Kplus+Kminus-H, the computed packed register is

    Pconcept-GX-Fsign.

Thus the packed-index comparison has exact earlier-source correction
GX+Fsign. The prior auxiliary-norm correction is unchanged. The checker
expands all 22 source comparisons; no power or numeral product is free.

The fixed controller uses the usual positive distinct Sidon coordinates
a_i, with its cyclic initial state at the minimum a_0. It has at least two
states. Its table has edge terms, one marker term d-a_i for each state,
and sign/nozero terms d+bs-a_i and d+bz-a_i where applicable. The sign and
nozero ports are hs=3^(d+bs), hz=3^(d+bz), with bs,bz above all state
coordinates and bz above bs. The exponents of K are distinct. Consequently

    min exponent(K)=d-amax, uniquely;   K<hz.                  (4)

Every edge exponent exceeds d-amax because its destination coordinate is
positive; the label exponents do too. All table exponents are strictly
below d+bz. These are properties of the same standard fixed encoding, not
new constraints on supplied witnesses. Initial-state numbering can be
chosen first when compiling the fixed program.

As in 101, all predecessors of cyclic entry have zero-request label zero.
The marked universal prefix also ensures that every positive return visits
a true-zero request. The former follows from the nozero second bank of
every physical macro; the latter is the verified mandatory prefix in
`EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md`. These conventions will restore
strict positivity of the removed word only after the controller is decoded.

## 2. Pre-power bounds and use of the kernel

The retained fixed grid gives, before digit interpretation,

    R-1>(B0-1)Zon>=8Zon,
    Zon>max(4S,8(hs+hz),g(I+1),(K+g)(S+1),81).

In particular R>=27, R>K, R>g, R>2gI and R>2gS. Since W=R³ and v is
positive, q>=R³. The positive sign pair and time equation give, with
A=A0+A1 and delta=Kplus-Kminus>-H,

    0<A<WH/(W-1)<(q-1)/4,
    H=2(q-1)/(R-1), SH<q/4, 0<zH<q/4.                       (5)

These are the same elementary pretyping estimates as 101. No bound on D or
t is imported from the deleted equation.

Every term of the factored expression (2) is positive. The index/bound
equations imply

    0<P<=q^12-1, q^12/2<=r<q^12.

The positive top contribution is now

    P>=q^10[(q-1)C+SH].                                    (6)

If C>=q+1, (6) is at least q^12, because SH>=1. Thus C<=q.
Independently the scale L=q^12 satisfies L>=81, r>=27, r<2L and L<r².
These are all the hypotheses of the general 43-operation kernel. Its
soundness applies now, with no parity assumption, and gives the power
recovery and central-binomial divisibility of 101.

As in 101, write q=3^e. The factor R³|q makes R=3^m. The equation
(R-1)|2(q-1) forces m|e: a nonzero remainder s<m would require
(R-1)|2(3^s-1), strictly between zero and R-1. Therefore

    q=R^u, u>=3, J=q-1 even, H=2(1+R+...+R^(u-1)).

The paid grid aligns m with its fixed spacing. The unit-two mask theorem
and 2r+1=L+P say that the normalized ternary digits of P are 0/2 and its
unit digit is 2. In particular every normalized base-q field is even and
at most q-1. This does not yet identify those fields with (1).

Reducing the cyclic route modulo R gives

    C=2I mod M, M=R/g a power of three, 0<2I<M.              (7)

The endpoint C=q from (6) is incompatible with (7), since q is divisible
by M. Thus C<q. Positivity in the route, together with (4), now implies

    D<(K/hz)C<(K/hz)q<q,    V<KC<Kq.                       (8)

This is the new use of the top state pair. In the old ordering the initial
bound was on V, and it did not control D.

## 3. No lower pair carries into the program block

The positive sign fields lie below H<q and are their actual doubled
chunks. For the zero pair (H-D,D), (8) gives -q<H-D<q and 0<D<q.
It may borrow once, replacing its upper field by D-1, but cannot emit a
carry into the guard block. Its sign is not assumed.

Let k=(R-3)/6, an integer after power recovery. Since 0<D<q,
t=kD<Rq/6. For either guard pair (t-Ai,Ai), the low quotient satisfies

    -1<=floor((t-Ai)/q)<R/6.

The normalized upper coefficient is Ai plus that quotient. It is
nonnegative because Ai>=1, and it is less than q/4+R/6<q because
q>=R³. Thus neither guard pair has an outgoing carry. Their internal
carries can be positive and large; no zero-carry assumption is made inside
them. There is exactly zero incoming carry to the pair (zH-V,V).

Let kappa be this pair's outgoing carry into the last state pair. Its
two-field value is zH+(q-1)V. By (5),(8),

    0<=kappa=floor((zH+(q-1)V)/q²)<K.                       (9)

The normalized state pair begins with SH-C+kappa. This lies in(-q,q):
SH<q/4, kappa<K<R, and q>=R³. Hence there is at most one borrow and
no positive carry inside this final pair. If the low field were negative,
its normalized upper field would be C-1. The mask would imply

    C=2c+1, with c a Boolean ternary word.

For every power M of three, (2c+1) mod M is odd or zero: the residue of c
is at most(M-1)/2. This contradicts the strictly positive even residue (7).
There is no state-pair borrow. It follows that

    C is an actual doubled word,  C<=SH+kappa<SH+K.          (10)

Now the route improves the old bound on V:

    V<KC<K(SH+K)<q/4+q/R<q/2.                             (11)

Indeed R-1>8KS gives KSH<q/4, while K<R and q>=R³ give K²<q/R.
Thus V<q, and its pair value zH+(q-1)V is less than q². Equation(9)
gives kappa=0. The last two normalized fields are consequently the actual
SH-C and C, both doubled words. There was no need to infer initial-state
support while kappa was still present.

## 4. The lowest ROM trit excludes simultaneous odd borrows

Divide the actual state pair by two. Both words are Boolean and their sum
is S(H/2). A sum of two Boolean ternary words has no carries. It follows
that C/2 is supported on the allowed state columns, and each row of C is
at most 2S. By R>2gS and (7), its first row is exactly 2I.
Define the mathematical next-state word

    Next=(C-2I+2Iq)/R.

It is a positive even integer, supported on the same state columns, with
fixed singleton terminal row 2I. The route becomes exactly

    KC=g Next+V+hs*Kplus+hz*D.                              (12)

All terms other than KC and V are divisible by 3^d. Meanwhile C's first
nonzero ternary digit is 2 at a_0=amin. By the unique minimum in (4), KC's
first nonzero trit is 2 at

    p=d-amax+amin<d.

Consequently (12) forces V's first nonzero ternary trit to be 2, at p.
This argument is an integer congruence modulo 3^(p+1); it does not require
the controller to have been decoded or the unknown D to be head-supported.

By(11), the junk complement zH-V lies in(-q,q). If it were negative, its
normalized upper field would be V-1, a doubled word, so V=2v+1 for a
Boolean ternary word v. But every positive 2v+1 has first nonzero trit 1:
adding one to a 0/2 word clears its initial run of twos and changes the next
zero to one. This contradicts the preceding trit 2. Therefore zH-V>=0;
both junk fields are actual doubled words, and V is even.

The cyclic route has even C,Kplus and 2J. Since R and hz are odd, its parity
now forces D even. If H-D were negative, its normalized lower field would
be q+H-D, which is odd. The doubled mask forbids this. Therefore D<=H,
and the zero pair (H-D,D) is also its actual doubled pair. This closes the
simultaneous odd-D/odd-V possibility without assuming zero-label typing.

## 5. Decode the controller and restore all strict positive witnesses

Divide H, the four program fields and the two flag pairs by two. The state
pair proves the old state support. The junk pair proves the old global-grid
complement support, because its sum is z(H/2). The sign pair and recovered
zero pair prove both Boolean labels are subsets of the same row-head word.
These are exactly the hypotheses of the already proved fixed ROM/count
marker argument of 102/101. The intermediate zero word may be zero; that
argument uses its Booleanity, head support and complement equation, not
strict positivity. It recovers a genuine cyclic controller path with its
exact sign and zero labels from(12).

Every positive return visits the mandatory marked prefix, so its true-zero
word is nonzero. Thus the removed coordinate is reconstructed as

    Z=H-D>0.

This is a conclusion of decoded control. It was not used in Sections 2-4.
The last source has no zero request by the compiler's terminal convention.
Therefore

    D>=2q/R,  t>=(R-3)q/(3R),
    A=A0+A1<WH/(W-1)<3q/R.

For R>=27 the first lower bound exceeds the last upper bound. Hence t>A
and both guard complements are strictly positive. Also D<=H now gives
t<q/3; neither guard has any internal carry. They and their following
tracks are actual doubled words. Every one of the recovered raw coordinates
is even, positive where supplied, and satisfies the decoded counter and
controller sources of 101.

The established counter argument thus gives the same ordinary-input
accepting computation, including valid source-zero tests, nonnegative
counters, complete physical banks and the first-return acceptance
convention. Changing the order of the two program pairs does not change
any of those decoded relations.

## 6. Positive converse and the changed packed index

Take an accepting computation of the already compiled universal machine.
Choose a sufficiently wide fixed-grid-aligned R with R>4x, and form its
canonical doubled 101 outer coordinates. Omit Z as a supplied variable.
Reorder the last two mask pairs as in(1). All twelve resulting fields remain
0/2 words below q, and the first field has unit trit 2. Their concatenation
is positive and below L=q^12. Define freshly

    r=(L+P-1)/2, beta=L-r>0.

The complete numerical counter history has even serial height, since each
residue chain starts even and ends zero. Thus h=H/2 is even. The sum of the
undoubled twelve fields is 2h+2(t/2)+(S+z)h, which is even. Since q is odd,
the undoubled packed word is even, regardless of field order. Also
(q^12-1)/2 is even. Therefore r is even.

The same unit-two ternary mask theorem supplies central divisibility, and
the general 43-operation positive Pell converse supplies all its positive
witnesses at this new r. No assertion is made that r or the Pell variables
are unchanged from the differently ordered 101 packing. All outer supplied
variables remain positive, including both signs, both tracks and t; the
mandatory prefix and the terminal nozero property are the same ones used
in the verified predecessor's converse.

This proves both directions for the same compiled ordinary-input predicate
with 100 operations. It does not reduce the established 90-operation frontier.

## 7. Evidence and review boundary

The checker verifies the complete 100-instruction schedule, all 22 expanded
source comparisons and the exact earlier-source corrections. It checks the
actual fixed ROM minimum, K<hz, the leading trit below the marker, and the
example's mandatory true-zero return property. It also reuses the prior
focused test of actual physical-macro and accepting-predecessor labels.

Separate finite checks cover positive internal guard carries with zero
outgoing carry, contaminated last-state pairs including real borrow cases,
the first-trit property of odd Boolean successors, and nonpower-inclusive
numerical bounds for(10)-(11). The two complete canonical examples are
rebuilt at the actual program width, with the new packed index, all twelve
masks, all twelve outer residuals, positive slacks and exact central
valuation checked. Enormous Pell coordinates are supplied by the general
positive converse and are not numerically materialized. The author gate
and two independent complete proof/source reviews and fresh verification
runs pass, with no findings. The final checker imports the published 101
predecessor directly; its elementary zero-coordinate elimination is
included in this source. These gates are separate from publication and
from the established 90-operation frontier.
