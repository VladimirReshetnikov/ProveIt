# Routed parity permits zero-pair fusion in doubled coordinates: 104 operations

This separate successor to `EXPLORATION_DOUBLED_RAW_COORDINATES.md`
eliminates its supplied positive zero word Z. It has **104 operations:
56 multiplications and48 additions/subtractions**,33 positive unknowns
and21 equations. It retains the original positive counter guards.
It does not compose with the complemented-guard construction merely by
substitution. The established universal frontier remains90.

The exact source/checker is
`../verification/explore_doubled_zero_fusion.py/.json`. Here J=q-1 is
the doubled repunit, and all raw field values are eventually shown to
have ternary digits zero or two. The prerequisite doubled105 proof
is a separate audit gate; its theorem is used only after the new
positivity issue is resolved below.

## 1. The arithmetic and its source correction

The two adjacent conceptual fields Z,D satisfy Z+D=H. Substitute the
mathematical expression Z=H-D into their packing contribution:

    Z+qD=H+(q-1)D=H+JD.

The register J is already supplied. With Bprog denoting the high
four-field program block, replace

    D+q Bprog, Z+q(D+q Bprog)

by the four instructions

    q² Bprog, JD, H+JD, q² Bprog+(H+JD).

Both arrangements cost2M+2A. Deleting the old comparison Z+D=H
therefore saves its one addition and removes the one supplied unknown.
The existing q² power is used; it is not recomputed. This gives
105-1=104=56M+48A.

The retained radix source is s0=q-J-1. Off that source, the evaluated
new raw packing differs from the substituted old packing by
-q6 D s0. Since the doubled-coordinate packed source is now
2r+1-q12-P rather than2r+1-q12-2P, its exact source identity is

    new_pack=old_pack[Z:=H-D]+q6 D s0.

Every other retained source is the predecessor source with that
substitution, and the deleted zero-pair source becomes zero identically.
The checker verifies all21 comparisons, including the unchanged
preceding-norm correction and this undoubled packing correction.

## 2. Bounds before any typing

Do not assume H-D is initially nonnegative. Its grouped packing
contribution H+(q-1)D is strictly positive. The other six lower
conceptual fields are positive; hence the lower eight-field polynomial
is positive. The complete high-program argument from doubled105
therefore still recovers TC=C+J-SH>0 before typing, then TV<=J and

    R-1>2Zstar, R>=9, q>=R³, H<=J/4.

All this uses the positive factored expression, not a sign assertion
about its formal Z coefficient. The retained positive sign pair and
time equation give A=A0+A1<9J/32. The supplied T is still positive;
the retained top equation gives

    0<T<J,
    0<D<6J/(R-3)<=J,
    D<3(R-1)H/(R-3)<=4H.

Thus Z=H-D>-J, although it may be negative. Each positive guard
Ai+T is below2q and its following track satisfies Ai+1<q.
The entire zero pair X=H+(q-1)D satisfies0<X<q², because D<J=q-1
and H<=J/4. It has no outgoing carry, even if its low formal field
is negative.

The fixed forbidden-position constant obeys Zstar>hs+4hz. Hence

    O=V+hs Kp+hz D<V+Zstar H=TV<=J<q.

As in doubled105, R>2gI, R>g and K>=3 imply RK-g>2gI+R, giving
C<q from the unchanged route. Also V<TV<=J and0<TC<2q. Grouped
positivity gives P>q11 and q11<r<q12<r². All43-kernel hypotheses
hold without assuming Z>=0.

## 3. Decode the program past the unresolved zero pair

The same kernel and exponent-remainder geometry lemma recover
q=R^u with q,R powers of three, and H even. Also J=q-1 is even.
The packed-index identity and native mask imply that the complete
raw P has only ternary digits zero or two.

Kp is its first in-range even chunk. Each guard/track pair may have
one internal carry, but has no outgoing carry because Ai+1<q.
Thus Km is an actual even chunk. The zero pair X lies below q²,
so its two normalized chunks likewise have no carry into the program
block. Consequently C and V, already below q, are even actual chunks.

Now TC=C+J-SH is even. Its preliminary bound is0<TC<2q. A single
carry would give odd low chunk TC-q, impossible under the doubled
mask. Hence TC<q and it and TV are even actual chunks too.
At this point the zero pair has deliberately not yet been decoded
as Z,D. Only its lack of outgoing carry was needed.

## 4. The route forces even D and excludes a negative Z

Use the exact route equation modulo2:

    (RK-g)C=(gI)(2J)+R(V+hs Kp+hz D).

C,V,Kp,J are now even. R and the fixed hz are odd powers of three.
All terms except R hz D are even, so D is even. This conclusion
does not assume the zero label has already been typed.

Since H is even, Z=H-D is even as well. If Z<0, then-J<Z<0
and the actual zero-pair chunks are q+Z and D-1. The first is odd
because q is odd, contradicting the doubled mask. Therefore Z>=0.
As D<q and0<=Z<H<q, these are now the actual two chunks. Both
have digits zero or two, and they sum to the doubled row-head mask.
Their halves are typed complementary head subsets.

This routed parity step is necessary. The unrestricted doubled mask
admits the local example q=9,H=2,D=3,Z=-1, whose pair is26, or
ternary222. Its two chunks8 and2 both have digits zero or two.
But odd D contradicts the route parity once its other relevant
coordinates are even. The checker retains this example explicitly;
it does not mislabel local masking alone as a sufficient argument.

## 5. Strict positivity and exact positive extension

Divide the already typed program words and flags by2. Their complete
marked-ROM equations have the original support, row bounds and count
markers. Thus the program path and both opcode labels decode before
counter-track carries need to be resolved. The compulsory initial
prefix visits its true-zero annotated second lane, so the Z/2 word
has a one coefficient there. Consequently Z>0.

For the concrete fixed table, the only edge out of initial state zero
goes to state one, whose zero label is one; the checker verifies this
fixed fact. For each represented recursively enumerable set, the
existing marked-prefix compiler supplies the same property. This
argument is independent of the counter-track interpretation: it
establishes a requested zero label, not yet its counter-value truth.

We can now restore Z=H-D as a strictly positive supplied coordinate
of doubled105. Its source equation holds identically; the packing
correction vanishes under q=J+1. Every other source and every other
positive coordinate are unchanged. Thus the full doubled105 theorem
applies, including its first-nozero-label argument and initial-residue
exclusion of the internal guard carries. It recovers the same ordinary
input acceptance predicate.

Conversely, from any doubled105 solution delete Z and use the exact
pair identity. Its retained coordinates, P,r,beta and all Pell
auxiliaries are unchanged. The two maps are inverse because the
eliminated Z is uniquely H-D. This is an exact positive-witness
bijection with doubled105 at its existing frame; no new width
condition or parity change is introduced by this fusion.

## 6. Evidence scope

The source checker freshly verifies all104 primitives and21 source
comparisons, as well as the q-J-1 correction and the route-parity
constant hypotheses. Its bounded pair regression includes negative
formal zero words, actual odd-D local mask aliases, their rejection
under routed parity, and locally allowed Z=0 cases. The last cases
are excluded only by the separate marked-prefix argument.

Both complete doubled105 canonical outer tuples and valuations are
recomputed. The new source identity then transports their12 old outer
comparisons to11 retained outer comparisons with identical packed
indices. The receipt distinguishes that exact transport from an
independent numerical instantiation of huge Pell coordinates; those
are supplied by the unchanged positive converse. Full independent
proof/source reviews and fresh complete verification pass.
