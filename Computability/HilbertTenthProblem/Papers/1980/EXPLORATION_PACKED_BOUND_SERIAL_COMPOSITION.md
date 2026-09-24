# Bound the packed certificate directly: 115 operations

This construction replaces the program/guard bound of the complete
117-operation complementary-zero construction by

    r+beta=D0=q^12.                                      (1)

The positive variable r is already equated to the twelve-field packed
word P. The old three additions computing TC+TV+T+beta are replaced
by the one addition in (1). The complete count is **115 operations,
56 products and 59 additions/subtractions**, with the same 43 positive
unknowns and 31 equations. Independent complete proof/source audits
and fresh verification pass; the maintained universal frontier is still 90.

The source/checker is
`../verification/explore_packed_bound_serial_composition.py`.
The predecessor is `EXPLORATION_COMPLEMENT_ZERO_SERIAL_COMPOSITION.md`.
All its source equations and fixed constants are retained except the
single bound. In particular, both sign flags, both zero flags, all four
native program fields, the width threshold, and the complete Pell
kernel remain present.

## 1. The kernel has its bounds before any digit interpretation

Write J=(q-1)/2, W=R^3 and H(R-1)=2J. The paid fixed width gives
R>=9, while q=Wv>=R^3>=729 and H<=J/4. The packing order remains

    FKplus,G0,F0,G1,F1,FKminus,FZ,FZbar,NC,NV,NTC,NTV.

All fields are positive integers. Thus (1) and r=P imply

    q^11<P<q^12=D0, D0<P^2, P>=27, D0>=81.

These are the complete general-scale bounds required by the retained
43-operation kernel, independent of individual field sizes. It gives
q a power of three and v3(binomial(2P,P))>=log_3(D0). Since P<D0,
the unit-two native-mask theorem applies directly. Every normalized
base-q chunk of P has all ternary digits in {1,2}, hence is at least J.
Its lowest ternary digit is two. This does not yet assert that the
supplied fields equal those normalized chunks.

## 2. Recover the two zero flags before bounding T

Let c_i denote the nonnegative carry into field i, with c_0=0; field i
has normalized value (field_i+c_i) mod q and outgoing carry c_(i+1).
There is no final carry because P<q^12.

The sign-pair sum is 2J+H. In particular FKplus<2J+H<q+J. A carry
from FKplus would therefore leave a remainder below J, impossible.
Thus c_1=0, FKplus is native and FKplus>=J. Put

    A=F0+F1-2J, delta=FKplus-FKminus.

The sign pair gives delta=2(FKplus-J)-H>=-H. The retained time source
is (W-1)A=-W*delta-2x, so

    A<WH/(W-1)<=729J/(4*728)<J,
    F0,F1<3J.                                      (2)

Here A need not yet be nonnegative. The complementary top equation
and positive FZbar give, before either zero flag is decoded,

    6(J-T)=(R-3)(FZbar-J),
    T<(R+3)J/6.                                    (3)

Equations (2)--(3) imply G_i+1<Rq. Indeed
G_i+1<(R+21)J/6+1<R(2J+1) for R>=9.
Also F_i+R-1<2q, because R<J+2 follows from q>=R^3.
Consequently the two guard/base pairs have carries

    c_2<=R-1, c_3<=1, c_4<=R-1, c_5<=1.

Since FKminus<=J+H, one has FKminus+c_5<=J+H+1<q.
Thus c_6=0, regardless of what happened inside either guard pair.

Now FZ<2J+H<q+J. Its normalized chunk cannot have an outgoing
carry, for that would leave a remainder below J. Hence FZ is native,
FZ>=J and c_7=0. The pair sum then gives FZbar<=J+H<q, so FZbar
is also native and c_8=0. In particular FZbar>=J. The top equation
now proves T<=J. Both zero words are therefore typed before this
strong guard bound is used.

## 3. Recover every raw counter field

Revisit G0=F0+T, using F0<3J and T<=J. If G0 had an outgoing
carry, its native remainder would require G0>=q+J=3J+1. Thus
F0>=q. But then F0+1<q+J, so the following base field, with
incoming carry one, would have a remainder below J. Contradiction.
The guard cannot have carry more than one because G0<4J<2q.

Therefore G0 has no outgoing carry. The following F0 has no incoming
carry and is below 3J<q+J; the same remainder argument excludes its
outgoing carry. Both supplied fields equal their native chunks.
Repeat the identical argument for G1,F1. All four supplied fields
are native, their carries vanish, and FKminus is now its unshifted
native chunk as well.

The native sign pair gives Boolean complementary subsets of H, and
the zero pair does the same. Let Kplus=FKplus-J and D=FZbar-J.
Thus 0<=Kplus,D<=H, and the top mask has exactly the predecessor's
meaning: a permanent top bit and a full zero guard wherever D=0.
The raw-counter proof now recovers ordinary nonnegative +/-1 histories,
the raw input [2x,0,0], the zero target, first-plus condition and complete
even banks. No program support interpretation was needed for these steps.

## 4. Routing bounds C and then decodes the program fields

The last supplied field already satisfies NTV<q, simply because it
is positive and occupies the highest base-q position of P<q^12.
The retained adapters and forbidden-support equality give

    TV=NTV-J<=J, 0<V<TV<=J.

The strict inequality follows from TV=V+Zall*H and Zall,H>0.
Define the proof expression O=V+hs*Kplus+hz*D. The fixed threshold
Rmin>12(KS+Zall+1) implies (hs+hz)H<J/6, whence

    0<O<7J/6<q.                                    (4)

The fixed table has K>=3, S>=I>=1, gS<R and hence gI<R and g<R.
Therefore

    RK-g>gI+R>0.

The cyclic routing source and (4) imply

    (RK-g)C=gI(q-1)+RO<(gI+R)q<(RK-g)q,

so C<q. This bound has used neither Booleanity of C nor its source
support: only the typed counter flags, top-field bound and exact route.

Since the first eight fields have no carry, NC=J+C<q+J has no
incoming carry. A native remainder again excludes NC>=q. Thus NC
is its native chunk, NC<q and C is Boolean. Next NV=J+V<q, so
NV is decoded without a carry. The source-support equation gives

    NTC=J+TC=NC+J-SH<q+J.

Its native remainder excludes overflow as before. Finally NTV<q
has no incoming carry and is also its supplied native chunk. All
twelve fields have now been recovered.

In particular TC and TV are positive Boolean words at most J, so

    TC+TV<q.                                       (5)

The predecessor's program-support, count-marker and label arguments
apply in full. They recover exactly one state per row, only allowed
edges, the correct sign, and the complement of the true zero requirement.
The initial and final vertices coincide with the same first-return
acceptance contract. No bare syntactic cycle is treated as acceptance.

## 5. Exact positive witnesses and universal interface

To restore the complete 117-operation predecessor at the same width,
set beta_old=q-T-TC-TV. Its positivity is proved after the labelled
history has been decoded. The last active counter source is one,
has sign minus and cannot request a source-zero test. Hence its D
bit is one and its T block is R/3. Exactly the retained merged-bound
width proof gives

    T<=q/3+q/(2R)-1/2, TC<=J, TV<(KS+Zall)H,
    T+TC+TV<q.

Every other supplied coordinate, including every Pell witness, stays
the same. Thus every new solution yields a positive old solution.
Conversely, a predecessor solution has all twelve fields native and
P<q^12. Set beta_new=q^12-P>0 and leave every other coordinate
unchanged. This satisfies (1). The slacks on both sides are uniquely
determined by the unchanged coordinates, giving an exact bijection
of positive witnesses at the same width.

The complete ordinary-input universal compiler therefore transfers
without a change to its graph, program constants, input, halt event
or positive kernel converse. This 115-operation family is an alternative
universal bound above the existing 90-operation frontier.

## 6. Exact evidence and its limits

The full primitive/source checker verifies 56 multiplications and 59
additions/subtractions, all 31 source comparisons, and the unchanged
acyclic auxiliary-norm correction. Exhaustive finite guard/base checks
cover 446,226 assignments, including 2,667 accepted native pairs, and
1,008 coarse carry extremes. Two scalar inequalities also have exact
polynomial proofs with positive coefficients after shifting their
parameters to the stated lower bounds.

Both full canonical histories are checked afresh at a counter width
of 1,506 ternary digits. Each satisfies all 21 new outer equations and
all 21 predecessor equations after restoring its old slack. Their
packed words have 343,721 and 515,581 bits, with exact valuations
216,864 and 325,296. All twelve fields, the positive slacks, even
unit-two index and complete kernel bounds are checked. The enormous
Pell coordinates are supplied by the proved positive converse, not
materialized by these finite tests. Independent reviewers read the
full proof and source; a separate full rerun reproduced these results.
