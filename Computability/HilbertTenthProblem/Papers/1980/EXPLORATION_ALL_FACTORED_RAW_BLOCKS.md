# All three raw packing factorizations: 105 operations

Combine the guard and program factorizations of
`EXPLORATION_FACTORED_RAW_BLOCKS.md` with the zero/complement fusion of
`EXPLORATION_FUSED_ZERO_COMPLEMENT.md`. The complete result has **105
operations, 55 multiplications and 50 additions/subtractions**, with
**33 positive unknowns and 21 equations**. All twelve semantic mask
positions remain. Full independent proof/source review and fresh
verification pass. The established universal frontier remains 90.

The source and receipt are `../verification/explore_all_factored_raw_blocks.py/.json`.

## 1. The evaluated packing and exact sources

The source keeps the 109 unknowns except B0,B1,Z,TC,TV. Define

    Prog=(1+q^2)(C+qV)+q^2[J+(q Zstar-S)H],
    ZeroPair=H+(2J)D,
    Rest=Km+q(ZeroPair+q^2 Prog),
    Guard=(q+1)(A0+q^2 A1)+(1+q^2)T,
    Praw=Kp+q(Guard+q^4 Rest).                   (1)

The existing q^2,q^4,q^6,q^12 power chain is evaluated once before
packing. The register 1+q^2 is evaluated once and shared by Prog and
Guard. The register 2J is already required by geometry and routing.

The five deleted coordinates have the formal replacements

    B0*=A0+T, B1*=A1+T, Z*=H-D,
    TC*=C+J-SH, TV*=V+Zstar H.                  (2)

On the retained source q=2J+1, equation (1) is exactly the original
twelve-field raw packing with replacements (2). Off that source, its
raw polynomial differs by -(q-2J-1)D q^6. Thus the new doubled-index
packing residual is precisely

    old109_pack[all five substitutions] + 2q^6 D old_q_geometry. (3)

The packing source 2r+1=q^12+2Praw and positive bound r+beta=q^12
remain. All other retained sources are the original sources after
(2); the five deleted defining equations become identities. The full
checker verifies every source against the actual schedule, including
(3) and the correctly reindexed auxiliary norm correction.

## 2. Restore the program and guard words before decoding

The guard replacements are positive immediately. The formal Z* may
be negative, so positivity of every separate lower field cannot be used
to invoke the 106 proof unchanged. Instead group its two positions.
For q=2J+1>=3, the expression

    Z*+qD=H+(q-1)D

is strictly positive. Hence the full lower-eight polynomial

    Low8=Kp+q Guard+q^5 Km+q^6[H+(q-1)D]

is positive, using only supplied positive quantities.

Set Q=V+(Zstar-S)H>0. The same exact difference used in the standalone
program proof now holds with this grouped Low8:

    Praw-Qq^11
      =Low8+Cq^8+Vq^9+(C+J)q^10+SH(q^11-q^10)>0. (4)

The global offset and positive packed slack imply
Praw<=(q^12-1)/2. Equations (4) and q=2J+1 imply Q<=J, so
J>(Zstar-S)H>SH. Consequently TC*=C+J-SH>0 and TV*=V+Zstar H>0.
This proof precedes all kernel and digit arguments and does not assume
Z*>=0. It also gives the top-field bound TV*<=J: after restoring TC*,
all lower contributions are positive when the zero pair stays grouped.
Thus the full intrinsic-width inequality R-1>2Zstar follows as before.

Restore B0,B1,TC,TV by (2). All are positive and satisfy their defining
equations. The exact identity (1) then yields a full solution of the
independently proved zero-fused 108 system, with every other supplied
value unchanged. This provides a precise order of reconstruction that
avoids presupposing the missing Z coordinate is positive.

## 3. Restore the zero word and the complete universal interface

Apply the zero-fusion theorem to that reconstructed solution. Its
preliminary bounds give D<J and D<4H. Routing uses
Zstar>hs+4hz; the unchanged fixed mask already satisfies this condition.
The grouped pair has no outgoing carry. If Z*=H-D were negative, its
lower actual chunk would be q+Z*>J, contradicting the Boolean native
mask. Thus Z*>=0, and all twelve semantic chunks decode in order.

The full positive-native 114 system can then be restored, including
native J+Z*>0 when Z*=0. Its soundness theorem recovers the fixed
annotated compiler path. The compulsory initial zero request proves
Z*>0. This is the independently established zero-fusion proof; it is
not an additional assumption of the combined construction.

All five restored coordinates now form a complete positive 109 solution.
Each restoration is unique. Conversely, delete the five coordinates
from any positive 109 solution and use the polynomial identities to
obtain a 105 solution. The maps are inverse and preserve the exact
packed integer, parity, input, every retained witness and every Pell
coordinate. The same fixed program and numeral choices therefore give
the full ordinary-input universal family, with the unchanged positive
Pell converse. No semantic mask is omitted.

## 4. Arithmetic and evidence

The independently checked combined guard/program schedule costs 106.
Its zero pair still has the two old Horner stages plus the separate
Z+D comparison. Replace those two stages, costing 2M+2A, by

    q^2 Prog, (2J)D, H+(2J)D, q^2 Prog+[H+(2J)D],

again costing 2M+2A. Delete the single addition Z+D. This gives
106-1=105=55M+50A, removes one supplied coordinate and one equation,
and leaves 33 positive unknowns and 21 comparisons.

The source checker compares directly with all five substitutions in
109 and the geometry correction, rather than trusting only the sum
of isolated savings. It reruns both prerequisite arithmetic checks,
the local zero-pair borrow checks, and a fresh composed positivity
regression with formally negative Z and TC values. Some negative Z
cases deliberately pass the preliminary packed bound; the subsequent
native-mask proof is still required. All nonpositive TC cases fail
that bound, as (4) requires. These algebra tuples are not claimed full
controller solutions.

The complete canonical packed integers and valuations from 106 and
its predecessors are explicitly inherited unchanged. Fresh source
transport takes its twelve outer comparisons to eleven. The full
positive converse supplies enormous Pell coordinates without asserting
their numerical instantiation in the finite regression.
