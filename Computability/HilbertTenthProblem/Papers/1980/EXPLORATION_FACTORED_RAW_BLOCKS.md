# Shared guard and program block factorizations: 106 operations

Combining the two independently proved 108-operation factorizations and
sharing their coefficient \(1+q^2\) gives a complete universal family with
**106 operations: 55 multiplications and 51 additions or subtractions**,
34 positive unknowns and 22 source equations. All twelve semantic masks
remain. The established universal frontier remains 90; this improves the
separate raw-counter/controller construction.

The exact source, full schedule and receipt are
`../verification/explore_factored_raw_blocks.py/.json`. The two predecessor
proofs are `EXPLORATION_GUARD_BLOCK_PACKING.md` and
`EXPLORATION_FACTORED_RAW_PROGRAM_BLOCK.md`. Both start from the same frozen
109-operation system in `EXPLORATION_SHARED_PELL_INDEX_OFFSET.md`.

## 1. The combined source

Keep all the 109 coordinates except the four supplied fields
\(B_0,B_1,T_C,T_V\), and delete their four defining equations. Define their
mathematical replacements

\[
 B_0^*=A_0+T,\quad B_1^*=A_1+T,\quad
 T_C^*=C+J-SH,\quad T_V^*=V+Z_*H.                 \tag{1}
\]

The fixed program constants \(S,Z_*\), and every other fixed numeral, are
unchanged. In particular \(Z_*>3S>0\). All remaining supplied coordinates
are strictly positive.

Use the following combined polynomial in place of the twelve-field raw
packing:

\[
\begin{aligned}
 B_{\rm prog}&=(1+q^2)(C+qV)+q^2\{J+(qZ_*-S)H\},\\
 Q&=K_-+qZ+q^2D+q^3B_{\rm prog},\\
 G&=(q+1)(A_0+q^2A_1)+(1+q^2)T,\\
 P_{\rm raw}&=K_++q\{G+q^4Q\}.
\end{aligned}                                                   \tag{2}
\]

The retained packed equations are

\[
 2r+1=q^{12}+2P_{\rm raw},\qquad r+\beta=q^{12}.   \tag{3}
\]

All other retained 109 source equations are unchanged. The doubled index
on the left of (3) is still the already charged Pell register
\(\mathtt{tr1}\). The power chain \(q^2,q^4,q^6,q^{12}\) is charged once
and evaluated before (2).

Expansion, for arbitrary integer coordinates, gives

\[
\begin{aligned}
P_{\rm raw}={}&K_++qB_0^*+q^2A_0+q^3B_1^*+q^4A_1
 +q^5K_-+q^6Z+q^7D\\
 &+q^8C+q^9V+q^{10}T_C^*+q^{11}T_V^*.
\end{aligned}                                                   \tag{4}
\]

Thus the twelve conceptual fields keep exactly their old values and
positions. No digit, carry or power-of-three assumption enters (4).

## 2. Positive reconstruction before the kernel

The guard replacements \(B_i^*=A_i+T\) are positive immediately. All eight
lower conceptual fields in (4) are consequently positive. Let \(L_8\)
be their polynomial. Then \(L_8>0\).

The retained geometry \(q=2J+1\) makes \(q\) an odd integer at least three.
Equation (3), together with positive \(\beta\), gives

\[
 P_{\rm raw}\le(q^{12}-1)/2.                     \tag{5}
\]

To recover the only potentially signed replacement \(T_C^*\), put
\(Q_*=V+(Z_*-S)H>0\). The exact difference

\[
 P_{\rm raw}-Q_*q^{11}
 =L_8+Cq^8+Vq^9+(C+J)q^{10}+SH(q^{11}-q^{10})>0  \tag{6}
\]

also proves \(P_{\rm raw}>0\). Since
\(\lfloor(q^{12}-1)/(2q^{11})\rfloor=J\), (5)--(6) imply

\[
 Q_*\le J,\qquad J>(Z_*-S)H>SH.
\]

Therefore \(T_C^*=C+J-SH>0\), while
\(T_V^*=V+Z_*H>0\) directly. All four reconstructed fields are now
positive, before any power recovery, Pell inference or digit decoding.
The retained geometry \(H(R-1)=2J\) also recovers the width bounds from
the standalone program-factorization proof; after positivity, the usual
top-field bound yields \(T_V^*\le J\) and \(R-1>2Z_*\).

From any positive 106 solution, restore the four fields by (1). Their
definitions hold, (4) restores the old packing, and every other retained
source is identical to 109. Conversely, delete those four fields from a
positive 109 solution and use (4). These maps are inverse and preserve all
remaining coordinates, including \(r,\beta\) and every Pell auxiliary.

This is an exact positive-witness bijection, not a conditional decoding
argument. In particular all twelve masks, the fixed program, ordinary raw
input, the first-positive-return acceptance proof, prefix positivity and
the even-index positive Pell construction transfer unchanged. Necessity
requires no wider frame or re-encoding. The same fixed compiled program
therefore represents the same recursively enumerable set in 106
operations.

## 3. Exact operation count

The standalone guard factorization replaces its former \(5M+7A\)
segment by \(5M+6A\), saving one addition. The standalone program
factorization replaces its former \(5M+6A\) segment by \(5M+5A\), saving
another addition. Their affected definitions and Horner segments are
disjoint.

Each standalone replacement computes \(1+q^2\). In (2), evaluate it once
and use it in both \((1+q^2)(C+qV)\) and \((1+q^2)T\). This saves a third
addition, with no extra multiplication. The exact total is

\[
 109-1-1-1=106=55M+51A.
\]

The checker starts from the guard-108 schedule, inserts the program
factorization, and removes the second definition of the shared
coefficient. It checks that \(q^2\) and \(1+q^2\) are each constructed
exactly once and that the latter has both intended consumers. All source
comparisons are checked directly against the four substitutions in the
original 109 source. The existing auxiliary norm correction uses the
source's original-index mapping, so deleting four earlier comparisons
does not silently change the required correction.

Deleting four positive unknowns and four source equations from 109 leaves
34 positive unknowns and 22 equations. This coordinate reduction does not
delete any of the twelve conceptual mask positions.

## 4. Verification scope

The fresh complete source check passes 106 operations and all 22 source
comparisons. Both standalone 108 source checks are rerun as dependencies.
There are 576 additional combined polynomial cases, including signed
fields, and 192 cases testing the strict positive lower-block difference;
16 satisfy the packed bound. The independent program positivity
regression is also rerun, including all its formally nonpositive test
words, which the packed bound rejects.

Canonical evidence is explicitly inherited from the just-rerun standalone
guard-108 receipt. Its exact packed integers for inputs 1 and 2 are
unchanged, as are their central valuations 217152 and 325728. The new
symbolic source transport takes the 14 predecessor outer comparisons to
12 retained outer comparisons. The receipt does not call this a fresh
large-integer rerun and does not claim to instantiate enormous Pell
auxiliary tuples. Their existence follows from the exact witness
bijection and the proved predecessor construction.
