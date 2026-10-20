# Independent review of the source reassociation used by K220

## The actual candidate needs only closed reassociation

The source files inspected were the K221 baseline, `decoder_work/reencode_seed/sites.json`,
and `decoder_work/weak_reencode/found/sites.json`.

The first rotation is at source prefix `11101001001101`:

\[
 ((A,B),C)\longmapsto(A,(B,C)).
\]

The primitive leaf counts of A, B, C are respectively 52, 27, 295. All three
boundary triples are exactly `(0,0,False)`.

The second rotation, applied to that seed, is at prefix `111010010011011`:

\[
 (A,(B,C))\longmapsto((A,B),C).
\]

The leaf counts are respectively 27, 52, 243; again all three boundary
triples are `(0,0,False)`.

I independently checked exact source-tree reconstruction at both stages,
identity of the complete 4,744-primitive word, and equality of the full
guarded control-flow graph using the arithmetic resolver and the independent
subtree-interval resolver. The number of guarded cases remains 6,167.
The actual proof therefore does not depend on the broader weak-boundary
criterion used to explore rotations.

The relevant expansion of the search space was physical, not logical:
state 132 had an old read-1 transition `(1,L,163)` rather than a pure
right-moving decoder edge. Reencoding its new source role permits the
rotation while a pure-decoder-only search would skip it. This must be
justified by the resulting table's complete source-to-binary interface,
not by assuming that a nonpure edge can be moved literally.

## The weaker reassociation lemma is nevertheless sound

Let `break(X)` and `continue(X)` be the maximum unresolved outward break and
continue depths of a source subtree, as calculated by the retained boundary
recursion. The reassociation

\[
 (A,(B,C))\leftrightarrow((A,B),C)
\]

preserves the primitive guarded CFG whenever

\[
 \operatorname{break}(A)=0,\qquad
 \operatorname{continue}(C)=0.
\]

B is unrestricted. A may have outward continues, C may have outward breaks,
and none of the factors needs to be halt-free for this source-CFG statement.

To prove this, let p be the prefix of the whole reassociated block. Relative
paths to A, B, C change as follows:

| Factor | First tree | Second tree |
|---|---|---|
| A | `p0` | `p00` |
| B | `p10` | `p01` |
| C | `p11` | `p1` |

Break/decrement control counts zero edges; continue control counts one edges.
A gains one zero edge, so no A-break is affected when every such target is
resolved inside A. A's outward continue counts are unchanged. C loses one
one edge, so no C-continue is affected when every such target is resolved
inside C. C's outward break counts are unchanged.

For B, the new prefixes contain the same number of zero and one edges.
Internal targets are unchanged. Its first outward break skips the right
subtree `(B,C)` in the first tree, or the whole block in the second; both
have exactly the same ending ordinal. Its first outward continue targets
the whole block in the first tree, or its left subtree `(A,B)` in the
second; both have exactly the same starting ordinal. Further outward
controls see the same external context p after consuming one zero or one
one respectively. This proves equality of all B targets even when B has
outward control instructions.

All increment successors are fixed by the unchanged ordinal word, and
halts stay at the same ordinal. Thus every guarded instruction has the
same register effect and successor ordinal. This is an equality of whole
register-program transition systems, not a bounded execution observation.

## Limits of the lemma

The lemma concerns the source's interval/control semantics. A changed binary
parenthesization still needs a valid program-counter encoding, a no-stray
suffix check for the arithmetic successor resolver, the literal compound
decoder relation, all primitive source-to-binary interfaces, and blank-start
initialization. Those obligations are not supplied by the source lemma.

Likewise, folding native state 202 into 171 through helper 7 needs an
invariant or complete symbolic runtime proof covering every relevant entry
context. A bounded execution or the visual resemblance of two transition
rows is insufficient. Root and the decoder agent are checking those
separate obligations for the literal 220-state table.
