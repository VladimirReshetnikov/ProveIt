# Arithmetic and finite-list window envelopes

## Purpose and evidence boundary

The earlier PA searches deliberately left the arithmetic-engine controls at
the generic all-tape window abstraction. Their other controls could use
source-specific contexts, but an arithmetic control was not narrowed merely
because a source checker skipped its body using a box oracle.

`collect_literal_contexts.py` instead hooks the independent **literal**
symbolic runtime checker. The four arbitrary-list traversal identities are
first rederived from the actual transition rows. All source outcomes are then
replayed with arbitrary affine register values, an arbitrary nonnegative
header gap, and an arbitrary nonempty finite spare list. The collector covers
intermediate unary-scan positions and intermediate positions within arbitrary
finite-list traversals. It includes the complete finite blank startup.

This is a new executable envelope and a bounded search input. It does not
supply an absolute iPRA proof of the machine/refutation calibration. Any
reported absence of a candidate is confined to the specified finite search
template and bounds.

## Prefix lemma

The finite words used by the literal symbolic engine consist of constant
bits, affine-length constant-symbol runs, arbitrary finite lists of blocks,
and an infinite blank exterior. The block families are

\[
B(v)=0\,1^{v+1},\qquad C(v)=1\,0\,1^v.
\]

For every requested prefix length `k`, the collector computes a finite set
containing every concrete `k`-bit prefix of the symbolic stream. A constant
run is truncated at `k`. A nonconstant affine run whose constant term is `c`
is overapproximated by all lengths at least `c`; correlations among affine
parameters are intentionally forgotten. An arbitrary finite list is
expanded as either the empty word or one block followed by another arbitrary
finite list. Each block has length at least two, so computing a fixed-length
prefix terminates. A blank exterior contributes zeros forever. The same
construction handles reversed blocks and reversed lists.

Discarding atoms once their minimum total width reaches `k` is sound for
prefix queries. It is a cache optimization, not an additional inference.
The collector computes left and right prefixes independently, hence includes
all genuine windows even when parameters occur on both sides of the head.

## Unary interiors

Suppose a row reads `b`, writes `w`, moves in the scan direction, and returns
to the same control. The symbolic engine may traverse a whole affine run at
once. For a concrete run of length `L`, every intermediate configuration has
`w^u` behind the head and `b^(L-u)` ahead, for `0 <= u < L`. Those intermediate
windows are explicitly added.

For radius `r`, lengths above `2r+1` can be represented by length `2r+1` for
this local observation: a window sees the left endpoint, the right endpoint,
or an interior stretch, and cannot distinguish a larger separation of the
endpoints. Shorter admissible lengths are enumerated separately. Parameter
correlations with the outside streams are again discarded conservatively.

## List interiors

A checked list-sweep lemma traverses one `B` or `C` block, returns to the
same entry control, and has duration `v+2`. Its input and output block
families may differ. For a selected block inside a finite list, the collector
places an arbitrary already-processed output-family prefix behind the head
and an arbitrary remaining input-family suffix ahead. It replays the
literal one-block proof in this context, adding every literal and unary-scan
window. The first and last blocks are included by choosing an empty prefix
or suffix. Different prefix, suffix, and block values are permitted
independently. Thus all internal positions of every finite list traversal
are covered, while no fixed bound is imposed on list length or entries.

The normalizer's word identity

\[
C(A)1=1B(A)
\]

and its reversal are inherited from the independent checker and checked by
its empty/cons algebra. The collector preserves that normalizer rather than
introducing an alternative tape representation.

## Composition and startup

Every source instruction has both decrement outcomes checked where
applicable. The literal checker establishes the next complete source frame,
with the updated register file, header gap, and spare list. Therefore the
window envelopes compose over any finite sequence of these source steps.
The collector separately replays the blank startup until it reaches the
exact complete initialized source frame, checking the entire finite support.
The union covers every standard finite execution of the supplied table from
blank tape under the source/runtime correspondence already checked by the
literal engine.

`check_context_samples.py` additionally runs deterministic randomized literal
source-frame examples, with both small and longer unary values, varied gap
lengths, and varied spare-list lengths. Its purpose is to catch implementation
mistakes in the envelope collector; finite examples are not the universal
coverage proof.

## Search templates

The quotient search attempts to identify two controls while replacing the
two outgoing rows of the retained control. Each allowed window must reach
exactly the old one-step endpoint, up to the identification, within the
specified positive number of replacement steps, without accessing outside
the observed window.

The incoming-edge search instead removes one non-start control and rewrites
each of its incoming rows separately. It permits either write bit, either
direction, and any remaining control or the actual terminal label as the
first successor. A replacement must meet a positive old execution prefix,
with identical control, head position, and entire observed window. Detours
cannot execute a removed control or a rewritten row. Thus the independently
selected detours do not interfere. The old-prefix and replacement bounds are
explicit input parameters, not claims of global completeness.

## Provenance

The literal verifier and its list algebra come from the pinned
`pa194_ax11gh_research_2026-11-14(1).zip` incoming packet. The two-row quotient
synthesizer comes from `pa_sub194_research_2026-11-13`. The incoming-edge
synthesizer comes from `pa194_loop_continuation_research_2026-11-14`; its local
adaptation accepts this explicit envelope and includes the actual terminal
label among replacement successors. Original licenses and attributions must
remain with any redistributed vendor files.
