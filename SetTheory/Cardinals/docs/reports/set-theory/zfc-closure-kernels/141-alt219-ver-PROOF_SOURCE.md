# Exact source transport and literal table-patch audit

This is a reproducible mathematical certificate for source transport, table
identity, and state-label normalization. It does not replace fresh blank-tape
startup or unbounded physical-runtime certification of either table. No
physical runtime engine or discovery helper is imported by source_check.py.

## Inputs and source semantics

All core source and table bytes are SHA256-pinned in the standalone checker
and source_transport.json. Each complete source is a full binary syntax tree
with 4,744 primitive occurrences, in left-to-right ordinal order. A positive
decrement subtracts one and returns normally. A zero decrement preserves its
register and returns break 1. Breaks count enclosing left edges; continues
count enclosing right edges. Matching break exits its pair, whereas matching
continue reenters its pair. Source control falling through the root restarts
at ordinal 0. CH halts.

Two independently implemented resolvers validate every ordered CFG edge.
The first walks ancestor edges and descends to the first leaf. The second
uses integer successor modulo address length, bit cuts, and binary search in
the dyadic interval partition induced by the leaves. Every arithmetic target
is also checked for the stronger property that any suffix extending beyond
the resolved leaf consists entirely of zeros. Thus a mere interval hit
cannot accidentally validate a target with stray ones. Both decrement guards
are included, even if a later reachability argument makes one unreachable.

## Retagging preserves every source primitive step

Write I = CI1. Exactly 81 occurrences of

    (((I,I),(I,I)),CC2)

are replaced with

    ((I,I),((I,I),CC3)).

This changes 405 primitive addresses and exactly 81 arguments, each CC2 to
CC3. CI, CD, and CH operations and every other primitive argument are
unchanged. The checker reconstructs the actual complete trees and applies
these literal replacements; it does not trust a discovery recipe.

Supplementarily, both displayed open trees increment R1 four times and
return continue 1, changing no other register. In the first tree CC2 is
propagated through one enclosing right edge. In the second tree CC3 is
propagated through two enclosing right edges. All increments terminate for
every natural register vector, so this local contract itself is also exact.

The original and standalone-retagged programs have identical ordinal CFGs.
The zero-terminal and combined programs likewise have identical ordinal
CFGs, with precisely the same retag changes. All register operations and
branch conditions are equal at corresponding ordinals. Hence induction on
source primitive steps gives lockstep equality from corresponding ordinals
and arbitrary equal natural register vectors, including halt and divergence.
This is an exact finite syntactic/CFG check supporting an all-natural theorem,
not numerical testing of finitely many register values.

## Guarded zero terminals

The only operation differences original-to-zero, and retagged-to-combined,
are CB1 to CD6 at ordinals 4570, 4576, 4588, 4594, 4602, 4608, 4711, 4717.
For each changed ordinal i, the checker builds the complete incoming-edge
list, including both decrement branches. Its unique incoming edge is the
zero edge of the unchanged CD6 at i-2. Initial ordinal 0 is not changed.
Consequently every reachable entry to a changed leaf has R6=0. Its new CD6
step is register identity and its zero successor is precisely the old CB1
successor. Every other primitive and ordered edge is unchanged. Induction
proves lockstep equivalence from source entry for every initial natural
register vector. No incoming edge or generic runtime case is omitted.

There is an independent local open-tree explanation. Set P=(CD6,CC2),
U=(P,CB1), V=(P,CD6), and A=(CD5,CC1). If R6 is positive, P decrements it
and returns continue 1, propagated by both U and V without entering their
right child. If R6 is zero, P returns normally with the register still zero;
both right children then return break 1 without changing registers. Thus U
and V have equal finite open-tree contracts for all natural registers.
The checker finds exactly four literal full-tree replacements

    (((CD5,U),CD6),(A,U)) -> (((CD5,V),CD6),(A,V)).

## Exact composition, not an inference from disjoint table rows

The checker starts from the complete original tree O. Let T be the 81 literal
retagging/reassociation substitutions and Z the four equality-macro zero
substitutions. It checks T(O)=R, Z(O)=Z0, T(Z0)=C, and Z(R)=C, where R, Z0,
and C are the pinned standalone-retagged, zero-terminal, and combined source
files. Counts and occurrence paths agree in both orders. A second,
ordinal-by-ordinal reconstruction checks the complete combined source again.
The zero-entry predecessor proof is separately repeated in the retagged
background. Therefore both the source transformations and their all-natural
proofs compose. Disjoint table patch rows alone would not prove this result.

## Literal tables and normalization

Every table is independently parsed and checked for 219 working states,
438 binary transition rows, start 0, dispatcher 84, halt target 254, and
graph reachability of every working label. Native source-table state labels
301 and 302 are normalized to absent search labels 102 and 120, respectively;
all other state labels are fixed. This mapping is checked to be bijective
on every source and target label. For the combined table both forward and
inverse normalizations reproduce the exact pinned bytes, not just behavior.

Against the normalized original table, the zero-terminal table changes
exactly nine literal rows. The standalone retagged table changes exactly
three: 139/0 becomes 0 R 99, 139/1 becomes 1 R 160, and 160/1 becomes 1 L 63.
The combined construction uses a DIFFERENT retagged physical seed: its
139/0 row is 0 L 139. That seed differs from the standalone retagged table
at exactly this one row and has the same source file. The combined table is
exactly the nine-row zero patch plus that three-row seed patch. All old/new
rows, hashes, and the one-row seed distinction are recorded in the report.
No physical refinement is inferred merely from patch disjointness.

## Reproduction and scope

Run `python source_check.py` in the research checkout. For an archive with a
different layout, run `python source_check.py --help` and set each input path
using its named option; use `--output-dir` for the two generated reports.
All paths are configurable but the accepted input bytes are not weakened.
Only Python's standard library is needed. Checks remain active under -O.

Successful source_transport.json status means all assertions above passed.
Its source equivalences can be combined with independently certified startup
and unbounded primitive refinement to transport the accepted source theorem
to the two exact physical machines. This certificate by itself does not claim
that pending physical proofs passed, prove consistency, or satisfy the goal
of at most 218 states.
