# Fixed seam columns and exact horizontal initialization cases

Date: 2026-10-26. Independent complete source/check reviewer and fresh
replay: ROOT. See the author receipts for [seam columns](wang-tiles942-seam-columns-author.md)
and [horizontal initialization](wang-tiles942-initial-horizontal-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942SeamColumns.lean (106 lines) | 654d4b1c570526742157496f96b312fc8dd32a32a7a0b629840f6f6486dbc6c4 |
| WangTiles942SeamColumnsChecks.lean (87 lines) | 8101f6b08db7a71a2e19d29ed71b08b3d13b27131dfdcc7f1dce77bda3ae7ef8 |
| WangTiles942InitialHorizontal.lean (136 lines) | f989a80b56aac3c1ee31f41fc18cd4e4ac0486bbce73cb22d220f6630ced9536 |
| WangTiles942InitialHorizontalChecks.lean (70 lines) | 97bca6abaa994b64a9d41e246c90dc9d9e4dab747ab51353737a75c03e0b813c |

ROOT read every line of the four frozen files before fresh direct
`lake env lean -M6000 -j1` runs. Both main outputs went to separate
temporary objects; the checks imported their frozen author-built objects.
All four runs passed. Main logs are empty; the eleven seam and eight
horizontal axiom reports contain only the standard axioms. No entire
dependency closure or umbrella rebuild is claimed.

SeamColumns uses precisely allowedness and actual time matching. The
local north437 iff south437 classification gives one-step seam invariance;
integer induction covers the future and past. A column containing a seam
at one time has actual seam tuples at every time, but the two finite
horizontal parameters may vary. A column containing Start is never a seam.
The marked-word specialization retains the literal signed plane address.
Negative checks establish that allowedness alone and time matching alone
are each insufficient; a separate allowed time-matched family lacks
horizontal matching, demonstrating that horizontal matching is unneeded
for this column theorem.

InitialHorizontal eliminates operating transitions and receiving tiles
using valid rails at least6. It classifies East2 as initLeft or a seam
with East2, West3 as the actual head initializer, West4 as initRight or a
seam with West4, East3 as Start, and West2 as Start or initLeft. Seam West
colors are squares0,1,4, and East colors0,1,2. The real seam(4,437,2,437)
is a simultaneous negative control against dropping either initializer
exception. Explicit nonseam corollaries remove those alternatives only
with their stated local north-not437 premise.

Neither packet assumes a strip, a unique Start, a machine run or halting.
Together they support deriving finite initialization-strip walls from
actual horizontal periodicity. That finite-strip theorem and subsequent
run extraction remain separate work. The displayed decimal equation and
metrics are unchanged.
