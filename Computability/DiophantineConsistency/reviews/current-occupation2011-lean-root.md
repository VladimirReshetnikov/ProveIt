# Every actual polynomial cell contains exactly one tile

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. See the [author receipt](current-occupation2011-lean-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentOccupation2011.lean (141 lines) | 6b3d2cd7ec4c3f9380b63ee1211e6e93138f4f4e265aa9e1f8f83ddef01e6b5f |
| CurrentOccupation2011Checks.lean (62 lines) | d4f24e70405b2e890775c59535c429048bbfcab28fa0cf96b006b3f990d2a906 |

Both complete frozen files were read before fresh direct root runs with
`lake env lean -M6000 -j1`. The main output was a separate temporary
object; checks imported the frozen author-built main object. Both passed,
the main log is empty and all seven axiom audits are standard-only. This
replays the new sources against existing prerequisites, not the full
dependency closure or umbrella. ROOT authored the OneHot/DecodedWindow
prerequisites, so the review is independent of this new implementation,
not the whole chain's authorship.

The original origin bit and actual physical Start index0 establish one
selected tile. An occupied cell's decoded West word is the actual positive
complement255-west, using the proved horizontal color bound<250. The
literal copies place that same positive word in the successor's East
block. Its decoded empty case would instead force that block to zero,
so the successor must select an actual tile. The exact spatial-cycle
propagation theorem then reaches every aligned cell of the same word.

`facts_occupied` takes only the original Facts and retains the same c.
Each witness is Selected, including zeros at all other actual indices;
selection uniqueness follows within each cell. The exact abstract count
and full physical Fin942 sum are both1. The proof permits repeated Start
tiles and does not assume a marker value, occupation, rectangular tiling
or positive temporal stride. N=1 remains covered by the generic proof.

The polynomial endpoint retains the complete original arithmetic
witnesses and augments them with all-cell occupation. A globally chosen
tile word, its marked color-matching interpretation and actual machine
semantics remain further compositions. The displayed decimal equation
and its size metrics are unchanged.
