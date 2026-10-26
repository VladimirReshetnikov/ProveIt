# Current tile colors: independent peer review

Result: **PASS within the stated local-color and nonzero-shift scope.**
I read all 104 main lines and 43 check lines, inspected the actual label,
copy, bounds and Start interfaces they use, and freshly rebuilt both
modules in an isolated object overlay. No mathematical gap or requested
source correction was found.

ROOT authored the reviewed module. I did not edit either reviewed source.
I authored the earlier whole-field alignment module and some of its
cycle/South-aggregation dependencies. This is an independent review of
ROOT's new composition, not an independent authorship claim for every
dependency or a fresh replay of the entire native chain.

## Exact sources

Paths are relative to `Computability/DiophantineConsistency/`.

| Source | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentTileColors2011.lean` | `c1f7fc6fda51795f182c0d14379206c781f8cdcae212e27ff5c0a9bede21b8f9` |
| `Lean/DiophantineConsistency/CurrentTileColors2011Checks.lean` | `2c3f698e2ddc61bf19f8c608f2cf2ebe64f85a3f2ab6644db225c0cffc9a1c7d` |
| `reviews/current-tile-colors2011-lean-root.md` | `ad51d09b1035f1de9d2ff85122d9e540e7f5e181d3f22792c6e8a94be81bd5ee` |

The exact relevant dependency sources inspected at the composition boundary
were `CurrentWholeField2011` (`16c06800d326578b5898f2353229b574f2c0c8783bfadc362d517d34d2a5d079`),
`CurrentAdjacency2011` (`160cef12e27cda2ece581ba0acfb2fcbbf194d918fe75d630705a7feb8e97133`),
`CurrentDecodedWindow2011` (`fd52d069a146d13287cd7da987cc54117e19282efabba6c30c9b4a4f2a48b217`),
`CurrentCellLabels2011` (`88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d`),
and `WangTiles942Core` (`7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85`).

## Mathematical audit

`binaryWord_congr` sums exactly the supplied bitwise equality over
`Finset.range n`; it neither drops an endpoint nor adds a Boolean premise.

`facts_selected_labels` obtains the selected tile's packed word from
`facts_decode_cell` on the original functions, then applies the actual
Boolean block decoder. I checked the true packed-coordinate mapping:

| Physical fields | Actual complemented color |
| --- | --- |
| 978 through 985 | `255 - west` |
| 960 through 968 | `511 - north` |
| 969 through 976 | `255 - east` |
| 942 through 950 | `511 - south` |

Thus the earlier informal East/West terminology problem is not reproduced
here. The local horizontal result is precisely East(current)=West(previous),
and the temporal result is South(current)=North(shifted). The selected
neighbor indices are explicit premises in these two local theorems.
Neither local theorem asserts global occupation.

The two color equalities use every corresponding physical copy equality
from `facts_adjacency`. Whole-field alignment is derived from the same
original `Facts`, not supplied as a new hypothesis. The neighbor cell
alignment proofs come from that exact adjacency result. Complement
cancellation uses the actual tile bounds: both horizontal colors are less
than 256, and both temporal colors less than 512. This matters because
natural subtraction alone would otherwise not be injective.

`facts_temporal_shift_nonzero` has only the original `Facts` as its native
premise. If the original rank-based shift divided by 47 were zero in the
full group `ZMod (N*2011)`, its temporal source at the origin would be the
origin itself. The selector at that point is the literal Start index 0,
because physical position 0 and `Facts.origin` are both used explicitly.
The already proved local temporal color equality would then give
Start's South 1 equal to its North 435, contrary to the actual
`start_zero : tile 0 = (2,435,3,1)` theorem.

This contradiction does not assume any other cell is occupied, does not
require a unique Start, and excludes every full-word-period displacement,
including a positive or arbitrarily large natural representative. The
focused divisibility check confirms that scope. The separate zero-phase
check correctly retains the fact that mere alignment alone permits zero.

## Independent kernel replay

The temporary overlay is
`/tmp/current-tile-colors2011-peer-efu8vik6`.
Other `DiophantineConsistency` objects are symlinked from the existing
dependency directory. Both target module stems were excluded from those
links. The main source was compiled to a genuinely fresh local object;
the check module then imported that object through the overlay placed
first in `LEAN_PATH`. Neither shared target object was overwritten or
created. Both commands used the configured Lean executable with
`-M 6000 -j 1`, and both sources disable asynchronous elaboration.

The exact commands, environment and before/after shared-object hashes are
recorded in `receipt.json` in that temporary directory, SHA-256
`6a1c94788d7db8d13e24f2fcf2d82ce60d917bf39d3347ff806332b910ae4e58`.
Both final exit codes are 0. The main log is empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The check log has SHA-256
`a766244562c2e0d633ba71d507e93d34441b1a0d047f2515a98d38f771935dd2`
and all five axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The fresh main object is byte-identical to the existing
main object, SHA-256
`4dca4f478500f4e6169f2f770b47a5e23ad9ccd5132f89515cb1af57aba76f64`.

Two orchestration-only staging issues were corrected: the initial overlay
needed namespace dependency symlinks, and the hash recorder needed to
permit an absent shared check object. The former stopped before source
elaboration; the latter stopped after the successful fresh main build and
before starting the checks. No Lean source changed during this review.

No full import-closure replay, global machine-language equivalence,
canonical converse or internal-ZFC consistency theorem is claimed here.
The accepted result is the literal selected-neighbor color matching and
the full-cyclic nonzero temporal shift on the original arithmetic word.
