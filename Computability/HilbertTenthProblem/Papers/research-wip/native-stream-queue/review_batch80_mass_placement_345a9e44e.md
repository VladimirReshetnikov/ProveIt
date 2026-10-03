# Conserved-mass companion placement at 345a9e44e

**PASS for the disclosed companion-placement stage.** At
`345a9e44e665c5e21888fcb1be6da9d1a94e2d25`, all 116 newly placed files
match their intended members of the five batch80 archives. The existing
signal report's article, PDF and README are unchanged; it still has only
Parts I–IV at this pin. The commit describes intended Parts V–VI, but this
placement does not yet write their mathematical text. No source-transfer or
new typesetting theorem claim is inferred from the commit title.

The [portable checker](review_batch80_mass_placement_345a9e44e.py) reads only
immutable Git objects, authenticates all five archive hashes, matches each
new path by its package prefix, intended member name and exact bytes, and
accounts for all 162 published member occurrences. It runs no delivered
program or build. The [receipt](review_batch80_mass_placement_345a9e44e.json)
contains complete member hashes, direct mappings, explicit aliases and
archive-only members. Arrival is
`4e270aa4648c5fd7e18626507531046715976535`.

| Package | Published members | Newly placed files | Explicit existing/shared aliases | Archive-only members |
|---|---:|---:|---:|---:|
| Three-mass reversible computation | 66 | 51 | 1 | 14 |
| Exact-target cleanup | 38 | 28 | 5 | 5 |
| Revised single-unit three-mass | 13 | 9 | 0 | 4 |
| Four-mass decidability | 33 | 28 | 0 | 5 |
| Original single-unit three-mass | 12 | 0 | 7 | 5 |
| **Total** | **162** | **116** | **13** | **33** |

The five vendored exact-target modules reuse the corresponding native
three-mass sources, with identical bytes. The native two-mass arithmetic
receipt reuses the earlier sparse-lattice receipt. Seven unchanged members
of the superseded single-unit edition are recoverable through the revised
edition's placements; its five changed members remain in arrival history.
These aliases are explicit source-qualified mappings, not arbitrary
cross-package equal-hash guesses. They explain why 46 members are not
newly placed while only 33 lack a direct/shared maintained counterpart.

The archive-only inventory includes the original mathematical manuscripts,
delivery PDFs/READMEs/manifests, five large native exports, the four modular
native TeX files, and the four-mass raster figure. The article's four-mass
PDF figure is intentionally retained as a new companion. The CSV retains
all 46 CRLF rows exactly; the only `.gitattributes` change appends the
specific `-text` rule for that file. The entire commit delta is accounted
for: 116 additions, this one attributes edit, and five archive removals.
The original ZIPs remain available from the pinned arrival commit.

The prefixed, flattened companions preserve source bytes rather than the
original executable layout. For example, the native shell replay still
invokes `code/three_mass_collision_generator.py`, and the cleanup compiler
still expects `vendor/` modules. Those paths are absent from the placed
report tree. Reconstruct the original ZIP layout to use those release
commands; a renamed companion by itself is not a runnable package. The
prior [three-mass/exact-target review](review_batch80_three_mass.md) and
[low-mass review](review_batch80_low_mass.md) already ran the complete
intended suites in their original layouts and retain their mathematical
and API scope.

The placement message's statement that this research session had not yet
reviewed the archives refers to its expressly cited `abfc0cb25` snapshot.
Subsequent completed reviews and root replays are indexed in
[the twelve-archive review](incoming_substrate_review_4e270aa46.md). This
historical timing statement does not change the source identity or call
for a second execution of unchanged suites.

Run the transfer audit from any directory with standard-library Python
and Git:

```sh
python review_batch80_mass_placement_345a9e44e.py \
  --repo /path/to/Proofs \
  --expect review_batch80_mass_placement_345a9e44e.json
```

A separate reviewer read and replayed the helper and independently checked
the disjoint 116/13/33 partition, unique physical paths, CRLF counts and
unchanged four-Part presentation. Root's fresh `--expect --output` replay
also matches the saved receipt byte for byte. No working-tree source,
archive, PDF, or Git state is mutated by this checker. A subsequent
assembled mathematical write will need a new semantic-transfer review.
