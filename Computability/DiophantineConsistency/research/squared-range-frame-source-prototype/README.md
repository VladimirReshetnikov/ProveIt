# Eight squared range-output ports and 64 predicates

This fresh arithmetic prototype starts from the frozen common-radius RAW
source. It replaces exactly eight range power output summands in the frame
by their squares, appends eight ordinary square gates, and deletes exactly
the eight corresponding fused range quotient guard graphs. It retains61
scalar predicates and the existing V/product/joint-factorial predicates,
for64 total. The common factorial radii and every actual power port remain
unchanged. The three high quotient guards534/548/561 remain present.

The source has1267 coordinates and1185 rows. The complete RAW quadratic
parent has1459 coordinates and1249 rows. CUTS.json maps every old row,
retained or removed guard and auxiliary coordinate. Retained auxiliary
names and metadata are copied exactly, with explicit new indices after
the eight added body coordinates. FRAME_POLICY.json distinguishes actual
power ports from their squared bounding ports. All other historical source
metadata is preserved as provenance; it grants no old frame calibration.

These are arithmetic prototypes. **No ordinary source equivalence or
accepted frontier measurement is claimed by this packet.** The ordinary
signed-output, absolute frame, guard recovery and fresh canonical source
proof is reviewed separately in `research/range-output-square-frame`.
FEASIBILITY.md records the chronology and its limits. New squares are
ordinary equations; their late numeric allocation is not a chronological
premise for deriving their nonnegativity or constructing a fresh frame.

The RAW family uses the literal changed parent. The optional CSE family
uses the separately certified unit row operation at711, replacing the
second equal-base modulus definition by raw764-raw730. It preserves every
coordinate and all other constraints over unrestricted integers.
CSE_BRIDGE.json records both universal directions. This does not assume a
compact bridge or equality of old and new source tuples.

Both families contain the same twelve reviewed monic optimizer settings.
Every setting includes its entire equation, signed restoration certificate
and complete expanded quartic. The separate optimizer-free checker checks
the whole source/domain/auxiliary delta, both complete squared-frame
identities, both CSE row identities, every monic substitution/inverse,
every quartic coefficient and census field, signed fixtures and deliberate
corruptions. MEASURED_COMPARISON.json compares arithmetic measurements only
against the same frozen591 settings. Source calibration cannot follow from
these finite checks or signed samples.

Run the four release commands through the historical archive wrapper:

```sh
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/squared-range-frame-source-prototype/build.py --check
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/squared-range-frame-source-prototype/check.py --output /tmp/squared-range-frame-normal.json
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B -O Computability/DiophantineConsistency/research/squared-range-frame-source-prototype/build.py --check
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B -O Computability/DiophantineConsistency/research/squared-range-frame-source-prototype/check.py --output /tmp/squared-range-frame-optimized.json
```

The optional --source-only producer mode materializes the complete basic
source/parent/domain/policies before optimizer work; it supplies no metrics.
Final records use .json/.txt and the manifest closes the packet. Frozen
sources, common reports, pages and Lean remain unchanged; no commit is made.
