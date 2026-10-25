# Full ROOT static review: CHANGES REQUIRED

This full static review binds HOLD
`11444fb3dadefec4ea147da06789d748c55a0f00b5dac87b3fbb6175b7ff8c43`
and SOURCE_PINS
`db0511289e3508d0df41719cff33139fc161736f3ed05d24df9becdd16fb246c`.
ROOT read every line of guard.py164, build.py184 and check.py441,
the entire README/PROOF/TOOLCHAIN, all HOLD metadata and all SOURCE_PINS
fields/records. All seven held payloads125877 bytes, six own-core pins,
186 external pins and eight whole-tree exact memberships authenticate.
No application, import of new/adopted code, AST or compilation occurred.

## Finding: fixed receipt paths prevent the planned fresh replays

guard.external_receipt accepts exactly one path for each role:
`/tmp/balanced-crt-shear-{role}.json`, and rejects existing receipts.
The first five commands consume the build/check/check-optimized/rebuild/
rebuild-optimized paths. The unchanged read-only check and pure rebuild
scripts consequently have no route to fresh independent receipts at
distinct ROOT paths. PROOF and TOOLCHAIN leave fresh runs to a later
ROOT release, but such a release cannot add a permitted path to this
immutable program. Running again at its existing path fails freshness;
changing held code would change the approved seal. Deleting or moving
original captures to reuse their paths is outside the planned workflow.

Before execution, provide explicitly reviewed distinct fresh paths for
the four read-only roles and include their absent output/capture paths
in the plan. Keep receipt mathematical content independent of the chosen
first/fresh pathname so complete fresh/first byte comparisons remain
possible. The single data destination and materialization policy can
remain unchanged. This is a workflow finding; no arithmetic or first-run
failure has been observed. Preserve both first full static reports and
the entire initial checkpoint before any separately authorized repair.

## Complete code and proof assessment

Both entry scripts authenticate all seven held payloads with stdlib-only
code before importing the sole local guard; bytecode writing is disabled.
The guard authenticates every direct record and exact whole-tree member
set before arithmetic. The old observed source still has no MANIFEST.
No old arithmetic module, source compiler, optimizer or native code is
imported. Held/authentication closures are checked again around writes.
The fixed external paths reject relative paths, parent traversal, symlink
components, changed destinations and existing receipts. Materialization
exclusively creates the absent data directory and thirteen canonical
files; partial failure requires evidence preservation, not a retry.

Producer substitution multiplies each actual monomial factor by factor,
and collects every complete row square by ordered pair multiplication.
The checker independently uses three-way multinomial expansion for the
one changed coordinate and unordered-pair square collection with factor2
off diagonal. Both formulas are exact over finite integer polynomials.
The producer is never imported by the checker. Shared guard operations
are JSON/hash/path utilities, not algebra. Both modes use explicit
exceptions rather than assertions.

prepare verifies the entire old SOS against the saved old quartic,
the exact source namespaces and all thirteen actual coordinate21 row
occurrences, each complete ordinary formula, all transformed squares,
direct substitution of the whole old quartic and its complete inverse.
verify_profile checks each actual saved row, every unchanged row,
metadata and labels, every saved quartic coefficient, actual inverse,
degree4, quadratic row bound, all-coordinate liveness, complete census
and all seven selected coefficient identities. The thirteen formulas
include all constants/linear terms; the row15 transcription is correct.
No transformed height or support value is assumed in either route.

The complete centered maps, translation certificate and endpoint are
embedded and compared without dropping fields. Inverse order adds the
new shear first, then follows the exact parent's fixed58 shift, free83,
204/203 monic restorations, mandatory Horn private overwrites and whole
source ordinary calibration. Only the new chart and old translation are
whole-space bijections. All original native/source boundaries remain
unchanged. The actual parent schema supports every accessed key and
the first monic restoration mutation used by controls.

INDEX binds all twelve profile files and exact code/pin bytes; each
endpoint binds all five preceding profile files. Saved JSON and term
lists have separate canonical guards. Rebuild regenerates the entire
thirteen-object bundle, compares canonical serialization and reads all
saved bytes back. Reports contain no pathname or timing dependency;
the sole missing fresh-path permission can be repaired without changing
the mathematical algorithms or report semantics.

ROOT traced every one of33 negative cases in each profile to its actual
semantic rejection, after chart/endpoint/index hash rebinding. The cases
cover row direction/sign/gate/omission, unchanged corruption, metadata,
strict integer/Boolean/float types, full quartic coefficients, certificate
schema/direction/inverse/policy/source/coverage, source witness-map order/
free/monic/calibration fields, census, endpoint and index search/schema.
Schema controls are correctly qualified. The four valid cases per
profile reorder row terms, split a coefficient, reorder quartic terms
or add a canceling pair; they retain all semantic checks. Canonical
saved-form checking remains a separate outer requirement.

All16 first output/data/capture paths were checked absent by inert
inspection. The old interrupted exit143 remains preserved and unresolved.
No new data, tuple, metric, Lean, TeX or PDF artifact was produced. No
execution is approved by this review. After preservation, bounded repair,
refreeze and two full final static approvals, ROOT must separately decide
whether to release the first commands.
