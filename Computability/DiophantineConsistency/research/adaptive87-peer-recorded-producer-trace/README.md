# Bounded producer-edge trace for the 658-object peer overlay

For the five roots `HAAdaptiveFactor87`, `ArithmeticAdaptiveFactorUnits2011`,
`IPRAExpressionNative`, `HAExpressionSameZero`, and `PRAPositiveCode`, this
read-only trace finds **1,081 matching recorded project-import edges and no
mismatching edges in the explored trace**. It rehashes 541 currently selected
project objects. For each object it searches the explicitly pinned producer
records by logical module and output hash, prefers the actual repaired peer
records over older records that produced byte-identical outputs, and follows
recorded `DiophantineConsistency` imports. Forty objects terminate the trace
because these selected record sets do not provide their outgoing edges; 111
non-`DiophantineConsistency` names are listed as an unverified external
frontier. The direct-input subset recorded for the rank-17 suffix excludes
nonproject inputs in this trace. Neither count asserts a complete closure.

This is a **concrete hash-consistent recorded subset**, not authentication of
a full provider environment, proof of byte reproducibility in all environments,
Lean compatibility, or a runnable 88/30 build. The trace can match a selected
object to a historical producer record with the same module and output hash;
in particular where paths differ it does not prove that record physically
produced the selected file. It stops on a missing record or differing hash,
and the receipt retains all such cases. Hash equality alone establishes neither
source identity nor semantic compatibility. The 658 inventory's current
source declarations are not a complete inventory of historical compiled imports.

## Important boundaries and observations

* The selected `HAAdaptiveFactor87` object is `33e6b87c…`, and its repaired
  build record names the selected `HAExpressionAssembly` and
  `ArithmeticAdaptiveEquivalenceUnconditional2011` object hashes. The selected
  `ArithmeticAdaptiveFactorUnits2011` object is `e357624f…` and its matched
  prefix producer records select the same factor-magnitude input. The 52-row
  prefix was deliberately interrupted after its completed rows; the interrupted
  parent run is not itself a complete endpoint replay. The fixed-continuation
  result has historical-source and inherited ancestry limitations.
* Twenty-seven traced modules lie outside the earlier 658-name source closure.
  In particular a matching producer record for the selected
  `HAExpressionSameZero` object requires `HAAdaptiveDirectOrdinate86`
  `ee49ed47…`; it is outside the earlier inventory but present and hash-matching
  in this overlay. This does not establish its complete provider ancestry.
* The separately documented historical mismatch between old
  `PRAPositiveMapPack` and two reused objects cannot simply be attributed to
  this selection. Here `PRAPositivePackedNormal` and `PRAPositiveCode` resolve
  to the later ancestry-repair root, and that root's records bind the packed
  normal object to the **selected** `PRAPositiveMapPack` hash `5902bb1a…`.
  This local repair does not establish the rest of the endpoint chain.
* An initial comparison that chose older producer rows for byte-identical
  outputs found 12 apparent differing edges. The later repaired-peer rows for
  those same output hashes record the selected inputs instead. The checker
  uses those higher-priority records; this is why those are not reported as
  contradictions. The finding illustrates why object hashes alone cannot
  determine which producer history applies.
* The independent source-origin audit of the frozen repair records an exact
  `(module, object hash, resolved object path)` match for 380 traced objects,
  including all 40 objects at the direct-edge frontier. This checker pins and
  compares that prior audit's inventory; it does not rerun its source, log,
  provider-state, package or dynamic provenance checks. The old audit itself
  explicitly retains historical fixed-snapshot and external ancestry limits.

The JSON receipt records every selected physical path/hash, matching record
class, every mismatched edge, missing-record names, nonproject frontier, names
outside the original 658 and source-origin matches. Reproduce from
`Computability/DiophantineConsistency` with:

```
python3 -I -S -B research/adaptive87-peer-recorded-producer-trace/check.py | cmp - research/adaptive87-peer-recorded-producer-trace/receipt.json
```

This rehashes the selected object bytes and pinned input records, and reads but
does not mutate the temporary providers. Temporary files may disappear. No
Lean, build, cleaning, staging, package replay, complete companion check or
new axiom inspection was performed.
