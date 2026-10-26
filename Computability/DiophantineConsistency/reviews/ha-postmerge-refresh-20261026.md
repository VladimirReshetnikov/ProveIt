# Post-merge refresh of native and equation proofs

Root merged `origin/main` at `180e99fc75b4c89396a275f5a1b34ceb3f847b69`
into the equation/HA branch as `891c86e0b2970feb2b7442420d61c37ee7233ff2`.
The incoming delta has13 active Lean sources and two review/adoption files.
Root read every Lean diff and the complete added review/adoption text.
`complemented47_review` independently reviewed all13 diffs and the relevant
arithmetic, model-semiring, reflection, Pell and LTE contracts, with no findings.
This was source reasoning, separate from root's compilation below.

Existing public definitions, theorem statements and premises are preserved.
PrimePowerOrder adds `lift_dvd_iff`, including exponent zero; controller
units removes its direct finite-field import and uses a generic monoid
fixed-point induction. The remaining changes simplify existing proof bodies.
No incoming executable or archive program was run. Equation artifacts,
coefficient recipes, toolchain, manifest and library configuration are unchanged.
The incoming author's56 final calls retain their separately recorded scope;
they are not counted as root executions.

Root wrote and fully reviewed an explicit private refresh driver before
execution. The new run in `/tmp/ha-postmerge-refresh-validation-20261026c`
passed all94 commands on the first attempt in352.34 seconds. It freshly
compiled all13 changed modules, their selected checks, both current equation
endpoints and both new mixed-carrier leaves, plus the additional prerequisites
needed for the previously separate annotated/object arithmetic branches.
Five existing focus files also ran. All191 axiom reports use only the standard
`propext`, `Classical.choice`, `Quot.sound` set or subsets. Existing warnings
remain in NativeBinaryScale (unused width premise), CurrentControllerUnits2011
(large exponent display) and ArithmeticDAGSemantics (five unused simp entries).
No limits were raised: every command used `-M6000 -j1 -DElab.async=false`.

The selected graph has447 custom modules:94 fresh and353 authenticated reuses.
Reused source/object pairs come from the completed361-module validation and
its15-command refresh, with the independently replayed narrow decoder and
corrected-strong parent substituted at explicit pins. All selected sources
match the merged snapshot; reused sources also match their prior receipts.
The80 direct external package/toolchain imports and their recorded companions
are an explicit precompiled boundary, not a freshly rebuilt package closure.
All source/object/boundary hashes were checked before and after execution.

This remains a LIMITED refresh. Twelve unchanged clients of freshly compiled
modules retain their authenticated earlier objects: NativePellScaleBounds,
CurrentKernelResidues2011, CurrentWordHighMask2011, CurrentAuxiliaryOrder2011,
CurrentControllerPositions2011, CurrentSafeController2011, CurrentDummySafety2011,
CurrentPackingParity2011, CurrentRankStride2011, WangTiles942ControllerDimensions,
NativePositiveSourceConstruction and ThirteenCorrectedStrong. Their source
interfaces are unchanged. The run is not a new fresh elaboration of all447
modules or a whole umbrella build. It supersedes neither historical closure
receipt nor separately validated HA/Foundation leaves.

Durable driver, manifest, execution state, driver output and188 individual
log/time files are in
[ha-postmerge-refresh-20261026/](ha-postmerge-refresh-20261026/manifest.json).
Root checked all94 source/object/log/time records and archive integrity.

| Evidence | SHA-256 |
|---|---|
| manifest | `e94b25caebfbcab887e1a90d10ea55d584d0998f3300d866bf6f9f4449a00fe0` |
| execution state | `3a91c6434d55bb3d3b0b07f4d8e53f17ee1ce46effa24771b1f3f656f60119be` |
| logs archive | `1469a48398f2511983ebc794fc72ec1fb104ac54bee9aa9746596507bb956f5c` |

The exact current external consistency endpoints remain checked. No new
internal consistency equivalence or HA proof-existence endpoint is claimed.
The decimal14/65/150 TeX/PDF remain unchanged; size reduction and the HA
internalization goal continue.
