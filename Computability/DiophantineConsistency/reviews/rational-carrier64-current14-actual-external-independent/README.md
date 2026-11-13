# Independent review: actual-port rational external zero iff

**PASS within captured-provider scope.** The checked
[`actual_rational_zero_iff`](../../research/rational-carrier64-current14-actual-external/RationalCarrier64ActualExternal.lean)
applies the previous arbitrary-integer-port positive-zero iff to exactly
`CurrentWindowCarry2011.ports`, using the separately checked nonzero theorem
for that tuple's beta. The rational 64-row side and integer current14 syntax
side use the same four ports and the same strictly positive 14-coordinate
integer valuation. This is an external Lean proposition; it is not an
object-language rational sentence or an iPRA derivation.

Attempt01's retained result/log match their temporary originals and record
Lean exit 0, no stop and the expected axiom report. The output object, both
direct predecessor objects and their successful receipts match their pinned
hashes. Independent [check.py](check.py) ran exit 0, rechecking all 35
captured direct/companion/shadow guards and the pinned successful fresh-base
state; [result.json](result.json) records the result. The predecessor
[beta](../rational-carrier64-current14-beta-nonzero-independent/README.md)
and [specialization](../rational-carrier64-current14-specialization-independent/README.md)
reviews cover their direct source and provider evidence. No Lean replay or
complete transitive/dynamic ancestry audit was run; sampled resource
monitoring limitations remain inherited.

This result does not itself combine the external iff with a formal iPRA
proof, establish a PDF binding, or provide an integer-leaf 64-operation
Diophantine equation. No witness or consistency statement is asserted.

Checker SHA-256
`cdc582166c6851424b883c056063e4a2acde285b3f98ef98d457cdaba16e59a6`;
result SHA-256
`bea84066278c37dea5ee04b6837df32a81fdcd85dcb4da99722dac08162489fa`.
