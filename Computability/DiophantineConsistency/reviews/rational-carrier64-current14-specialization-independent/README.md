# Independent review: rational specialization against current14 syntax

**PASS within captured-provider scope.** The checked
[`RationalCarrier64CurrentSpecialization.lean`](../../research/rational-carrier64-current14-specialization/RationalCarrier64CurrentSpecialization.lean)
uses arbitrary integer ports p with the explicit premise `p 0 ≠ 0` and
integer valuations v. It proves that the 64-row evaluator over ℚ, with fixed
leaves `(p 3:ℚ)/(p 0:ℚ)` and `(p 2:ℚ)−(p 3:ℚ)`, equals the rational
cast of the integer evaluation of `ObjectCurrentEquation2011.expressionAt p`.
It separately proves the pointwise zero iff and the existential iff over
strictly positive integer valuations; both sides use the same valuation.

The proof casts the nonzero beta into ℚ before multiplication/division
cancellation, applies the predecessor's two-assumption ring identity, uses
its own checked homomorphism law `value65_map`, and applies the predecessor's
integer syntax binding. Integer-to-rational cast injectivity supplies the
reverse zero direction. This is not an iPRA derivation, a fixed-port
instantiation or a proof of an integer-leaf 64-operation equation.

Attempt01's retained result/log match their temporary originals and record
Lean exit 0, no resource stop and all four expected axiom reports. The
output object and the two directly imported `RationalCarrier64Current` and
Mathlib rational-cast objects match their pinned hashes. The recorded search
path consists of the current14 identity object, the fresh current14 base and
its package overlay; it does not include the earlier historical Carrier65
provider. Independent [check.py](check.py) rechecked all 42 direct,
companion and shadow guards, plus the predecessor receipt, fresh-base
state/manifest link, and the base syntax producer record and object; it ran
exit 0 and retained [result.json](result.json). The base syntax object is
inherited through the predecessor, not a direct import guarded by this
specialization run. See the [predecessor review](../rational-carrier64-current14-base-independent/README.md)
for its source/row and producer checks. No Lean replay or transitive/dynamic
ancestry audit was run; sampled monitoring and historical-source-snapshot
limits remain inherited.

Checker SHA-256
`9bc19c6641378c598bbc08060776414aa09aac291c6ca998156ffccb09111ceb`;
result SHA-256
`1882884a312c278853b8a52c221ee8d286ecbff4f08161d4c6bba43af7c779ef`.
