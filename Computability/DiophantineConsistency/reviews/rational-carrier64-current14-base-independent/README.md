# Independent review: literal 64/65 identity against current14 syntax

**PASS within the fresh-base and captured-provider scope.** The checked
[`RationalCarrier64Current.lean`](../../research/rational-carrier64-current14-base-draft/RationalCarrier64Current.lean)
proves the two literal outputs equal over any commutative ring when
`beta*Urank=MF` and `Wrank=MC−MF`, and gives their pointwise zero iff.
Its separate `value65_eq_expressionAt` theorem is specifically for integer
ports and integer valuations, and identifies the 65-row value with evaluation
of the imported `ObjectCurrentEquation2011.expressionAt` at those inputs.
The binding alone is neither rational-leaf specialization nor an iPRA proof.

Independent [check.py](check.py) compared all literal row operations,
aliases, head tuple and value wiring against the pinned 64/65 JSON graphs,
confirming the common 28-row prefix, 5/6-row rank and 31-row suffix. It
also verified that the shared definitions and ring proof match the previously
reviewed literal source. This is an external transcription comparison, not
a Lean theorem about JSON or a direct PDF binding.

Attempt04's retained log/result match their temporary originals, record Lean
exit 0 and no stop, and contain exactly the three expected axiom reports.
The output object, syntax object, tactic provider and all 39 captured direct,
companion and shadow guards match their pinned hashes. The checker also
verifies the fresh-base manifest/state pins, successful syntax-module producer
record, its source hash, direct import names/input hashes and producer log,
and the current workspace source against the frozen snapshot. Its observed
exit-0 output is [result.json](result.json). The base's broader transitive and
dynamic ancestry and sampling qualifications remain inherited; this is not a
new source-closure rebuild or Lean replay. Earlier failed or rejected
attempts are not used as evidence for attempt04.

The actual fixed ports, nonzero beta, rational-leaf instantiation and
internal iPRA derivation require further work. A rational leaf is not an
integer-leaf 64-operation record.

Checker SHA-256
`7e305fe55fe000254b86f4f134a9da3c9f31df51811150d2e0fcf12693e0f953`;
result SHA-256
`af0e6f403d865d0870d275c0a9aaf92a1548deac60af81c59d136e1a1a128613`.
