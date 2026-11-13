# Independent review: rational 64/65 specialization

**PASS within captured-provider scope.** The checked
[`RationalCarrier64Specialization.lean`](../../research/rational-carrier64-lean-specialization/RationalCarrier64Specialization.lean)
quantifies over arbitrary integer ports p satisfying the explicit condition
`p 0 ≠ 0` and arbitrary integer valuations v. It casts p and v to ℚ, sets
`Urank=(p 3:ℚ)/(p 0:ℚ)` and `Wrank=(p 2:ℚ)−(p 3:ℚ)`, and proves
that the rational 64-row value equals the rational cast of the integer
`Carrier65.value p v`. The proof first derives nonzero rational beta from
integer beta, discharges the multiplication/division relation and subtraction
relation required by the prior identity, and uses `Carrier65.value_map` for
the cast. Injectivity of the integer-to-rational cast yields the pointwise
zero iff. The positive-zero iff quantifies only over strictly positive integer
valuations and uses the same valuation on both sides.

Attempt02's retained log/result match their temporary originals, record Lean
exit 0 and no stop, and contain the three expected axiom reports. The output
object and both directly imported objects (`RationalCarrier64` and the
Mathlib rational-cast lemmas) match their pinned hashes. Independent
[check.py](check.py) ran exit 0 and rechecked all 42 recorded direct,
companion and shadow guards; [result.json](result.json) records its output.
Attempt01 failed and is not proof evidence. No Lean replay or
transitive/dynamic ancestry audit was run; the predecessor's captured
`Carrier65` provider and sampled monitoring qualifications remain.

This Lean theorem is a rational-coefficient specialization at arbitrary
integer ports. It does not instantiate the actual fixed ports or establish
their nonzero beta, prove a PDF/iPRA endpoint, or show that the fixed rational
leaf is an integer. Clearing denominators, if used to obtain an integer
polynomial, requires its own operation-count and equivalence analysis.

Checker SHA-256
`da5c4b58a7cf6178b0e31ddc9c46fe0597cead557e56a363d052f372ba076a5e`;
result SHA-256
`e648e51237e645247e2070e5cee5aa8d7829ab08bfa5e15e4f529f3c4027f13c`.
