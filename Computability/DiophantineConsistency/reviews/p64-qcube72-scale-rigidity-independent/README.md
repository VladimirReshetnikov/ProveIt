# Independent review: generic scale rigidity

**PASS within the captured-provider scope.** The checked
[`same_rank_root_carrier`](../../research/p64-qcube72-scale-rigidity-draft/FreeMainScaleRigidity.lean)
works for an arbitrary IΣ₁ model and arbitrary model elements `a,X,Y,c`.
Given two indices with equal Pell ordinate c and x-coordinates g,g', strict
monotonicity makes the indices equal and then makes g=g'. If both supplied
free-carrier identities use the same `X,Y,a,c`, subtracting their common
part and cancelling the positive `4a+3` gives h=h'. The source explicitly
assumes these coordinate and carrier identities; it does not derive them
from graph zeros, assume `a=(X+1)Y`, or prove any zero-existence or reverse
witness statement.

The retained attempt01 log/result match the temporary originals, record Lean
exit 0, no stop and the expected axiom report. The output object and direct
`ArithmeticPellCongruences` provider match their pinned hashes. The
independent [checker](check.py) ran exit 0, rehashing the retained artifacts
and all 232 captured direct-input/companion/shadow guards; its output is
[result.json](result.json). No Lean replay was run, and the provider's
transitive/dynamic ancestry and sampled resource-monitoring limits remain.

Independent checker SHA-256
`0e4b414950e06930b49119bb057073a78f861d40fc8fd223a7b423d5a76b217b`;
result SHA-256
`9c861bb271f7220f2eb705875359a1132283477737c05785914a60d22088c42f`.
