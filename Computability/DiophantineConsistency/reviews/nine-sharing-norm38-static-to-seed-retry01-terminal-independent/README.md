# Independent terminal audit of static-to-seed retry

The post-hoc author record reports outer session **86310, exit 0**. Retained
dependency and compile runs each exited 0 without monitor stops; the compile
log contains one unnecessary-`simpa` linter warning and no axiom report. The
output object remains under
`/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105/`, SHA-256
`1e1cbb3ca4feb02070c15c0a70d65e2ae77ec6772cf170620cda45a8d8e00a84`.

The checked `static_implies_seed_zero` theorem states that in an IΣ₁ model,
given all four integer-port-to-natural-representative cast equalities,
`gatesHold` and `fiveNorms` together imply a seed zero at distinguished input
1. It is the same theorem as the preceding failed attempt; only the final
list-index proof was changed. It does not identify static constraints with the
original equation or establish the iPRA endpoint.

`check.py` verifies the source, retained logs and object, 600 candidate direct
guard slots and 1,105 overlay links. It also authenticates the immediate
forward-prefix base producer, the each-slot producer and ten successful slot
group producers against their recorded source/object/log and direct-guard
hashes. The preceding batch's separately failed assembly is excluded; its ten
successful group objects are the candidate's direct imports. The source-delta
review and prior failure audit are rerun.

The outer receipt is an author record, not a raw transcript or independently
observed historical exit. No Lean process was run during this review.
Inherited package/dynamic ancestry, between-observation changes and sampled
resource limits remain.
