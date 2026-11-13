# Independent source review: root74 refusal-only preflight

The inspector has no subprocess, Lean launch, output creation or file-write
mode and always exits nonzero with `can_launch: false`; both its default and
`--launch` invocations were checked. Its selected source/inventory and key
provider-object pins match at the observation point, and the candidate-name
collision scan covers the 159 bare snapshots plus the two FreeJ names and
`DiscreteOrderedRingFacts` across five named search roots and 13 suffixes.
This is a bounded collision observation, not actual Lean name resolution.

The independent checker substitutes synthetic resource observations at exactly
5,100,000,000 bytes and one byte above, and at and below the 10-GiB memory
boundary. The disk test is strict, the memory test inclusive, and every case
still refuses. The documented 4-GiB sampled RSS, 180-second stage, six-hour
run and 0.2-second monitoring limits describe a future runner; this inspector
does not execute or enforce a runner. The `/proc` scan is not an atomic slot
reservation, and the retained provider objects are sampled rather than made
immutable. The separate root74 provider survey is pinned as evidence but is
not independently reviewed or replayed by this packet.

The result is a source/read-only controls review only. Lean was not run;
provider compatibility, complete dependency closure, exclusive allocation,
prelaunch review and the model/iPRA endpoint remain open.
