# Independent audit of failed sign25 endpoint attempt

The author observed outer session 63793 exit 1. This independent checker
completed as session 46555 with observed exit 0 and recorded `result.json`.
It verifies the frozen state and source hashes against the output directory,
the author's numeric outer-exit record, the first dependency and compile
logs, all 100 direct guard slots and 1,382 overlay links, and reruns the
independent terminal checker for the upstream sign25 polynomial bridge.

The first stage's dependency scan exited 0, but its Lean compilation exited
`-6` and reported a Lean interpreter memory exception under `-M2800`. The
sampled runner recorded no monitor stop, with a 4 GiB RSS limit and 120-second
limit. The first object is absent; no later endpoint stage or final postflight
was attempted. This is evidence of failure under these limits, not an endpoint
proof and not a diagnosis of the exact declaration or dependency causing it.

The runner's state scope mistakenly says sign26; the pinned stage source and
manifest are sign25. Provider guards are point-in-time observations rather
than a complete dynamic or transitive ancestry proof. The inherited 4,000,000
heartbeat syntax setting and stale earlier seed label remain as documented in
the prelaunch audit. No nine-variable Jones, Lean degree, JSON or PDF binding
is claimed.
