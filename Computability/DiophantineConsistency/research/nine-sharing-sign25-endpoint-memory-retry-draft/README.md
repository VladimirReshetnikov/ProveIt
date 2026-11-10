# Sign25 narrowly scoped Lean memory retry

Multiple guarded endpoint and diagnostic attempts hit Lean's interpreter
memory exception at `-M2800`, with sampled peak session RSS between roughly
2.938 and 2.944 billion bytes, including a repeated attempt of a native source
that compiled in an earlier run. Splitting imports, aliases, generic transfer,
and fully pretyped assertions did not eliminate the observed specialization
failure. Their failure receipts and limits are documented in the proof plan.

This one retry raises only Lean's interpreter limit to `-M3600` for the three
existing no-alias endpoint stages. It retains the 4 GiB monitored session-RSS
cap, 10 GiB available-host-memory floor, 120-second per-command timeout,
single-threading, all source/provider guards and a fresh output directory. The
wrapper sources use the previously reviewed local irreducibility settings. The
expected observed peak is not known; the monitor can terminate the attempt at
its existing cap and sampled monitoring may miss transient or escaped spikes.

At preparation, `/proc/meminfo` reported about 18 GiB available host memory,
`/tmp` had about 9.3 GiB free, and `memory.max` was `max` in the current
session scope, its user slice and its parent user slice. These are point-time
observations, not launch guarantees; the runner repeats its own checks. This is
an uncompiled retry: independent prelaunch review and an assigned Lean slot are
required. No endpoint, exact Lean degree, JSON or PDF binding is claimed.
