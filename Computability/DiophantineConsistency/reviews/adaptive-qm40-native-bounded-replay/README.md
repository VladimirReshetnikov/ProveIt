# Incomplete bounded replay of the 40-variable quartic

Tool session `2241` exited 1. Its author side reported exit 0 for
`AdaptiveQM40Context`, `AdaptiveQM40Zeros`, `AdaptiveQM40Maps`,
`AdaptiveQM40Norm`, `AdaptiveQM40Model` and `AdaptiveQM40Checks`. The
`IPRAQM40Native` child exceeded the enforced 180-second wall-clock timeout;
the child terminated and no native object was observed. The second side did
not start. The first six source snapshots, logs and output objects had the
post-run hashes in `terminal-observation.json`; the workspace source hashes
matched the snapshots when sampled after termination. Compiler logs and the
recorded exception are retained here. The model object is a first-side result,
not a matched replay or a completed iPRA endpoint.

The run used the [bounded driver](../../research/adaptive-qm40-proof/replay_native_bounded.py)
over `/tmp/ipra-qf41-native-peer-ghjxtk23/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, with `-M3000 -j1`
and async elaboration disabled. The driver checked the historical parent
receipt, the candidate literal and direct dependency companions as it advanced;
its final receipt and full direct-guard inventory were not written because the
run failed. Project-transitive, package-transitive and dynamic-loading ancestry
remain inherited, and post-run hashes do not authenticate intermediate states.
During the native child, a Lean worker was observed waiting on a page operation;
that observation does not determine the cause of the timeout or establish that
a longer retry will succeed.
