# Expanded compact/iPRA rebuild: stage 224 exact-warning retry

The stopped attempt emitted two warnings about included section variables in
`tsing_tagged` and `tsing_members`. Their arguments are supplied later in the
same source, so this retry preserves the source and theorem interfaces. The
exception accepts only the complete, source-pinned warning text after
normalizing the two source paths. It rejects any extra or missing warning,
error, or `sorryAx`; the mutation check rejects added-warning, missing-warning,
and wrong-variable examples. This is a warning exception, not a proof audit.

The runner rechecked the existing 425 source pins, selected overlay, prior
receipts, exact warning baselines and the rejected attempt's dependency guards.
It quarantined the exact rejected object and rebuilt `KLowerQHyp`. Lean exited
0 in 0.819 seconds; source and direct guards were unchanged, the exact-warning
verifier passed, and the wrapper's final guard checks passed at 224/425. The
new object and quarantined rejected object both have SHA-256
`e4012864d6877d2c0591c859c51d87fedf8f44578e6b3552cc9d063531b82671`.

The source, rejected log, normalized warning, verifier, and runner SHA-256s are
respectively `342485cb6294e12d0c52cc747758d447221670ce7dfda096b2f242d7a2974e62`,
`119d46f5ec116c6f36cfd69045c6489a0cec956e8d8a0a6dcbb6f7ca682638f5`,
`8ca0f9a532f94049c3016af5efdfdec0e2ff3c3457f6c0c56efd0d69a65108b0`,
`91647165a79121ba71645006675932d96bda7ebb11a7f5c6506964392a7dc940`, and
`51538b99aad19ba369c9245e2ed65f8550df3ef3f56ab8b2fcfb84da1f0b0e32`.
Raw logs, snapshots, mutation results, and quarantine receipt are retained.

The five-second monitor saw no Lean child and recorded minimum sampled
MemAvailable 18,660,940 KiB. Brief children or overlaps can occur between
samples. This author prefix is not an iPRA endpoint, independent replay, or
complete provider audit; 201 rebuild stages and the compact model-to-iPRA
join remain, and package and dynamic ancestry are not authenticated.
