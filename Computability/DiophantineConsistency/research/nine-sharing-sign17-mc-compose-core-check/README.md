# MC aligned digit/byte block composition: generic core

This nineteen-stage source-only attempt replays the independently audited
symbolic MC runs and six finite chunk equalities, then proposes generic
composition lemmas. `aligned` requires eight radix digits and 47 bytes with
equal decoded values. The core proposes `radix^8 = 256^47`, preservation under
repetition/append, and equality of flattened block decodings with any matching
tail. The final shorter three-digit/18-byte block is intended as that tail.

The guard independently pins both audited source/state/outer receipts; it
recompiles both sources in one fresh dependency chain rather than assuming
byte-identical replayed objects. The bounded resources remain unchanged.
No claim yet connects the generic lemma to the actual MC block sequence,
whole-port literal, gzip, JSON or PDF. Author no-Lean preflight exited 0.
Runner SHA-256:
`eea4da8c1245449430688f7529af433fc92d51594627230c2bc0de6c356e8bc1`;
manifest SHA-256:
`0c73c49f71772e8cea09ec1125f9d82328136db23e056335c0a3296f5eeecc17`;
new source SHA-256:
`016b434e20034f3f86520828a9a54967298e87e0a7a2370d9df454fe3f7cd7d9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-compose-core-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-compose-core-terminal-independent/README.md) passed; the packet is frozen.
