# Model rank-ordinate helper

This checked lemma extracts the maintained first-index argument from the
original completion proof. Given an internal zero of the maintained
natural expression and its positive shift `w`, it proves that the carrier
ordinate `(w 10+w 11)*Y w+w 10` equals `ycoord (rank w) (X w*Y w+Y w)`.
The source reuses the original proof block and adds the explicit conclusion.
It does not construct a thirteen-variable zero or prove an iPRA equivalence.

Actual outer session 35425 exited 0, with both dependency and Lean compilation
exits 0 and an empty compile log. The retained [state](attempt01/state.json)
SHA-256 is `55a477d517914a577be497963800661d31775fd0e81cb14e5f84e700527871cb`;
the output object SHA-256 is
`07fe448925823258ff75480a6bc775eb2b46566654c67906f97a8be59052b6f7`.
The source SHA-256 is
`5809fb104c3c59e973c967d901c58ad6546ae463a225e8ec9a9e080751f620f2`;
the runner SHA-256 is
`9b66effabb0774e1aed963823217f8978f80a1baaa56fb8c64047cbfede58998`.
The guarded isolated overlay rechecked the same generic core, model prelude,
seven predecessors and direct provider paths used for the invariant helper.

The check used `-M2800`, one worker, a 180-second GNU foreground timeout and
resource prechecks. It had no automatic group-RSS or host-memory stopping and
is not a new clean rebuild or complete dynamic/package-transitive load trace.
