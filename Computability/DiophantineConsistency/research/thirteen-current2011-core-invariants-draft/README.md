# Ring-core invariant lemma

This checked helper extracts seven identities from the unchanged `complete`
proof: for an arbitrary model tuple `w` satisfying `w 1 < q w`, it identifies
the ring carrier's `q`, `Y`, `E`, `a`, `c`, `delta` and `rank` with the
corresponding images of model quantities. Its proof copies the earlier local
proof blocks and derives the two bounds on `q` locally. This is one intended
factoring step; no theorem in this packet constructs a thirteen-variable zero
or proves consistency equivalence.

Actual outer session 3181 exited 0, and both nested dependency and Lean
compilation exits were 0. The compilation log is empty. The runner used the
checked generic core, model prelude and seven captured predecessor outputs,
with direct paths, source/object hashes, captured guards and isolated overlay
links checked around the run. The retained [state](attempt01/state.json)
SHA-256 is `b8da4543225cefb27c28573215589f9ed1c2d57aad6e34379d0296096ae4f197`;
the output object SHA-256 is
`3a4a7d8b04de145836ef2ccdfdd6cdf84cfc4c728caf5a4ec64785eb85c1a467`.
The source SHA-256 is
`2e30e6042941ac449c68e1db49cc2aee818098a823e1c2e51a81198671d3e9c8`;
the runner SHA-256 is
`1ed4970e93de6a788448680a52f34169a69552efce30627d28d15e20fa272a9e`.

The run used `-M2800`, one worker, a 180-second GNU foreground timeout and
resource prechecks, without automatic group-RSS or host-memory stopping.
This is not a clean rebuild or complete dynamic/package-transitive ancestry.
