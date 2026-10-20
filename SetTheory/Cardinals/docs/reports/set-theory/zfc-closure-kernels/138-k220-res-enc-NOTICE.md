# Research supplement attribution and status

Prepared for Vladimir Reshetnikov's ProveIt repository on 2026-10-20.

The baseline is the K221 construction packet at ProveIt commit `c011e44b`.
Its native transition table has SHA-256
`e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc`;
its source site file has SHA-256
`691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9`.

The local finite searches and emitter permutation studies in this supplement
did not establish a smaller machine. The main packet's successful 220-state
construction uses a separately validated source re-encoding and contextual
decoder fold. The finite counterexamples in this supplement explain why two
different apparent 220-state shortcuts were rejected.

Scripts importing the K221 compiler or runtime retain its dependency and
licensing structure. In particular, `scripts/recompile.py` adapts the ProveIt
candidate-k222 stack compiler, and `scripts/spare_usage.py` creates an explicitly
marked adaptation of the K221 symbolic verifier for the optional all-one spare
audit. New files use the MIT No Attribution terms in `LICENSE`; no
repository-wide relicensing is asserted. See the retained notices in
`licenses/` for earlier work and proof boundaries.
