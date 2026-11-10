# Conditional K candidate-rank certificate

This source-only, sixteen-stage proposal replays the audited symbolic
provider and asks Lean to prove a generic rank criterion for the existing
`physicalMap`. A candidate map must send zero to zero, send nonzero positions
to nonzero indices, and have strictly descending actual selector weights at
nonzero positions. The proposed conclusion identifies every candidate position
with the actual physical map of its selected index. The proof uses the
existing weight-order theorem and strict-monotone finite-order rigidity.
It does not check that the external witness satisfies these hypotheses, or
prove complete K, a file binding, or a new consistency equivalence.

This experiment explicitly imports and pins the package's
`Mathlib.Order.WellFounded.olean`; compatibility of this import with the
existing provider remains to be tested by Lean. A source import-graph scan
found no route to the previously conflicting `Mathlib.LinearAlgebra.Matrix.Defs`,
but that scan is not a kernel or complete runtime compatibility proof. The
usual per-child limits and resource guards apply. Author no-Lean preflight
exited 0. Runner SHA-256:
`96aa964781bddd99ee98e217b5d944aa1fbc0c52dc093391c531b59df4f1a7ed`;
manifest SHA-256:
`f7f6cbd78d6228cd64c89e442674a250917422d7e397c31207f611ec8d8e78c0`;
new source SHA-256:
`67c8b7af4dd4347309c04c121f6c8661c44d501337c8701977bd0fa2f3986ec9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-rank-certificate-prelaunch-independent/README.md) passed; import compatibility and the criterion itself remain untested.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-k-rank-certificate-terminal-independent/README.md) passed; the packet is frozen.
