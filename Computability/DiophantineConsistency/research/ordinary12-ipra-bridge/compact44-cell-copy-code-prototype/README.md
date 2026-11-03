# Compact payload-slot inverse

`CompactCellCopyCode.lean` defines a model-internal inverse lookup for the
41 payload positions using a 49-entry table and three anchor cases. On the
author-side word provider, Lean proves that the lookup is Σ₁-definable,
vanishes below the 943 selector positions and at the dummy position, and
maps each actual payload slot to its one-based bit index.

The first bounded attempt failed on numeral subtraction in the model. The
second proved the dummy case but still failed on the slot cases. Their exact
sources and logs are retained. The third attempt first transports standard
subtraction and computes the finite lookup in ℕ before casting it into the
model. Tool session `83330` exited 0 without warnings or `sorryAx`; all four
printed theorem reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The runner's sampled direct dependency and companion records
were unchanged. Its output object and command are recorded in
`observations/attempt03/terminal.json`.

This is an incremental single-author check on the existing word provider,
not a paired replay or a fully authenticated project/package closure. It
does not yet construct the cell word, establish packing or no-carry, bind
retained coefficients, or prove the graph equivalence in iPRA.
