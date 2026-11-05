# Natural-seed composition helper

This fixed-port-free checked lemma composes `ArithmeticThirteenSeed.strong_index`
and `auxiliary_seed_of`. For model quantities `a,R,b,c`, it assumes `b,c>0`,
`R % 4 = 3`, and `c = ycoord R a`. It returns a positive multiplier and
strong/auxiliary witnesses with the full seed equalities and residue. It does
not yet construct the positive carrier or prove the thirteen-variable endpoint.

The only source change from the [failed first attempt](../thirteen-current2011-natural-seed-draft/README.md)
opens `ArithmeticPellHalfIndex`, which supplies `absdiff`. Actual outer session
49737 exited 0, both nested Lean runs exited 0, and the explicit axiom report
contains only `propext`, `Classical.choice` and `Quot.sound`. The retained
[state](attempt02/state.json) SHA-256 is
`52073f969c3881dd7190c703207b432c6f839600d707a33c9a4fc0d8406d4df9`;
the output object SHA-256 is
`78e8605697fb3cb622288d99b50a32796027622a58f0080b890ff124c30d54c2`.
The source SHA-256 is
`818258c51d3477637a04f4fcb55c9803d4bc0810617c07fde311e37f69b89583`;
the runner SHA-256 is
`99b1f453ee1b0c45e56452c5507a9881431f66bebc3d98190120f48316f62b56`.

The bounded run used the previously checked prelude, generic core and seven
captured predecessors, rechecking sources, objects, direct guards and overlay
links. It used `-M2800`, one worker, a 180-second GNU foreground timeout and
resource prechecks; it did not provide automatic group-RSS/host-memory
stopping or a complete dynamic/package-transitive provider trace.
