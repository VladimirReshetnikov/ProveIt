# Additional encoding research

The accepted consistency machine is `../machines/zfc238.tm`. The two branches here have different statuses.

## Structural witness sharing: proved ordinary interpretation

`stack937/` specializes the inspected 946-bit parent by defining

```text
Target(b) = Q(b)
Next(b,z) = P(b,z)
Mem(b,z) = A(b,z)
```

The complete transformed packet has 937 bits, 14 equations, 215 term nodes, 10 operations and three local variables. `build.py` reconstructs and pins the parent, produces the exact transformed equations and bit stream, runs two independent parsers, rejects all strict truncations and malformed controls, and checks the Boolean transcription. The main report supplies the new unbounded interpretation proof: a free tagged cover of a countable EPSC model, total selectors, finite descriptor descent, and a weighted raw-value recursion with `Q < P < A` dependencies. The reverse interpretation is literal expansion to the parent.

The packet keeps native equality and complete equational substitution. The equality-free restriction applies to the raw membership matrices transferred through the projection. Its consistency-bearing query is the nonderivability of `N(d,d) = d`; every equational theory itself has a one-element model.

This is a nine-bit improvement within this inspected family. It is not a claim of shortest encoding and has no new binary machine state count. A complete equational interpreter, fair certificate enumeration and blank-tape loading remain to be implemented and charged. The inherited raw-EPSC/ZFC calibration and Boolean-basis result remain explicit dependencies.

## Direct reassociation at state 74: rejected

`source_search/rejected_rotation/` contains the exact experimental table, source sites and rejection metadata. This alternate source edit was attempted on the coordinated239 machine. It removes state 74 and has a 238-state syntactic census, but it fails an exact runtime frame at source occurrence 40, zero-guard `CD 1`.

For zero primary values, no additional gap and one spare of value zero, the experiment returns to the dispatcher after 658 steps with the expected head, but the tape differs at cells 13 and 16. `../verification/check_rejected_rotation.py` reproduces the discrepancy. The counterexample invalidates the proposed universal compiler contract; it does not assert that this frame occurs on the blank computation or that every state-74 reduction must fail.

`source_search/source_to_tm.json` retains the observed mapping from source decoder nodes to inherited state labels that motivated this experiment. It is research data, not an additional correctness premise for the accepted machine.
