# Lean outline status and module plan

**UNCOMPILED.** No Lean executable was available in the delivery environment.
No completed object-iPRA proof of a main complexity theorem is claimed.

The five semantic outline modules contain concrete finite definitions plus
precise pending theorem statements in comments. They contain no admitted
substantive proof bodies or custom axiom declarations. CountingOutline has
two elementary recursion-equation proof bodies, also uncompiled.

| Module | Role |
|---|---|
| CoreOutline | Numeric words, canonical machines, clocks, diagonal descriptions |
| ReductionsOutline | Circuits, CNF, Tseitin, reductions, 2SAT and solver targets |
| SpaceOutline | Finite graphs, reachability, midpoint tables, QBF and games |
| CountingOutline | Finite counts, randomness, advice, lower-bound targets |
| QuantumOutline | Exact signed paths, acceptance numerators and PP branches |
| integration/ObjectTargets | Actual ProveIt syntax for final proof targets |

The report's formalization chapter gives the full completion plan. Complete
finite semantic proofs, build fixed PR syntax and bounded formulas, prove
operational machine/printer bounds, and construct actual `Prf PRAAx` terms.
Higher-order host parameters in helper folds are specialized metatheoretically;
they are not function quantifiers in first-order iPRA.

All theorem group IDs in `CLAIMS.json` map to this common kernel and the
relevant domain module. The source packet does not vendor the full ProveIt
repository.
